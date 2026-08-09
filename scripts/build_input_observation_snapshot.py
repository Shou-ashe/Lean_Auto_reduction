#!/usr/bin/env python3
"""Build fingerprint-bound observations of compiled Lean input declarations."""

from __future__ import annotations

import argparse
import json
import secrets
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.input_observation import (  # noqa: E402
    InputObservationError,
    parse_input_observation,
)
from agent.hardness.lean_runner import (  # noqa: E402
    build_input_observation_batch_source,
    build_module_command,
    module_file,
    run_command,
    sha256_file,
)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description="Inspect Lean input declarations without selecting a reduction route"
    )
    command.add_argument("--module", required=True)
    command.add_argument(
        "--input-declaration",
        action="append",
        required=True,
        help="repeat to inspect several declarations in one Lean process",
    )
    command.add_argument(
        "--output",
        type=Path,
        default=None,
        help="single-observation JSON path",
    )
    command.add_argument(
        "--output-dir",
        type=Path,
        default=None,
        help="directory for one JSON file per declaration in batch mode",
    )
    command.add_argument("--lean-timeout", type=int, default=600)
    command.add_argument("--skip-build", action="store_true")
    command.add_argument("--require-supported", action="store_true")
    return command


def main() -> int:
    args = parser().parse_args()
    lean_root = ROOT / "Lean"
    input_path = module_file(lean_root, args.module)
    declarations = tuple(args.input_declaration)
    if len(declarations) > 1 and args.output_dir is None:
        print("--output-dir is required for more than one input declaration", file=sys.stderr)
        return 2
    if args.output is not None and args.output_dir is not None:
        print("--output and --output-dir cannot be used together", file=sys.stderr)
        return 2
    if len(declarations) == 1 and args.output_dir is None:
        output_paths = (
            args.output or ROOT / ".reduction-agent" / "input-observation.json",
        )
    else:
        output_dir = args.output_dir
        assert output_dir is not None
        leaf_names = tuple(declaration.rsplit(".", 1)[-1] for declaration in declarations)
        if len(set(leaf_names)) != len(leaf_names):
            print(
                "batch declarations must have distinct final names for deterministic output files",
                file=sys.stderr,
            )
            return 2
        output_paths = tuple(output_dir / f"{name}.json" for name in leaf_names)
    for output_path in output_paths:
        output_path.parent.mkdir(parents=True, exist_ok=True)

    if not args.skip_build:
        build = run_command(
            build_module_command([args.module]),
            cwd=lean_root,
            timeout_seconds=args.lean_timeout,
        )
        if not build.ok:
            print(build.stderr or build.stdout, file=sys.stderr)
            return 1

    nonces = tuple(secrets.token_hex(16) for _ in declarations)
    generated_source = build_input_observation_batch_source(
        input_module=args.module,
        requests=tuple(zip(nonces, declarations, strict=True)),
    )
    if len(output_paths) == 1:
        generated_path = output_paths[0].with_suffix(".lean")
    else:
        generated_path = output_paths[0].parent / "InputObservationBatch.lean"
    generated_path.write_text(generated_source, encoding="utf-8")
    command = run_command(
        ["lake", "env", "lean", str(generated_path.resolve())],
        cwd=lean_root,
        timeout_seconds=args.lean_timeout,
        output_limit=max(16000, len(declarations) * 8192),
    )
    if not command.ok:
        print(command.stderr or command.stdout, file=sys.stderr)
        return 1

    input_module_sha256 = sha256_file(input_path)
    toolchain = (lean_root / "lean-toolchain").read_text(encoding="utf-8").strip()
    lake_manifest_sha256 = sha256_file(lean_root / "lake-manifest.json")
    observations = []
    try:
        for nonce in nonces:
            observations.append(
                parse_input_observation(
                    stdout=command.stdout,
                    stderr=command.stderr,
                    nonce=nonce,
                    input_module=args.module,
                    input_module_sha256=input_module_sha256,
                    toolchain=toolchain,
                    lake_manifest_sha256=lake_manifest_sha256,
                )
            )
    except InputObservationError as error:
        print(str(error), file=sys.stderr)
        return 1

    summaries = []
    for output_path, observation in zip(output_paths, observations, strict=True):
        output_path.write_text(
            json.dumps(observation.to_dict(), ensure_ascii=False, indent=2, sort_keys=True)
            + "\n",
            encoding="utf-8",
        )
        summaries.append(
            {
                "output": str(output_path),
                "input_declaration": observation.input_declaration,
                "input_kind": observation.input_kind,
                "supported": observation.supported,
                "failure_code": observation.failure_code,
                "observation_id": observation.observation_id,
            }
        )
    print(
        json.dumps(
            summaries[0] if len(summaries) == 1 else summaries,
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    if args.require_supported and any(
        not observation.supported for observation in observations
    ):
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
