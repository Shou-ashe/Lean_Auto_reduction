#!/usr/bin/env python3
"""Build fingerprint-bound problem, connection, and hardness-target catalogs."""

from __future__ import annotations

import argparse
import json
import secrets
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.lean_runner import (  # noqa: E402
    PROBLEM_CATALOG_MODULE,
    TARGET_CATALOG_MODULE,
    build_problem_catalog_source,
    run_command,
    sha256_file,
)
from agent.hardness.connection_catalog import (  # noqa: E402
    ConnectionCatalogError,
    parse_connection_catalog,
)
from agent.hardness.problem_catalog import (  # noqa: E402
    ProblemCatalogError,
    parse_problem_catalog,
)
from agent.hardness.hardness_target_catalog import (  # noqa: E402
    HardnessTargetCatalogError,
    parse_hardness_target_catalog,
)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description="Export public PresentedProblem declarations from compiled Lean"
    )
    command.add_argument(
        "--output",
        type=Path,
        default=ROOT / ".reduction-agent" / "problem-catalog.json",
    )
    command.add_argument(
        "--connection-output",
        type=Path,
        default=ROOT / ".reduction-agent" / "connection-catalog.json",
    )
    command.add_argument(
        "--target-output",
        type=Path,
        default=ROOT / ".reduction-agent" / "hardness-target-catalog.json",
    )
    command.add_argument("--lean-timeout", type=int, default=900)
    command.add_argument("--skip-build", action="store_true")
    command.add_argument(
        "--registered-only",
        action="store_true",
        help="export only registry-validated PresentedProblem declarations",
    )
    command.add_argument(
        "--module",
        action="append",
        default=[],
        help=(
            "repeat to export the catalogs in the same Lean environment as "
            "additional input/fixture modules"
        ),
    )
    return command


def main() -> int:
    args = parser().parse_args()
    lean_root = ROOT / "Lean"
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.connection_output.parent.mkdir(parents=True, exist_ok=True)
    args.target_output.parent.mkdir(parents=True, exist_ok=True)

    if not args.skip_build:
        build = run_command(
            [
                "lake",
                "build",
                PROBLEM_CATALOG_MODULE,
                TARGET_CATALOG_MODULE,
                *args.module,
            ],
            cwd=lean_root,
            timeout_seconds=args.lean_timeout,
        )
        if not build.ok:
            print(build.stderr or build.stdout, file=sys.stderr)
            return 1

    nonce = secrets.token_hex(16)
    generated_path = args.output.with_suffix(".lean")
    generated_path.write_text(
        build_problem_catalog_source(
            nonce=nonce,
            additional_modules=tuple(args.module),
            registered_only=args.registered_only,
        ),
        encoding="utf-8",
    )
    command = run_command(
        ["lake", "env", "lean", str(generated_path.resolve())],
        cwd=lean_root,
        timeout_seconds=args.lean_timeout,
        output_limit=16 * 1024 * 1024,
    )
    if not command.ok:
        print(command.stderr or command.stdout, file=sys.stderr)
        return 1

    toolchain = (lean_root / "lean-toolchain").read_text(encoding="utf-8").strip()
    manifest_hash = sha256_file(lean_root / "lake-manifest.json")
    try:
        catalog = parse_problem_catalog(
            stdout=command.stdout,
            stderr=command.stderr,
            nonce=nonce,
            toolchain=toolchain,
            lake_manifest_sha256=manifest_hash,
        )
        connection_catalog = parse_connection_catalog(
            stdout=command.stdout,
            stderr=command.stderr,
            nonce=nonce,
            toolchain=toolchain,
            lake_manifest_sha256=manifest_hash,
        )
        target_catalog = parse_hardness_target_catalog(
            stdout=command.stdout,
            stderr=command.stderr,
            nonce=nonce,
            toolchain=toolchain,
            lake_manifest_sha256=manifest_hash,
        )
    except (
        ProblemCatalogError,
        ConnectionCatalogError,
        HardnessTargetCatalogError,
    ) as error:
        print(str(error), file=sys.stderr)
        return 1
    fingerprints = {
        catalog.registry_fingerprint,
        connection_catalog.registry_fingerprint,
        target_catalog.registry_fingerprint,
    }
    if len(fingerprints) != 1:
        print(
            "problem, connection, and target catalogs have different registry fingerprints",
            file=sys.stderr,
        )
        return 1

    args.output.write_text(
        json.dumps(catalog.to_dict(), ensure_ascii=False, indent=2, sort_keys=True)
        + "\n",
        encoding="utf-8",
    )
    args.connection_output.write_text(
        json.dumps(
            connection_catalog.to_dict(),
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    args.target_output.write_text(
        json.dumps(
            target_catalog.to_dict(),
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    print(
        json.dumps(
            {
                "output": str(args.output),
                "catalog_id": catalog.catalog_id,
                "problem_count": len(catalog.entries),
                "connection_output": str(args.connection_output),
                "connection_catalog_id": connection_catalog.catalog_id,
                "connection_count": len(connection_catalog.entries),
                "target_output": str(args.target_output),
                "target_catalog_id": target_catalog.catalog_id,
                "target_count": len(target_catalog.entries),
                "target_evidence_count": target_catalog.evidence_count,
                "registry_fingerprint": catalog.registry_fingerprint,
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
