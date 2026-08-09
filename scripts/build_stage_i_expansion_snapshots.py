#!/usr/bin/env python3
"""Build fresh, Lean-validated snapshots for the Stage-I expansion batch."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.benchmark import load_benchmark_suite  # noqa: E402
from agent.hardness.connection_catalog import (  # noqa: E402
    load_connection_catalog_snapshot,
)
from agent.hardness.hardness_target_catalog import (  # noqa: E402
    load_hardness_target_catalog_snapshot,
)
from agent.hardness.lean_runner import (  # noqa: E402
    assert_generated_source_is_safe,
    run_command,
)
from agent.hardness.frontier_efficiency import (  # noqa: E402
    FRONTIER_EFFICIENCY_SUITE_ID,
    validate_frontier_efficiency_suite,
)
from agent.hardness.problem_catalog import load_problem_catalog_snapshot  # noqa: E402
from agent.hardness.stage_i_expansion import (  # noqa: E402
    STAGE_I_SUITE_ID,
    validate_stage_i_expansion_suite,
)
from agent.hardness.transported_hardness_catalog import (  # noqa: E402
    build_transported_hardness_catalog,
    build_transported_hardness_validation_source,
)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description="Build fresh Stage-I observations and transported-hardness catalogs"
    )
    command.add_argument(
        "--suite",
        type=Path,
        default=ROOT / "Benchmark" / "Hardness" / "Suites" / "stage_i_expansion.json",
    )
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "stage-i-expansion-snapshots",
    )
    command.add_argument("--maximum-transport-atoms", type=int, default=6)
    command.add_argument("--lean-timeout", type=int, default=1200)
    return command


def _fresh_directory(path: Path) -> None:
    if path.exists():
        if not path.is_dir():
            raise ValueError(f"snapshot root is not a directory: {path}")
        if any(path.iterdir()):
            raise ValueError("Stage-I snapshot root must be empty")
    path.mkdir(parents=True, exist_ok=True)


def _run_python(arguments: list[str], *, timeout_seconds: int) -> None:
    result = run_command(
        [sys.executable, *arguments],
        cwd=ROOT,
        timeout_seconds=timeout_seconds,
        output_limit=512 * 1024,
    )
    if not result.ok:
        raise RuntimeError(result.stderr or result.stdout or "snapshot command failed")


def _write_json(path: Path, value: object) -> None:
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _validate_suite(suite: object) -> tuple[object, ...]:
    suite_id = getattr(suite, "id", None)
    if suite_id == STAGE_I_SUITE_ID:
        return validate_stage_i_expansion_suite(suite)  # type: ignore[arg-type,return-value]
    if suite_id == FRONTIER_EFFICIENCY_SUITE_ID:
        return validate_frontier_efficiency_suite(suite)  # type: ignore[arg-type,return-value]
    raise ValueError(f"unsupported expansion snapshot suite: {suite_id}")


def main() -> int:
    args = parser().parse_args()
    try:
        suite = load_benchmark_suite(args.suite)
        cases = _validate_suite(suite)
        _fresh_directory(args.output_root)
        observations_root = args.output_root / "observations"
        observations_root.mkdir()

        problem_path = args.output_root / "problem-catalog.json"
        connection_path = args.output_root / "connection-catalog.json"
        native_target_path = args.output_root / "native-hardness-target-catalog.json"
        transported_target_path = args.output_root / "hardness-target-catalog.json"
        _run_python(
            [
                "scripts/build_problem_catalog_snapshot.py",
                "--output",
                str(problem_path),
                "--connection-output",
                str(connection_path),
                "--target-output",
                str(native_target_path),
                "--lean-timeout",
                str(args.lean_timeout),
            ],
            timeout_seconds=args.lean_timeout + 180,
        )
        problem_catalog = load_problem_catalog_snapshot(problem_path)
        connection_catalog = load_connection_catalog_snapshot(
            connection_path,
            expected_registry_fingerprint=problem_catalog.registry_fingerprint,
        )
        native_target_catalog = load_hardness_target_catalog_snapshot(
            native_target_path,
            expected_registry_fingerprint=problem_catalog.registry_fingerprint,
        )
        transported = build_transported_hardness_catalog(
            problem_catalog=problem_catalog,
            connection_catalog=connection_catalog,
            native_target_catalog=native_target_catalog,
            maximum_transport_atoms=args.maximum_transport_atoms,
        )
        _write_json(transported_target_path, transported.catalog.to_dict())

        validation_source = build_transported_hardness_validation_source(transported)
        assert_generated_source_is_safe(validation_source)
        validation_path = args.output_root / "TransportedHardnessCatalogValidation.lean"
        validation_path.write_text(validation_source, encoding="utf-8")
        validation = run_command(
            ["lake", "env", "lean", str(validation_path.resolve())],
            cwd=ROOT / "Lean",
            timeout_seconds=args.lean_timeout,
            output_limit=256 * 1024,
        )
        if not validation.ok:
            raise RuntimeError(
                validation.stderr
                or validation.stdout
                or "transported hardness validation failed"
            )

        declarations_by_module: dict[str, list[str]] = defaultdict(list)
        for case in cases:
            declaration = case.effective_input_declaration
            if declaration not in declarations_by_module[case.module]:
                declarations_by_module[case.module].append(declaration)
        for module, declarations in sorted(declarations_by_module.items()):
            output_dir = observations_root / module.rsplit(".", 1)[-1]
            command = [
                "scripts/build_input_observation_snapshot.py",
                "--module",
                module,
                "--output-dir",
                str(output_dir),
                "--lean-timeout",
                str(args.lean_timeout),
            ]
            for declaration in declarations:
                command.extend(("--input-declaration", declaration))
            _run_python(command, timeout_seconds=args.lean_timeout + 180)

        summary = {
            "status": "BUILT",
            "suite_id": suite.id,
            "case_count": len(cases),
            "module_count": len(declarations_by_module),
            "output_root": str(args.output_root.resolve()),
            "registry_fingerprint": problem_catalog.registry_fingerprint,
            "problem_catalog_id": problem_catalog.catalog_id,
            "connection_catalog_id": connection_catalog.catalog_id,
            "native_target_catalog_id": native_target_catalog.catalog_id,
            "transported_target_catalog_id": transported.catalog.catalog_id,
            "transported_hardness": transported.to_summary(),
            "validation": {
                "lean_process_count": 1,
                "ok": validation.ok,
                "exit_code": validation.exit_code,
                "duration_seconds": validation.duration_seconds,
                "artifact_path": str(validation_path.resolve()),
                "artifact_sha256": hashlib.sha256(
                    validation_source.encode("utf-8")
                ).hexdigest(),
                "assert_standard_axioms_count": validation_source.count(
                    "assert_standard_axioms"
                ),
            },
            "resume_or_replay_used": False,
        }
        _write_json(args.output_root / "snapshot-summary.json", summary)
        print(json.dumps(summary, ensure_ascii=False, sort_keys=True))
        return 0
    except Exception as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
