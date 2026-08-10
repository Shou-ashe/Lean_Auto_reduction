#!/usr/bin/env python3
"""Build fresh, fingerprint-bound Stage-L observations and Core capability views."""

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
from agent.hardness.connection_catalog import load_connection_catalog_snapshot  # noqa: E402
from agent.hardness.core_capability_catalog import (  # noqa: E402
    build_core_capability_validation_source,
    build_core_native_evidence_catalog,
    build_core_reduction_catalog,
)
from agent.hardness.core_generalization import (  # noqa: E402
    validate_core_generalization_suite,
)
from agent.hardness.hardness_target_catalog import (  # noqa: E402
    load_hardness_target_catalog_snapshot,
)
from agent.hardness.lean_runner import (  # noqa: E402
    assert_generated_source_is_safe,
    run_command,
)
from agent.hardness.problem_catalog import (  # noqa: E402
    ProblemCatalog,
    load_problem_catalog_snapshot,
)
from agent.hardness.transported_hardness_catalog import (  # noqa: E402
    build_transported_hardness_catalog,
    build_transported_hardness_validation_source,
)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description="Build fresh Stage-L Core generalization snapshots"
    )
    command.add_argument(
        "--suite",
        type=Path,
        default=ROOT / "Gate" / "Suites" / "core_generalization.json",
    )
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "core-generalization-snapshots",
    )
    command.add_argument("--maximum-transport-atoms", type=int, default=6)
    command.add_argument("--lean-timeout", type=int, default=1200)
    return command


def _fresh_directory(path: Path) -> None:
    if path.exists():
        if not path.is_dir():
            raise ValueError(f"snapshot root is not a directory: {path}")
        if any(path.iterdir()):
            raise ValueError("Stage-L snapshot root must be empty")
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


def _run_validation(source: str, path: Path, *, lean_timeout: int) -> object:
    assert_generated_source_is_safe(source)
    path.write_text(source, encoding="utf-8")
    result = run_command(
        ["lake", "env", "lean", str(path.resolve())],
        cwd=ROOT / "Lean",
        timeout_seconds=lean_timeout,
        output_limit=256 * 1024,
    )
    if not result.ok:
        raise RuntimeError(result.stderr or result.stdout or f"validation failed: {path}")
    return result


def main() -> int:
    args = parser().parse_args()
    try:
        suite = load_benchmark_suite(args.suite)
        cases = validate_core_generalization_suite(suite)
        _fresh_directory(args.output_root)
        observations_root = args.output_root / "observations"
        observations_root.mkdir()

        problem_path = args.output_root / "problem-catalog.json"
        internal_problem_path = args.output_root / "problem-catalog-internal.json"
        connection_path = args.output_root / "connection-catalog.json"
        native_target_path = args.output_root / "native-hardness-target-catalog.json"
        transported_target_path = args.output_root / "hardness-target-catalog.json"
        native_evidence_path = args.output_root / "native-evidence-catalog.json"
        core_reduction_path = args.output_root / "core-reduction-catalog.json"

        suite_modules = tuple(sorted({case.module for case in cases}))

        _run_python(
            [
                "scripts/build_problem_catalog_snapshot.py",
                "--output",
                str(internal_problem_path),
                "--connection-output",
                str(connection_path),
                "--target-output",
                str(native_target_path),
                "--lean-timeout",
                str(args.lean_timeout),
                *(
                    argument
                    for module in suite_modules
                    for argument in ("--module", module)
                ),
            ],
            timeout_seconds=args.lean_timeout + 180,
        )
        internal_problem_catalog = load_problem_catalog_snapshot(
            internal_problem_path
        )
        problem_catalog = ProblemCatalog(
            registry_fingerprint=internal_problem_catalog.registry_fingerprint,
            entries=tuple(
                entry
                for entry in internal_problem_catalog.entries
                if entry.registered
            ),
            toolchain=internal_problem_catalog.toolchain,
            lake_manifest_sha256=internal_problem_catalog.lake_manifest_sha256,
        )
        if not problem_catalog.entries:
            raise ValueError("Stage-L registered problem view is empty")
        _write_json(problem_path, problem_catalog.to_dict())
        connection_catalog = load_connection_catalog_snapshot(
            connection_path,
            expected_registry_fingerprint=internal_problem_catalog.registry_fingerprint,
        )
        native_target_catalog = load_hardness_target_catalog_snapshot(
            native_target_path,
            expected_registry_fingerprint=internal_problem_catalog.registry_fingerprint,
        )

        transported = build_transported_hardness_catalog(
            problem_catalog=internal_problem_catalog,
            connection_catalog=connection_catalog,
            native_target_catalog=native_target_catalog,
            maximum_transport_atoms=args.maximum_transport_atoms,
        )
        _write_json(transported_target_path, transported.catalog.to_dict())

        native_evidence = build_core_native_evidence_catalog(native_target_catalog)
        core_reductions = build_core_reduction_catalog(
            problem_catalog=internal_problem_catalog,
            connection_catalog=connection_catalog,
            evidence_catalog=native_evidence,
        )
        _write_json(native_evidence_path, native_evidence.to_dict())
        _write_json(core_reduction_path, core_reductions.to_dict())

        transported_source = build_transported_hardness_validation_source(
            transported,
            additional_modules=suite_modules,
        )
        transported_path = args.output_root / "TransportedHardnessCatalogValidation.lean"
        transported_validation = _run_validation(
            transported_source,
            transported_path,
            lean_timeout=args.lean_timeout,
        )
        capability_source = build_core_capability_validation_source(
            evidence_catalog=native_evidence,
            reduction_catalog=core_reductions,
            additional_modules=suite_modules,
        )
        capability_path = args.output_root / "CoreCapabilityCatalogValidation.lean"
        capability_validation = _run_validation(
            capability_source,
            capability_path,
            lean_timeout=args.lean_timeout,
        )

        declarations_by_module: dict[str, list[str]] = defaultdict(list)
        for case in cases:
            declarations = [case.effective_input_declaration]
            if case.target is not None:
                declarations.append(case.target)
            for declaration in declarations:
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

        def validation_record(result: object, source: str, path: Path) -> dict[str, object]:
            return {
                "ok": bool(getattr(result, "ok")),
                "exit_code": int(getattr(result, "exit_code")),
                "duration_seconds": float(getattr(result, "duration_seconds")),
                "artifact_path": str(path.resolve()),
                "artifact_sha256": hashlib.sha256(source.encode("utf-8")).hexdigest(),
                "assert_standard_axioms_count": source.count("assert_standard_axioms"),
            }

        summary = {
            "status": "BUILT",
            "suite_id": suite.id,
            "case_count": len(cases),
            "module_count": len(declarations_by_module),
            "catalog_environment_modules": list(suite_modules),
            "problem_catalog_registered_only": True,
            "internal_problem_catalog_id": internal_problem_catalog.catalog_id,
            "internal_problem_count": len(internal_problem_catalog.entries),
            "model_problem_count": len(problem_catalog.entries),
            "observation_declaration_count": sum(
                len(declarations) for declarations in declarations_by_module.values()
            ),
            "output_root": str(args.output_root.resolve()),
            "registry_fingerprint": problem_catalog.registry_fingerprint,
            "problem_catalog_id": problem_catalog.catalog_id,
            "connection_catalog_id": connection_catalog.catalog_id,
            "native_target_catalog_id": native_target_catalog.catalog_id,
            "transported_target_catalog_id": transported.catalog.catalog_id,
            "native_evidence_catalog_id": native_evidence.catalog_id,
            "core_reduction_catalog_id": core_reductions.catalog_id,
            "native_evidence_counts": native_evidence.to_dict()["evidence_kind_counts"],
            "cook_levin_root_count": sum(
                entry.is_cook_levin_root for entry in core_reductions.entries
            ),
            "transported_hardness": transported.to_summary(),
            "validation": {
                "lean_process_count": 2,
                "transported_hardness": validation_record(
                    transported_validation, transported_source, transported_path
                ),
                "core_capabilities": validation_record(
                    capability_validation, capability_source, capability_path
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
