#!/usr/bin/env python3
"""Build a fresh, fingerprint-coherent snapshot set for Stage H."""

from __future__ import annotations

import argparse
import json
import sys
from collections import defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.benchmark import load_benchmark_suite  # noqa: E402
from agent.hardness.lean_runner import run_command  # noqa: E402
from agent.hardness.predicate_input import validate_predicate_input_suite  # noqa: E402


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description="Build fresh Stage H predicate-input observations and catalogs"
    )
    command.add_argument(
        "--suite",
        type=Path,
        default=ROOT / "Benchmark" / "Hardness" / "Suites" / "predicate_input.json",
    )
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "stage-h-snapshots",
    )
    command.add_argument("--lean-timeout", type=int, default=900)
    return command


def _fresh_directory(path: Path) -> None:
    if path.exists():
        if not path.is_dir():
            raise ValueError(f"snapshot root is not a directory: {path}")
        if any(path.iterdir()):
            raise ValueError(
                "snapshot root is not empty; Stage H snapshots must be regenerated fresh"
            )
    path.mkdir(parents=True, exist_ok=True)


def _run_python(arguments: list[str], *, timeout_seconds: int) -> None:
    result = run_command(
        [sys.executable, *arguments],
        cwd=ROOT,
        timeout_seconds=timeout_seconds,
        output_limit=256 * 1024,
    )
    if not result.ok:
        raise RuntimeError(result.stderr or result.stdout or "snapshot command failed")


def main() -> int:
    args = parser().parse_args()
    try:
        suite = load_benchmark_suite(args.suite)
        cases = validate_predicate_input_suite(suite)
        _fresh_directory(args.output_root)
        observations_root = args.output_root / "observations"
        observations_root.mkdir()

        _run_python(
            [
                "scripts/build_problem_catalog_snapshot.py",
                "--output",
                str(args.output_root / "problem-catalog.json"),
                "--connection-output",
                str(args.output_root / "connection-catalog.json"),
                "--target-output",
                str(args.output_root / "hardness-target-catalog.json"),
                "--lean-timeout",
                str(args.lean_timeout),
            ],
            timeout_seconds=args.lean_timeout + 120,
        )

        declarations_by_module: dict[str, list[str]] = defaultdict(list)
        for case in cases:
            declaration = case.effective_input_declaration
            if declaration not in declarations_by_module[case.module]:
                declarations_by_module[case.module].append(declaration)
        for module, declarations in sorted(declarations_by_module.items()):
            module_leaf = module.rsplit(".", 1)[-1]
            output_dir = observations_root / module_leaf
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
            _run_python(command, timeout_seconds=args.lean_timeout + 120)

        summary = {
            "status": "BUILT",
            "suite_id": suite.id,
            "case_count": len(cases),
            "module_count": len(declarations_by_module),
            "output_root": str(args.output_root.resolve()),
            "resume_or_replay_used": False,
        }
        (args.output_root / "snapshot-summary.json").write_text(
            json.dumps(summary, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        print(json.dumps(summary, ensure_ascii=False, sort_keys=True))
        return 0
    except Exception as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
