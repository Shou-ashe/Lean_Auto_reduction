#!/usr/bin/env python3
"""Run the G-A baseline for the dedicated NP-hard generalization suite."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_generalization_benchmark import (  # noqa: E402
    run_np_hard_generalization_baseline,
)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description="Validate the NP-hard generalization inventory and public blockers"
    )
    command.add_argument(
        "--suite",
        type=Path,
        default=ROOT / "Gate" / "Suites" / "np_hard_generalization.json",
    )
    command.add_argument("--output-root", type=Path, required=True)
    command.add_argument(
        "--report",
        type=Path,
        default=(
            ROOT
            / "Benchmark"
            / "Hardness"
            / "NP_HARD_GENERALIZATION_BASELINE_REPORT.json"
        ),
    )
    return command


def main() -> int:
    arguments = parser().parse_args()
    try:
        report = run_np_hard_generalization_baseline(
            root=ROOT,
            suite_path=arguments.suite,
            output_root=arguments.output_root,
            report_path=arguments.report,
        )
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(json.dumps({"status": "FAILED", "error": str(error)}, ensure_ascii=False))
        return 1
    print(
        json.dumps(
            {
                "status": "VERIFIED" if report["passed"] else "FAILED",
                "report": str(arguments.report),
                "cases": report["metrics"]["case_count"],
                "model_calls": report["metrics"]["model_calls"],
            },
            ensure_ascii=False,
        )
    )
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

