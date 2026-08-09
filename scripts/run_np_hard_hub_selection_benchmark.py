#!/usr/bin/env python3
"""Run the G-D deterministic NP-hard hub-selection qualification."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_hub_benchmark import (  # noqa: E402
    run_np_hard_hub_selection_benchmark,
)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description="Run G-D NP-hard hub benchmark")
    command.add_argument(
        "--suite",
        type=Path,
        default=ROOT / "Benchmark" / "Hardness" / "Suites" / "np_hard_hub_selection.json",
    )
    command.add_argument("--output-root", type=Path, required=True)
    command.add_argument(
        "--report",
        type=Path,
        default=ROOT / "Benchmark" / "Hardness" / "NP_HARD_HUB_SELECTION_REPORT.json",
    )
    return command


def main() -> int:
    arguments = parser().parse_args()
    try:
        report = run_np_hard_hub_selection_benchmark(
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
                "cases": report["metrics"]["case_count"],
                "multi_seed_inputs": report["metrics"]["multi_seed_input_count"],
                "ordering_checks": report["metrics"]["stable_ordering_check_count"],
                "report": str(arguments.report),
            },
            ensure_ascii=False,
        )
    )
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
