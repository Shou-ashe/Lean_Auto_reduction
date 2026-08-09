#!/usr/bin/env python3
"""Run the formal existing-route native NP-hardness MVP suite."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_benchmark import run_np_hard_mvp_offline  # noqa: E402


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description="Run the NP-hard MVP offline suite")
    command.add_argument(
        "--suite",
        type=Path,
        default=ROOT / "Benchmark" / "Hardness" / "Suites" / "np_hard_mvp.json",
    )
    command.add_argument("--output-root", type=Path, required=True)
    command.add_argument(
        "--report",
        type=Path,
        default=ROOT / "Benchmark" / "Hardness" / "NP_HARD_MVP_OFFLINE_REPORT.json",
    )
    return command


def main() -> int:
    arguments = parser().parse_args()
    try:
        report = run_np_hard_mvp_offline(
            root=ROOT,
            suite_path=arguments.suite,
            output_root=arguments.output_root,
            report_path=arguments.report,
        )
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(json.dumps({"status": "FAILED", "error": str(error)}))
        return 1
    print(
        json.dumps(
            {
                "status": "VERIFIED" if report["passed"] else "FAILED",
                "report": str(arguments.report),
                "cases": report["metrics"]["case_count"],
            }
        )
    )
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
