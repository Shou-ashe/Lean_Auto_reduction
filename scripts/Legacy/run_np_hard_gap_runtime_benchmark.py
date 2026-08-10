#!/usr/bin/env python3
"""Run the G-C sequential NP-hard capability runtime qualification."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_gap_benchmark import (  # noqa: E402
    run_np_hard_gap_runtime_benchmark,
)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description="Run G-C NP-hard gap runtime benchmark")
    command.add_argument(
        "--suite",
        type=Path,
        default=ROOT / "Gate" / "Suites" / "np_hard_generalization.json",
    )
    command.add_argument("--output-root", type=Path, required=True)
    command.add_argument(
        "--report",
        type=Path,
        default=ROOT / "Reports" / "NP_HARD_GAP_RUNTIME_REPORT.json",
    )
    return command


def main() -> int:
    arguments = parser().parse_args()
    try:
        report = run_np_hard_gap_runtime_benchmark(
            root=ROOT,
            suite_path=arguments.suite,
            output_root=arguments.output_root,
            report_path=arguments.report,
        )
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(json.dumps({"status": "FAILED", "error": str(error)}, ensure_ascii=False))
        return 1
    metrics = report["metrics"]
    print(
        json.dumps(
            {
                "status": "VERIFIED" if report["passed"] else "FAILED",
                "tasks": metrics["task_count"],
                "accepted_nodes": metrics["accepted_node_count"],
                "fresh_core_rediscoveries": metrics["fresh_core_rediscovery_count"],
                "checkpoint_resumes": metrics["checkpoint_resume_verified_count"],
                "report": str(arguments.report),
            },
            ensure_ascii=False,
        )
    )
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
