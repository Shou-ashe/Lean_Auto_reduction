#!/usr/bin/env python3
"""Independently score a stored target-hardness capability run."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_capability import (  # noqa: E402
    NPHardCapabilityError,
    score_np_hard_capability_benchmark,
)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Verify stored evidence and score it with the scorer-only oracle"
    )
    parser.add_argument(
        "--manifest",
        type=Path,
        default=ROOT / "Archive/CAPABILITY_MANIFEST.json",
    )
    parser.add_argument("--run-report", type=Path, required=True)
    parser.add_argument(
        "--report",
        type=Path,
        default=None,
        help="defaults to score.json beside the run report",
    )
    return parser


def main() -> int:
    arguments = build_parser().parse_args()
    score_path = (
        arguments.report.resolve()
        if arguments.report is not None
        else arguments.run_report.resolve().with_name("score.json")
    )
    try:
        score = score_np_hard_capability_benchmark(
            root=ROOT,
            manifest_path=arguments.manifest,
            run_report_path=arguments.run_report,
            score_report_path=score_path,
        )
    except (NPHardCapabilityError, OSError, UnicodeError, ValueError) as error:
        print(
            json.dumps(
                {
                    "score_valid": False,
                    "failure_code": getattr(
                        error, "code", "np_hard_capability_scorer_failed"
                    ),
                    "error": str(error),
                },
                ensure_ascii=False,
            )
        )
        return 2
    print(
        json.dumps(
            {
                "run_valid": score["run_valid"],
                "score_valid": score["score_valid"],
                "score_id": score["score_id"],
                "metrics": score["metrics"],
                "boundary": score["boundary"],
                "report": str(score_path),
            },
            ensure_ascii=False,
        )
    )
    return 0 if score["run_valid"] and score["score_valid"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
