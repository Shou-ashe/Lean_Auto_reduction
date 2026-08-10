#!/usr/bin/env python3
"""Independently score an H-K.3 publication reuse run."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_publication_reuse import (  # noqa: E402
    NPHardPublicationReuseError,
    score_publication_reuse_benchmark,
)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=ROOT / "Publications/PUBLICATION_REUSE_MANIFEST_V3.json",
    )
    parser.add_argument("--run-report", type=Path, required=True)
    parser.add_argument("--report", type=Path, default=None)
    args = parser.parse_args(argv)
    output = args.report or args.run_report.with_name("score.json")
    try:
        score = score_publication_reuse_benchmark(
            root=ROOT,
            manifest_path=args.manifest,
            run_report_path=args.run_report,
            score_report_path=output,
        )
    except (NPHardPublicationReuseError, OSError, UnicodeError, ValueError) as error:
        print(
            json.dumps(
                {
                    "score_valid": False,
                    "failure_code": getattr(error, "code", "reuse_scorer_failed"),
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
                "reuse_scorecard": score["reuse_scorecard"],
                "report": str(output.resolve()),
            },
            ensure_ascii=False,
        )
    )
    return 0 if score["run_valid"] and score["score_valid"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
