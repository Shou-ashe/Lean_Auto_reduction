#!/usr/bin/env python3
"""Build the formal R-D aggregate from exactly three fresh full-run reports."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_stability import (  # noqa: E402
    build_np_hard_stability_aggregate,
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--run-report", action="append", type=Path, required=True)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "Benchmark/Hardness/NP_HARD_MVP_STABILITY_AGGREGATE.json",
    )
    arguments = parser.parse_args()
    aggregate = build_np_hard_stability_aggregate(
        root=ROOT,
        run_reports=arguments.run_report,
        output_path=arguments.output,
    )
    print(
        json.dumps(
            {
                "passed": aggregate["passed"],
                "output": str(arguments.output),
                "real_api_calls_total": aggregate["real_api_calls_total"],
            },
            ensure_ascii=False,
        )
    )
    return 0 if aggregate["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
