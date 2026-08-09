#!/usr/bin/env python3
"""Run the G-E input-normalization and model-auto qualification."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_entrypoint_benchmark import (  # noqa: E402
    run_np_hard_entrypoint_benchmark,
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument(
        "--suite",
        type=Path,
        default=ROOT / "Benchmark/Hardness/Suites/np_hard_generalization.json",
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=ROOT / "Benchmark/Hardness/NP_HARD_ENTRYPOINT_REPORT.json",
    )
    arguments = parser.parse_args()
    report = run_np_hard_entrypoint_benchmark(
        root=ROOT,
        suite_path=arguments.suite,
        output_root=arguments.output_root,
        report_path=arguments.report,
    )
    print(json.dumps({"passed": report["passed"], "metrics": report["metrics"]}))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
