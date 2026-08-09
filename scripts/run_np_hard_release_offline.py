#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_release_benchmark import run_np_hard_release_offline  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--suite", type=Path, default=ROOT / "Benchmark/Hardness/Suites/np_hard_generalization.json")
    parser.add_argument("--report", type=Path, default=ROOT / "Benchmark/Hardness/NP_HARD_RELEASE_OFFLINE_REPORT.json")
    args = parser.parse_args()
    report = run_np_hard_release_offline(root=ROOT, suite_path=args.suite, output_root=args.output_root, report_path=args.report)
    print(json.dumps({"passed": report["passed"], "metrics": report["metrics"]}))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
