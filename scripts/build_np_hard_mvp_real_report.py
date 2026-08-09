#!/usr/bin/env python3
"""Build the formal real-model prove_np_hard R-C report."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_real_report import build_np_hard_real_report  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--verified-job-report", type=Path, required=True)
    parser.add_argument("--deletion-audit-report", type=Path, required=True)
    parser.add_argument("--model", required=True)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "Benchmark/Hardness/NP_HARD_MVP_REPORT.json",
    )
    arguments = parser.parse_args()
    report = build_np_hard_real_report(
        root=ROOT,
        verified_job_report=arguments.verified_job_report,
        deletion_audit_report=arguments.deletion_audit_report,
        output_path=arguments.output,
        model_name=arguments.model,
    )
    print(
        json.dumps(
            {"passed": report["passed"], "output": str(arguments.output)},
            ensure_ascii=False,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

