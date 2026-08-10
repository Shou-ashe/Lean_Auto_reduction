#!/usr/bin/env python3
"""Run the complete fixed-model Stage O O-B offline qualification."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.stage_o_benchmark import run_stage_o_full_suite  # noqa: E402


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    command.add_argument(
        "--positive-suite",
        type=Path,
        default=ROOT / "Gate/Suites/stage_o_multi_gap.json",
    )
    command.add_argument(
        "--negative-suite",
        type=Path,
        default=ROOT / "Gate/Suites/stage_o_adversarial.json",
    )
    command.add_argument(
        "--microbenchmark",
        type=Path,
        default=ROOT / "Gate/Suites/stage_o_lean_service_microbenchmark.json",
    )
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent/stage-o-offline",
    )
    command.add_argument(
        "--canonical-report",
        type=Path,
        default=ROOT / "Reports/STAGE_O_MULTI_GAP_OFFLINE_REPORT.json",
    )
    command.add_argument("--run-label", default="stage-o-o-b-offline")
    command.add_argument("--jobs", type=int, default=4)
    command.add_argument("--lean-timeout", type=int, default=1200)
    return command


def main() -> int:
    args = parser().parse_args()
    report, code = run_stage_o_full_suite(
        root=ROOT,
        positive_suite_file=args.positive_suite,
        negative_suite_file=args.negative_suite,
        microbenchmark_file=args.microbenchmark,
        output_root=args.output_root,
        jobs=args.jobs,
        real=False,
        qualification="offline",
        run_label=args.run_label,
        deepseek_config=None,
        canonical_report=None,
        lean_timeout_seconds=args.lean_timeout,
    )
    if code == 0:
        args.canonical_report.parent.mkdir(parents=True, exist_ok=True)
        args.canonical_report.write_text(
            (args.output_root / "report.json").read_text(encoding="utf-8"), encoding="utf-8"
        )
    print(json.dumps({"status": report["status"], "report": str(args.output_root / "report.json")}))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
