#!/usr/bin/env python3
"""Run a fresh complete Stage O suite with real DeepSeek API calls."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import replace
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.model_client import DeepSeekConfig  # noqa: E402
from agent.hardness.stage_o_benchmark import run_stage_o_full_suite  # noqa: E402


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    command.add_argument(
        "--positive-suite",
        type=Path,
        default=ROOT / "Benchmark/Hardness/Suites/stage_o_multi_gap.json",
    )
    command.add_argument(
        "--negative-suite",
        type=Path,
        default=ROOT / "Benchmark/Hardness/Suites/stage_o_adversarial.json",
    )
    command.add_argument(
        "--microbenchmark",
        type=Path,
        default=ROOT / "Benchmark/Hardness/Suites/stage_o_lean_service_microbenchmark.json",
    )
    command.add_argument("--output-root", type=Path, required=True)
    command.add_argument("--canonical-report", type=Path)
    command.add_argument("--qualification", choices=("o-b", "official", "stability"), required=True)
    command.add_argument("--run-label", required=True)
    command.add_argument("--env-file", type=Path, default=ROOT / ".env")
    command.add_argument("--jobs", type=int, default=4)
    command.add_argument("--lean-timeout", type=int, default=1200)
    command.add_argument("--model-timeout", type=int, default=300)
    command.add_argument("--model-max-tokens", type=int, default=4096)
    command.add_argument("--model-max-retries", type=int, default=2)
    return command


def main() -> int:
    args = parser().parse_args()
    config = DeepSeekConfig.from_environment(env_file=args.env_file)
    config = replace(
        config,
        timeout_seconds=args.model_timeout,
        max_tokens=args.model_max_tokens,
        max_retries=args.model_max_retries,
    )
    report, code = run_stage_o_full_suite(
        root=ROOT,
        positive_suite_file=args.positive_suite,
        negative_suite_file=args.negative_suite,
        microbenchmark_file=args.microbenchmark,
        output_root=args.output_root,
        jobs=args.jobs,
        real=True,
        qualification=args.qualification,
        run_label=args.run_label,
        deepseek_config=config,
        canonical_report=args.canonical_report,
        lean_timeout_seconds=args.lean_timeout,
    )
    print(
        json.dumps(
            {
                "status": report["status"],
                "report": str(args.output_root / "report.json"),
                "real_model_call_count": report.get("summary", {}).get("real_model_call_count", 0),
            }
        )
    )
    return code


if __name__ == "__main__":
    raise SystemExit(main())
