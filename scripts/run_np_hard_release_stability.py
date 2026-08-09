#!/usr/bin/env python3
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
from agent.hardness.np_hard_release_benchmark import run_np_hard_release_stability  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--report", type=Path, default=ROOT / "Benchmark/Hardness/NP_HARD_RELEASE_STABILITY_AGGREGATE.json")
    parser.add_argument("--suite", type=Path, default=ROOT / "Benchmark/Hardness/Suites/np_hard_generalization.json")
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument("--model", default="deepseek-chat")
    parser.add_argument("--model-timeout", type=int, default=120)
    parser.add_argument("--model-max-tokens", type=int, default=3000)
    parser.add_argument("--model-max-retries", type=int, default=0)
    args = parser.parse_args()
    config = replace(
        DeepSeekConfig.from_environment(env_file=args.env_file),
        model=args.model,
        timeout_seconds=args.model_timeout,
        max_tokens=args.model_max_tokens,
        max_retries=args.model_max_retries,
    )
    report = run_np_hard_release_stability(
        root=ROOT,
        suite_path=args.suite,
        output_root=args.output_root,
        report_path=args.report,
        deepseek=config,
        round_count=3,
    )
    print(json.dumps({"passed": report["passed"], "metrics": report["metrics"]}))
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
