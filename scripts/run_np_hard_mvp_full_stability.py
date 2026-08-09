#!/usr/bin/env python3
"""Run one fresh, real-DeepSeek NP-hard MVP full benchmark."""

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
from agent.hardness.np_hard_stability import (  # noqa: E402
    run_np_hard_mvp_full_stability,
)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument(
        "--suite",
        type=Path,
        default=ROOT / "Benchmark/Hardness/Suites/np_hard_mvp.json",
    )
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument("--model", default="deepseek-chat")
    parser.add_argument("--model-timeout", type=int, default=60)
    parser.add_argument("--model-max-tokens", type=int, default=3000)
    parser.add_argument("--model-max-retries", type=int, default=0)
    parser.add_argument("--authoring-attempts", type=int, default=4)
    parser.add_argument("--lean-timeout", type=int, default=600)
    arguments = parser.parse_args()
    config = DeepSeekConfig.from_environment(env_file=arguments.env_file)
    config = replace(
        config,
        model=arguments.model,
        timeout_seconds=arguments.model_timeout,
        max_tokens=arguments.model_max_tokens,
        max_retries=arguments.model_max_retries,
    )
    report = run_np_hard_mvp_full_stability(
        root=ROOT,
        suite_path=arguments.suite,
        output_root=arguments.output_root,
        report_path=arguments.report,
        deepseek=config,
        authoring_attempts=arguments.authoring_attempts,
        lean_timeout_seconds=arguments.lean_timeout,
    )
    print(
        json.dumps(
            {
                "passed": report["passed"],
                "report": str(arguments.report),
                "real_api_calls": report["metrics"]["real_api_calls"],
            },
            ensure_ascii=False,
        )
    )
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
