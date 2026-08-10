#!/usr/bin/env python3
"""Run the fresh 8-case Stage-M suite with real DeepSeek API calls."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import replace
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.model_client import DEFAULT_MODEL, DeepSeekConfig  # noqa: E402
from scripts.typed_authoring_benchmark import DEFAULT_SUITE, run_full_suite  # noqa: E402


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    command.add_argument("--suite", type=Path, default=DEFAULT_SUITE)
    command.add_argument("--env-file", type=Path, default=ROOT / ".env")
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "deepseek-typed-authoring-full",
    )
    command.add_argument(
        "--canonical-report",
        type=Path,
        default=ROOT / "Reports" / "TYPED_AUTHORING_REPORT.json",
    )
    command.add_argument("--jobs", type=int, default=4)
    command.add_argument("--lean-timeout", type=int, default=1800)
    command.add_argument("--model-timeout", type=int, default=300)
    command.add_argument("--model-max-tokens", type=int, default=8192)
    command.add_argument("--model", default=DEFAULT_MODEL)
    command.add_argument("--run-label", default="stage-m-typed-authoring-full-real-deepseek")
    return command


def main() -> int:
    args = parser().parse_args()
    config = DeepSeekConfig.from_environment(env_file=args.env_file)
    config = replace(
        config,
        model=args.model,
        timeout_seconds=args.model_timeout,
        max_tokens=args.model_max_tokens,
    )
    report, code = run_full_suite(
        suite_file=args.suite,
        output_root=args.output_root,
        jobs=args.jobs,
        real=True,
        deepseek_config=config,
        canonical_report=args.canonical_report,
        lean_timeout_seconds=args.lean_timeout,
        run_label=args.run_label,
    )
    print(json.dumps({"status": report["status"], "report": str(args.output_root / "report.json")}))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
