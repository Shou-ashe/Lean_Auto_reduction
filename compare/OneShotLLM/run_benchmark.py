#!/usr/bin/env python3
"""Run the frozen hardness registry with one direct LLM request per case."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_production import (  # noqa: E402
    load_np_hard_production_model_config,
)
from compare.OneShotLLM.benchmark import run_oneshot_llm_benchmark  # noqa: E402


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run the direct one-request LLM hardness benchmark control"
    )
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--lean-timeout", type=int, default=600)
    parser.add_argument(
        "--lane",
        action="append",
        choices=("capability", "frontier", "exact_edge"),
        default=None,
    )
    parser.add_argument("--case", action="append", default=None)
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument(
        "--baseline-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "benchmark-real-20260810-092600",
    )
    parser.add_argument(
        "--archon-report",
        type=Path,
        default=(
            ROOT
            / ".reduction-agent"
            / "benchmark-archon-blackbox-jobs4-20260810-v2"
            / "report.json"
        ),
    )
    parser.add_argument("--no-preflight", action="store_true")
    return parser


def main() -> int:
    arguments = build_parser().parse_args()
    try:
        model = load_np_hard_production_model_config(env_file=arguments.env_file)
        report = run_oneshot_llm_benchmark(
            root=ROOT,
            output_root=arguments.output_root,
            model_config=model,
            jobs=arguments.jobs,
            lean_timeout_seconds=arguments.lean_timeout,
            lanes=arguments.lane,
            selected_case_ids=arguments.case,
            baseline_root=arguments.baseline_root,
            archon_report_path=arguments.archon_report,
            preflight=not arguments.no_preflight,
        )
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as error:
        print(
            json.dumps(
                {
                    "run_valid": False,
                    "failure_code": "oneshot_llm_benchmark_failed",
                    "error": str(error),
                },
                ensure_ascii=False,
            )
        )
        return 2
    print(
        json.dumps(
            {
                "run_valid": report["run_valid"],
                "real_api_called": report["real_api_called"],
                "output_root": report["output_root"],
                "parallelism": report["parallelism"],
                "metrics": report["metrics"],
                "usage": report["usage"],
                "archon_comparison": report["archon_comparison"],
            },
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
