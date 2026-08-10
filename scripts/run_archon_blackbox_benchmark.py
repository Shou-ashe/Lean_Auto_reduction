#!/usr/bin/env python3
"""Run the frozen hardness registry through source-hidden case-level Archon."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.archon_blackbox_benchmark import (  # noqa: E402
    run_archon_blackbox_benchmark,
)
from agent.hardness.np_hard_production import (  # noqa: E402
    load_np_hard_production_model_config,
)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Run compare/Archon on whole public benchmark cases while hiding "
            "ComplexityReduction source and benchmark-authored proof hints"
        )
    )
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument(
        "--archon-cli",
        type=Path,
        default=ROOT / "compare" / "Archon" / ".venv" / "bin" / "archon",
    )
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--archon-iterations", type=int, default=4)
    parser.add_argument("--archon-tool-rounds", type=int, default=16)
    parser.add_argument("--archon-timeout", type=int, default=7200)
    parser.add_argument("--lean-timeout", type=int, default=600)
    parser.add_argument(
        "--lane",
        action="append",
        choices=("capability", "frontier", "exact_edge"),
        default=None,
    )
    parser.add_argument("--case", action="append", default=None)
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument("--model", default=None)
    parser.add_argument("--model-timeout", type=int, default=None)
    parser.add_argument("--model-max-tokens", type=int, default=None)
    parser.add_argument("--model-max-retries", type=int, default=None)
    parser.add_argument("--reasoning-effort", default=None)
    parser.add_argument(
        "--baseline-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "benchmark-real-20260810-092600",
    )
    parser.add_argument("--no-preflight", action="store_true")
    return parser


def main() -> int:
    arguments = build_parser().parse_args()
    try:
        model = load_np_hard_production_model_config(
            env_file=arguments.env_file,
            model=arguments.model,
            timeout_seconds=arguments.model_timeout,
            max_tokens=arguments.model_max_tokens,
            max_retries=arguments.model_max_retries,
            reasoning_effort=arguments.reasoning_effort,
        )
        report = run_archon_blackbox_benchmark(
            root=ROOT,
            output_root=arguments.output_root,
            archon_cli=arguments.archon_cli,
            model_config=model,
            jobs=arguments.jobs,
            max_iterations=arguments.archon_iterations,
            max_tool_rounds=arguments.archon_tool_rounds,
            loop_timeout_seconds=arguments.archon_timeout,
            lean_timeout_seconds=arguments.lean_timeout,
            lanes=arguments.lane,
            selected_case_ids=arguments.case,
            baseline_root=arguments.baseline_root,
            preflight=not arguments.no_preflight,
        )
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as error:
        print(
            json.dumps(
                {
                    "run_valid": False,
                    "failure_code": "archon_blackbox_benchmark_failed",
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
            },
            ensure_ascii=False,
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
