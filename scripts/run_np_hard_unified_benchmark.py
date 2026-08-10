#!/usr/bin/env python3
"""Run the unified NP-hard R0/R1 regression benchmark."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_production import (  # noqa: E402
    load_np_hard_production_model_config,
)
from agent.hardness.np_hard_unified_benchmark import (  # noqa: E402
    UnifiedBenchmarkError,
    load_unified_registry,
    load_unified_taxonomy,
    run_unified_benchmark,
    select_unified_cases,
)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description=(
            "Run de-duplicated NP-hard regression logical cases through the "
            "contract lane, one production round, or both"
        )
    )
    parser.add_argument(
        "--registry",
        type=Path,
        default=ROOT / "Gate/NP_HARD_UNIFIED_BENCHMARK_REGISTRY.json",
    )
    parser.add_argument(
        "--taxonomy",
        type=Path,
        default=ROOT / "Gate/BENCHMARK_TAXONOMY.json",
    )
    parser.add_argument(
        "--selector", choices=("contract", "production", "all"), default="all"
    )
    parser.add_argument("--output-root", type=Path)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument("--model", default=None)
    parser.add_argument("--model-timeout", type=int, default=None)
    parser.add_argument("--model-max-tokens", type=int, default=None)
    parser.add_argument("--model-max-retries", type=int, default=None)
    parser.add_argument("--reasoning-effort", default=None)
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument(
        "--list",
        action="store_true",
        help="validate registry/taxonomy and list logical cases without Lean or API calls",
    )
    return parser


def main() -> int:
    parser = build_parser()
    arguments = parser.parse_args()
    try:
        registry = load_unified_registry(arguments.registry, root=ROOT)
        load_unified_taxonomy(arguments.taxonomy, registry=registry)
        selected = select_unified_cases(registry, selector=arguments.selector)
        if arguments.list:
            print(
                json.dumps(
                    {
                        "benchmark_id": registry.benchmark_id,
                        "selector": arguments.selector,
                        "logical_cases": len(selected),
                        "cases": [
                            {
                                "logical_case_id": case.logical_case_id,
                                "tier": case.tier,
                                "selector": case.selector,
                                "execution_backend": case.execution_backend,
                                "source_case_id": case.source_case_id,
                                "capability_weight": case.capability_weight,
                            }
                            for case in selected
                        ],
                    },
                    ensure_ascii=False,
                    sort_keys=True,
                )
            )
            return 0
        if arguments.output_root is None:
            parser.error("--output-root is required unless --list is used")
        deepseek = load_np_hard_production_model_config(
            env_file=arguments.env_file,
            model=arguments.model,
            timeout_seconds=arguments.model_timeout,
            max_tokens=arguments.model_max_tokens,
            max_retries=arguments.model_max_retries,
            reasoning_effort=arguments.reasoning_effort,
        )
        report_path = arguments.report or arguments.output_root / "report.json"
        report = run_unified_benchmark(
            root=ROOT,
            registry_path=arguments.registry,
            taxonomy_path=arguments.taxonomy,
            selector=arguments.selector,
            output_root=arguments.output_root,
            report_path=report_path,
            env_file=arguments.env_file,
            deepseek=deepseek,
            jobs=arguments.jobs,
        )
    except UnifiedBenchmarkError as error:
        print(
            json.dumps(
                {
                    "schema_version": "hardness_np_hard_unified_benchmark_error_v1",
                    "run_valid": False,
                    "error": error.code,
                    "message": error.message,
                },
                ensure_ascii=False,
                sort_keys=True,
            ),
            file=sys.stderr,
        )
        return 2
    print(
        json.dumps(
            {
                "run_valid": report["run_valid"],
                "passed": report["passed"],
                "selector": report["selector"],
                "counts": report["counts"],
                "parallel_execution": report["parallel_execution"],
                "report": str(report_path.resolve()),
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
