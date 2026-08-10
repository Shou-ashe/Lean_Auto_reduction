#!/usr/bin/env python3
"""Run and independently score the answer-free exact-edge benchmark."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.authoring import MODEL_AUTO_MODE, MODEL_REQUIRED_MODE  # noqa: E402
from agent.hardness.model_client import DeepSeekConfig  # noqa: E402
from agent.hardness.np_hard_production import (  # noqa: E402
    load_np_hard_production_model_config,
)
from agent.hardness.np_hard_exact_edge import (  # noqa: E402
    ExactEdgeContractError,
    combine_exact_edge_suites,
    load_exact_edge_manifest,
    load_exact_edge_oracle,
    run_exact_reduction_edge_benchmark,
    score_exact_reduction_edge_run,
    write_exact_edge_report,
)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description="Run exact CertifiedReduction source-to-target capability cases"
    )
    command.add_argument(
        "--manifest",
        type=Path,
        default=ROOT / "Benchmark/Hardness/EXACT_REDUCTION_EDGE_MANIFEST.json",
    )
    command.add_argument(
        "--oracle",
        type=Path,
        default=ROOT / "Evaluation/exact_reduction_edge_oracle_v1.json",
        help="loaded only after the production run completes",
    )
    command.add_argument(
        "--split",
        action="append",
        choices=("dev", "validation", "heldout"),
        help="repeat to select splits; defaults to all frozen splits",
    )
    command.add_argument("--output-root", type=Path, required=True)
    command.add_argument("--report", type=Path, default=None)
    command.add_argument("--score-report", type=Path, default=None)
    command.add_argument("--jobs", type=int, default=None)
    command.add_argument("--env-file", type=Path, default=ROOT / ".env")
    command.add_argument("--model", default="deepseek-v4-flash")
    command.add_argument("--model-timeout", type=int, default=300)
    command.add_argument("--model-max-tokens", type=int, default=16000)
    command.add_argument("--model-max-retries", type=int, default=0)
    command.add_argument("--reasoning-effort", default="low")
    command.add_argument(
        "--no-score",
        action="store_true",
        help="development-only: write the answer-free run without loading the oracle",
    )
    return command


def _model_configuration(
    *, arguments: argparse.Namespace, authoring_required: bool
) -> DeepSeekConfig | None:
    if not authoring_required:
        return None
    if arguments.model_timeout <= 0 or arguments.model_max_tokens <= 0:
        raise ValueError("model timeout and max tokens must be positive")
    if arguments.model_max_retries < 0:
        raise ValueError("model max retries must be nonnegative")
    return load_np_hard_production_model_config(
        env_file=arguments.env_file,
        model=arguments.model,
        timeout_seconds=arguments.model_timeout,
        max_tokens=arguments.model_max_tokens,
        max_retries=arguments.model_max_retries,
        reasoning_effort=arguments.reasoning_effort,
    )


def main() -> int:
    arguments = parser().parse_args()
    try:
        manifest = load_exact_edge_manifest(arguments.manifest)
        selected_names = tuple(arguments.split or ("dev", "validation", "heldout"))
        selected_suites = tuple(manifest.suites[name] for name in selected_names)
        suite = (
            selected_suites[0]
            if len(selected_suites) == 1
            else combine_exact_edge_suites(selected_suites)
        )
        selected_profiles = {
            case.budget_profile for case in suite.cases
        }
        authoring_required = any(
            manifest.budget_profiles[name].authoring_mode
            in {MODEL_AUTO_MODE, MODEL_REQUIRED_MODE}
            for name in selected_profiles
        )
        deepseek = _model_configuration(
            arguments=arguments, authoring_required=authoring_required
        )
        report = run_exact_reduction_edge_benchmark(
            root=ROOT,
            suite=suite,
            budget_profiles=manifest.budget_profiles,
            output_root=arguments.output_root,
            deepseek=deepseek,
            jobs=arguments.jobs or manifest.max_jobs,
            isolate_workspace=manifest.isolate_workspace,
            runtime_prebuilt=manifest.runtime_prebuilt,
            manifest_sha256=manifest.sha256,
            expected_oracle_sha256=manifest.oracle_sha256,
        )
        if arguments.report is not None:
            write_exact_edge_report(arguments.report, report)
        score = None
        if not arguments.no_score:
            # Deliberately load the scorer-only oracle only after every production
            # case and prompt has finished.
            oracle = load_exact_edge_oracle(arguments.oracle)
            score = score_exact_reduction_edge_run(
                manifest=manifest,
                suite=suite,
                oracle=oracle,
                run_report=report,
            )
            score_path = arguments.score_report or (
                arguments.output_root.resolve() / "score.json"
            )
            write_exact_edge_report(score_path, score)
    except (OSError, UnicodeError, json.JSONDecodeError, ValueError, ExactEdgeContractError) as error:
        print(
            json.dumps(
                {
                    "run_valid": False,
                    "failure_code": getattr(error, "code", "exact_edge_benchmark_failed"),
                    "error": str(error),
                },
                ensure_ascii=False,
            )
        )
        return 1
    payload = {
        "run_valid": report["run_valid"],
        "metrics": report["metrics"],
        "parallel_execution": report["parallel_execution"],
    }
    if score is not None:
        payload["scorer_run_valid"] = score["run_valid"]
        payload["scorecard"] = score["scorecard"]
    print(json.dumps(payload, ensure_ascii=False))
    return 0 if report["run_valid"] and (score is None or score["run_valid"]) else 1


if __name__ == "__main__":
    raise SystemExit(main())
