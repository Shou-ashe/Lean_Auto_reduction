#!/usr/bin/env python3
"""Prove one exact NP-hardness goal with the general generative agent."""

from __future__ import annotations

import argparse
from dataclasses import replace
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.generative_reduction import (  # noqa: E402
    GeneralNPHardRequest,
    GenerativeReductionConfig,
    GenerativeReductionOrchestrator,
    ModelPolicy,
    ProofStatus,
    SearchBudget,
    Strategy,
)
from agent.hardness.model_client import DeepSeekConfig  # noqa: E402


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="General typed theorem/path reuse and reduction-synthesis NP-hard agent"
    )
    parser.add_argument("--module", required=True, dest="input_module")
    parser.add_argument("--problem", required=True, dest="problem_declaration")
    parser.add_argument(
        "--strategy",
        choices=tuple(item.value for item in Strategy),
        default=Strategy.REUSE_FIRST.value,
    )
    parser.add_argument(
        "--profile",
        choices=("research", "strict-release", "benchmark"),
        default="research",
    )
    parser.add_argument(
        "--model-policy",
        choices=tuple(item.value for item in ModelPolicy),
        default=ModelPolicy.AUTO.value,
    )
    parser.add_argument(
        "--plugins",
        default="",
        help="comma-separated removable plugins: boolean_csp,graph,numeric",
    )
    parser.add_argument(
        "--forbid-declaration",
        action="append",
        default=[],
        help=(
            "fully-qualified Lean declaration that must not occur in the selected "
            "or elaborated transitive proof route; may be repeated"
        ),
    )
    parser.add_argument("--output-dir", type=Path, default=None)
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument("--model", default=None)
    parser.add_argument("--model-timeout", type=int, default=None)
    parser.add_argument("--model-max-tokens", type=int, default=None)
    parser.add_argument("--model-max-retries", type=int, default=None)
    parser.add_argument("--reasoning-effort", default=None)
    parser.add_argument("--lean-timeout", type=int, default=600)
    parser.add_argument("--runtime-prebuilt", action="store_true")

    defaults = SearchBudget()
    for field_name in defaults.__dataclass_fields__:
        parser.add_argument(
            "--" + field_name.replace("_", "-"),
            type=int,
            default=getattr(defaults, field_name),
        )
    return parser


def _model_config(arguments: argparse.Namespace) -> DeepSeekConfig:
    config = DeepSeekConfig.from_environment(env_file=arguments.env_file)
    updates = {
        "model": arguments.model,
        "timeout_seconds": arguments.model_timeout,
        "max_tokens": arguments.model_max_tokens,
        "max_retries": arguments.model_max_retries,
        "reasoning_effort": arguments.reasoning_effort,
    }
    return replace(
        config,
        **{key: value for key, value in updates.items() if value is not None},
    )


def main() -> int:
    arguments = build_parser().parse_args()
    plugins = tuple(
        item.strip() for item in arguments.plugins.split(",") if item.strip()
    )
    request = GeneralNPHardRequest(
        input_module=arguments.input_module,
        problem_declaration=arguments.problem_declaration,
        strategy=Strategy(arguments.strategy),
        profile=arguments.profile,
        model_policy=ModelPolicy(arguments.model_policy),
        plugins=plugins,
        forbidden_declarations=tuple(arguments.forbid_declaration),
    )
    output_dir = arguments.output_dir or (
        ROOT
        / ".reduction-agent"
        / "general-np-hard"
        / request.fingerprint.removeprefix("sha256:")[:24]
    )
    budget = SearchBudget(
        **{
            field_name: getattr(arguments, field_name)
            for field_name in SearchBudget.__dataclass_fields__
        }
    )
    try:
        result = GenerativeReductionOrchestrator(
            GenerativeReductionConfig(
                root=ROOT,
                input_module=arguments.input_module,
                problem_declaration=arguments.problem_declaration,
                output_dir=output_dir,
                strategy=Strategy(arguments.strategy),
                profile=arguments.profile,
                model_policy=ModelPolicy(arguments.model_policy),
                plugins=plugins,
                forbidden_declarations=tuple(arguments.forbid_declaration),
                budget=budget,
                lean_timeout_seconds=arguments.lean_timeout,
                deepseek=_model_config(arguments),
                runtime_prebuilt=arguments.runtime_prebuilt,
            )
        ).run()
    except (OSError, ValueError) as error:
        print(
            json.dumps(
                {
                    "schema_version": "general_np_hard_cli_error_v1",
                    "proof_status": "INPUT_ERROR",
                    "error": str(error),
                },
                ensure_ascii=False,
                indent=2,
                sort_keys=True,
            )
        )
        return 2
    print(json.dumps(result.to_dict(), ensure_ascii=False, indent=2, sort_keys=True))
    if result.proof_status == ProofStatus.VERIFIED:
        return 0
    if result.proof_status in {
        ProofStatus.BLOCKED,
        ProofStatus.INPUT_ERROR,
        ProofStatus.BUDGET_EXHAUSTED,
    }:
        return 2
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
