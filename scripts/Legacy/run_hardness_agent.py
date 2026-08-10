#!/usr/bin/env python3
"""Run the ComplexityReduction hardness agent."""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import replace
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.model_client import DeepSeekConfig  # noqa: E402
from agent.hardness.runner import HardnessAgent, HardnessAgentConfig  # noqa: E402
from agent.hardness.np_hard import NPHardAgentConfigV1, NPHardAgentV1  # noqa: E402
from agent.hardness.catalog import CATALOG_MODES, FULL_CATALOG  # noqa: E402
from agent.hardness.authoring import (  # noqa: E402
    DETERMINISTIC_TEMPLATE_MODE,
    DISABLED_MODE,
    MODEL_AUTO_MODE,
    MODEL_MODES,
    MODEL_REQUIRED_MODE,
)


OBJECTIVES = {
    "reduce-to": "reduce_to",
    "reduce-to-known-np": "reduce_to_known_np",
    "prove-in-np": "prove_in_np",
    "prove-np-complete": "prove_np_complete",
    "prove-np-hard": "prove_np_hard",
}


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description="Build a Lean-checked hardness artifact")
    command.add_argument("--module", required=True, help="importable input module")
    command.add_argument(
        "--source",
        "--problem",
        dest="source",
        required=True,
        help="fully-qualified PresentedProblem declaration or registered stable ID",
    )
    command.add_argument("--membership", help="fully-qualified exact NativeTMInNP declaration")
    command.add_argument("--target", help="fully-qualified validated PresentedProblem declaration")
    command.add_argument(
        "--objective", choices=tuple(OBJECTIVES), default="reduce-to-known-np"
    )
    command.add_argument(
        "--planner",
        choices=("deterministic",),
        default="deterministic",
        help="validated route search is always deterministic",
    )
    command.add_argument(
        "--catalog-mode",
        choices=tuple(sorted(CATALOG_MODES)),
        default=FULL_CATALOG,
        help="validated edge view: full, flat end-to-end API, or reusable IR components",
    )
    command.add_argument("--output-dir", type=Path)
    command.add_argument("--env-file", type=Path, default=ROOT / ".env")
    command.add_argument("--lean-timeout", type=int, default=300)
    command.add_argument(
        "--authoring",
        choices=(
            DISABLED_MODE,
            DETERMINISTIC_TEMPLATE_MODE,
            MODEL_AUTO_MODE,
            MODEL_REQUIRED_MODE,
        ),
        default=None,
        help=(
            "bounded job-local authoring policy; defaults to disabled for flat/IR "
            "catalog studies and deterministic-template for the full catalog"
        ),
    )
    command.add_argument("--authoring-attempts", type=int, default=4)
    command.add_argument("--model-timeout", type=int, default=None)
    command.add_argument("--model-max-tokens", type=int, default=None)
    command.add_argument(
        "--resume",
        action="store_true",
        help="revalidate an existing job; missing or changed candidates fail closed",
    )
    return command


def main() -> int:
    arguments = parser().parse_args()
    np_hard_objective = OBJECTIVES[arguments.objective] == "prove_np_hard"
    if np_hard_objective and arguments.membership is not None:
        parser().error("prove-np-hard rejects --membership; target membership is not required")
    if np_hard_objective and arguments.target is not None:
        parser().error("prove-np-hard rejects --target; --source is the exact hardness target")
    if np_hard_objective and arguments.catalog_mode != FULL_CATALOG:
        parser().error("prove-np-hard currently requires --catalog-mode full")
    authoring_mode = arguments.authoring or (
        DISABLED_MODE
        if np_hard_objective or arguments.catalog_mode != FULL_CATALOG
        else DETERMINISTIC_TEMPLATE_MODE
    )
    if np_hard_objective and authoring_mode == DETERMINISTIC_TEMPLATE_MODE:
        parser().error(
            "prove-np-hard rejects deterministic-template; use disabled, model-auto, or model-required"
        )
    deepseek = None
    if authoring_mode in MODEL_MODES:
        deepseek = DeepSeekConfig.from_environment(env_file=arguments.env_file)
        if arguments.model_timeout is not None:
            if arguments.model_timeout <= 0:
                parser().error("--model-timeout must be positive")
            deepseek = replace(deepseek, timeout_seconds=arguments.model_timeout)
        if arguments.model_max_tokens is not None:
            if arguments.model_max_tokens <= 0:
                parser().error("--model-max-tokens must be positive")
            deepseek = replace(deepseek, max_tokens=arguments.model_max_tokens)
    try:
        if np_hard_objective:
            result = NPHardAgentV1(
                NPHardAgentConfigV1(
                    root=ROOT,
                    input_module=arguments.module,
                    problem_declaration=arguments.source,
                    output_dir=arguments.output_dir,
                    lean_timeout_seconds=arguments.lean_timeout,
                    planner_mode=arguments.planner,
                    authoring_mode=authoring_mode,
                    authoring_attempt_budget=arguments.authoring_attempts,
                    deepseek=deepseek,
                )
            ).run()
        else:
            config = HardnessAgentConfig(
                root=ROOT,
                input_module=arguments.module,
                source_declaration=arguments.source,
                membership_declaration=arguments.membership,
                target_declaration=arguments.target,
                objective=OBJECTIVES[arguments.objective],
                planner_mode=arguments.planner,
                catalog_mode=arguments.catalog_mode,
                output_dir=arguments.output_dir,
                lean_timeout_seconds=arguments.lean_timeout,
                deepseek=deepseek,
                authoring_mode=authoring_mode,
                authoring_attempt_budget=arguments.authoring_attempts,
                resume=arguments.resume,
            )
            result = HardnessAgent(config).run()
    except (OSError, UnicodeError, ValueError) as error:
        print(json.dumps({"status": "FAILED", "error": str(error)}, ensure_ascii=False))
        return 1
    print(
        json.dumps(
            {
                "status": result.status,
                "job_id": result.job_id,
                "report": result.report_file,
                "artifact": result.artifact_file,
            },
            ensure_ascii=False,
        )
    )
    if result.verified:
        return 0
    return 2 if result.status == "BLOCKED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
