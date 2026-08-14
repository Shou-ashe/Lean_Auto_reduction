#!/usr/bin/env python3
"""Single-command production entrypoint for exact native NP-hardness."""

from __future__ import annotations

import argparse
import json
import secrets
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_input import (  # noqa: E402
    NPHardInputError,
    discover_np_hard_input_module,
)
from agent.hardness.np_hard_orchestrator import NPHardOrchestratorError  # noqa: E402
from agent.hardness.np_hard_production import (  # noqa: E402
    NP_HARD_CLI_RESULT_SCHEMA_V1,
    is_formal_np_hard_qualification_config,
    load_np_hard_production_model_config,
    public_np_hard_status,
)
from agent.reduction import (  # noqa: E402
    PROFILE_NAMES,
    ReductionOrchestrator,
    ReductionOrchestratorConfig,
    SearchBudget,
    public_status,
)


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Prove NativeTMNPHard for one library encoding")
    parser.add_argument(
        "--module",
        help="optional public module override; inferred from a full --problem declaration",
    )
    parser.add_argument("--problem", required=True)
    parser.add_argument(
        "--authoring", choices=("disabled", "model-auto", "model-required"), default="model-auto"
    )
    parser.add_argument("--profile", choices=PROFILE_NAMES, default="research")
    parser.add_argument("--max-search-depth", type=int, default=6)
    parser.add_argument("--max-expanded-states", type=int, default=128)
    parser.add_argument("--max-candidates-per-goal", type=int, default=16)
    parser.add_argument("--max-lean-checks", type=int, default=48)
    parser.add_argument("--max-synthesis-rounds", type=int, default=2)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument("--model", default=None)
    parser.add_argument("--model-timeout", type=int, default=None)
    parser.add_argument("--model-max-tokens", type=int, default=None)
    parser.add_argument("--model-max-retries", type=int, default=None)
    parser.add_argument("--reasoning-effort", default=None)
    parser.add_argument("--authoring-attempts", type=int, default=4)
    parser.add_argument(
        "--model-call-budget",
        type=int,
        default=None,
        help="optional override; auto mode reserves attempts × typed DAG nodes",
    )
    parser.add_argument("--lean-timeout", type=int, default=600)
    parser.add_argument(
        "--qualification",
        action="store_true",
        help="fail closed unless the accepted formal V4 Flash profile is active",
    )
    parser.add_argument(
        "--qualification-authoring",
        action="store_true",
        help=(
            "formally qualify model authoring for a public ComplexityReduction input; "
            "implies --qualification and model-required"
        ),
    )
    return parser


def _output_dir(arguments: argparse.Namespace) -> Path:
    if arguments.output_dir is not None:
        return arguments.output_dir.resolve()
    return (
        ROOT
        / ".reduction-agent"
        / "np-hard-cli"
        / secrets.token_hex(16)
    ).resolve()


def _error_payload(
    *,
    error: NPHardInputError | NPHardOrchestratorError,
    requested_problem: str,
    input_module: str | None,
    preflight_file: Path | None,
) -> dict[str, object]:
    public_status = public_np_hard_status(
        internal_status="FAILED", failure_code=error.code
    )
    if isinstance(error, NPHardInputError) and error.code == "candidate_dependency_stale":
        public_status = "INPUT_ERROR"
    return {
        "schema_version": NP_HARD_CLI_RESULT_SCHEMA_V1,
        "status": public_status,
        "internal_status": "FAILED",
        "failure_code": error.code,
        "explanation": error.message,
        "requested_term": requested_problem,
        "input_module": input_module,
        "candidates": list(getattr(error, "candidates", ())),
        "model_calls": 0,
        "preflight": str(preflight_file) if preflight_file is not None else None,
    }


def main() -> int:
    arguments = build_parser().parse_args()
    output_dir = _output_dir(arguments)
    preflight_path = output_dir / "preflight.json"
    authoring_policy = (
        "model-required" if arguments.qualification_authoring else arguments.authoring
    )

    deepseek = load_np_hard_production_model_config(
        env_file=arguments.env_file,
        model=arguments.model,
        timeout_seconds=arguments.model_timeout,
        max_tokens=arguments.model_max_tokens,
        max_retries=arguments.model_max_retries,
        reasoning_effort=arguments.reasoning_effort,
    )
    if (arguments.qualification or arguments.qualification_authoring) and not (
        is_formal_np_hard_qualification_config(deepseek)
    ):
        print(
            json.dumps(
                {
                    "schema_version": NP_HARD_CLI_RESULT_SCHEMA_V1,
                    "status": "FAILED_MODEL",
                    "internal_status": "FAILED",
                    "failure_code": "qualification_model_profile_mismatch",
                    "explanation": (
                        "formal qualification requires the accepted DeepSeek V4 Flash profile"
                    ),
                    "requested_term": arguments.problem,
                    "input_module": arguments.module,
                    "model_calls": 0,
                    "preflight": None,
                },
                ensure_ascii=False,
            )
        )
        return 1
    try:
        input_module = arguments.module or discover_np_hard_input_module(
            root=ROOT,
            requested_term=arguments.problem,
            timeout_seconds=arguments.lean_timeout,
        )
    except NPHardInputError as error:
        print(
            json.dumps(
                _error_payload(
                    error=error,
                    requested_problem=arguments.problem,
                    input_module=arguments.module,
                    preflight_file=None,
                ),
                ensure_ascii=False,
            )
        )
        return 2

    print(
        json.dumps(
            {
                "event": "np_hard_preflight",
                "provider": "DeepSeek",
                "model_configuration": deepseek.to_public_dict(),
                "authoring_policy": authoring_policy,
                "qualification_force_authoring": arguments.qualification_authoring,
                "attempt_budget": arguments.authoring_attempts,
                "profile": arguments.profile,
                "call_budget": (
                    arguments.model_call_budget
                    if arguments.model_call_budget is not None
                    else 2
                ),
                "input_module": input_module,
                "requested_problem": arguments.problem,
                "output_dir": str(output_dir),
            },
            ensure_ascii=False,
        ),
        file=sys.stderr,
    )
    try:
        result = ReductionOrchestrator(
            ReductionOrchestratorConfig(
                root=ROOT,
                input_module=input_module,
                problem_declaration=arguments.problem,
                output_dir=output_dir,
                profile=arguments.profile,
                lean_timeout_seconds=arguments.lean_timeout,
                budget=SearchBudget(
                    max_search_depth=arguments.max_search_depth,
                    max_expanded_states=arguments.max_expanded_states,
                    max_candidates_per_goal=arguments.max_candidates_per_goal,
                    max_lean_checks=arguments.max_lean_checks,
                    max_model_calls=(
                        arguments.model_call_budget
                        if arguments.model_call_budget is not None
                        else 2
                    ),
                    max_synthesis_rounds=arguments.max_synthesis_rounds,
                    wall_clock_timeout_seconds=arguments.lean_timeout,
                ),
                model_policy={
                    "disabled": "disabled",
                    "model-auto": "auto",
                    "model-required": "required",
                }[authoring_policy],
                deepseek=deepseek,
            )
        ).run()
    except (NPHardInputError, NPHardOrchestratorError) as error:
        print(
            json.dumps(
                _error_payload(
                    error=error,
                    requested_problem=arguments.problem,
                    input_module=input_module,
                    preflight_file=(preflight_path if preflight_path.is_file() else None),
                ),
                ensure_ascii=False,
            )
        )
        failure_status = public_np_hard_status(
            internal_status="FAILED", failure_code=error.code
        )
        return 1 if failure_status.startswith("FAILED_") else 2
    payload = result.to_dict()
    identity = payload.get("input_identity") or {}
    status = public_status(result)
    print(
        json.dumps(
            {
                "schema_version": NP_HARD_CLI_RESULT_SCHEMA_V1,
                "proof_result_schema_version": payload["schema_version"],
                "status": status,
                "internal_status": payload["status"],
                "request_id": None,
                "job_id": None,
                "failure_code": payload.get("failure_code"),
                "requested_term": identity.get("requested_term", arguments.problem),
                "input_module": input_module,
                "requested_declaration": identity.get("requested_declaration"),
                "resolved_encoding": identity.get("resolved_encoding"),
                "canonical_problem": identity.get("canonical_problem"),
                "normalization_certificate": identity.get(
                    "normalization_certificate"
                ),
                "input_identity": payload.get("input_identity"),
                "profile": payload.get("profile"),
                "selected_hub": payload.get("selected_theorem"),
                "capability_dag": payload.get("proof_tree"),
                "model_calls": payload.get("model_call_count"),
                "model_call_records": payload.get("model_calls"),
                "artifact": {
                    "file": payload.get("artifact_file"),
                    "sha256": payload.get("artifact_sha256"),
                    "endpoint": identity.get("canonical_problem"),
                },
                "independent_replay": {
                    "passed": payload.get("independent_replay_passed") is True
                },
                "axiom_audit": {"passed": payload.get("axiom_audit_passed") is True},
                "endpoint_equality_audit": {
                    "passed": payload.get("endpoint_equality_audit_passed") is True,
                    "expected": identity.get("canonical_problem"),
                    "actual": identity.get("canonical_problem"),
                },
                "preflight": None,
                "report": str(Path(payload["output_dir"]) / "report.json"),
            },
            ensure_ascii=False,
        )
    )
    return 0 if status == "VERIFIED" else (1 if status.startswith("FAILED_") else 2)


if __name__ == "__main__":
    raise SystemExit(main())
