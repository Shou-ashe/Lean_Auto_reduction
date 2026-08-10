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
from agent.hardness.np_hard_orchestrator import (  # noqa: E402
    NPHardOrchestratorConfigV2,
    NPHardOrchestratorError,
    NPHardOrchestratorV2,
)
from agent.hardness.np_hard_production import (  # noqa: E402
    NP_HARD_CLI_RESULT_SCHEMA_V1,
    load_np_hard_production_model_config,
    public_np_hard_status,
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
                "call_budget": (
                    arguments.model_call_budget
                    if arguments.model_call_budget is not None
                    else "auto: attempt_budget × typed_DAG_nodes"
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
        result = NPHardOrchestratorV2(
            NPHardOrchestratorConfigV2(
                root=ROOT,
                input_module=input_module,
                problem_declaration=arguments.problem,
                output_dir=output_dir,
                lean_timeout_seconds=arguments.lean_timeout,
                authoring_policy=authoring_policy,
                attempt_budget=arguments.authoring_attempts,
                call_budget=arguments.model_call_budget,
                deepseek=deepseek,
                preflight_path=preflight_path,
                formal_qualification=(
                    arguments.qualification or arguments.qualification_authoring
                ),
                qualification_force_authoring=arguments.qualification_authoring,
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
        public_status = public_np_hard_status(
            internal_status="FAILED", failure_code=error.code
        )
        return 1 if public_status.startswith("FAILED_") else 2
    payload = result.to_dict()
    identity = payload.get("input_identity") or {}
    status = public_np_hard_status(
        internal_status=result.status,
        failure_code=result.failure_code,
        model_calls=result.model_calls,
    )
    print(
        json.dumps(
            {
                "schema_version": NP_HARD_CLI_RESULT_SCHEMA_V1,
                "proof_result_schema_version": payload["schema_version"],
                "status": status,
                "internal_status": payload["status"],
                "request_id": payload.get("request_id"),
                "job_id": payload.get("job_id"),
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
                "selected_hub": payload.get("selected_hub"),
                "capability_dag": payload.get("capability_dag"),
                "model_calls": payload.get("model_calls"),
                "artifact": payload.get("artifact"),
                "independent_replay": payload.get("independent_replay"),
                "axiom_audit": payload.get("axiom_audit"),
                "endpoint_equality_audit": {
                    "passed": (
                        (payload.get("artifact") or {}).get("endpoint")
                        == identity.get("canonical_problem")
                    ),
                    "expected": identity.get("canonical_problem"),
                    "actual": (payload.get("artifact") or {}).get("endpoint"),
                },
                "preflight": str(preflight_path),
                "report": str(Path(payload["output_dir"]) / "report.json"),
            },
            ensure_ascii=False,
        )
    )
    return 0 if status == "VERIFIED" else (1 if status.startswith("FAILED_") else 2)


if __name__ == "__main__":
    raise SystemExit(main())
