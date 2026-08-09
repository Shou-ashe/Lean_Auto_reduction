#!/usr/bin/env python3
"""Single-command production entrypoint for exact native NP-hardness."""

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
from agent.hardness.np_hard_input import NPHardInputError  # noqa: E402
from agent.hardness.np_hard_orchestrator import (  # noqa: E402
    NPHardOrchestratorConfigV2,
    NPHardOrchestratorError,
    NPHardOrchestratorV2,
)


def main() -> int:
    parser = argparse.ArgumentParser(description="Prove NativeTMNPHard for one library encoding")
    parser.add_argument("--module", required=True)
    parser.add_argument("--problem", required=True)
    parser.add_argument(
        "--authoring", choices=("disabled", "model-auto", "model-required"), default="model-auto"
    )
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument("--model", default=None)
    parser.add_argument("--model-timeout", type=int, default=120)
    parser.add_argument("--model-max-tokens", type=int, default=4096)
    parser.add_argument("--model-max-retries", type=int, default=0)
    parser.add_argument("--authoring-attempts", type=int, default=4)
    parser.add_argument("--model-call-budget", type=int, default=8)
    parser.add_argument("--lean-timeout", type=int, default=600)
    arguments = parser.parse_args()

    deepseek = None
    if arguments.authoring in {"model-auto", "model-required"}:
        deepseek = DeepSeekConfig.from_environment(env_file=arguments.env_file)
        deepseek = replace(
            deepseek,
            model=arguments.model or deepseek.model,
            timeout_seconds=arguments.model_timeout,
            max_tokens=arguments.model_max_tokens,
            max_retries=arguments.model_max_retries,
        )
    try:
        result = NPHardOrchestratorV2(
            NPHardOrchestratorConfigV2(
                root=ROOT,
                input_module=arguments.module,
                problem_declaration=arguments.problem,
                output_dir=arguments.output_dir,
                lean_timeout_seconds=arguments.lean_timeout,
                authoring_policy=arguments.authoring,
                attempt_budget=arguments.authoring_attempts,
                call_budget=arguments.model_call_budget,
                deepseek=deepseek,
            )
        ).run()
    except (NPHardInputError, NPHardOrchestratorError) as error:
        print(
            json.dumps(
                {
                    "status": "BLOCKED",
                    "failure_code": error.code,
                    "explanation": error.message,
                    "candidates": list(getattr(error, "candidates", ())),
                },
                ensure_ascii=False,
            )
        )
        return 2
    payload = result.to_dict()
    identity = payload.get("input_identity") or {}
    print(
        json.dumps(
            {
                "schema_version": payload["schema_version"],
                "status": payload["status"],
                "request_id": payload.get("request_id"),
                "job_id": payload.get("job_id"),
                "failure_code": payload.get("failure_code"),
                "requested_term": identity.get("requested_term", arguments.problem),
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
                "report": str(Path(payload["output_dir"]) / "report.json"),
            },
            ensure_ascii=False,
        )
    )
    return 0 if result.verified else (2 if result.status == "BLOCKED" else 1)


if __name__ == "__main__":
    raise SystemExit(main())
