"""Shared production contract for native NP-hardness entrypoints.

This module owns the formally qualified DeepSeek profile, CLI/environment
precedence, preflight records, model-call budgeting, and the public status
vocabulary.  Keeping those rules outside individual scripts prevents runners
from silently drifting back to historical defaults.
"""

from __future__ import annotations

import json
import os
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from .model_client import DeepSeekConfig, read_dotenv


NP_HARD_PRODUCTION_PREFLIGHT_SCHEMA_V1 = "hardness_np_hard_production_preflight_v1"
NP_HARD_CLI_RESULT_SCHEMA_V1 = "hardness_np_hard_cli_result_v1"

FORMAL_PROVIDER = "DeepSeek"
FORMAL_BASE_URL = "https://api.deepseek.com"
FORMAL_MODEL = "deepseek-v4-flash"
FORMAL_REASONING_EFFORT = "low"
FORMAL_TIMEOUT_SECONDS = 300
FORMAL_MAX_TOKENS = 64_000
FORMAL_MAX_RETRIES = 0
FORMAL_TEMPERATURE = 0.0

PUBLIC_STATUSES = {
    "VERIFIED",
    "BLOCKED_NOT_TARGET",
    "BLOCKED_MISSING_PREREQUISITE",
    "FAILED_MODEL",
    "FAILED_LEAN",
    "INPUT_ERROR",
}

INPUT_FAILURE_CODES = {
    "ambiguous_lawful_presentation",
    "ambiguous_input_module",
    "input_not_presented_problem",
    "input_problem_not_found",
    "missing_lawful_presentation",
}
NOT_TARGET_FAILURE_CODES = {"auxiliary_or_non_target"}
LEAN_FAILURE_CODES = {
    "candidate_dependency_stale",
    "deletion_audit_failed",
    "final_lean_failed",
    "fresh_core_resolve_failed",
    "independent_replay_failed",
    "lean_infrastructure_error",
    "scope_policy_conflict",
}
MODEL_FAILURE_CODES = {
    "authoring_failed",
    "authoring_gap_budget_exhausted",
    "candidate_exact_type_mismatch",
    "candidate_nonstandard_axiom",
    "candidate_outside_edit_boundary",
    "invalid_np_hard_gap_runtime_schema",
    "model_provider_unavailable",
    "qualification_model_profile_mismatch",
}


def _merged_environment(
    *, env_file: Path | None, environ: Mapping[str, str] | None
) -> dict[str, str]:
    """Return defaults < dotenv < process environment.

    ``DeepSeekConfig.from_environment`` has historical generic defaults.  The
    NP-hard production lane must instead start from the formally accepted
    profile while preserving the normal environment precedence.
    """

    merged = {
        "DEEPSEEK_BASE_URL": FORMAL_BASE_URL,
        "DEEPSEEK_MODEL": FORMAL_MODEL,
        "DEEPSEEK_TIMEOUT_SECONDS": str(FORMAL_TIMEOUT_SECONDS),
        "DEEPSEEK_MAX_TOKENS": str(FORMAL_MAX_TOKENS),
        "DEEPSEEK_MAX_RETRIES": str(FORMAL_MAX_RETRIES),
        "DEEPSEEK_REASONING_EFFORT": FORMAL_REASONING_EFFORT,
    }
    if env_file is not None:
        merged.update({key: value for key, value in read_dotenv(env_file).items() if value})
    source = os.environ if environ is None else environ
    merged.update({key: value for key, value in source.items() if value})
    return merged


def load_np_hard_production_model_config(
    *,
    env_file: Path | None,
    environ: Mapping[str, str] | None = None,
    model: str | None = None,
    timeout_seconds: int | None = None,
    max_tokens: int | None = None,
    max_retries: int | None = None,
    reasoning_effort: str | None = None,
) -> DeepSeekConfig:
    """Resolve explicit CLI overrides over env/.env over formal defaults."""

    config = DeepSeekConfig.from_environment(
        environ=_merged_environment(env_file=env_file, environ=environ)
    )
    return DeepSeekConfig(
        api_key=config.api_key,
        base_url=config.base_url,
        model=model if model is not None else config.model,
        timeout_seconds=(
            timeout_seconds if timeout_seconds is not None else config.timeout_seconds
        ),
        temperature=FORMAL_TEMPERATURE,
        max_tokens=max_tokens if max_tokens is not None else config.max_tokens,
        max_retries=max_retries if max_retries is not None else config.max_retries,
        reasoning_effort=(
            reasoning_effort
            if reasoning_effort is not None
            else config.reasoning_effort
        ),
    )


def is_formal_np_hard_qualification_config(config: DeepSeekConfig) -> bool:
    return (
        config.public_base_url == FORMAL_BASE_URL
        and config.model == FORMAL_MODEL
        and config.reasoning_effort == FORMAL_REASONING_EFFORT
        and config.timeout_seconds == FORMAL_TIMEOUT_SECONDS
        and config.max_tokens == FORMAL_MAX_TOKENS
        and config.max_retries == FORMAL_MAX_RETRIES
        and config.temperature == FORMAL_TEMPERATURE
    )


def required_model_call_budget(*, gap_node_count: int, attempt_budget: int) -> int:
    """Reserve every allowed attempt for every node in the typed DAG."""

    if gap_node_count < 0:
        raise ValueError("gap node count cannot be negative")
    if not 1 <= attempt_budget <= 4:
        raise ValueError("attempt budget must be in 1..4")
    return gap_node_count * attempt_budget


def public_np_hard_status(
    *, internal_status: str, failure_code: str | None, model_calls: int = 0
) -> str:
    if internal_status == "VERIFIED":
        return "VERIFIED"
    if failure_code in INPUT_FAILURE_CODES:
        return "INPUT_ERROR"
    if failure_code in NOT_TARGET_FAILURE_CODES:
        return "BLOCKED_NOT_TARGET"
    if failure_code in LEAN_FAILURE_CODES:
        return "FAILED_LEAN"
    if failure_code in MODEL_FAILURE_CODES or model_calls > 0:
        return "FAILED_MODEL"
    return "BLOCKED_MISSING_PREREQUISITE"


@dataclass(frozen=True)
class NPHardProductionPreflightV1:
    authoring_policy: str
    qualification_force_authoring: bool
    attempt_budget: int
    call_budget: int
    model_configuration: Mapping[str, Any]
    formal_qualification: bool
    qualification_profile_matched: bool
    input_module: str | None
    requested_problem: str
    output_dir: str
    schema_version: str = NP_HARD_PRODUCTION_PREFLIGHT_SCHEMA_V1

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "provider": FORMAL_PROVIDER,
            "authoring_policy": self.authoring_policy,
            "qualification_force_authoring": self.qualification_force_authoring,
            "attempt_budget": self.attempt_budget,
            "call_budget": self.call_budget,
            "model_configuration": dict(self.model_configuration),
            "formal_qualification": self.formal_qualification,
            "qualification_profile_matched": self.qualification_profile_matched,
            "input_module": self.input_module,
            "requested_problem": self.requested_problem,
            "output_dir": self.output_dir,
        }

    def write(self, path: Path) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        temporary = path.with_suffix(path.suffix + ".tmp")
        temporary.write_text(
            json.dumps(self.to_dict(), indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        temporary.replace(path)
