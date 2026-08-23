"""Machine-verifiable freeze contract for staged Boolean-CSP evaluation."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from .capability_gate_policy import CapabilityGatePolicy


GADGET_AUTHORING_FREEZE_SCHEMA = "boolean_csp_gadget_authoring_freeze_v2"
GADGET_AUTHORING_FREEZE_RECEIPT_SCHEMA = (
    "boolean_csp_gadget_authoring_freeze_receipt_v2"
)
GADGET_AUTHORING_FREEZE_POLICY_VERSIONS = (
    "gadget-authoring-policy-v7",
    "gadget-authoring-validation-policy-v2",
    "gadget-authoring-heldout-policy-v2",
)
GADGET_AUTHORING_FREEZE_CASE_SET_NAMES = (
    "validation",
    "heldout",
    "full",
)
GADGET_AUTHORING_FREEZE_COMPONENTS = (
    "Benchmark/Hardness/Suites/boolean_csp_np_hard_public_v1.json",
    "Lean/Reference/ComplexityReduction/Agent/GenerativeReduction/Plugins/BooleanCSPFiniteGadget.lean",
    "Lean/Reference/ComplexityReduction/Agent/Hardness/GadgetAuthoringSources.lean",
    "agent/generative_reduction/boolean_csp_capability_gate.py",
    "agent/generative_reduction/boolean_csp_gadget_authoring.py",
    "agent/generative_reduction/boolean_csp_regression.py",
    "agent/generative_reduction/capability_gate_policy.py",
    "agent/generative_reduction/gadget_authoring_freeze.py",
    "agent/generative_reduction/generator_protocol.py",
    "agent/generative_reduction/model/gadget_authoring.py",
    "agent/generative_reduction/models.py",
    "agent/generative_reduction/orchestrator.py",
    "agent/generative_reduction/reconstruction.py",
    "agent/generative_reduction/recursive_runtime.py",
    "agent/generative_reduction/search.py",
    "agent/hardness/model_client.py",
)
DEFAULT_GADGET_AUTHORING_FREEZE_MANIFEST = Path(
    "Benchmark/Hardness/Development/boolean_csp_gadget_authoring_freeze_v2.json"
)

_TOP_LEVEL_KEYS = {
    "schema_version",
    "freeze_id",
    "policies",
    "case_sets",
    "suite",
    "model",
    "runtime",
    "budget",
    "semantic_contract",
    "component_sha256",
}
_MODEL_KEYS = (
    "base_url",
    "model",
    "timeout_seconds",
    "temperature",
    "max_tokens",
    "max_retries",
    "reasoning_effort",
)


class GadgetAuthoringFreezeError(ValueError):
    """The requested run differs from its committed freeze manifest."""


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return "sha256:" + digest.hexdigest()


def _read_object(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise GadgetAuthoringFreezeError(
            f"cannot read gadget-authoring freeze manifest: {path}"
        ) from error
    if not isinstance(value, dict):
        raise GadgetAuthoringFreezeError(
            "gadget-authoring freeze manifest must be a JSON object"
        )
    return value


def _mapping(value: object, *, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise GadgetAuthoringFreezeError(f"freeze {label} must be an object")
    return value


def _string_sequence(value: object, *, label: str) -> tuple[str, ...]:
    if not isinstance(value, list) or not all(isinstance(item, str) for item in value):
        raise GadgetAuthoringFreezeError(f"freeze {label} must be a string array")
    result = tuple(value)
    if len(result) != len(set(result)):
        raise GadgetAuthoringFreezeError(f"freeze {label} repeats values")
    return result


def gadget_authoring_semantic_contract(
    policy: CapabilityGatePolicy,
) -> dict[str, Any]:
    """Return the policy fields that define model authorship semantics."""

    return {
        "require_model_semantic_payload": policy.require_model_semantic_payload,
        "require_final_artifact_use": policy.require_final_artifact_use,
        "require_independent_lean": policy.require_independent_lean,
        "require_zero_forbidden_dependencies": (
            policy.require_zero_forbidden_dependencies
        ),
        "semantic_payload_schema": policy.semantic_payload_schema,
        "generator_name": policy.generator_name,
        "generator_version": policy.generator_version,
        "renderer_name": policy.renderer_name,
        "renderer_version": policy.renderer_version,
        "checker_name": policy.checker_name,
        "checker_version": policy.checker_version,
        "truth_table_context_version": policy.truth_table_context_version,
        "allowed_gadget_source_declarations": list(
            policy.allowed_gadget_source_declarations
        ),
        "disabled_finite_synthesis_plugins": list(
            policy.disabled_finite_synthesis_plugins
        ),
        "max_gadget_variable_count": policy.max_gadget_variable_count,
        "max_gadget_constraint_count": policy.max_gadget_constraint_count,
        "max_gadget_repairs": policy.max_gadget_repairs,
        "gadget_authoring_base_max_tokens": (
            policy.gadget_authoring_base_max_tokens
        ),
        "gadget_authoring_escalated_max_tokens": (
            policy.gadget_authoring_escalated_max_tokens
        ),
        "gadget_authoring_reasoning_effort": (
            policy.gadget_authoring_reasoning_effort
        ),
        "max_gadget_token_escalations_per_attempt": (
            policy.max_gadget_token_escalations_per_attempt
        ),
    }


def _frozen_model_config(model_config: Mapping[str, Any]) -> dict[str, Any]:
    missing = set(_MODEL_KEYS).difference(model_config)
    if missing:
        raise GadgetAuthoringFreezeError(
            f"runtime model config omitted frozen fields: {sorted(missing)!r}"
        )
    return {key: model_config[key] for key in _MODEL_KEYS}


def validate_gadget_authoring_freeze(
    *,
    root: Path,
    manifest_path: Path,
    policy: CapabilityGatePolicy,
    case_set_name: str,
    selected_case_ids: Sequence[str],
    suite_identity: Mapping[str, Any],
    model_config: Mapping[str, Any],
    runtime_config: Mapping[str, Any],
    budget: Mapping[str, Any],
) -> dict[str, Any]:
    """Validate a frozen run configuration before any external API call."""

    root = root.resolve()
    resolved_manifest = (
        manifest_path
        if manifest_path.is_absolute()
        else root / manifest_path
    ).resolve()
    manifest = _read_object(resolved_manifest)
    if set(manifest) != _TOP_LEVEL_KEYS:
        raise GadgetAuthoringFreezeError(
            "freeze manifest fields differ: "
            f"missing={sorted(_TOP_LEVEL_KEYS - set(manifest))!r}, "
            f"extra={sorted(set(manifest) - _TOP_LEVEL_KEYS)!r}"
        )
    if case_set_name not in GADGET_AUTHORING_FREEZE_CASE_SET_NAMES:
        raise GadgetAuthoringFreezeError(
            f"unsupported frozen case set: {case_set_name!r}"
        )

    policies = _mapping(manifest["policies"], label="policies")
    case_sets = _mapping(manifest["case_sets"], label="case_sets")
    suite = _mapping(manifest["suite"], label="suite")
    component_hashes = _mapping(
        manifest["component_sha256"], label="component_sha256"
    )
    frozen_case_ids = _string_sequence(
        case_sets.get(case_set_name), label=f"case_sets.{case_set_name}"
    )
    selected = tuple(str(item) for item in selected_case_ids)
    if len(selected) != len(set(selected)):
        raise GadgetAuthoringFreezeError("runtime selected case IDs are not unique")

    actual_component_hashes: dict[str, str] = {}
    component_paths_safe = True
    component_files_present = True
    component_hashes_match = True
    for raw_path, expected_hash in component_hashes.items():
        if not isinstance(raw_path, str) or not isinstance(expected_hash, str):
            raise GadgetAuthoringFreezeError(
                "freeze component_sha256 must map strings to strings"
            )
        relative = Path(raw_path)
        safe = not relative.is_absolute() and ".." not in relative.parts
        component_paths_safe = component_paths_safe and safe
        if not safe:
            component_hashes_match = False
            continue
        source = root / relative
        if not source.is_file():
            component_files_present = False
            component_hashes_match = False
            continue
        actual_hash = _sha256_file(source)
        actual_component_hashes[raw_path] = actual_hash
        component_hashes_match = (
            component_hashes_match and actual_hash == expected_hash
        )

    policy_versions_exact = set(policies) == set(
        GADGET_AUTHORING_FREEZE_POLICY_VERSIONS
    )
    case_set_names_exact = set(case_sets) == set(
        GADGET_AUTHORING_FREEZE_CASE_SET_NAMES
    )
    component_inventory_exact = set(component_hashes) == set(
        GADGET_AUTHORING_FREEZE_COMPONENTS
    )
    checks = {
        "schema_version_matches": (
            manifest["schema_version"] == GADGET_AUTHORING_FREEZE_SCHEMA
        ),
        "freeze_id_present": bool(manifest["freeze_id"]),
        "policy_versions_match_inventory": policy_versions_exact,
        "policy_hash_matches": (
            policies.get(policy.policy_version) == policy.policy_sha256
        ),
        "case_set_names_match_inventory": case_set_names_exact,
        "selected_case_ids_match": frozen_case_ids == selected,
        "policy_case_ids_match_selected_suite": (
            set(policy.selected_case_ids) == set(selected)
            and len(policy.selected_case_ids) == len(selected)
        ),
        "suite_identity_matches": dict(suite) == dict(suite_identity),
        "model_config_matches": (
            dict(_mapping(manifest["model"], label="model"))
            == _frozen_model_config(model_config)
        ),
        "runtime_config_matches": (
            dict(_mapping(manifest["runtime"], label="runtime"))
            == dict(runtime_config)
        ),
        "budget_matches": (
            dict(_mapping(manifest["budget"], label="budget")) == dict(budget)
        ),
        "semantic_contract_matches": (
            dict(
                _mapping(
                    manifest["semantic_contract"], label="semantic_contract"
                )
            )
            == gadget_authoring_semantic_contract(policy)
        ),
        "component_inventory_matches": component_inventory_exact,
        "component_paths_are_safe": component_paths_safe,
        "component_files_present": component_files_present,
        "component_hashes_match": component_hashes_match,
    }
    failures = tuple(name for name, passed in checks.items() if not passed)
    if failures:
        raise GadgetAuthoringFreezeError(
            "gadget-authoring freeze validation failed: " + ", ".join(failures)
        )
    return {
        "schema_version": GADGET_AUTHORING_FREEZE_RECEIPT_SCHEMA,
        "freeze_id": manifest["freeze_id"],
        "manifest_path": str(resolved_manifest),
        "manifest_sha256": _sha256_file(resolved_manifest),
        "case_set_name": case_set_name,
        "selected_case_ids": list(selected),
        "policy_version": policy.policy_version,
        "policy_sha256": policy.policy_sha256,
        "verified_component_count": len(actual_component_hashes),
        "verified_component_sha256": actual_component_hashes,
        "integrity_checks": checks,
        "integrity_passed": True,
    }


__all__ = [
    "DEFAULT_GADGET_AUTHORING_FREEZE_MANIFEST",
    "GADGET_AUTHORING_FREEZE_CASE_SET_NAMES",
    "GADGET_AUTHORING_FREEZE_COMPONENTS",
    "GADGET_AUTHORING_FREEZE_POLICY_VERSIONS",
    "GADGET_AUTHORING_FREEZE_RECEIPT_SCHEMA",
    "GADGET_AUTHORING_FREEZE_SCHEMA",
    "GadgetAuthoringFreezeError",
    "gadget_authoring_semantic_contract",
    "validate_gadget_authoring_freeze",
]
