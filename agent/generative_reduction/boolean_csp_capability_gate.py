"""Run one isolated Boolean-CSP generation-capability gate over the full suite."""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import replace
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from .capability_gate_policy import (
    BOOLEAN_CSP_GADGET_AUTHORING_ANCHOR_CASE_IDS,
    BOOLEAN_CSP_GADGET_AUTHORING_HELDOUT_CASE_IDS,
    BOOLEAN_CSP_GADGET_AUTHORING_REQUIRED_CASE_IDS,
    BOOLEAN_CSP_GADGET_AUTHORING_VALIDATION_CASE_IDS,
    CapabilityGatePolicy,
    gadget_authoring_dev_policy,
    gadget_authoring_heldout_policy,
    gadget_authoring_policy,
    gadget_authoring_validation_policy,
)
from .boolean_csp_regression import run_recursive_boolean_csp_regression
from .models import CapabilityKind, ContributionClass
from agent.hardness.boolean_csp_gadget_authoring_dev import (
    load_gadget_authoring_dev_suite,
)
from agent.hardness.boolean_csp_np_hard_benchmark import load_suite


ROOT = Path(__file__).resolve().parents[2]
HARDNESS = "ComplexityReduction.Domain.BooleanCSP.Hardness."

GADGET_AUTHORING_CASE_STATUSES = (
    "ANCHOR_REUSE_VERIFIED",
    "MODEL_GADGET_VERIFIED_AND_FINAL_USED",
    "ROUTE_NOT_REACHED",
    "MODEL_PLAN_NOT_PRODUCED",
    "MODEL_SEARCH_NONCONVERGENT",
    "MODEL_PROTOCOL_INVALID",
    "GADGET_PLAN_SCHEMA_INVALID",
    "GADGET_SEMANTIC_COUNTEREXAMPLE",
    "GADGET_SEMANTIC_REPAIR_FAILED",
    "LEAN_MATERIALIZATION_FAILED",
    "FORBIDDEN_DEPENDENCY",
    "ATTRIBUTION_MISMATCH",
    "CAPABILITY_NOT_FINAL_USED",
    "BUDGET_EXHAUSTED",
    "SYSTEM_ERROR",
)

_GADGET_CAPABILITY_KINDS = {
    CapabilityKind.GADGET.value,
    CapabilityKind.LANGUAGE_INTERPRETATION.value,
}

_AUTHORSHIP_VALIDATION_STEPS = (
    "schema-validate-model-payload",
    "check-single-explicit-plan-over-finite-truth-tables",
    "render-plan-without-semantic-additions",
    "lean-kernel-check-spec-correct-and-to-gadget",
)

# These declarations are legitimate packaging/search routes, but selecting
# them directly leaves an unconstrained PresentedProblem binder and tests route
# guessing instead of the requested local generation capability.  They remain
# legal transitive dependencies of the explicit transport packager.
TRANSPORT_CANDIDATE_EXCLUSIONS = (
    "ComplexityReduction.Agent.GenerativeReduction.FinalCheck.exactEndpoint",
    "ComplexityReduction.Agent.GenerativeReduction.ProofReconstruction.exactEndpoint",
    "ComplexityReduction.Agent.GenerativeReduction.RuleKernel.completenessProjection",
    "ComplexityReduction.Agent.GenerativeReduction.RuleKernel.exactHardness",
    "ComplexityReduction.Certificate.NativeTMNPComplete.nativeHardness",
    "ComplexityReduction.Protocol.TypedNPHardEvidenceV1.toNativeHardness",
    "ComplexityReduction.Protocol.TypedNPHardResultV1.extractNativeHardness",
    "ComplexityReduction.Agent.GenerativeReduction.RuleKernel.completenessAlongPath",
    "ComplexityReduction.Agent.GenerativeReduction.RuleKernel.hardnessAlongPath",
    "ComplexityReduction.Certificate.NativeTMNPHard.alongPath",
    "ComplexityReduction.Certificate.NativeTMNPHard.ofCompleteAlongPath",
)

SHARED_TRANSPORT_FORBIDDEN = (
    HARDNESS + "nPHard_of_interpretation_auto",
    HARDNESS + "certifiedReduction_of_interpretation_auto",
    HARDNESS + "nPHard_of_interpretsHardCore",
    HARDNESS + "nPHard_oneInThree_of_exactlyTwo3",
    HARDNESS + "nPHard_exactlyTwo3_of_oneInThree",
    HARDNESS + "exactlyTwo3CoreNPHard_of_oneInThree",
    HARDNESS + "exactlyTwo3CoreNPHard",
)

DIRECT_TM_FORBIDDEN = (
    *SHARED_TRANSPORT_FORBIDDEN,
    HARDNESS + "interpretation_tmPolyTime",
)

SEMANTIC_FORBIDDEN = (
    *SHARED_TRANSPORT_FORBIDDEN,
    HARDNESS + "nPHard_of_interpretation",
    HARDNESS + "certifiedReduction_of_interpretation",
    HARDNESS + "interpret_satisfiable_iff",
    HARDNESS + "interpret_satisfies_forward",
    HARDNESS + "interpret_satisfies_reverse",
    HARDNESS + "oneInThree_satisfiable_iff_exactlyTwo3",
    HARDNESS + "exactlyTwo3_satisfiable_iff_oneInThree",
)


def _artifact_uses(artifact: object, declaration: object) -> bool:
    if not isinstance(artifact, str) or not isinstance(declaration, str):
        return False
    path = Path(artifact)
    if not path.is_file():
        return False
    return declaration in path.read_text(encoding="utf-8")


def _matches_gate(gate: str, capability: Mapping[str, Any]) -> bool:
    exact_type = str(capability.get("exact_type") or "")
    if gate == "direct-tm":
        return "ComplexityReduction.TMPolyTimeMap" in exact_type
    return (
        "ExecutableSemanticProof" in exact_type
        or "ProgramSemanticProof" in exact_type
        or "CertifiedReduction" in exact_type
        or ("Satisfiable" in exact_type and ("↔" in exact_type or "Iff" in exact_type))
        or ("accepts" in exact_type and ("↔" in exact_type or "Iff" in exact_type))
    )


def evaluate_capability_gate(
    report: Mapping[str, Any],
    gate: str,
    policy: CapabilityGatePolicy | None = None,
) -> dict[str, Any]:
    if policy is None:
        policy = _legacy_gate_policy(gate)
    required_case_ids = set(policy.required_case_ids)
    matched: list[dict[str, Any]] = []
    final_used: list[dict[str, Any]] = []
    verified_with_final_used: set[str] = set()
    target_specific_plan_cases: set[str] = set()
    context_ready_plan_cases: set[str] = set()
    executable_typed_plan_cases: set[str] = set()
    capability_budget_reserved_cases: set[str] = set()
    final_used_contributions: list[dict[str, Any]] = []
    for row in report.get("cases", ()):
        if not isinstance(row, dict):
            continue
        case_id = str(row.get("case_id") or row.get("case") or "")
        for capability in row.get("generated_capabilities", ()):
            if not isinstance(capability, dict) or not _matches_gate(gate, capability):
                continue
            item = {
                "case": case_id,
                "proof_status": row.get("proof_status"),
                "declaration": capability.get("declaration"),
                "exact_type": capability.get("exact_type"),
                "used_by_final_artifact": _artifact_uses(
                    row.get("artifact"), capability.get("declaration")
                ),
            }
            matched.append(item)
            if item["used_by_final_artifact"]:
                final_used.append(item)
                if item["proof_status"] == "VERIFIED" and case_id:
                    verified_with_final_used.add(case_id)
        for plan in row.get("typed_capability_plans", ()):
            if not isinstance(plan, dict):
                continue
            plan_id = str(plan.get("plan_id") or "")
            matches_plan = (
                (gate == "direct-tm" and plan_id.startswith("direct-tm-plan-"))
                or (gate == "semantic" and plan_id.startswith("semantic-plan-"))
            )
            if matches_plan and case_id:
                case = case_id
                target_specific_plan_cases.add(case)
                exact_goal = " ".join(str(plan.get("exact_goal") or "").split())
                capsules = row.get("context_capsules", ())
                if any(
                    isinstance(capsule, dict)
                    and bool(capsule.get("generation_context_ready"))
                    and " ".join(str(capsule.get("exact_goal") or "").split())
                    == exact_goal
                    for capsule in capsules
                ):
                    context_ready_plan_cases.add(case)
                if gate == "direct-tm":
                    nodes = tuple(
                        node
                        for node in plan.get("nodes", ())
                        if isinstance(node, dict)
                    )
                    node_ids = {str(node.get("node_id") or "") for node in nodes}
                    if (
                        nodes
                        and str(plan.get("final_node_id") or "") in node_ids
                        and all(
                            all(
                                str(dependency) in node_ids
                                for dependency in node.get("dependency_node_ids", ())
                            )
                            for node in nodes
                        )
                    ):
                        executable_typed_plan_cases.add(case)
                else:
                    forward = plan.get("forward")
                    reverse = plan.get("reverse")
                    if (
                        isinstance(forward, dict)
                        and forward.get("direction") == "forward"
                        and bool(forward.get("witness_schema"))
                        and isinstance(reverse, dict)
                        and reverse.get("direction") == "reverse"
                        and bool(reverse.get("witness_schema"))
                    ):
                        executable_typed_plan_cases.add(case)
        for receipt in row.get("contribution_receipts", ()):
            if not isinstance(receipt, dict):
                continue
            if receipt.get("capability_kind") != gate:
                continue
            if not receipt.get("final_artifact_used"):
                continue
            final_used_contributions.append(
                {
                    "case": case_id,
                    "capability_declaration": receipt.get(
                        "capability_declaration"
                    ),
                    "plan_id": receipt.get("plan_id"),
                    "brief_id": receipt.get("brief_id"),
                    "contribution_class": receipt.get("contribution_class"),
                    "forbidden_audit_passed": receipt.get(
                        "forbidden_audit_passed"
                    ),
                    "independent_lean_passed": receipt.get(
                        "independent_lean_passed"
                    ),
                }
            )
        for reservation in row.get("capability_budget_reservations", ()):
            if not isinstance(reservation, dict):
                continue
            hierarchy = tuple(str(item) for item in reservation.get("hierarchy", ()))
            expected_prefix = (
                "capability:direct-tm-plan-"
                if gate == "direct-tm"
                else "capability:semantic-plan-"
            )
            if (
                reservation.get("status")
                == "reserved-for-immediate-sequential-execution"
                and any(item.startswith(expected_prefix) for item in hierarchy)
                and case_id
            ):
                capability_budget_reserved_cases.add(case_id)
    completed_case_count = int((report.get("suite") or {}).get("completed_case_count", 0))
    selected_case_count = int(
        (report.get("suite") or {}).get(
            "selected_case_count", completed_case_count
        )
    )
    verified_case_count = int((report.get("results") or {}).get("verified_case_count", 0))
    validation = report.get("validation") if isinstance(report.get("validation"), dict) else {}
    real_api = report.get("real_api") if isinstance(report.get("real_api"), dict) else {}
    required_nonreuse_cases = len(policy.required_case_ids)
    accepted_contribution_classes = {
        item.value for item in policy.required_contribution_classes
    }
    receipt_consistency = all(
        item["forbidden_audit_passed"]
        and item["independent_lean_passed"]
        and item["plan_id"]
        and item["brief_id"]
        and item["contribution_class"] in accepted_contribution_classes
        for item in final_used_contributions
    )
    hard_checks = {
        "all_cases_completed": completed_case_count == selected_case_count,
        "all_cases_verified": verified_case_count == selected_case_count,
        "real_api_was_called": int(real_api.get("total_calls", 0)) > 0,
        "all_called_requests_http_200": bool(
            validation.get("all_called_requests_http_200")
        ),
        "forbidden_dependency_count_is_zero": int(
            validation.get("forbidden_direct_or_transitive_dependency_count", 0)
        )
        == 0,
        "unresolved_probe_handle_count_is_zero": bool(
            validation.get("unresolved_probe_handle_count_is_zero")
        ),
        "empty_context_generator_call_count_is_zero": bool(
            validation.get("empty_context_generator_call_count_is_zero")
        ),
        "target_specific_plan_coverage": (
            target_specific_plan_cases >= required_case_ids
        ),
        "typed_plan_is_executable": (
            executable_typed_plan_cases >= required_case_ids
        ),
        "typed_context_coverage": (
            context_ready_plan_cases >= required_case_ids
        ),
        "capability_budget_reservation_coverage": (
            capability_budget_reserved_cases >= required_case_ids
        ),
        "generated_capability_final_use_coverage": (
            verified_with_final_used >= required_case_ids
        ),
        "contribution_receipt_final_use_coverage": (
            {str(item.get("case")) for item in final_used_contributions}
            >= required_case_ids
        ),
        "receipt_consistency": receipt_consistency,
    }
    gate_passed = all(hard_checks.values())
    return {
        "gate": gate,
        "policy_name": policy.name,
        "policy_version": policy.policy_version,
        "policy_sha256": policy.policy_sha256,
        "required_generated_shape": (
            "TMPolyTimeMap exact capability"
            if gate == "direct-tm"
            else "semantic iff or semantic-bearing CertifiedReduction capability"
        ),
        "matched_generated_capability_count": len(matched),
        "final_used_matched_capability_count": len(final_used),
        "verified_case_count_with_final_used_match": len(verified_with_final_used),
        "verified_cases_with_final_used_match": sorted(verified_with_final_used),
        "capability_generation_observed": bool(final_used),
        "target_specific_plan_case_count": len(target_specific_plan_cases),
        "target_specific_plan_cases": sorted(target_specific_plan_cases),
        "context_ready_plan_case_count": len(context_ready_plan_cases),
        "context_ready_plan_cases": sorted(context_ready_plan_cases),
        "executable_typed_plan_case_count": len(executable_typed_plan_cases),
        "executable_typed_plan_cases": sorted(executable_typed_plan_cases),
        "capability_budget_reserved_case_count": len(
            capability_budget_reserved_cases
        ),
        "capability_budget_reserved_cases": sorted(
            capability_budget_reserved_cases
        ),
        "required_nonreuse_case_count": required_nonreuse_cases,
        "required_nonreuse_case_ids": sorted(required_case_ids),
        "final_used_contribution_count": len(final_used_contributions),
        "final_used_contributions": final_used_contributions,
        "receipt_consistency_passed": receipt_consistency,
        "hard_checks": hard_checks,
        "gate_passed": gate_passed,
        "matched_capabilities": matched,
    }


def _legacy_gate_policy(gate: str) -> CapabilityGatePolicy:
    capability_kind = (
        CapabilityKind.DIRECT_TM if gate == "direct-tm" else CapabilityKind.SEMANTIC
    )
    return CapabilityGatePolicy(
        name=gate,
        policy_version=f"{gate}-policy-v1",
        required_case_ids=BOOLEAN_CSP_GADGET_AUTHORING_REQUIRED_CASE_IDS,
        anchor_case_ids=BOOLEAN_CSP_GADGET_AUTHORING_ANCHOR_CASE_IDS,
        required_capability_kind=capability_kind,
        required_contribution_classes=(
            ContributionClass.DETERMINISTIC_GENERATED_CAPABILITY,
            ContributionClass.MODEL_GENERATED_CAPABILITY,
            ContributionClass.HYBRID_GENERATED_CAPABILITY,
        ),
    )


def evaluate_gadget_authoring_policy_enforcement(
    report: Mapping[str, Any], policy: CapabilityGatePolicy
) -> dict[str, Any]:
    suite = report.get("suite") if isinstance(report.get("suite"), Mapping) else {}
    validation = (
        report.get("validation")
        if isinstance(report.get("validation"), Mapping)
        else {}
    )
    enforcement = (
        report.get("policy_enforcement")
        if isinstance(report.get("policy_enforcement"), Mapping)
        else {}
    )
    real_api = (
        report.get("real_api")
        if isinstance(report.get("real_api"), Mapping)
        else {}
    )
    hard_checks = {
        "all_cases_completed": suite.get("completed_case_count")
        == suite.get("selected_case_count"),
        "real_api_was_called": int(real_api.get("total_calls", 0)) > 0,
        "all_called_requests_http_200": bool(
            validation.get("all_called_requests_http_200")
        ),
        "policy_integrity_passed": bool(enforcement.get("integrity_passed")),
        "forbidden_dependency_count_is_zero": int(
            validation.get("forbidden_direct_or_transitive_dependency_count", 0)
        )
        == 0,
        "required_cases_exercised_runtime_policy": int(
            enforcement.get("required_case_runtime_receipt_count", 0)
        )
        == len(policy.required_case_ids),
    }
    return {
        "gate": policy.name,
        "policy_name": policy.name,
        "policy_version": policy.policy_version,
        "policy_sha256": policy.policy_sha256,
        "required_case_count": len(policy.required_case_ids),
        "anchor_case_count": len(policy.anchor_case_ids),
        "hard_checks": hard_checks,
        "policy_enforcement_passed": all(hard_checks.values()),
        "strict_authorship_gate_evaluated": False,
        "strict_authorship_gate_passed": False,
    }


def _sha256_with_prefix(value: object) -> str:
    text = str(value or "")
    if not text:
        return ""
    return text if text.startswith("sha256:") else "sha256:" + text


def _structured_gadget_receipts(row: Mapping[str, Any]) -> tuple[Mapping[str, Any], ...]:
    return tuple(
        item
        for item in row.get("typed_capability_plans", ())
        if isinstance(item, Mapping)
        and str(item.get("schema_version") or "").startswith(
            "boolean_csp_gadget_authoring_receipt_v"
        )
    )


def _gadget_contribution_receipts(
    row: Mapping[str, Any],
) -> tuple[Mapping[str, Any], ...]:
    return tuple(
        item
        for item in row.get("contribution_receipts", ())
        if isinstance(item, Mapping)
        and item.get("capability_kind") in _GADGET_CAPABILITY_KINDS
    )


def _row_disabled_plugin_violation(
    row: Mapping[str, Any], policy: CapabilityGatePolicy
) -> bool:
    disabled = set(policy.disabled_finite_synthesis_plugins)
    runtime = row.get("gate_policy_runtime")
    if isinstance(runtime, Mapping):
        if runtime.get("disabled_plugins_absent_from_runtime") is False:
            return True
        if disabled.intersection(runtime.get("runtime_finite_synthesis_plugins", ())):
            return True
    return any(
        isinstance(step, Mapping) and step.get("solver") in disabled
        for step in row.get("proof_tree", ())
    )


def _row_has_forbidden_dependency(
    row: Mapping[str, Any], policy: CapabilityGatePolicy
) -> bool:
    route = row.get("final_route_audit_receipt")
    if isinstance(route, Mapping):
        if route.get("passed") is False:
            return True
        if route.get("forbidden_dependencies_passed") is False:
            return True
    forbidden = set(policy.forbidden_declarations)
    if any(
        isinstance(step, Mapping) and step.get("declaration") in forbidden
        for step in row.get("proof_tree", ())
    ):
        return True
    blocker = row.get("blocker")
    blocker_text = json.dumps(blocker, ensure_ascii=False, sort_keys=True).lower()
    return "forbidden dependency" in blocker_text or "route audit rejected" in blocker_text


def _positive_dependency_audit_passed(
    row: Mapping[str, Any], declaration: str
) -> bool:
    route = row.get("final_route_audit_receipt")
    if not isinstance(route, Mapping):
        return False
    dependencies = tuple(str(item) for item in route.get("required_dependencies", ()))
    return (
        bool(route.get("required_dependency_audit_emitted"))
        and bool(route.get("required_dependencies_passed"))
        and int(route.get("required_dependency_count", -1)) == len(dependencies)
        and declaration in dependencies
    )


def _repair_payload_hashes_for_attempt(
    structured: Sequence[Mapping[str, Any]], verified: Mapping[str, Any]
) -> tuple[str, ...]:
    design_id = verified.get("design_id")
    verified_attempt = int(verified.get("attempt", 0))
    repairs = sorted(
        (
            item
            for item in structured
            if item.get("design_id") == design_id
            and item.get("kind") == "repair"
            and int(item.get("attempt", 0)) <= verified_attempt
        ),
        key=lambda item: (
            int(item.get("attempt", 0)),
            int(item.get("transport_attempt", 1)),
        ),
    )
    return tuple(
        str((item.get("model_attempt") or {}).get("response_payload_sha256") or "")
        for item in repairs
    )


def _authorship_binding_errors(
    *,
    row: Mapping[str, Any],
    receipt: Mapping[str, Any],
    policy: CapabilityGatePolicy,
) -> tuple[str, ...]:
    errors: list[str] = []
    evidence = receipt.get("authorship_evidence")
    if not isinstance(evidence, Mapping):
        return ("authorship_evidence_missing",)
    semantic_hash = str(evidence.get("semantic_payload_sha256") or "")
    model_hash = str(evidence.get("model_response_sha256") or "")
    if evidence.get("origin") != "model":
        errors.append("authorship_origin_not_model")
    if evidence.get("semantic_payload_schema") != policy.semantic_payload_schema:
        errors.append("semantic_payload_schema_mismatch")
    if not semantic_hash.startswith("sha256:"):
        errors.append("semantic_payload_hash_missing")
    if not model_hash.startswith("sha256:"):
        errors.append("model_response_hash_missing")
    if evidence.get("renderer_name") != policy.renderer_name:
        errors.append("renderer_name_mismatch")
    if evidence.get("renderer_version") != policy.renderer_version:
        errors.append("renderer_version_mismatch")
    if evidence.get("renderer_added_semantic_atom_count") != 0:
        errors.append("renderer_added_semantic_atoms")
    if tuple(evidence.get("validation_only_steps", ())) != _AUTHORSHIP_VALIDATION_STEPS:
        errors.append("validation_only_steps_mismatch")
    source_hashes = tuple(
        str(item) for item in receipt.get("model_generated_source_hashes", ())
    )
    if not source_hashes or any(not item.startswith("sha256:") for item in source_hashes):
        errors.append("model_generated_source_hash_missing")
    if receipt.get("deterministic_solver_steps"):
        errors.append("deterministic_solver_steps_present")

    same_case_model_hashes = {
        _sha256_with_prefix(call.get("response_sha256"))
        for call in row.get("model_calls", ())
        if isinstance(call, Mapping)
        and str(call.get("purpose") or "").startswith("gadget-authoring")
        and bool(call.get("called"))
    }
    if model_hash not in same_case_model_hashes:
        errors.append("model_response_hash_not_bound_to_case_call")

    declaration = str(receipt.get("capability_declaration") or "")
    structured = _structured_gadget_receipts(row)
    verified_attempts = tuple(
        item
        for item in structured
        if item.get("status") == "lean-verified"
        and item.get("declaration") == declaration
    )
    matched = False
    for attempt in verified_attempts:
        model_attempt = attempt.get("model_attempt")
        semantic_checker = attempt.get("semantic_checker")
        renderer = attempt.get("renderer")
        gadget_plan = attempt.get("gadget_plan")
        if not all(
            isinstance(item, Mapping)
            for item in (model_attempt, semantic_checker, renderer, gadget_plan)
        ):
            continue
        assert isinstance(model_attempt, Mapping)
        assert isinstance(semantic_checker, Mapping)
        assert isinstance(renderer, Mapping)
        assert isinstance(gadget_plan, Mapping)
        outputs = tuple(
            int(variable)
            for gadget in gadget_plan.get("gadgets", ())
            if isinstance(gadget, Mapping)
            for variable in gadget.get("outputs", ())
        )
        relation_symbols = tuple(
            dict.fromkeys(
                str(constraint.get("target_symbol"))
                for gadget in gadget_plan.get("gadgets", ())
                if isinstance(gadget, Mapping)
                for constraint in gadget.get("constraints", ())
                if isinstance(constraint, Mapping)
            )
        )
        if (
            attempt.get("case_id") == row.get("case_id")
            and attempt.get("source_sha256") in source_hashes
            and model_attempt.get("model_response_sha256") == model_hash
            and model_attempt.get("semantic_payload_sha256") == semantic_hash
            and semantic_checker.get("semantic_payload_sha256") == semantic_hash
            and bool(semantic_checker.get("success"))
            and renderer.get("semantic_payload_sha256_before") == semantic_hash
            and renderer.get("semantic_payload_sha256_after") == semantic_hash
            and renderer.get("renderer_name") == evidence.get("renderer_name")
            and renderer.get("renderer_version") == evidence.get("renderer_version")
            and renderer.get("renderer_added_semantic_atom_count") == 0
            and gadget_plan.get("semantic_payload_sha256") == semantic_hash
            and gadget_plan.get("maximum_variable_count")
            == evidence.get("variable_count")
            and gadget_plan.get("constraint_count") == evidence.get("constraint_count")
            and outputs == tuple(evidence.get("output_mapping", ()))
            and relation_symbols == tuple(evidence.get("relation_symbols_used", ()))
            and _repair_payload_hashes_for_attempt(structured, attempt)
            == tuple(evidence.get("repair_payload_hashes", ()))
        ):
            matched = True
            break
    if not matched:
        errors.append("structured_lean_verified_receipt_binding_failed")
    return tuple(dict.fromkeys(errors))


def _explicit_budget_failure(row: Mapping[str, Any]) -> bool:
    if row.get("proof_status") == "BUDGET_EXHAUSTED":
        return True
    blocker = row.get("blocker")
    if not isinstance(blocker, Mapping):
        return False
    code = str(blocker.get("code") or "").lower()
    return "budget" in code


def _system_failure(row: Mapping[str, Any]) -> bool:
    return bool(row.get("exception_type")) or row.get("proof_status") in {
        "INTERNAL_ERROR",
        "INPUT_ERROR",
    }


def _required_case_status(
    row: Mapping[str, Any], policy: CapabilityGatePolicy
) -> tuple[str, tuple[str, ...]]:
    if _row_has_forbidden_dependency(row, policy):
        return "FORBIDDEN_DEPENDENCY", ("forbidden_dependency_detected",)
    if _row_disabled_plugin_violation(row, policy):
        return "ATTRIBUTION_MISMATCH", ("disabled_plugin_executed",)

    receipts = _gadget_contribution_receipts(row)
    wrong_final_receipts = tuple(
        receipt
        for receipt in receipts
        if bool(receipt.get("final_artifact_used"))
        and receipt.get("contribution_class")
        != ContributionClass.MODEL_GENERATED_CAPABILITY.value
    )
    if wrong_final_receipts:
        return "ATTRIBUTION_MISMATCH", ("final_gadget_contribution_class_mismatch",)

    model_receipts = tuple(
        receipt
        for receipt in receipts
        if receipt.get("contribution_class")
        == ContributionClass.MODEL_GENERATED_CAPABILITY.value
    )
    binding_errors = {
        str(receipt.get("capability_declaration") or ""): _authorship_binding_errors(
            row=row, receipt=receipt, policy=policy
        )
        for receipt in model_receipts
    }
    valid_bindings = tuple(
        receipt
        for receipt in model_receipts
        if not binding_errors[str(receipt.get("capability_declaration") or "")]
    )
    verification = row.get("verification")
    verification_passed = isinstance(verification, Mapping) and bool(
        verification.get("kernel_verified")
    ) and bool(verification.get("independent_replay_passed"))
    successful_receipts = tuple(
        receipt
        for receipt in valid_bindings
        if row.get("proof_status") == "VERIFIED"
        and bool(receipt.get("final_artifact_used"))
        and bool(receipt.get("forbidden_audit_passed"))
        and bool(receipt.get("independent_lean_passed"))
        and verification_passed
        and _positive_dependency_audit_passed(
            row, str(receipt.get("capability_declaration") or "")
        )
    )
    if successful_receipts:
        return "MODEL_GADGET_VERIFIED_AND_FINAL_USED", ()
    if model_receipts and not valid_bindings:
        return (
            "ATTRIBUTION_MISMATCH",
            tuple(
                dict.fromkeys(
                    error for errors in binding_errors.values() for error in errors
                )
            ),
        )
    if valid_bindings and any(
        not bool(receipt.get("independent_lean_passed")) for receipt in valid_bindings
    ):
        return "LEAN_MATERIALIZATION_FAILED", ("independent_lean_failed",)
    if valid_bindings and any(
        not bool(receipt.get("final_artifact_used"))
        or not _positive_dependency_audit_passed(
            row, str(receipt.get("capability_declaration") or "")
        )
        for receipt in valid_bindings
    ):
        return "CAPABILITY_NOT_FINAL_USED", ("kernel_dependency_final_use_missing",)
    if model_receipts:
        return "ATTRIBUTION_MISMATCH", ("model_receipt_not_gate_eligible",)

    structured = _structured_gadget_receipts(row)
    if any(item.get("status") == "lean-verified" for item in structured):
        return "ATTRIBUTION_MISMATCH", ("verified_plan_missing_contribution_receipt",)
    if _explicit_budget_failure(row):
        return "BUDGET_EXHAUSTED", ("explicit_budget_exhaustion",)
    if any(
        item.get("status") == "transport-escalation-budget-exhausted"
        for item in structured
    ):
        return "BUDGET_EXHAUSTED", ("token_escalation_budget_exhausted",)
    if _system_failure(row):
        return "SYSTEM_ERROR", ("system_or_input_failure",)
    if any(item.get("status") == "lean-failed" for item in structured):
        return "LEAN_MATERIALIZATION_FAILED", ("lean_materialization_failed",)
    if any(
        item.get("status") == "semantic-repair-escalation-exhausted"
        for item in structured
    ):
        return "GADGET_SEMANTIC_REPAIR_FAILED", (
            "semantic_repair_search_nonconvergent",
        )
    if any(
        item.get("status") == "transport-escalation-exhausted"
        for item in structured
    ):
        return "MODEL_SEARCH_NONCONVERGENT", (
            "bounded_16k_to_64k_search_nonconvergent",
        )
    if any(item.get("status") == "semantic-failed" for item in structured):
        return "GADGET_SEMANTIC_COUNTEREXAMPLE", ("finite_counterexample",)
    if any(
        item.get("status") in {"schema-failed", "renderer-failed"}
        and (item.get("failure") or {}).get("error_code")
        == "gadget_plan_schema_invalid"
        for item in structured
    ):
        return "GADGET_PLAN_SCHEMA_INVALID", ("gadget_plan_schema_invalid",)
    if any(
        item.get("status")
        in {
            "schema-failed",
            "renderer-failed",
            "duplicate-semantic-payload-rejected",
            "duplicate-source-rejected",
        }
        for item in structured
    ):
        return "MODEL_PROTOCOL_INVALID", ("model_protocol_invalid",)
    if any(item.get("status") == "transport-failed" for item in structured):
        return "MODEL_PLAN_NOT_PRODUCED", ("model_transport_returned_no_plan",)
    gadget_calls = tuple(
        call
        for call in row.get("model_calls", ())
        if isinstance(call, Mapping)
        and str(call.get("purpose") or "").startswith("gadget-authoring")
    )
    if gadget_calls:
        return "MODEL_PLAN_NOT_PRODUCED", ("gadget_call_produced_no_plan",)
    route_reached = bool(structured) or any(
        isinstance(plan, Mapping)
        and plan.get("capability_kind") in _GADGET_CAPABILITY_KINDS
        for plan in row.get("capability_plans", ())
    )
    if not route_reached:
        return "ROUTE_NOT_REACHED", ("structured_gadget_route_not_reached",)
    return "MODEL_PLAN_NOT_PRODUCED", ("structured_route_produced_no_model_plan",)


def evaluate_gadget_authoring_gate(
    report: Mapping[str, Any], policy: CapabilityGatePolicy
) -> dict[str, Any]:
    rows = tuple(
        row for row in report.get("cases", ()) if isinstance(row, Mapping)
    )
    row_ids = tuple(str(row.get("case_id") or "") for row in rows)
    rows_by_id = {str(row.get("case_id") or ""): row for row in rows}
    expected_ids = tuple(policy.selected_case_ids)
    expected_set = set(expected_ids)
    suite = report.get("suite") if isinstance(report.get("suite"), Mapping) else {}
    validation = (
        report.get("validation")
        if isinstance(report.get("validation"), Mapping)
        else {}
    )
    real_api = (
        report.get("real_api")
        if isinstance(report.get("real_api"), Mapping)
        else {}
    )
    enforcement = (
        report.get("policy_enforcement")
        if isinstance(report.get("policy_enforcement"), Mapping)
        else {}
    )
    evaluation_protocol = (
        report.get("evaluation_protocol")
        if isinstance(report.get("evaluation_protocol"), Mapping)
        else {}
    )
    configuration_freeze = (
        report.get("configuration_freeze")
        if isinstance(report.get("configuration_freeze"), Mapping)
        else {}
    )

    case_results: list[dict[str, Any]] = []
    for case_id in expected_ids:
        role = "anchor" if case_id in set(policy.anchor_case_ids) else "required"
        row = rows_by_id.get(case_id)
        if row is None:
            status = "SYSTEM_ERROR"
            reasons = ("case_missing_from_report",)
            proof_status = None
        elif role == "anchor":
            proof_status = row.get("proof_status")
            if _row_has_forbidden_dependency(row, policy):
                status = "FORBIDDEN_DEPENDENCY"
                reasons = ("forbidden_dependency_detected",)
            elif proof_status == "VERIFIED":
                status = "ANCHOR_REUSE_VERIFIED"
                reasons = ()
            elif _explicit_budget_failure(row):
                status = "BUDGET_EXHAUSTED"
                reasons = ("explicit_budget_exhaustion",)
            elif _system_failure(row):
                status = "SYSTEM_ERROR"
                reasons = ("system_or_input_failure",)
            else:
                status = "LEAN_MATERIALIZATION_FAILED"
                reasons = ("anchor_root_not_verified",)
        else:
            proof_status = row.get("proof_status")
            status, reasons = _required_case_status(row, policy)
        case_results.append(
            {
                "case_id": case_id,
                "role": role,
                "proof_status": proof_status,
                "status": status,
                "reasons": list(reasons),
            }
        )

    gadget_receipts = tuple(
        receipt
        for row in rows
        for receipt in _gadget_contribution_receipts(row)
    )
    model_receipts = tuple(
        (row, receipt)
        for row in rows
        for receipt in _gadget_contribution_receipts(row)
        if receipt.get("contribution_class")
        == ContributionClass.MODEL_GENERATED_CAPABILITY.value
    )
    all_model_receipts_replayable = all(
        not _authorship_binding_errors(row=row, receipt=receipt, policy=policy)
        for row, receipt in model_receipts
    )
    final_used_receipts = tuple(
        (row, receipt)
        for row in rows
        for receipt in _gadget_contribution_receipts(row)
        if bool(receipt.get("final_artifact_used"))
    )
    final_use_receipts_kernel_asserted = all(
        _positive_dependency_audit_passed(
            row, str(receipt.get("capability_declaration") or "")
        )
        for row, receipt in final_used_receipts
    )
    no_final_deterministic_gadget = all(
        receipt.get("contribution_class")
        == ContributionClass.MODEL_GENERATED_CAPABILITY.value
        for _, receipt in final_used_receipts
    )
    no_disabled_plugin_execution = not any(
        _row_disabled_plugin_violation(row, policy) for row in rows
    )
    selected_ids_reported = tuple(str(item) for item in suite.get("selected_case_ids", ()))
    completed_ids_reported = tuple(
        str(item) for item in suite.get("completed_case_ids", ())
    )
    structured_validation_keys = (
        "structured_gadget_briefs_are_answer_free",
        "structured_gadget_renderer_added_zero_semantic_atoms",
        "structured_gadget_receipts_are_case_bound",
        "structured_gadget_source_cores_match_policy",
        "structured_gadget_unique_plans_have_semantic_checker_receipts",
        "structured_gadget_lean_attempts_passed_semantic_checker",
        "structured_gadget_semantic_failures_skipped_lean",
        "structured_gadget_checker_versions_match_policy",
        "structured_gadget_checker_inputs_are_hash_bound",
        "structured_gadget_counterexamples_are_direction_complete",
        "structured_gadget_authorship_evidence_present",
        "structured_gadget_authorship_evidence_is_model_origin",
        "structured_gadget_authorship_hashes_are_case_bound",
        "structured_gadget_authorship_semantic_hashes_match",
        "structured_gadget_authorship_repair_hashes_match",
        "structured_gadget_final_use_is_kernel_dependency_audited",
        "structured_gadget_token_profiles_match_policy",
        "structured_gadget_escalations_follow_length_on_same_prompt",
        "structured_gadget_escalation_lineage_complete",
        "structured_gadget_nonconvergence_receipts_complete",
        "structured_gadget_source_route_attribution_complete",
    )
    integrity_checks = {
        "case_rows_match_policy_exactly": (
            len(row_ids) == len(set(row_ids))
            and set(row_ids) == expected_set
            and len(row_ids) == len(expected_ids)
        ),
        "suite_counts_match_policy": (
            int(suite.get("selected_case_count", -1)) == len(expected_ids)
            and int(suite.get("completed_case_count", -1)) == len(expected_ids)
        ),
        "suite_selected_case_ids_match_policy": (
            len(selected_ids_reported) == len(set(selected_ids_reported))
            and set(selected_ids_reported) == expected_set
        ),
        "suite_completed_case_ids_match_policy": (
            len(completed_ids_reported) == len(set(completed_ids_reported))
            and set(completed_ids_reported) == expected_set
        ),
        "policy_enforcement_passed": bool(enforcement.get("integrity_passed")),
        "real_api_was_called": int(real_api.get("total_calls", 0)) > 0,
        "real_api_call_accounting_complete": bool(
            real_api.get("call_accounting_complete")
        ),
        "all_called_requests_http_200": (
            int(real_api.get("total_calls", 0))
            == int(real_api.get("http_200_calls", -1))
            and bool(validation.get("all_called_requests_http_200"))
        ),
        "all_structured_validation_receipts_passed": all(
            bool(validation.get(key)) for key in structured_validation_keys
        ),
        "forbidden_dependency_count_is_zero": (
            int(validation.get("forbidden_direct_or_transitive_dependency_count", 0))
            == 0
            and not any(_row_has_forbidden_dependency(row, policy) for row in rows)
        ),
        "no_disabled_plugin_execution": no_disabled_plugin_execution,
        "no_final_deterministic_or_hybrid_gadget": no_final_deterministic_gadget,
        "all_model_authorship_receipts_replayable": all_model_receipts_replayable,
        "all_final_use_receipts_kernel_dependency_asserted": (
            final_use_receipts_kernel_asserted
        ),
    }
    if bool(evaluation_protocol.get("requires_configuration_freeze")):
        integrity_checks["configuration_freeze_integrity_passed"] = (
            bool(validation.get("configuration_freeze_integrity_passed"))
            and bool(configuration_freeze.get("integrity_passed"))
            and configuration_freeze.get("policy_version")
            == policy.policy_version
            and configuration_freeze.get("policy_sha256") == policy.policy_sha256
            and set(configuration_freeze.get("selected_case_ids", ()))
            == expected_set
        )
    integrity_passed = all(integrity_checks.values())
    status_counts = Counter(item["status"] for item in case_results)
    authored_success_count = status_counts[
        "MODEL_GADGET_VERIFIED_AND_FINAL_USED"
    ]
    anchor_verified_count = status_counts["ANCHOR_REUSE_VERIFIED"]
    required_case_count = len(policy.required_case_ids)
    route_failure_statuses = {
        "ROUTE_NOT_REACHED",
        "MODEL_PLAN_NOT_PRODUCED",
        "MODEL_SEARCH_NONCONVERGENT",
        "MODEL_PROTOCOL_INVALID",
        "GADGET_PLAN_SCHEMA_INVALID",
    }
    strict_gate_passed = (
        integrity_passed
        and anchor_verified_count == len(policy.anchor_case_ids)
        and authored_success_count == required_case_count
    )
    return {
        "gate": policy.name,
        "policy_name": policy.name,
        "policy_version": policy.policy_version,
        "policy_sha256": policy.policy_sha256,
        "required_case_count": required_case_count,
        "anchor_case_count": len(policy.anchor_case_ids),
        "integrity_checks": integrity_checks,
        "integrity_passed": integrity_passed,
        "authored_success_count": authored_success_count,
        "authored_success_rate": (
            authored_success_count / required_case_count
            if required_case_count
            else 0.0
        ),
        "anchor_verified_count": anchor_verified_count,
        "route_failure_count": sum(
            status_counts[status] for status in route_failure_statuses
        ),
        "mathematical_failure_count": status_counts[
            "GADGET_SEMANTIC_COUNTEREXAMPLE"
        ],
        "semantic_repair_failure_count": status_counts[
            "GADGET_SEMANTIC_REPAIR_FAILED"
        ],
        "search_nonconvergence_count": status_counts[
            "MODEL_SEARCH_NONCONVERGENT"
        ],
        "lean_only_failure_count": status_counts["LEAN_MATERIALIZATION_FAILED"],
        "system_failure_count": status_counts["SYSTEM_ERROR"],
        "budget_exhausted_count": status_counts["BUDGET_EXHAUSTED"],
        "status_counts": {
            status: status_counts[status]
            for status in GADGET_AUTHORING_CASE_STATUSES
            if status_counts[status]
        },
        "case_results": case_results,
        "strict_authorship_gate_evaluated": True,
        "strict_authorship_gate_passed": strict_gate_passed,
        "strict_gate_passed": strict_gate_passed,
        "gate_passed": strict_gate_passed,
        "policy_enforcement_passed": bool(enforcement.get("integrity_passed")),
        "model_authorship_receipt_count": len(model_receipts),
        "gadget_contribution_receipt_count": len(gadget_receipts),
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run one capability gate on the Boolean CSP suite"
    )
    parser.add_argument(
        "--gate",
        choices=(
            "direct-tm",
            "semantic",
            "gadget-authoring",
            "gadget-authoring-dev",
            "gadget-authoring-validation",
            "gadget-authoring-heldout",
        ),
        required=True,
    )
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--report-path", type=Path, required=True)
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--lean-timeout", type=int, default=600)
    parser.add_argument("--model", default=None)
    parser.add_argument("--model-timeout", type=int, default=900)
    parser.add_argument("--model-max-tokens", type=int, default=64000)
    parser.add_argument("--model-max-retries", type=int, default=0)
    parser.add_argument("--reasoning-effort", default="low")
    parser.add_argument(
        "--freeze-manifest",
        type=Path,
        default=None,
        help="machine-verifiable configuration freeze for staged evaluation",
    )
    parser.add_argument(
        "--evaluation-role",
        choices=("frozen-engineering-full30", "frozen-final-full30"),
        default=None,
        help="label a frozen full-suite run without changing its configuration",
    )
    return parser


def main() -> int:
    parser = build_parser()
    arguments = parser.parse_args()
    suite = None
    freeze_case_set = None
    evaluation_protocol: dict[str, Any] | None = None
    gadget_authoring_gates = {
        "gadget-authoring",
        "gadget-authoring-dev",
        "gadget-authoring-validation",
        "gadget-authoring-heldout",
    }
    if arguments.gate in gadget_authoring_gates:
        if arguments.gate == "gadget-authoring-dev":
            if arguments.freeze_manifest is not None:
                parser.error("development canaries do not consume a freeze manifest")
            policy = gadget_authoring_dev_policy()
            suite = load_gadget_authoring_dev_suite(
                ROOT
                / "Benchmark"
                / "Hardness"
                / "Development"
                / "boolean_csp_gadget_authoring_dev_v1.json"
            )
            evaluation_protocol = {
                "run_role": "development-canary",
                "formal_score": False,
                "suite_kind": "non-scoring-answer-free-fixtures",
                "requires_configuration_freeze": False,
            }
        elif arguments.gate == "gadget-authoring-validation":
            if arguments.freeze_manifest is None:
                parser.error("frozen validation requires --freeze-manifest")
            policy = gadget_authoring_validation_policy()
            public_suite = load_suite(
                ROOT
                / "Benchmark"
                / "Hardness"
                / "Suites"
                / "boolean_csp_np_hard_public_v1.json"
            )
            selected = tuple(
                case
                for case in public_suite.cases
                if case.case_id
                in set(BOOLEAN_CSP_GADGET_AUTHORING_VALIDATION_CASE_IDS)
            )
            suite = replace(public_suite, cases=selected)
            freeze_case_set = "validation"
            evaluation_protocol = {
                "run_role": "frozen-validation",
                "formal_score": False,
                "suite_kind": "public-validation-q05-q10",
                "requires_configuration_freeze": True,
            }
        elif arguments.gate == "gadget-authoring-heldout":
            if arguments.freeze_manifest is None:
                parser.error("frozen heldout evaluation requires --freeze-manifest")
            policy = gadget_authoring_heldout_policy()
            public_suite = load_suite(
                ROOT
                / "Benchmark"
                / "Hardness"
                / "Suites"
                / "boolean_csp_np_hard_public_v1.json"
            )
            selected = tuple(
                case
                for case in public_suite.cases
                if case.case_id in set(BOOLEAN_CSP_GADGET_AUTHORING_HELDOUT_CASE_IDS)
            )
            suite = replace(public_suite, cases=selected)
            freeze_case_set = "heldout"
            evaluation_protocol = {
                "run_role": "frozen-heldout",
                "formal_score": False,
                "suite_kind": "public-heldout-q11-q30",
                "requires_configuration_freeze": True,
            }
        else:
            policy = gadget_authoring_policy()
            freeze_case_set = (
                "full" if arguments.freeze_manifest is not None else None
            )
            run_role = arguments.evaluation_role or (
                "frozen-engineering-full30"
                if arguments.freeze_manifest is not None
                else "engineering-unfrozen-full30"
            )
            if arguments.evaluation_role is not None and arguments.freeze_manifest is None:
                parser.error("a frozen evaluation role requires --freeze-manifest")
            evaluation_protocol = {
                "run_role": run_role,
                "formal_score": run_role == "frozen-final-full30",
                "suite_kind": "public-full30",
                "requires_configuration_freeze": (
                    arguments.freeze_manifest is not None
                ),
            }
        gate_forbidden = ()
    else:
        if arguments.freeze_manifest is not None or arguments.evaluation_role is not None:
            parser.error("freeze options apply only to gadget-authoring gates")
        policy = _legacy_gate_policy(arguments.gate)
        gate_forbidden = (
            DIRECT_TM_FORBIDDEN
            if arguments.gate == "direct-tm"
            else SEMANTIC_FORBIDDEN
        )
    report = run_recursive_boolean_csp_regression(
        root=ROOT,
        output_root=arguments.output_root,
        env_file=arguments.env_file,
        jobs=arguments.jobs,
        profile="benchmark",
        lean_timeout_seconds=arguments.lean_timeout,
        model=arguments.model,
        model_timeout_seconds=arguments.model_timeout,
        model_max_tokens=arguments.model_max_tokens,
        model_max_retries=arguments.model_max_retries,
        reasoning_effort=arguments.reasoning_effort,
        report_path=None,
        extra_forbidden_declarations=gate_forbidden,
        excluded_candidate_declarations=TRANSPORT_CANDIDATE_EXCLUSIONS,
        gate_policy=(
            policy
            if arguments.gate in gadget_authoring_gates
            else None
        ),
        suite=suite,
        freeze_manifest=arguments.freeze_manifest,
        freeze_case_set=freeze_case_set,
        evaluation_protocol=evaluation_protocol,
    )
    if arguments.gate in gadget_authoring_gates:
        report["capability_gate_evaluation"] = evaluate_gadget_authoring_gate(
            report, policy
        )
    else:
        report["capability_gate_evaluation"] = evaluate_capability_gate(
            report, arguments.gate, policy
        )
    report["route_policy"]["capability_gate"] = arguments.gate
    arguments.report_path.parent.mkdir(parents=True, exist_ok=True)
    arguments.report_path.write_text(
        json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    (arguments.output_root / "summary.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True))
    passed = report["capability_gate_evaluation"].get(
        "gate_passed",
        report["capability_gate_evaluation"].get("policy_enforcement_passed"),
    )
    return 0 if passed else 2


if __name__ == "__main__":
    raise SystemExit(main())


__all__ = [
    "DIRECT_TM_FORBIDDEN",
    "SEMANTIC_FORBIDDEN",
    "TRANSPORT_CANDIDATE_EXCLUSIONS",
    "evaluate_capability_gate",
    "evaluate_gadget_authoring_gate",
    "evaluate_gadget_authoring_policy_enforcement",
    "main",
]
