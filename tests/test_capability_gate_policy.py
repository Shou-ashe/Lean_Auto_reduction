from __future__ import annotations

from copy import deepcopy
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from agent.generative_reduction.capability_gate_policy import (
    CapabilityGatePolicy,
    FINITE_GADGET_NAMESPACE,
    GADGET_AUTHORING_DISABLED_FINITE_PLUGINS,
    gadget_authoring_dev_policy,
    gadget_authoring_policy,
)
from agent.generative_reduction.boolean_csp_gadget_authoring import (
    GADGET_AUTHORING_ALLOWED_SOURCE_CORES,
    GADGET_PLAN_SCHEMA,
    GADGET_RENDERER_VERSION,
    GADGET_SEMANTIC_CHECKER_VERSION,
)
from agent.generative_reduction.boolean_csp_capability_gate import (
    evaluate_gadget_authoring_gate,
    evaluate_gadget_authoring_policy_enforcement,
)
from agent.generative_reduction.boolean_csp_regression import _policy_enforcement
from agent.generative_reduction.models import CapabilityKind, ContributionClass
from agent.generative_reduction.orchestrator import filter_finite_synthesis_plugins
from agent.generative_reduction.plugins.registry import load_plugin
from agent.generative_reduction.recursive_runtime import (
    _gadget_authoring_action_rejection,
    _gadget_authoring_data_witness_entries,
)
from agent.hardness.boolean_csp_gadget_authoring_dev import (
    load_gadget_authoring_dev_suite,
)
from agent.hardness.boolean_csp_np_hard_benchmark import load_suite


ROOT = Path(__file__).resolve().parents[1]
SUITE = (
    ROOT
    / "Benchmark"
    / "Hardness"
    / "Suites"
    / "boolean_csp_np_hard_public_v1.json"
)
DEV_SUITE = (
    ROOT
    / "Benchmark"
    / "Hardness"
    / "Development"
    / "boolean_csp_gadget_authoring_dev_v1.json"
)


def test_gadget_authoring_policy_partitions_the_full_public_suite() -> None:
    suite = load_suite(SUITE)
    policy = gadget_authoring_policy()

    policy.validate_case_ids(tuple(case.case_id for case in suite.cases))
    assert set(policy.required_case_ids).isdisjoint(policy.anchor_case_ids)
    assert set(policy.selected_case_ids) == {case.case_id for case in suite.cases}
    assert policy.anchor_case_ids == (
        "q-b01-canonical-three-sat-like",
        "q-b03-positive-nae3",
        "q-b04-positive-exactly-one3",
    )
    assert "q-b07-positive-exactly-two3" in policy.required_case_ids
    assert policy.semantic_payload_schema == GADGET_PLAN_SCHEMA
    assert policy.renderer_version == GADGET_RENDERER_VERSION
    assert policy.checker_version == GADGET_SEMANTIC_CHECKER_VERSION
    assert policy.max_gadget_variable_count == 12
    assert policy.max_gadget_constraint_count == 24
    assert policy.max_gadget_repairs == 5
    assert policy.gadget_authoring_base_max_tokens == 16_000
    assert policy.gadget_authoring_escalated_max_tokens == 64_000
    assert policy.gadget_authoring_reasoning_effort == "low"
    assert policy.max_gadget_token_escalations_per_attempt == 1
    assert policy.allowed_gadget_source_declarations == (
        GADGET_AUTHORING_ALLOWED_SOURCE_CORES
    )
    assert policy.policy_sha256 == gadget_authoring_policy().policy_sha256


def test_gadget_authoring_dev_policy_partitions_only_non_scoring_canaries() -> None:
    suite = load_gadget_authoring_dev_suite(DEV_SUITE)
    policy = gadget_authoring_dev_policy()

    policy.validate_case_ids(tuple(case.case_id for case in suite.cases))
    assert policy.anchor_case_ids == ()
    assert policy.required_case_ids == tuple(case.case_id for case in suite.cases)
    assert policy.max_gadget_variable_count == 8
    assert policy.max_gadget_constraint_count == 16
    assert policy.allowed_gadget_source_declarations == (
        GADGET_AUTHORING_ALLOWED_SOURCE_CORES
    )


def test_gadget_authoring_action_filter_rejects_unsupported_source_core() -> None:
    policy = gadget_authoring_policy()
    target = (
        "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case02PositiveNAE4.gamma"
    )
    unsupported = (
        "ComplexityReduction.Domain.BooleanCSP.Hardness.LanguageInterpretation "
        "ComplexityReduction.Domain.BooleanCSP.Hardness.exactlyTwo3Core "
        + target
    )
    allowed = (
        "ComplexityReduction.Domain.BooleanCSP.Hardness.LanguageInterpretation "
        "ComplexityReduction.Domain.BooleanCSP.Hardness.nae3Core "
        + target
    )
    action = SimpleNamespace(residual_obligation_ids=("gadget",))
    root_goal = SimpleNamespace(exact_type="root")

    rejected = _gadget_authoring_action_rejection(
        policy=policy,
        case_id="q-b02-positive-nae4",
        goal=root_goal,
        plan=SimpleNamespace(
            residual_obligations=(
                SimpleNamespace(obligation_id="gadget", exact_type=unsupported),
            )
        ),
        action=action,
    )
    accepted = _gadget_authoring_action_rejection(
        policy=policy,
        case_id="q-b02-positive-nae4",
        goal=root_goal,
        plan=SimpleNamespace(
            residual_obligations=(
                SimpleNamespace(obligation_id="gadget", exact_type=allowed),
            )
        ),
        action=action,
    )

    assert rejected is not None and "exactlyTwo3Core" in rejected
    assert accepted is None


def test_gadget_authoring_action_filter_allows_unresolved_root_source() -> None:
    policy = gadget_authoring_policy()
    target = (
        "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case02PositiveNAE4.gamma"
    )
    unresolved = (
        "ComplexityReduction.Domain.BooleanCSP.Hardness.LanguageInterpretation "
        f"?m.12 {target}"
    )
    accepted = _gadget_authoring_action_rejection(
        policy=policy,
        case_id="q-b02-positive-nae4",
        goal=SimpleNamespace(exact_type="root"),
        plan=SimpleNamespace(
            residual_obligations=(
                SimpleNamespace(obligation_id="gadget", exact_type=unresolved),
            )
        ),
        action=SimpleNamespace(residual_obligation_ids=("gadget",)),
    )

    assert accepted is None


def test_gadget_authoring_data_witness_filter_runs_before_lookahead() -> None:
    policy = gadget_authoring_policy()
    allowed = tuple(
        SimpleNamespace(candidate_id=f"allowed-{index}", declaration=declaration)
        for index, declaration in enumerate(
            policy.allowed_gadget_source_declarations
        )
    )
    unsupported = SimpleNamespace(
        candidate_id="unsupported",
        declaration=(
            "ComplexityReduction.Domain.BooleanCSP.Hardness.exactlyTwo3Core"
        ),
    )
    source_slot = SimpleNamespace(
        slot_id="source",
        dependency_slot_ids=(),
        instantiated_exact_type="ComplexityReduction.Domain.BooleanCSP.Gamma",
    )
    interpretation_slot = SimpleNamespace(
        slot_id="interpretation",
        dependency_slot_ids=("source",),
        instantiated_exact_type=(
            "ComplexityReduction.Domain.BooleanCSP.Hardness."
            "LanguageInterpretation ?m.12 targetGamma"
        ),
    )

    filtered = _gadget_authoring_data_witness_entries(
        policy=policy,
        case_id="q-b02-positive-nae4",
        goal=SimpleNamespace(
            exact_type="ComplexityReduction.Domain.BooleanCSP.Gamma",
            producer_slot_id="source",
        ),
        frame=SimpleNamespace(slots=(source_slot, interpretation_slot)),
        entries=(*allowed, unsupported),
    )

    assert filtered == allowed


def test_gadget_authoring_policy_forbids_qb07_reuse_and_search_helpers() -> None:
    policy = gadget_authoring_policy()

    for declaration in (
        "ComplexityReduction.Domain.BooleanCSP.Hardness.oneInThreeGadgetOfExactlyTwo3",
        "ComplexityReduction.Domain.BooleanCSP.Hardness.exactlyTwo3InterpretsOneInThree",
        "ComplexityReduction.Domain.BooleanCSP.Hardness.exactlyTwo3CoreNPHard_of_oneInThree",
        "ComplexityReduction.Domain.BooleanCSP.Hardness.exactlyTwo3CoreNPHard",
        FINITE_GADGET_NAMESPACE + "gadgetOfPlannedSearch",
        FINITE_GADGET_NAMESPACE + "gadgetOfCandidates",
        FINITE_GADGET_NAMESPACE + "templates",
    ):
        assert not policy.candidate_declaration_allowed(declaration)
    assert policy.candidate_declaration_allowed(
        FINITE_GADGET_NAMESPACE + "Spec.toGadget"
    )
    assert policy.candidate_declaration_allowed(
        FINITE_GADGET_NAMESPACE + "FiniteFormula.Satisfies"
    )


def test_gadget_authoring_policy_filters_only_deterministic_gadget_plugins() -> None:
    finite_plugins = load_plugin("boolean_csp").finite_synthesis_plugins
    policy = gadget_authoring_policy()

    runtime, disabled = filter_finite_synthesis_plugins(finite_plugins, policy)
    assert tuple(plugin.name for plugin in disabled) == (
        GADGET_AUTHORING_DISABLED_FINITE_PLUGINS
    )
    assert tuple(plugin.name for plugin in runtime) == (
        "boolean-csp-direct-tm-compiler",
        "boolean-csp-semantic-compiler",
    )
    production, production_disabled = filter_finite_synthesis_plugins(
        finite_plugins, None
    )
    assert production == finite_plugins
    assert production_disabled == ()


def test_gate_policy_rejects_an_unknown_disabled_plugin() -> None:
    policy = replace(
        gadget_authoring_policy(),
        disabled_finite_synthesis_plugins=("unknown-finite-plugin",),
    )
    finite_plugins = load_plugin("boolean_csp").finite_synthesis_plugins

    with pytest.raises(ValueError, match="unknown finite plugins"):
        filter_finite_synthesis_plugins(finite_plugins, policy)


def test_policy_enforcement_rejects_a_disabled_plugin_action() -> None:
    policy = CapabilityGatePolicy(
        name="gadget-authoring",
        policy_version="test-policy-v1",
        required_case_ids=("required",),
        anchor_case_ids=("anchor",),
        required_capability_kind=CapabilityKind.GADGET,
        required_contribution_classes=(ContributionClass.MODEL_GENERATED_CAPABILITY,),
        disabled_finite_synthesis_plugins=(
            "boolean-csp-explicit-finite-gadget",
        ),
    )
    rows = (
        {
            "case_id": "anchor",
            "proof_tree": (),
            "gate_policy_runtime": None,
        },
        {
            "case_id": "required",
            "gate_policy_runtime": {
                "policy": {"policy_sha256": policy.policy_sha256},
                "case_id": "required",
                "case_role": "required",
                "structured_gadget_authoring_enabled": True,
                "disabled_finite_synthesis_plugins": [
                    "boolean-csp-explicit-finite-gadget"
                ],
                "runtime_finite_synthesis_plugins": [
                    "boolean-csp-direct-tm-compiler",
                    "boolean-csp-semantic-compiler",
                ],
            },
            "proof_tree": (
                {
                    "provider": "plugin",
                    "solver": "boolean-csp-explicit-finite-gadget",
                },
            ),
        },
    )

    enforcement = _policy_enforcement(rows, policy)
    assert not enforcement["integrity_passed"]
    assert enforcement["policy_violations"] == [
        {
            "case_id": "required",
            "code": "disabled_plugin_executed",
            "plugin": "boolean-csp-explicit-finite-gadget",
        }
    ]


def test_policy_gate_evaluation_checks_real_api_and_all_required_receipts() -> None:
    policy = CapabilityGatePolicy(
        name="gadget-authoring",
        policy_version="test-policy-v1",
        required_case_ids=("required",),
        anchor_case_ids=("anchor",),
        required_capability_kind=CapabilityKind.GADGET,
        required_contribution_classes=(ContributionClass.MODEL_GENERATED_CAPABILITY,),
    )
    report = {
        "suite": {"completed_case_count": 2, "selected_case_count": 2},
        "real_api": {"total_calls": 1},
        "validation": {
            "all_called_requests_http_200": True,
            "forbidden_direct_or_transitive_dependency_count": 0,
        },
        "policy_enforcement": {
            "integrity_passed": True,
            "required_case_runtime_receipt_count": 1,
        },
    }

    evaluation = evaluate_gadget_authoring_policy_enforcement(report, policy)
    assert evaluation["policy_enforcement_passed"]
    assert not evaluation["strict_authorship_gate_evaluated"]


def _synthetic_gadget_gate_report() -> dict[str, object]:
    policy = gadget_authoring_policy()
    rows: list[dict[str, object]] = []
    for ordinal, case_id in enumerate(policy.selected_case_ids, start=1):
        verification = {
            "kernel_verified": True,
            "independent_replay_passed": True,
        }
        runtime = {
            "case_id": case_id,
            "case_role": (
                "anchor" if case_id in policy.anchor_case_ids else "required"
            ),
            "disabled_plugins_absent_from_runtime": True,
            "runtime_finite_synthesis_plugins": [
                "boolean-csp-direct-tm-compiler",
                "boolean-csp-semantic-compiler",
            ],
        }
        if case_id in policy.anchor_case_ids:
            rows.append(
                {
                    "case_id": case_id,
                    "proof_status": "VERIFIED",
                    "proof_tree": [],
                    "gate_policy_runtime": runtime,
                    "verification": verification,
                    "model_calls": [],
                    "capability_plans": [],
                    "typed_capability_plans": [],
                    "contribution_receipts": [],
                    "final_route_audit_receipt": {
                        "passed": True,
                        "forbidden_dependencies_passed": True,
                        "required_dependencies": [],
                        "required_dependency_audit_emitted": False,
                        "required_dependency_count": 0,
                        "required_dependencies_passed": True,
                    },
                }
            )
            continue
        semantic_hash = "sha256:" + f"{ordinal:064x}"
        model_hash = "sha256:" + f"{ordinal + 100:064x}"
        response_payload_hash = "sha256:" + f"{ordinal + 200:064x}"
        source_hash = "sha256:" + f"{ordinal + 300:064x}"
        declaration = f"Synthetic.Generated.capability{ordinal}"
        design_id = f"design-{ordinal}"
        gadget_plan = {
            "schema": GADGET_PLAN_SCHEMA,
            "source_core": "nae3",
            "gadgets": [
                {
                    "source_symbol": "source-0",
                    "variable_count": 3,
                    "outputs": [0, 1, 2],
                    "constraints": [
                        {"target_symbol": "target-0", "vars": [0, 1, 2]}
                    ],
                }
            ],
            "mathematical_rationale": "synthetic fixture",
            "plan_id": f"gadget-plan-{ordinal}",
            "semantic_payload_sha256": semantic_hash,
            "constraint_count": 1,
            "maximum_variable_count": 3,
        }
        authorship = {
            "semantic_payload_schema": GADGET_PLAN_SCHEMA,
            "semantic_payload_sha256": semantic_hash,
            "model_response_sha256": model_hash,
            "origin": "model",
            "renderer_name": policy.renderer_name,
            "renderer_version": policy.renderer_version,
            "renderer_added_semantic_atom_count": 0,
            "validation_only_steps": [
                "schema-validate-model-payload",
                "check-single-explicit-plan-over-finite-truth-tables",
                "render-plan-without-semantic-additions",
                "lean-kernel-check-spec-correct-and-to-gadget",
            ],
            "variable_count": 3,
            "constraint_count": 1,
            "output_mapping": [0, 1, 2],
            "relation_symbols_used": ["target-0"],
            "repair_payload_hashes": [],
        }
        rows.append(
            {
                "case_id": case_id,
                "proof_status": "VERIFIED",
                "proof_tree": [],
                "gate_policy_runtime": runtime,
                "verification": verification,
                "model_calls": [
                    {
                        "purpose": "gadget-authoring-initial",
                        "called": True,
                        "ok": True,
                        "status_code": 200,
                        "response_sha256": model_hash.removeprefix("sha256:"),
                    }
                ],
                "capability_plans": [
                    {
                        "capability_kind": "gadget",
                        "selected_route": "structured-model-authored-gadget",
                    }
                ],
                "typed_capability_plans": [
                    {
                        "schema_version": (
                            "boolean_csp_gadget_authoring_receipt_v3"
                        ),
                        "case_id": case_id,
                        "attempt": 1,
                        "kind": "initial",
                        "design_id": design_id,
                        "status": "lean-verified",
                        "declaration": declaration,
                        "source_sha256": source_hash,
                        "gadget_plan": gadget_plan,
                        "model_attempt": {
                            "response_payload_sha256": response_payload_hash,
                            "model_response_sha256": model_hash,
                            "semantic_payload_sha256": semantic_hash,
                        },
                        "semantic_checker": {
                            "success": True,
                            "semantic_payload_sha256": semantic_hash,
                        },
                        "renderer": {
                            "renderer_name": policy.renderer_name,
                            "renderer_version": policy.renderer_version,
                            "renderer_added_semantic_atom_count": 0,
                            "semantic_payload_sha256_before": semantic_hash,
                            "semantic_payload_sha256_after": semantic_hash,
                        },
                    }
                ],
                "contribution_receipts": [
                    {
                        "capability_declaration": declaration,
                        "capability_kind": "gadget",
                        "contribution_class": "MODEL_GENERATED_CAPABILITY",
                        "model_generated_source_hashes": [source_hash],
                        "deterministic_solver_steps": [],
                        "authorship_evidence": authorship,
                        "final_artifact_used": True,
                        "forbidden_audit_passed": True,
                        "independent_lean_passed": True,
                    }
                ],
                "final_route_audit_receipt": {
                    "passed": True,
                    "forbidden_dependencies_passed": True,
                    "required_dependencies": [declaration],
                    "required_dependency_audit_emitted": True,
                    "required_dependency_count": 1,
                    "required_dependencies_passed": True,
                },
            }
        )
    validation_keys = (
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
    return {
        "suite": {
            "selected_case_count": len(policy.selected_case_ids),
            "completed_case_count": len(policy.selected_case_ids),
            "selected_case_ids": list(policy.selected_case_ids),
            "completed_case_ids": list(policy.selected_case_ids),
        },
        "real_api": {
            "total_calls": len(policy.required_case_ids),
            "http_200_calls": len(policy.required_case_ids),
            "call_accounting_complete": True,
        },
        "validation": {
            "all_called_requests_http_200": True,
            "forbidden_direct_or_transitive_dependency_count": 0,
            **{key: True for key in validation_keys},
        },
        "policy_enforcement": {
            "integrity_passed": True,
            "required_case_runtime_receipt_count": len(policy.required_case_ids),
        },
        "cases": rows,
    }


def _required_row(report: dict[str, object], case_id: str) -> dict[str, object]:
    return next(
        row
        for row in report["cases"]  # type: ignore[index]
        if row["case_id"] == case_id
    )


def _case_status(evaluation: dict[str, object], case_id: str) -> str:
    return next(
        item["status"]
        for item in evaluation["case_results"]  # type: ignore[index]
        if item["case_id"] == case_id
    )


def test_strict_gadget_authoring_evaluator_accepts_3_anchors_and_27_authored() -> None:
    policy = gadget_authoring_policy()
    evaluation = evaluate_gadget_authoring_gate(
        _synthetic_gadget_gate_report(), policy
    )

    assert evaluation["integrity_passed"]
    assert evaluation["anchor_verified_count"] == 3
    assert evaluation["authored_success_count"] == 27
    assert evaluation["authored_success_rate"] == 1.0
    assert evaluation["strict_gate_passed"]


def test_strict_gadget_authoring_evaluator_enforces_requested_freeze_receipt() -> None:
    policy = gadget_authoring_policy()
    report = _synthetic_gadget_gate_report()
    report["evaluation_protocol"] = {
        "run_role": "frozen-final-full30",
        "requires_configuration_freeze": True,
    }
    report["validation"]["configuration_freeze_integrity_passed"] = False  # type: ignore[index]

    missing = evaluate_gadget_authoring_gate(report, policy)
    assert not missing["integrity_passed"]
    assert not missing["integrity_checks"][
        "configuration_freeze_integrity_passed"
    ]

    report["validation"]["configuration_freeze_integrity_passed"] = True  # type: ignore[index]
    report["configuration_freeze"] = {
        "integrity_passed": True,
        "policy_version": policy.policy_version,
        "policy_sha256": policy.policy_sha256,
        "selected_case_ids": list(policy.selected_case_ids),
    }
    frozen = evaluate_gadget_authoring_gate(report, policy)
    assert frozen["integrity_passed"]
    assert frozen["strict_gate_passed"]


def test_strict_gadget_authoring_evaluator_rejects_attribution_and_final_use_mutations() -> None:
    policy = gadget_authoring_policy()
    case_id = policy.required_case_ids[0]

    missing_case = _synthetic_gadget_gate_report()
    missing_case["cases"] = [
        row
        for row in missing_case["cases"]  # type: ignore[index]
        if row["case_id"] != case_id
    ]
    missing_evaluation = evaluate_gadget_authoring_gate(missing_case, policy)
    assert not missing_evaluation["integrity_passed"]
    assert _case_status(missing_evaluation, case_id) == "SYSTEM_ERROR"

    wrong_class = deepcopy(_synthetic_gadget_gate_report())
    _required_row(wrong_class, case_id)["contribution_receipts"][0][  # type: ignore[index]
        "contribution_class"
    ] = "DETERMINISTIC_GENERATED_CAPABILITY"
    wrong_class_evaluation = evaluate_gadget_authoring_gate(wrong_class, policy)
    assert _case_status(wrong_class_evaluation, case_id) == "ATTRIBUTION_MISMATCH"
    assert not wrong_class_evaluation["strict_gate_passed"]

    empty_source = deepcopy(_synthetic_gadget_gate_report())
    _required_row(empty_source, case_id)["contribution_receipts"][0][  # type: ignore[index]
        "model_generated_source_hashes"
    ] = []
    empty_source_evaluation = evaluate_gadget_authoring_gate(empty_source, policy)
    assert _case_status(empty_source_evaluation, case_id) == "ATTRIBUTION_MISMATCH"
    assert not empty_source_evaluation["integrity_passed"]

    forbidden = deepcopy(_synthetic_gadget_gate_report())
    _required_row(forbidden, case_id)["final_route_audit_receipt"][  # type: ignore[index]
        "forbidden_dependencies_passed"
    ] = False
    forbidden["validation"][  # type: ignore[index]
        "forbidden_direct_or_transitive_dependency_count"
    ] = 1
    forbidden_evaluation = evaluate_gadget_authoring_gate(forbidden, policy)
    assert _case_status(forbidden_evaluation, case_id) == "FORBIDDEN_DEPENDENCY"
    assert not forbidden_evaluation["integrity_passed"]

    independent = deepcopy(_synthetic_gadget_gate_report())
    _required_row(independent, case_id)["contribution_receipts"][0][  # type: ignore[index]
        "independent_lean_passed"
    ] = False
    independent_evaluation = evaluate_gadget_authoring_gate(independent, policy)
    assert _case_status(independent_evaluation, case_id) == (
        "LEAN_MATERIALIZATION_FAILED"
    )

    not_final_used = deepcopy(_synthetic_gadget_gate_report())
    _required_row(not_final_used, case_id)["contribution_receipts"][0][  # type: ignore[index]
        "final_artifact_used"
    ] = False
    not_final_evaluation = evaluate_gadget_authoring_gate(not_final_used, policy)
    assert _case_status(not_final_evaluation, case_id) == "CAPABILITY_NOT_FINAL_USED"

    missing_dependency = deepcopy(_synthetic_gadget_gate_report())
    route = _required_row(missing_dependency, case_id)[  # type: ignore[index]
        "final_route_audit_receipt"
    ]
    route["required_dependencies"] = []
    route["required_dependency_audit_emitted"] = False
    route["required_dependency_count"] = 0
    missing_dependency_evaluation = evaluate_gadget_authoring_gate(
        missing_dependency, policy
    )
    assert _case_status(missing_dependency_evaluation, case_id) == (
        "CAPABILITY_NOT_FINAL_USED"
    )
    assert not missing_dependency_evaluation["integrity_passed"]

    disabled_plugin = deepcopy(_synthetic_gadget_gate_report())
    runtime = _required_row(disabled_plugin, case_id)[  # type: ignore[index]
        "gate_policy_runtime"
    ]
    runtime["disabled_plugins_absent_from_runtime"] = False
    runtime["runtime_finite_synthesis_plugins"].append(  # type: ignore[union-attr]
        "boolean-csp-explicit-finite-gadget"
    )
    disabled_evaluation = evaluate_gadget_authoring_gate(disabled_plugin, policy)
    assert _case_status(disabled_evaluation, case_id) == "ATTRIBUTION_MISMATCH"
    assert not disabled_evaluation["integrity_passed"]

    selected_drift = deepcopy(_synthetic_gadget_gate_report())
    selected_drift["suite"]["selected_case_ids"].pop()  # type: ignore[index,union-attr]
    drift_evaluation = evaluate_gadget_authoring_gate(selected_drift, policy)
    assert not drift_evaluation["integrity_passed"]

    cross_case_hash = deepcopy(_synthetic_gadget_gate_report())
    other_case_id = policy.required_case_ids[1]
    other_hash = _required_row(cross_case_hash, other_case_id)[
        "contribution_receipts"
    ][0]["authorship_evidence"]["model_response_sha256"]  # type: ignore[index]
    _required_row(cross_case_hash, case_id)["contribution_receipts"][0][  # type: ignore[index]
        "authorship_evidence"
    ]["model_response_sha256"] = other_hash
    cross_case_evaluation = evaluate_gadget_authoring_gate(cross_case_hash, policy)
    assert _case_status(cross_case_evaluation, case_id) == "ATTRIBUTION_MISMATCH"
    assert not cross_case_evaluation["integrity_passed"]


@pytest.mark.parametrize(
    ("terminal_status", "expected_status"),
    [
        (
            "transport-escalation-exhausted",
            "MODEL_SEARCH_NONCONVERGENT",
        ),
        (
            "semantic-repair-escalation-exhausted",
            "GADGET_SEMANTIC_REPAIR_FAILED",
        ),
    ],
)
def test_strict_gadget_authoring_evaluator_distinguishes_nonconvergence(
    terminal_status: str, expected_status: str
) -> None:
    policy = gadget_authoring_policy()
    case_id = policy.required_case_ids[0]
    report = deepcopy(_synthetic_gadget_gate_report())
    row = _required_row(report, case_id)
    row["proof_status"] = "BLOCKED"
    row["contribution_receipts"] = []
    row["typed_capability_plans"] = [
        {
            "schema_version": "boolean_csp_gadget_authoring_receipt_v3",
            "case_id": case_id,
            "status": terminal_status,
            "model_attempt": {
                "purpose": "gadget-authoring-repair",
            },
        }
    ]

    evaluation = evaluate_gadget_authoring_gate(report, policy)

    assert _case_status(evaluation, case_id) == expected_status
