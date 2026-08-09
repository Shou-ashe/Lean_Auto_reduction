"""Frozen Stage-L Core generalization benchmark and report contracts."""

from __future__ import annotations

from collections import Counter
from collections.abc import Mapping
from typing import Any

from .benchmark import BenchmarkCase, BenchmarkSuite
from .open_target import COVERAGE_FORBIDDEN_KEYS, _declaration_values, _forbidden_key_paths


CORE_GENERALIZATION_SUITE_ID = "core-generalization"
CORE_GENERALIZATION_CASE_COUNT = 16
CORE_GENERALIZATION_POSITIVE_COUNT = 8
CORE_GENERALIZATION_NEGATIVE_COUNT = 8
CORE_GENERALIZATION_MODULE = "Benchmark.Hardness.Inputs.CoreGeneralization.Inputs"
CORE_GENERALIZATION_REPORT_SCHEMA = "hardness_core_generalization_deepseek_report_v1"
CORE_GENERALIZATION_OFFLINE_REPORT_SCHEMA = "hardness_core_generalization_offline_report_v1"
CORE_GENERALIZATION_PROMPT_ABI = "hardness_core_generalization_prompt_v1"
CORE_GENERALIZATION_FINISH_ABI = "hardness_core_generalization_finish_v1"
CORE_GENERALIZATION_MAX_JOBS = 4

OBJECTIVE_CLASSES = {
    "reduce_to": "reduction",
    "reduce_to_known_np": "reduction",
    "reduce_to_known_hardness": "reduction",
    "prove_in_np": "membership",
    "prove_np_complete": "completeness",
}
ROUTE_BANDS = {"0", "1", "2_3", "5_7", "none"}
EXPECTED_FAILURES: Mapping[str, str] = {
    "coregen-closed-prop-rejected": "input_not_decision_problem",
    "coregen-ambiguous-predicate": "ambiguous_predicate_presentation",
    "coregen-representation-mismatch": "missing_lawful_presentation",
    "coregen-no-eligible-hardness-target": "no_eligible_hardness_target",
    "coregen-forward-route-absent": "eligible_target_has_no_existing_route",
    "coregen-reverse-only-route": "eligible_target_has_no_existing_route",
    "coregen-missing-native-membership": "missing_native_membership",
    "coregen-invalid-completeness-head": "missing_native_completeness",
}

EXPECTED_POSITIVE_OBJECTIVES: Mapping[str, str] = {
    "coregen-clause-presented-long": "reduce_to_known_hardness",
    "coregen-clause-predicate-long": "reduce_to_known_hardness",
    "coregen-graph-presented-route": "reduce_to",
    "coregen-graph-predicate-adapter": "reduce_to",
    "coregen-set-system-cross-family": "reduce_to_known_hardness",
    "coregen-registered-native-membership": "prove_in_np",
    "coregen-numeric-cook-levin-route": "reduce_to_known_np",
    "coregen-graph-transported-completeness": "prove_np_complete",
}


def objective_finish_payload(objective: str) -> dict[str, Any]:
    """Return the public, mutually exclusive finish schema for one objective."""

    common = ["action", "matched_problem", "match_relation", "connection_entry_id", "explanation"]
    common_shape: dict[str, Any] = {
        "action": "finish",
        "matched_problem": "<declaration or entry_id from retrieved.problems>",
        "match_relation": "<exact_defeq, accepts_exact_defeq, or retrieved relation>",
        "connection_entry_id": "<retrieved connection entry_id, or null for exact match>",
        "explanation": "<brief reason based only on retrieved rows>",
    }
    if objective in {"reduce_to", "reduce_to_known_np", "reduce_to_known_hardness"}:
        required = [*common, "reduction_entry_ids", "lean_term"]
        if objective != "reduce_to":
            required.extend(("target_entry_id", "target_evidence_id", "target_declaration"))
        return {
            "schema_version": CORE_GENERALIZATION_FINISH_ABI,
            "payload_kind": "reduction",
            "objective": objective,
            "required_fields": required,
            "forbidden_fields": [
                "membership_evidence_id",
                "membership_declaration",
                "membership_lean_term",
                "hub_completeness_evidence_id",
                "target_membership_evidence_id",
                "completeness_lean_term",
            ],
            "response_shape": {
                **common_shape,
                **(
                    {
                        "target_entry_id": "<retrieved target_entry_id>",
                        "target_evidence_id": "<retrieved evidence_id>",
                        "target_declaration": "<same retrieved target declaration>",
                    }
                    if objective != "reduce_to"
                    else {}
                ),
                "reduction_entry_ids": [
                    "<ordered entry_id from retrieved.reductions only; never retrieved.connections>"
                ],
                "lean_term": "<complete CertifiedPath term using retrieved lean_term values>",
            },
        }
    if objective == "prove_in_np":
        return {
            "schema_version": CORE_GENERALIZATION_FINISH_ABI,
            "payload_kind": "membership",
            "objective": objective,
            "required_fields": [*common, "membership_evidence_id", "membership_declaration", "membership_lean_term"],
            "forbidden_fields": [
                "target_entry_id",
                "target_evidence_id",
                "reduction_entry_ids",
                "lean_term",
                "hub_completeness_evidence_id",
                "target_membership_evidence_id",
                "completeness_lean_term",
            ],
            "response_shape": {
                **common_shape,
                "membership_evidence_id": "<retrieved native evidence entry_id>",
                "membership_declaration": "<same retrieved evidence declaration>",
                "membership_lean_term": "<untouched retrieved native evidence lean_term>",
            },
        }
    if objective == "prove_np_complete":
        return {
            "schema_version": CORE_GENERALIZATION_FINISH_ABI,
            "payload_kind": "completeness",
            "objective": objective,
            "required_fields": [
                *common,
                "hub_completeness_evidence_id",
                "target_membership_evidence_id",
                "reduction_entry_ids",
                "completeness_lean_term",
            ],
            "forbidden_fields": [
                "target_entry_id",
                "target_evidence_id",
                "membership_evidence_id",
                "membership_declaration",
                "membership_lean_term",
                "lean_term",
            ],
            "response_shape": {
                **common_shape,
                "hub_completeness_evidence_id": "<retrieved complete-hub entry_id>",
                "target_membership_evidence_id": "<retrieved exact target membership entry_id>",
                "reduction_entry_ids": [
                    "<ordered forward entry_id from retrieved.reductions only; never retrieved.connections>"
                ],
                "completeness_lean_term": (
                    "<CompletenessTransport.alongPath (<retrieved hub lean_term>) "
                    "(<complete CertifiedPath.step/cons term built from the ordered "
                    "retrieved reductions>) (<retrieved target membership lean_term>)>"
                ),
            },
        }
    raise ValueError(f"unsupported Stage-L objective: {objective}")


def validate_core_generalization_suite(
    suite: BenchmarkSuite,
) -> tuple[BenchmarkCase, ...]:
    """Enforce the independent, answer-free 16-case Stage-L contract."""

    cases = suite.cases
    if suite.id != CORE_GENERALIZATION_SUITE_ID:
        raise ValueError(f"expected suite {CORE_GENERALIZATION_SUITE_ID}, got {suite.id}")
    if len(cases) != CORE_GENERALIZATION_CASE_COUNT:
        raise ValueError("Core generalization suite must contain exactly 16 cases")
    if {case.id for case in cases} != set(EXPECTED_POSITIVE_OBJECTIVES) | set(EXPECTED_FAILURES):
        raise ValueError("Core generalization case IDs drifted from the Stage-L contract")
    status_counts = Counter(case.expected.final_status for case in cases)
    if status_counts != Counter({"VERIFIED": 8, "BLOCKED": 8}):
        raise ValueError("Core generalization must contain eight positives and eight negatives")

    family_counts: Counter[str] = Counter()
    input_forms: set[str] = set()
    objective_classes: set[str] = set()
    positive_route_bands: set[str] = set()
    comparable_count = 0
    for case in cases:
        if (
            case.module != CORE_GENERALIZATION_MODULE
            or case.effective_input_declaration != case.source
            or case.evaluation_lane != "core_generalization"
            or case.catalog_mode != "full"
            or case.execution_layer != "core_reuse"
            or case.verification_profile != "core"
            or case.authoring_policy != {"enabled": False, "mode": "disabled"}
            or case.objective_direction != "source_to_target"
            or case.group_id is not None
            or case.matched_pair_id is not None
            or case.comparison_group_id is not None
            or case.family_id is not None
            or case.source_form_id is not None
            or case.target_form_id is not None
            or case.hub_ids
        ):
            raise ValueError(f"case {case.id} is outside the Stage-L Core ABI")
        if case.resources.get("max_model_calls") not in {8, 10, 12, 14}:
            raise ValueError(f"case {case.id} has an unsupported model-call budget")
        if case.minimum_route_atoms < 0 or case.maximum_route_atoms is None:
            raise ValueError(f"case {case.id} must freeze a route-atom range")
        leaked_keys = _forbidden_key_paths(case.coverage, forbidden=COVERAGE_FORBIDDEN_KEYS)
        leaked_declarations = _declaration_values(case.coverage)
        if leaked_keys or leaked_declarations:
            raise ValueError(
                f"case {case.id} coverage contains target/route oracle data: "
                + ", ".join(sorted(leaked_keys | leaked_declarations))
            )

        family = case.coverage.get("family")
        input_form = case.coverage.get("input_form")
        objective_class = case.coverage.get("objective_class")
        route_band = case.coverage.get("route_band")
        comparable = case.coverage.get("comparable_subset")
        if not isinstance(family, str) or not family:
            raise ValueError(f"case {case.id} has no family coverage label")
        if input_form != case.input_kind:
            raise ValueError(f"case {case.id} input-form coverage does not match input_kind")
        if objective_class != OBJECTIVE_CLASSES[case.objective]:
            raise ValueError(f"case {case.id} objective-class coverage is inconsistent")
        if route_band not in ROUTE_BANDS:
            raise ValueError(f"case {case.id} has an unsupported route band")
        if not isinstance(comparable, bool):
            raise ValueError(f"case {case.id} must explicitly select the comparable subset")
        comparable_count += int(comparable)
        family_counts[family] += 1
        input_forms.add(input_form)
        objective_classes.add(objective_class)

        expected_failure = EXPECTED_FAILURES.get(case.id)
        if expected_failure is None:
            if case.objective != EXPECTED_POSITIVE_OBJECTIVES[case.id]:
                raise ValueError(f"case {case.id} changed its objective")
            if case.expected.final_status != "VERIFIED" or case.expected.final_failure_code is not None:
                raise ValueError(f"case {case.id} must be a positive case")
            positive_route_bands.add(route_band)
        elif (
            case.expected.final_status != "BLOCKED"
            or case.expected.final_failure_code != expected_failure
        ):
            raise ValueError(f"case {case.id} must expect blocker {expected_failure}")
        if case.expected.baseline_status is not None or case.expected.baseline_failure_code is not None:
            raise ValueError("Stage-L Expected records may contain only final outcome")

        objective_finish_payload(case.objective)

    if comparable_count != 8:
        raise ValueError("Stage L must freeze exactly eight comparable-subset cases")
    if not {"clause_csp", "graph", "set_system", "numeric"}.issubset(family_counts):
        raise ValueError("Stage L must cover at least four mathematical families")
    if not {"presented_problem", "predicate"}.issubset(input_forms):
        raise ValueError("Stage L must cover PresentedProblem and predicate inputs")
    if objective_classes != {"reduction", "membership", "completeness"}:
        raise ValueError("Stage L must cover reduction, membership, and completeness")
    if not {"0", "1", "2_3", "5_7"}.issubset(positive_route_bands):
        raise ValueError("Stage-L positives must cover all four route bands")
    return cases


def core_generalization_report_skeleton(*, offline: bool) -> dict[str, Any]:
    """Freeze the canonical top-level report layout before runner implementation."""

    return {
        "schema_version": (
            CORE_GENERALIZATION_OFFLINE_REPORT_SCHEMA
            if offline
            else CORE_GENERALIZATION_REPORT_SCHEMA
        ),
        "status": "RUNNING",
        "benchmark": {},
        "model": {},
        "catalogs": {},
        "observations": {},
        "parallel_execution": {},
        "execution_layers": {
            "core_reuse": {"case_count": 0, "model_calls": 0, "lean_process_count": 0},
            "optional_authoring": {"attempt_count": 0, "candidate_file_count": 0, "lean_precheck_count": 0},
        },
        "cases": [],
        "artifact": {},
        "lean": {},
        "grouped_metrics": {
            "family": {},
            "input_kind": {},
            "objective": {},
            "route_band": {},
            "outcome_class": {},
            "comparable_subset": {},
        },
        "summary": {},
    }
