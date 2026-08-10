import json
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.benchmark import load_benchmark_suite
from agent.hardness.open_target import (
    OPEN_TARGET_CASE_COUNT,
    validate_open_target_suite,
)
from agent.hardness.predicate_input import (
    COVERAGE_FORBIDDEN_KEYS,
    EXPECTED_CASE_SCENARIOS,
    EXPECTED_NEGATIVE_FAILURES,
    PREDICATE_INPUT_CASE_COUNT,
    PREDICATE_INPUT_FAILURE_CODES,
    PREDICATE_INPUT_NEGATIVE_COUNT,
    PREDICATE_INPUT_POSITIVE_COUNT,
    audit_predicate_input_prompt,
    find_predicate_input_coverage_oracles,
    find_predicate_input_prompt_forbidden_keys,
    validate_predicate_input_suite,
)


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "Gate" / "Suites" / "predicate_input.json"
OPEN_TARGET_SUITE = (
    ROOT / "Gate" / "Suites" / "open_target.json"
)
CONTRACT = (
    ROOT
    / "Benchmark"
    / "Hardness"
    / "Expected"
    / "Contracts"
    / "predicate-input.json"
)


def _all_keys(value: object) -> set[str]:
    if isinstance(value, dict):
        keys = set(value)
        for item in value.values():
            keys.update(_all_keys(item))
        return keys
    if isinstance(value, list):
        keys: set[str] = set()
        for item in value:
            keys.update(_all_keys(item))
        return keys
    return set()


def _all_strings(value: object) -> tuple[str, ...]:
    if isinstance(value, dict):
        return tuple(
            item for nested in value.values() for item in _all_strings(nested)
        )
    if isinstance(value, list):
        return tuple(item for nested in value for item in _all_strings(nested))
    return (value,) if isinstance(value, str) else ()


def test_predicate_input_suite_has_exactly_eight_balanced_boundary_cases() -> None:
    cases = validate_predicate_input_suite(load_benchmark_suite(SUITE))

    assert len(cases) == PREDICATE_INPUT_CASE_COUNT == 8
    assert (
        sum(case.is_positive for case in cases)
        == PREDICATE_INPUT_POSITIVE_COUNT
        == 4
    )
    assert (
        sum(not case.is_positive for case in cases)
        == PREDICATE_INPUT_NEGATIVE_COUNT
        == 4
    )
    assert sum(case.input_kind == "predicate" for case in cases) == 7
    assert sum(case.input_kind == "closed_prop" for case in cases) == 1
    assert {case.coverage["predicate_input_scenario"] for case in cases} == set(
        EXPECTED_CASE_SCENARIOS.values()
    )
    assert all(case.evaluation_lane == "predicate_open_target" for case in cases)
    assert all(case.target is None and case.membership is None for case in cases)
    assert all(case.resources["max_model_calls"] == 14 for case in cases)

    negatives = {case.id: case for case in cases if not case.is_positive}
    assert {
        case.expected.final_failure_code for case in negatives.values()
    } == PREDICATE_INPUT_FAILURE_CODES
    assert all(
        case.expected.final_failure_code == EXPECTED_NEGATIVE_FAILURES[case_id]
        for case_id, case in negatives.items()
    )


def test_stage_g_open_target_suite_remains_the_strict_seven_case_lane() -> None:
    cases = validate_open_target_suite(load_benchmark_suite(OPEN_TARGET_SUITE))

    assert len(cases) == OPEN_TARGET_CASE_COUNT == 7
    assert all(case.evaluation_lane == "open_target" for case in cases)
    assert all(case.input_kind == "presented_problem" for case in cases)


def test_predicate_input_coverage_contains_no_target_route_or_candidate_declaration() -> None:
    raw = json.loads(SUITE.read_text(encoding="utf-8"))
    for case in raw["cases"]:
        coverage = case["coverage"]
        assert not (_all_keys(coverage) & COVERAGE_FORBIDDEN_KEYS)
        assert find_predicate_input_coverage_oracles(coverage) == ()
        assert not any(
            value.startswith(("ComplexityReduction.", "Benchmark.Hardness."))
            for value in _all_strings(coverage)
        )
        assert case["target"] is None
        assert set(case["expected"]) <= {"final_status", "final_failure_code"}


def test_predicate_input_validator_rejects_failure_or_oracle_drift() -> None:
    suite = load_benchmark_suite(SUITE)
    cases = list(suite.cases)
    negative_index = next(
        index
        for index, case in enumerate(cases)
        if case.id == "predicate-input-missing-presentation"
    )
    cases[negative_index] = replace(
        cases[negative_index],
        expected=replace(
            cases[negative_index].expected,
            final_failure_code="predicate_requires_presentation",
        ),
    )
    with pytest.raises(ValueError, match="must expect blocker"):
        validate_predicate_input_suite(replace(suite, cases=tuple(cases)))

    cases = list(suite.cases)
    cases[0] = replace(
        cases[0],
        coverage={
            **cases[0].coverage,
            "candidate_declarations": ["ComplexityReduction.Hidden.Candidate"],
        },
    )
    with pytest.raises(ValueError, match="coverage contains target/route/candidate"):
        validate_predicate_input_suite(replace(suite, cases=tuple(cases)))


def test_predicate_input_prompt_allows_only_retrieved_candidate_declarations() -> None:
    payload = {
        "request": {
            "input_declaration": "Benchmark.Hardness.Inputs.PredicateInput.directCNFAccepts",
            "input_kind": "predicate",
            "required_hardness": "native_np",
            "allowed_target_evidence": ["native_membership"],
        },
        "retrieved": {
            "predicate_presentation_candidates": [
                {
                    "presentation_declaration": "ComplexityReduction.Public.Problem",
                    "relation": "accepts_exact_defeq",
                    "encoder_bound_identity_node_id": "lean-whnf:codec",
                }
            ]
        },
    }
    assert find_predicate_input_prompt_forbidden_keys(payload) == ()
    audit_predicate_input_prompt(payload)

    leaked = {
        **payload,
        "request": {
            **payload["request"],
            "presentation_declaration": "ComplexityReduction.Gold.Problem",
        },
        "expected_presentation": "ComplexityReduction.Gold.Problem",
    }
    assert find_predicate_input_prompt_forbidden_keys(leaked) == (
        "expected_presentation",
        "request.presentation_declaration",
    )
    with pytest.raises(ValueError, match="benchmark answer fields"):
        audit_predicate_input_prompt(leaked)


def test_predicate_input_contract_is_result_free_and_uses_stable_codes() -> None:
    contract = json.loads(CONTRACT.read_text(encoding="utf-8"))

    assert contract["authoritative"] is False
    assert contract["contract_only"] is True
    assert contract["contains_observed_results"] is False
    assert contract["study_boundary"]["execution_case_count"] == 8
    assert contract["study_boundary"]["positive_case_count"] == 4
    assert contract["study_boundary"]["negative_case_count"] == 4
    assert (
        contract["study_boundary"][
            "target_route_or_candidate_declarations_in_coverage"
        ]
        is False
    )
    assert set(contract["stable_negative_failure_codes"].values()) == (
        PREDICATE_INPUT_FAILURE_CODES
    )
    assert contract["execution_requirements"]["resume_or_replay_for_final_run"] is False
    assert contract["result_artifact"]["current_result"] is None
