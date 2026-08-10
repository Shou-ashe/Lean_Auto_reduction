import json
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.benchmark import load_benchmark_suite
from agent.hardness.input_grounding import (
    REPRESENTATION_COMPARISON_CATALOG_MODES,
    REPRESENTATION_COMPARISON_GROUP_COUNT,
    REPRESENTATION_COMPARISON_SUITE_ID,
    SimulatedInputGroundingClient,
    observation_snapshot_path,
    validate_representation_comparison_suite,
    validate_input_grounding_suite,
)


ROOT = Path(__file__).resolve().parents[1]
SUITE = (
    ROOT / "Gate" / "Suites" / "input_grounding_fixed_target.json"
)
COMPARISON_SUITE = (
    ROOT
    / "Benchmark"
    / "Hardness"
    / "Suites"
    / "input_grounding_representation_comparison.json"
)
COMPARISON_CONTRACT = (
    ROOT
    / "Benchmark"
    / "Hardness"
    / "Expected"
    / "Contracts"
    / "input-grounding-representation-comparison.json"
)
SYSTEM = "write the complete Lean term and use the auditable stop action"


def prompt_payload() -> dict:
    return {
        "input_observation": {
            "normalized_problem_node_id": "lean-whnf:source",
        },
        "fixed_target": {
            "declaration": "Benchmark.Input.target",
            "node_id": "lean-whnf:target",
        },
        "retrieved": {
            "problems": [],
            "connections": [],
            "reductions": [],
        },
        "query_history": [],
        "constraints": {"full_catalogs_are_not_included": True},
    }


def test_suite_boundary_and_observation_paths_are_generic() -> None:
    cases = validate_input_grounding_suite(load_benchmark_suite(SUITE))
    assert len(cases) == 24
    assert observation_snapshot_path(
        Path("snapshots"),
        module="Benchmark.Hardness.Inputs.InputGrounding.Clause",
        declaration="Benchmark.Hardness.Inputs.InputGrounding.Clause.threeSATAlias",
    ) == Path("snapshots/Clause/threeSATAlias.json")


def test_representation_comparison_suite_pairs_all_fixed_target_positives() -> None:
    fixed_cases = validate_input_grounding_suite(load_benchmark_suite(SUITE))
    fixed_positives = {case.id: case for case in fixed_cases if case.is_positive}
    comparison_cases = validate_representation_comparison_suite(
        load_benchmark_suite(COMPARISON_SUITE)
    )

    assert REPRESENTATION_COMPARISON_SUITE_ID == (
        "input-grounding-representation-comparison"
    )
    assert len(comparison_cases) == 36
    by_group = {}
    for case in comparison_cases:
        by_group.setdefault(case.comparison_group_id, []).append(case)
    assert len(by_group) == REPRESENTATION_COMPARISON_GROUP_COUNT == 18
    assert set(by_group) == set(fixed_positives)

    for group_id, pair in by_group.items():
        original = fixed_positives[group_id]
        assert {case.catalog_mode for case in pair} == (
            REPRESENTATION_COMPARISON_CATALOG_MODES
        )
        assert all(case.source == original.source for case in pair)
        assert all(case.target == original.target for case in pair)
        assert all(
            {
                key: value
                for key, value in case.coverage.items()
                if key != "study_family"
            }
            == original.coverage
            for case in pair
        )
        assert all(
            case.coverage.get("study_family") in {"graph", "clause_csp", "incidence"}
            for case in pair
        )
        assert all(case.matched_pair_id == group_id for case in pair)
        assert all(case.resources["max_model_calls"] > 0 for case in pair)
        assert all(case.coverage.get("forbid_model_call") is not True for case in pair)


def test_representation_comparison_validator_rejects_pair_metadata_drift() -> None:
    suite = load_benchmark_suite(COMPARISON_SUITE)
    cases = list(suite.cases)
    component_index = next(
        index
        for index, case in enumerate(cases)
        if case.comparison_group_id == "input-graph-direct"
        and case.catalog_mode == "component_catalog"
    )
    cases[component_index] = replace(
        cases[component_index], target="Benchmark.Hidden.OtherTarget"
    )

    with pytest.raises(ValueError, match="changes metadata"):
        validate_representation_comparison_suite(replace(suite, cases=tuple(cases)))


def test_representation_comparison_contract_contains_no_claimed_results() -> None:
    contract = json.loads(COMPARISON_CONTRACT.read_text(encoding="utf-8"))
    assert contract["authoritative"] is False
    assert contract["contract_only"] is True
    assert contract["contains_observed_results"] is False
    assert contract["study_boundary"]["execution_case_count"] == 36
    assert contract["study_boundary"]["comparison_group_count"] == 18
    assert contract["result_artifact"]["current_result"] is None


def test_simulated_model_chooses_only_visible_problem_and_reduction_results() -> None:
    client = SimulatedInputGroundingClient()
    payload = prompt_payload()
    first = json.loads(
        client.complete_json(system=SYSTEM, prompt=json.dumps(payload)).content
    )
    assert first == {
        "action": "search_problems",
        "searches": [{"limit": 8, "node_ids": ["lean-whnf:source"]}],
    }

    payload["retrieved"]["problems"] = [
        {
            "declaration": "ComplexityReduction.Presentation.Source.problem",
            "problem_node_id": "lean-whnf:source",
            "exact_defeq": True,
        }
    ]
    payload["query_history"].append(
        {
            "action": "search_problems",
            "searches": [{"node_ids": ["lean-whnf:source"], "limit": 8}],
            "result_count": 1,
        }
    )
    second = json.loads(
        client.complete_json(system=SYSTEM, prompt=json.dumps(payload)).content
    )
    assert second["action"] == "search_reductions"

    payload["retrieved"]["reductions"] = [
        {
            "declaration": "ComplexityReduction.Routes.Example.route",
            "source_node_id": "lean-whnf:source",
            "target_node_id": "lean-whnf:target",
        }
    ]
    payload["query_history"].append(
        {
            "action": "search_reductions",
            "searches": [
                {
                    "source_node_ids": ["lean-whnf:source"],
                    "target_node_ids": ["lean-whnf:target"],
                    "limit": 8,
                }
            ],
            "result_count": 1,
        }
    )
    third = json.loads(
        client.complete_json(system=SYSTEM, prompt=json.dumps(payload)).content
    )
    assert third["action"] == "finish"
    assert third["matched_problem"] == (
        "ComplexityReduction.Presentation.Source.problem"
    )
    assert third["reduction_declarations"] == [
        "ComplexityReduction.Routes.Example.route"
    ]
    assert "ComplexityReduction.Routes.Example.route" in third["lean_term"]


def test_simulated_model_expands_returned_frontiers_for_a_two_edge_path() -> None:
    client = SimulatedInputGroundingClient()
    payload = prompt_payload()
    payload["retrieved"]["problems"] = [
        {
            "declaration": "ComplexityReduction.Presentation.Source.problem",
            "problem_node_id": "lean-whnf:source",
            "exact_defeq": True,
        }
    ]
    payload["query_history"].append(
        {
            "action": "search_problems",
            "searches": [{"node_ids": ["lean-whnf:source"], "limit": 8}],
            "result_count": 1,
        }
    )

    direct_probe = json.loads(
        client.complete_json(system=SYSTEM, prompt=json.dumps(payload)).content
    )
    assert direct_probe["action"] == "search_reductions"
    assert direct_probe["searches"][0]["target_node_ids"] == ["lean-whnf:target"]
    payload["query_history"].append(
        {"action": "search_reductions", "searches": direct_probe["searches"], "result_count": 0}
    )

    source_outgoing = json.loads(
        client.complete_json(system=SYSTEM, prompt=json.dumps(payload)).content
    )
    assert source_outgoing == {
        "action": "search_reductions",
        "searches": [{"source_node_ids": ["lean-whnf:source"], "limit": 8}],
    }
    payload["retrieved"]["reductions"].append(
        {
            "declaration": "ComplexityReduction.Routes.Example.ingress",
            "source_node_id": "lean-whnf:source",
            "target_node_id": "lean-whnf:hub",
        }
    )
    payload["query_history"].append(
        {
            "action": "search_reductions",
            "searches": source_outgoing["searches"],
            "result_count": 1,
        }
    )

    hub_outgoing = json.loads(
        client.complete_json(system=SYSTEM, prompt=json.dumps(payload)).content
    )
    assert hub_outgoing == {
        "action": "search_reductions",
        "searches": [{"source_node_ids": ["lean-whnf:hub"], "limit": 8}],
    }
    payload["retrieved"]["reductions"].append(
        {
            "declaration": "ComplexityReduction.Routes.Example.shared",
            "source_node_id": "lean-whnf:hub",
            "target_node_id": "lean-whnf:target",
        }
    )
    payload["query_history"].append(
        {
            "action": "search_reductions",
            "searches": hub_outgoing["searches"],
            "result_count": 1,
        }
    )

    finish = json.loads(
        client.complete_json(system=SYSTEM, prompt=json.dumps(payload)).content
    )
    assert finish["action"] == "finish"
    assert finish["reduction_declarations"] == [
        "ComplexityReduction.Routes.Example.ingress",
        "ComplexityReduction.Routes.Example.shared",
    ]
    assert finish["lean_term"].count(
        "ComplexityReduction.Certificate.CertifiedPath.cons"
    ) == 1


@pytest.mark.parametrize(
    "forbidden_key",
    [
        "family_id",
        "study_family",
        "logical_source",
        "input_form",
        "matched_pair_id",
        "comparison_group_id",
        "gold_route",
    ],
)
def test_simulated_model_rejects_answer_fields_in_prompt(forbidden_key: str) -> None:
    client = SimulatedInputGroundingClient()
    payload = prompt_payload()
    payload[forbidden_key] = "hidden-benchmark-metadata"
    with pytest.raises(ValueError, match="answer fields"):
        client.complete_json(system=SYSTEM, prompt=json.dumps(payload))
