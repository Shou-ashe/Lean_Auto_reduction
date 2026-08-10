import json
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.benchmark import load_benchmark_suite
from agent.hardness.frontier_efficiency import (
    FRONTIER_EFFICIENCY_MAX_MODEL_CALLS,
    analyze_frontier_interactions,
    validate_frontier_efficiency_suite,
)
from agent.hardness.model_client import ModelResponse


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "Gate" / "Suites" / "frontier_efficiency.json"


def response(payload: dict) -> ModelResponse:
    return ModelResponse(
        called=True,
        ok=True,
        content=json.dumps(payload, sort_keys=True),
        error=None,
        status_code=200,
        duration_seconds=0.1,
        usage={"prompt_tokens": 1, "completion_tokens": 1, "total_tokens": 2},
        attempts=1,
        finish_reason="stop",
    )


def prompt(*, terminal: dict | None = None) -> str:
    payload = {
        "request": {"objective": "reduce_to_known_hardness"},
        "retrieved": {
            "problems": [{"problem_node_id": "node:a"}],
            "connections": [],
            "hardness_targets": [],
            "reductions": [],
        },
        "frontier_guidance": {
            "schema_version": "hardness_frontier_guidance_v1",
            "mode": "retrieved_endpoints_public_counts",
            "contains_declaration_names": False,
            "contains_target_or_route_selection": False,
            "frontier_origin": "retrieved endpoints",
            "catalog_use": "counts only",
            "ordering": "breadth_first_then_node_id",
            "retrieved_reachable_node_count": 1,
            "source_only_queried_node_count": 0,
            "unqueried_expandable_frontier_count": 1,
            "frontier_truncated": False,
            "frontier_nodes": [
                {
                    "node_id": "node:a",
                    "minimum_retrieved_atom_depth": 0,
                    "outgoing_reduction_count": 2,
                    "outgoing_endpoint_count": 2,
                    "source_only_query_attempted": False,
                }
            ],
            "suggested_searches": [
                {"source_node_ids": ["node:a"], "limit": 8}
            ],
            "instruction": "expand the retrieved frontier",
        },
    }
    if terminal is not None:
        payload["terminal_guidance"] = terminal
    return json.dumps(payload, sort_keys=True)


def test_frontier_efficiency_suite_is_independent_and_target_free() -> None:
    cases = validate_frontier_efficiency_suite(load_benchmark_suite(SUITE))

    assert len(cases) == 8
    assert sum(case.is_positive for case in cases) == 4
    assert all(case.target is None for case in cases)
    assert all(case.resources["max_model_calls"] == FRONTIER_EFFICIENCY_MAX_MODEL_CALLS for case in cases)
    raw = SUITE.read_text(encoding="utf-8")
    for forbidden in ("gold_target", "gold_route", "expected_target", "expected_route"):
        assert forbidden not in raw


def test_frontier_efficiency_validator_rejects_public_abi_drift() -> None:
    suite = load_benchmark_suite(SUITE)
    changed = replace(suite.cases[0], target="ComplexityReduction.Oracle.target")

    with pytest.raises(ValueError, match="outside the Stage-J public ABI"):
        validate_frontier_efficiency_suite(
            replace(suite, cases=(changed, *suite.cases[1:]))
        )


def test_frontier_interaction_metrics_track_suggestions_repeats_and_terminal_following() -> None:
    query = {
        "action": "search_reductions",
        "searches": [{"source_node_ids": ["node:a"], "limit": 8}],
    }
    prompts = (
        prompt(),
        prompt(),
        prompt(
            terminal={
                "mode": "stop_now",
                "failure_code": "no_eligible_hardness_target",
            }
        ),
    )
    responses = (
        response(query),
        response(query),
        response(
            {
                "action": "stop",
                "failure_code": "no_eligible_hardness_target",
                "explanation": "No eligible evidence remains.",
            }
        ),
    )

    metrics = analyze_frontier_interactions(prompts=prompts, responses=responses)

    assert metrics["frontier_guidance_error_count"] == 0
    assert metrics["frontier_suggestion_followed_round_count"] == 2
    assert metrics["source_only_reduction_search_action_count"] == 2
    assert metrics["repeated_reduction_search_count"] == 1
    assert metrics["terminal_guidance_counts"] == {"stop_now": 1}
    assert metrics["terminal_guidance_followed_counts"] == {"stop_now": 1}
    assert metrics["terminal_guidance_ignored_count"] == 0
