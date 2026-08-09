import hashlib
import json
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.models import sha256_id
from agent.hardness.np_hard import NPHardSeedV1
from agent.hardness.np_hard_hub_benchmark import load_np_hard_hub_selection_suite
from agent.hardness.np_hard_hub_selection import (
    NP_HARD_HUB_DIRECTION,
    NPHardHubSelectionError,
    NPHardHubSwitchSessionV1,
    build_np_hard_hub_selection_request,
    project_np_hard_hub_candidates,
    rank_np_hard_hub_candidates,
)


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "Benchmark" / "Hardness" / "Suites" / "np_hard_hub_selection.json"


def seed(index: int) -> NPHardSeedV1:
    return NPHardSeedV1(
        problem_declaration=f"Example.Seed{index}.problem",
        normalized_problem_node=f"seed-{index}",
        evidence_declaration=f"Example.Seed{index}.hardness",
        evidence_kind="native_hardness",
        registry_fingerprint="lean:test-snapshot",
    )


def profile(
    risk: str, *, gaps: int = 1, route: int = 0, nodes: int = 1
) -> dict[str, object]:
    return {
        "eligibility": "authorable_gap",
        "unresolved_gap_count": gaps,
        "gap_risk": risk,
        "existing_route_length": route,
        "representation_adapter_count": 0,
        "estimated_authoring_nodes": nodes,
        "task_class": risk.replace("-", "_"),
    }


def request_for(profiles):
    seeds = tuple(seed(index) for index in range(len(profiles)))
    candidates = project_np_hard_hub_candidates(
        seeds=seeds,
        target_problem="Example.Target.problem",
        profiles={item.problem_declaration: value for item, value in zip(seeds, profiles)},
    )
    request = build_np_hard_hub_selection_request(
        target_problem="Example.Target.problem",
        registry_fingerprint="lean:test-snapshot",
        candidates=candidates,
    )
    return request, candidates


def test_suite_is_strict_and_contains_three_multi_seed_positive_inputs() -> None:
    suite = load_np_hard_hub_selection_suite(SUITE)
    assert len(suite["cases"]) == 4
    assert sum(case["expected_selected_seed"] is not None for case in suite["cases"]) == 3
    assert all(len(case["profiles"]) >= 3 for case in suite["cases"])


def test_ranking_uses_the_exact_g_d_tuple_and_not_shortest_route_first() -> None:
    request, candidates = request_for(
        [
            profile("semantic-proof", route=5),
            profile("program-composition", route=0),
            profile("program-synthesis", route=0),
        ]
    )
    result = rank_np_hard_hub_candidates(request)
    by_id = {candidate.candidate_id: candidate for candidate in candidates}
    assert by_id[result.selected_candidate_id].seed_problem == "Example.Seed0.problem"
    assert [by_id[item].gap_risk for item in result.ranked_candidate_ids] == [
        "semantic-proof", "program-composition", "program-synthesis"
    ]


def test_request_and_ranking_are_permutation_stable() -> None:
    request, candidates = request_for(
        [profile("semantic-proof"), profile("program-composition"), profile("program-synthesis")]
    )
    result = rank_np_hard_hub_candidates(request)
    reversed_request = build_np_hard_hub_selection_request(
        target_problem=request.target_problem,
        registry_fingerprint=request.registry_fingerprint,
        candidates=reversed(candidates),
    )
    reversed_result = rank_np_hard_hub_candidates(reversed_request)
    assert reversed_request.request_id == request.request_id
    assert reversed_result.ranked_candidate_ids == result.ranked_candidate_ids


def test_reverse_only_and_missing_profiles_are_diagnosed_not_dropped() -> None:
    seeds = (seed(0), seed(1))
    reverse = {
        "eligibility": "reverse_only",
        "unresolved_gap_count": 0,
        "gap_risk": "unsupported",
        "existing_route_length": 0,
        "representation_adapter_count": 0,
        "estimated_authoring_nodes": 0,
        "task_class": None,
    }
    candidates = project_np_hard_hub_candidates(
        seeds=seeds,
        target_problem="Example.Target.problem",
        profiles={seeds[0].problem_declaration: reverse},
    )
    assert len(candidates) == 2
    assert {candidate.eligibility for candidate in candidates} == {"reverse_only", "unsupported"}
    request = build_np_hard_hub_selection_request(
        target_problem="Example.Target.problem",
        registry_fingerprint="lean:test-snapshot",
        candidates=candidates,
    )
    result = rank_np_hard_hub_candidates(request)
    assert result.selected_candidate_id is None
    assert result.failure_code == "no_authorable_hardness_hub"
    assert {item.code for item in result.rejected} == {
        "candidate_wrong_direction", "unsupported_hardness_hub_gap"
    }


def test_target_cannot_select_itself_as_a_seed() -> None:
    item = seed(0)
    candidate = project_np_hard_hub_candidates(
        seeds=(item,), target_problem=item.problem_declaration, profiles=None
    )
    request = build_np_hard_hub_selection_request(
        target_problem=item.problem_declaration,
        registry_fingerprint=item.registry_fingerprint,
        candidates=candidate,
    )
    result = rank_np_hard_hub_candidates(request)
    assert result.failure_code == "no_authorable_hardness_hub"
    assert result.rejected[0].code == "target_cannot_be_authoring_seed"


@pytest.mark.parametrize(
    ("mutation", "code"),
    [
        (lambda candidate: replace(candidate, direction="problem_to_hardness_seed"), "candidate_wrong_direction"),
        (lambda candidate: replace(candidate, registry_fingerprint="bad"), "candidate_dependency_stale"),
        (lambda candidate: replace(candidate, stable_seed_id="fabricated"), "fabricated_hardness_seed"),
    ],
)
def test_candidate_identity_mutations_fail_closed(mutation, code: str) -> None:
    _, candidates = request_for([profile("semantic-proof")])
    with pytest.raises(NPHardHubSelectionError) as captured:
        mutation(candidates[0]).validate()
    assert captured.value.code == code


def test_request_rejects_candidate_bound_to_another_endpoint() -> None:
    request, candidates = request_for([profile("semantic-proof")])
    bad = replace(candidates[0], target_problem="Example.Other.problem")
    with pytest.raises(NPHardHubSelectionError) as captured:
        build_np_hard_hub_selection_request(
            target_problem=request.target_problem,
            registry_fingerprint=request.registry_fingerprint,
            candidates=(bad,),
        )
    assert captured.value.code == "candidate_wrong_endpoint"


def test_switch_requires_irrecoverable_failure_or_full_candidate_budget() -> None:
    request, _ = request_for([profile("semantic-proof"), profile("program-composition")])
    selection = rank_np_hard_hub_candidates(request)
    session = NPHardHubSwitchSessionV1(request=request, selection=selection)
    with pytest.raises(NPHardHubSelectionError) as captured:
        session.reject_current(
            failure_code="semantic_proof_failed",
            failure_class="budget_exhausted",
            model_calls=1,
        )
    assert captured.value.code == "invalid_hardness_hub_switch"


def test_switch_reissues_request_and_invalidates_endpoint_bound_nodes() -> None:
    request, _ = request_for([profile("semantic-proof"), profile("program-composition")])
    selection = rank_np_hard_hub_candidates(request)
    session = NPHardHubSwitchSessionV1(request=request, selection=selection)
    before = session.current_request
    assert before is not None
    digest = sha256_id({"node": "old-endpoint"})
    after = session.reject_current(
        failure_code="semantic_proof_failed",
        failure_class="budget_exhausted",
        model_calls=4,
        accepted_node_hashes=(digest,),
    )
    assert after is not None
    assert after.request_id != before.request_id
    assert after.candidate_id != before.candidate_id
    assert session.events[0]["endpoint_reuse"] is False
    assert session.events[0]["invalidated_node_hashes"] == [digest]
    assert session.consumed_model_calls == 4


def test_all_candidate_failures_end_with_typed_failure_and_instance_budget() -> None:
    request, _ = request_for(
        [profile("semantic-proof"), profile("program-composition"), profile("program-synthesis")]
    )
    selection = rank_np_hard_hub_candidates(request)
    session = NPHardHubSwitchSessionV1(request=request, selection=selection)
    assert session.reject_current(
        failure_code="semantic_proof_failed",
        failure_class="budget_exhausted",
        model_calls=4,
    ) is not None
    assert session.reject_current(
        failure_code="program_synthesis_failed",
        failure_class="budget_exhausted",
        model_calls=4,
    ) is None
    assert session.complete is True
    assert session.failure_code == "no_authorable_hardness_hub"
    assert session.consumed_model_calls == 8


def test_formal_g_d_report_satisfies_exit_conditions() -> None:
    path = ROOT / "Benchmark" / "Hardness" / "NP_HARD_HUB_SELECTION_REPORT.json"
    if not path.is_file():
        pytest.skip("formal G-D hub-selection report has not been generated")
    report = json.loads(path.read_text(encoding="utf-8"))
    metrics = report["metrics"]
    assert report["passed"] is True
    assert metrics["case_count"] == metrics["matched_case_count"] == 4
    assert metrics["multi_seed_input_count"] >= 3
    assert metrics["minimum_actual_seed_count"] >= 3
    assert metrics["stable_ordering_check_count"] >= 12
    assert metrics["stable_ordering_failure_count"] == 0
    assert metrics["selected_hub_axiom_audit_count"] == 3
    assert metrics["reverse_only_selected_count"] == 0
    assert metrics["no_authorable_hardness_hub_count"] == 1
    assert metrics["shorter_higher_risk_overtake_count"] == 0
    assert metrics["candidate_switch_audit_count"] == 1
    assert metrics["model_calls"] == 0
    # G-D is a completed historical qualification. Its captured plan hash
    # remains immutable while the active plan advances to later work packages.
    assert len(report["active_plan_sha256"]) == 64
    int(report["active_plan_sha256"], 16)


def test_full_45_case_g_d_report_is_content_addressed_and_complete() -> None:
    summary_path = ROOT / "Benchmark" / "Hardness" / "MAIN_G_D_45_FULL_REPORT.json"
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    raw_path = ROOT / summary["raw_report"]["file"]
    raw = json.loads(raw_path.read_text(encoding="utf-8"))
    hub_path = ROOT / summary["g_d_hub_selection_report"]["file"]
    assert summary["passed"] is True
    assert hashlib.sha256(raw_path.read_bytes()).hexdigest() == summary["raw_report"]["sha256"]
    assert hashlib.sha256(hub_path.read_bytes()).hexdigest() == summary["g_d_hub_selection_report"]["sha256"]
    assert raw["total"] == raw["passed"] == 45
    assert raw["failed"] == 0
    assert summary["counts"]["positive_verified_count"] == 29
    assert summary["counts"]["negative_expected_outcome_count"] == 16
    assert summary["real_model"]["model_call_count"] == 1
    assert summary["real_model"]["http_ok_count"] == 1
    assert summary["real_model"]["status_code"] == 200
    assert all(summary["gates"].values())
