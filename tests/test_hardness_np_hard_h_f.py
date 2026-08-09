from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path
from types import SimpleNamespace

import pytest

from agent.hardness.model_client import DeepSeekConfig, ModelResponse
from agent.hardness.np_hard_h_f_benchmark import (
    FORBIDDEN_SUITE_KEYS,
    _load_oracle,
    _load_suite,
    run_np_hard_h_f_qualification_heldout,
)
from agent.hardness.np_hard_inventory import (
    FORBIDDEN_MODULE_COMPONENTS,
    _library_modules,
)
from agent.hardness.np_hard_target_matrix import (
    DISPOSITION_UNCLASSIFIED,
    classify_identity_qualification,
    load_np_hard_target_matrix,
)
from agent.hardness.np_hard_scope_policy import (
    NPHardScopePolicyError,
    NPHardScopePolicyV1,
    load_np_hard_scope_policy,
    validate_scope_policy_against_inventory,
)


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "Benchmark/Hardness/Suites/np_hard_h_f_qualification_inputs.json"
ORACLE = ROOT / "Benchmark/Hardness/Evaluation/np_hard_h_f_qualification_oracle.json"
MATRIX = ROOT / "Benchmark/Hardness/NP_HARD_TARGET_MATRIX.json"
INVENTORY = ROOT / "Benchmark/Hardness/NP_HARD_H_F_INVENTORY.json"


class RecommendedBodyModel:
    def __init__(self) -> None:
        self.calls = 0

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        assert "untrusted Lean 4 author" in system
        self.calls += 1
        payload = json.loads(prompt)
        response = dict(payload["response_template"])
        response["replacement_body"] = payload["recommended_first_body"]
        return ModelResponse(
            called=True,
            ok=True,
            content=json.dumps(response),
            error=None,
            status_code=200,
            duration_seconds=0.0,
            usage={"fixture_tokens": 0},
            attempts=1,
            finish_reason="stop",
        )


def test_h_f_input_suite_contains_no_task_answer_metadata() -> None:
    cases = _load_suite(SUITE)
    assert len(cases) == 14
    assert all(not FORBIDDEN_SUITE_KEYS.intersection(case) for case in cases)
    assert len({case["id"] for case in cases}) == 14
    raw = json.loads(SUITE.read_text(encoding="utf-8"))
    assert all(set(case) == {"id", "module", "problem", "family"} for case in raw["cases"])
    assert all(case["module"].startswith("ComplexityReduction.") for case in cases)


def test_h_f_oracle_is_separate_and_matches_the_qualified_matrix() -> None:
    cases = _load_suite(SUITE)
    oracle = _load_oracle(ORACLE, {case["id"] for case in cases})
    positives = [case for case in cases if oracle[case["id"]]["status"] == "VERIFIED"]
    negatives = [case for case in cases if oracle[case["id"]]["status"] == "BLOCKED"]
    authoring = [case for case in positives if oracle[case["id"]]["requires_model"]]
    assert len(positives) == 6
    assert len(negatives) == 8
    assert len(authoring) == 0
    assert {case["family"] for case in positives} >= {
        "graph",
        "set-system",
        "numeric",
        "sat-csp",
        "other",
    }
    matrix = load_np_hard_target_matrix(MATRIX)
    assert matrix["identity_count"] == (
        matrix["in_scope_count"]
        + matrix["blocked_count"]
        + matrix["auxiliary_count"]
    )
    assert matrix["blocked_count"] >= len(negatives)
    assert matrix["unclassified_count"] == 0
    identities = {row["canonical_declaration"]: row for row in matrix["identities"]}
    for case in positives:
        oracle_expected = oracle[case["id"]]
        row = identities[case["problem"]]
        assert row["disposition"] == "in_scope_np_hard"
        assert row["has_forward_route"] is True
    for case in negatives:
        row = identities[case["problem"]]
        assert row["disposition"] == oracle[case["id"]]["disposition"]
        assert row["blocker"] == oracle[case["id"]]["failure_code"]


def test_h_f_matrix_reached_zero_unclassified() -> None:
    matrix = load_np_hard_target_matrix(MATRIX)
    assert matrix["unclassified_count"] == 0
    assert all(
        row["disposition"] != DISPOSITION_UNCLASSIFIED for row in matrix["identities"]
    )
    inventory_raw = json.loads(INVENTORY.read_text(encoding="utf-8"))
    assert inventory_raw.get("target_matrix_id") == matrix["matrix_id"]
    assert inventory_raw["target_matrix_unclassified_count"] == 0


def test_library_inventory_scope_is_public_and_full_sized() -> None:
    modules = _library_modules(ROOT)
    assert len(modules) >= 150
    assert all(module.startswith("ComplexityReduction.") for module in modules)
    assert all(not module.startswith("ComplexityReduction.Agent.") for module in modules)
    assert all(
        not FORBIDDEN_MODULE_COMPONENTS.intersection(module.split("."))
        for module in modules
    )


def test_h_f_scope_policy_is_exact_identity_based_and_inventory_coherent() -> None:
    policy = load_np_hard_scope_policy(root=ROOT)
    assert len(policy.entries) == 5
    assert len({entry.identity_id for entry in policy.entries}) == len(policy.entries)
    assert {entry.category for entry in policy.entries} == {
        "encoding_well_formedness_predicate",
        "tractable_syntactic_class",
    }
    inventory = json.loads(INVENTORY.read_text(encoding="utf-8"))
    validate_scope_policy_against_inventory(
        policy=policy, inventory_rows=inventory["entries"]
    )
    stale = NPHardScopePolicyV1(
        entries=(replace(policy.entries[0], problem_node_id="lean-whnf:0"),),
        source_file=policy.source_file,
    )
    with pytest.raises(NPHardScopePolicyError, match="identity drifted"):
        validate_scope_policy_against_inventory(
            policy=stale, inventory_rows=inventory["entries"]
        )


def test_formal_scope_policy_overrides_a_syntactically_planned_gap() -> None:
    policy = load_np_hard_scope_policy(root=ROOT)
    graph_policy = next(
        entry
        for entry in policy.entries
        if entry.canonical_declaration.endswith("GraphAtoms.graphWellFormedProblem")
    )
    result = classify_identity_qualification(
        has_forward_route=False,
        known_hardness_seed=False,
        planner={
            "status": "PLANNED",
            "failure_code": None,
            "task_class": "semantic_proof",
            "gap_node_count": 1,
            "capability_dag_node_count": 8,
        },
        canonical_declaration=graph_policy.canonical_declaration,
        scope_policy=graph_policy,
        identity_has_registered_member=True,
    )
    assert result["disposition"] == "auxiliary_or_non_target"
    assert result["basis"] == "formal_scope_policy"


def test_h_f_inventory_reports_declarations_and_identities_separately() -> None:
    inventory = json.loads(INVENTORY.read_text(encoding="utf-8"))
    assert inventory["declaration_count"] == inventory["presented_problem_count"]
    assert inventory["identity_count"] == inventory["unique_problem_identity_count"]
    assert len(inventory["entries"]) == inventory["declaration_count"]
    assert len(inventory["identities"]) == inventory["identity_count"]
    assert inventory["known_forward_route_declaration_count"] > inventory[
        "known_forward_route_identity_count"
    ]
    assert inventory["known_forward_route_identity_count"] == 22
    assert all(
        identity["member_count"] == len(identity["members"])
        for identity in inventory["identities"]
    )


def test_h_f_full_runner_with_fixture_cannot_masquerade_as_real_qualification(
    tmp_path,
) -> None:
    model = RecommendedBodyModel()
    report = run_np_hard_h_f_qualification_heldout(
        root=ROOT,
        suite_path=SUITE,
        oracle_path=ORACLE,
        output_root=tmp_path / "heldout",
        report_path=tmp_path / "report.json",
        inventory_path=tmp_path / "inventory.json",
        matrix_path=MATRIX,
        deepseek=DeepSeekConfig(
            api_key="fixture-secret",
            base_url="https://fixture.invalid",
            model="fixture-model",
            max_tokens=16000,
            max_retries=0,
            reasoning_effort="low",
        ),
        model_client=model,
    )
    metrics = report["metrics"]
    assert report["passed"] is False
    assert report["security"]["fixture_model_used"] is True
    assert metrics["positive_verified_count"] == 6
    assert metrics["negative_matched_count"] == 8
    assert metrics["existing_route_model_calls"] == 0
    assert metrics["structural_negative_model_calls"] == 0
    assert metrics["authoring_problem_count"] == 0
    assert metrics["authoring_verified_count"] == 0
    assert metrics["independent_replay_count"] >= 6
    assert metrics["standard_axiom_audit_count"] >= 6
    assert metrics["endpoint_equality_audit_count"] >= 6
    assert metrics["worker_fallback_count"] == 0
    assert model.calls == 0


def test_directed_forward_reachability_contract() -> None:
    connections = (
        SimpleNamespace(source_node_id="seed", target_node_id="middle"),
        SimpleNamespace(source_node_id="middle", target_node_id="target"),
        SimpleNamespace(source_node_id="reverse-only", target_node_id="seed"),
    )
    from agent.hardness.np_hard_inventory import _shortest_hardness_distances

    distances = _shortest_hardness_distances(
        seed_nodes={"seed"}, connections=connections
    )
    assert distances == {"seed": 0, "middle": 1, "target": 2}
    assert "reverse-only" not in distances
