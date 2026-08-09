from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace

from agent.hardness.model_client import DeepSeekConfig, ModelResponse
from agent.hardness.np_hard_h_e_benchmark import (
    EXISTING_MODEL_AUTHORING_PROBLEMS,
    FORBIDDEN_SUITE_KEYS,
    _load_oracle,
    _load_suite,
    run_np_hard_h_e_heldout,
)
from agent.hardness.np_hard_inventory import (
    FORBIDDEN_MODULE_COMPONENTS,
    _family,
    _library_modules,
    _shortest_hardness_distances,
)


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "Benchmark/Hardness/Suites/np_hard_h_e_heldout_inputs.json"
ORACLE = ROOT / "Benchmark/Hardness/Evaluation/np_hard_h_e_heldout_oracle.json"


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


def test_h_e_input_suite_contains_no_task_answer_metadata() -> None:
    cases = _load_suite(SUITE)
    assert len(cases) == 12
    assert all(not FORBIDDEN_SUITE_KEYS.intersection(case) for case in cases)
    assert len({case["id"] for case in cases}) == 12
    raw = json.loads(SUITE.read_text(encoding="utf-8"))
    assert all(set(case) == {"id", "module", "problem", "family"} for case in raw["cases"])


def test_h_e_oracle_is_separate_and_meets_coverage_contract() -> None:
    cases = _load_suite(SUITE)
    oracle = _load_oracle(ORACLE, {case["id"] for case in cases})
    positives = [case for case in cases if oracle[case["id"]]["status"] == "VERIFIED"]
    negatives = [case for case in cases if oracle[case["id"]]["status"] == "BLOCKED"]
    authoring = [case for case in positives if oracle[case["id"]]["requires_model"]]
    assert len(positives) == 8
    assert len(negatives) == 4
    assert len({case["family"] for case in positives}) >= 4
    assert len(authoring) == 4
    assert sum(
        case["problem"] not in EXISTING_MODEL_AUTHORING_PROBLEMS for case in positives
    ) >= 4
    assert {oracle[case["id"]]["task_class"] for case in authoring} == {
        "semantic_proof",
        "program_composition",
        "program_synthesis",
    }
    assert any(oracle[case["id"]]["gap_count"] == 1 for case in authoring)
    assert any(oracle[case["id"]]["gap_count"] > 1 for case in authoring)
    assert {oracle[case["id"]]["failure_code"] for case in negatives} == {
        "wrong_direction_only",
        "missing_lawful_presentation",
        "ambiguous_lawful_presentation",
        "candidate_wrong_endpoint",
    }


def test_library_inventory_scope_is_public_and_full_sized() -> None:
    modules = _library_modules(ROOT)
    assert len(modules) >= 150
    assert all(module.startswith("ComplexityReduction.") for module in modules)
    assert all(not module.startswith("ComplexityReduction.Agent.") for module in modules)
    assert all(
        not FORBIDDEN_MODULE_COMPONENTS.intersection(module.split("."))
        for module in modules
    )


def test_inventory_forward_reachability_uses_directed_edges() -> None:
    connections = (
        SimpleNamespace(source_node_id="seed", target_node_id="middle"),
        SimpleNamespace(source_node_id="middle", target_node_id="target"),
        SimpleNamespace(source_node_id="reverse-only", target_node_id="seed"),
    )
    distances = _shortest_hardness_distances(
        seed_nodes={"seed"}, connections=connections
    )
    assert distances == {"seed": 0, "middle": 1, "target": 2}
    assert "reverse-only" not in distances


def test_inventory_family_classification_covers_required_families() -> None:
    assert _family("Example.ThreeSAT.problem") == "sat-csp"
    assert _family("Example.VertexCover.problem") == "graph"
    assert _family("Example.ExactCover.problem") == "set-system"
    assert _family("Example.BinaryKnapsack.problem") == "numeric"


def test_h_e_full_runner_with_fixture_cannot_masquerade_as_real_qualification(
    tmp_path,
) -> None:
    model = RecommendedBodyModel()
    report = run_np_hard_h_e_heldout(
        root=ROOT,
        suite_path=SUITE,
        oracle_path=ORACLE,
        output_root=tmp_path / "heldout",
        report_path=tmp_path / "report.json",
        inventory_path=tmp_path / "inventory.json",
        deepseek=DeepSeekConfig(
            api_key="fixture-secret",
            base_url="https://fixture.invalid",
            model="fixture-model",
            max_tokens=16000,
            max_retries=0,
        ),
        model_client=model,
    )
    metrics = report["metrics"]
    assert report["passed"] is False
    assert report["security"]["fixture_model_used"] is True
    assert metrics["positive_verified_count"] == 8
    assert metrics["negative_matched_count"] == 4
    assert metrics["real_api_calls"] == model.calls == 10
    assert metrics["existing_route_model_calls"] == 0
    assert metrics["structural_negative_model_calls"] == 0
    assert metrics["independent_replay_count"] == 8
    assert metrics["standard_axiom_audit_count"] == 8
    assert metrics["endpoint_equality_audit_count"] == 8
    assert metrics["deletion_audit_problem_count"] == 4
    assert metrics["deletion_audit_node_count"] == 10
    assert metrics["worker_fallback_count"] == 0
