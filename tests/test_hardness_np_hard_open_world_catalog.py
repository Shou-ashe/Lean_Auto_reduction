from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.model_client import ModelResponse
from agent.hardness.np_hard_authoring_planner import (
    NPHardAuthoringPlannerError,
    NPHardAuthoringPlannerV2,
    plan_np_hard_authoring_from_observation,
)
from agent.hardness.np_hard_orchestrator import (
    NPHardOrchestratorConfigV2,
    NPHardOrchestratorV2,
)


ROOT = Path(__file__).resolve().parents[1]
ENTRY = "Benchmark.Hardness.Inputs.HCCrossModule.Entry"
TARGET = "Benchmark.Hardness.Inputs.HCCrossModule.Problem.heldOutTarget"


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


@pytest.fixture(scope="module")
def cross_module_plan(tmp_path_factory):
    return NPHardAuthoringPlannerV2(
        root=ROOT,
        input_module=ENTRY,
        input_problem_declaration=TARGET,
        output_dir=tmp_path_factory.mktemp("h-c-open-world") / "plan",
    ).plan()


def test_cross_module_catalog_discovers_hub_route_programs_and_gap_dag(
    cross_module_plan,
) -> None:
    plan = cross_module_plan
    assert plan.status == "PLANNED"
    assert plan.model_calls == 0
    assert plan.task.task_class == "program_composition"
    assert plan.selected_hub == (
        "Benchmark.Hardness.Inputs.HCCrossModule.Problem.hardnessHub"
    )
    assert len(plan.task.gap_nodes) == 2
    assert plan.observation.input_module == ENTRY
    assert plan.observation.declaration_module == (
        "Benchmark.Hardness.Inputs.HCCrossModule.Problem"
    )
    assert plan.observation.import_closure_sha256.startswith("sha256:")
    assert plan.observation.lake_manifest_sha256.startswith("sha256:")
    assert plan.observation.hardness_seeds
    assert plan.observation.certified_reductions
    assert {
        item.module for item in plan.observation.poly_programs
    } >= {"Benchmark.Hardness.Inputs.HCCrossModule.Adapters"}
    capabilities = [node.capability for node in plan.capability_dag]
    assert "native_hardness_seed" in capabilities
    assert "certified_reduction_route" in capabilities
    assert capabilities.count("poly_program") >= 2
    assert "native_tm_np_hard" in capabilities
    public_sources = set(plan.task.public_source_files)
    assert any(path.endswith("HCCrossModule/Adapters.lean") for path in public_sources)
    assert any(path.endswith("HCCrossModule/Specification.lean") for path in public_sources)


def test_held_out_target_is_not_a_planner_constant_or_prompt_special_case(
    cross_module_plan,
) -> None:
    planner_source = (
        ROOT / "agent/hardness/np_hard_authoring_planner.py"
    ).read_text(encoding="utf-8")
    lean_source = (
        ROOT
        / "Lean/Reference/ComplexityReduction/Agent/Hardness/AuthoringPlanner.lean"
    ).read_text(encoding="utf-8")
    assert "HCCrossModule" not in planner_source
    assert "HCCrossModule" not in lean_source
    assert TARGET not in planner_source
    assert TARGET not in lean_source
    assert TARGET == cross_module_plan.task.target_problem.term


def test_stale_catalog_is_rejected_before_authoring(cross_module_plan) -> None:
    stale = replace(
        cross_module_plan.observation,
        import_closure_sha256="sha256:" + "0" * 64,
    )
    with pytest.raises(NPHardAuthoringPlannerError) as raised:
        plan_np_hard_authoring_from_observation(
            root=ROOT,
            input_module=ENTRY,
            input_problem_declaration=TARGET,
            observation=stale,
        )
    assert raised.value.code == "authoring_catalog_dependency_stale"


def test_equal_best_distinct_hubs_block_with_stable_ranking(cross_module_plan) -> None:
    observation = cross_module_plan.observation
    original_hub = next(
        problem
        for problem in observation.problems
        if problem.declaration == cross_module_plan.selected_hub
    )
    alternate_hub = replace(
        original_hub,
        declaration="Benchmark.Hardness.Inputs.HCCrossModule.Problem.alternateHub",
        endpoint_node="lean-whnf:alternate-hub-endpoint",
        representation_node="lean-whnf:alternate-hub-representation",
    )
    original_first = next(
        program
        for program in observation.poly_programs
        if program.declaration.endswith(".firstAdapter")
    )
    alternate_first = replace(
        original_first,
        declaration="Benchmark.Hardness.Inputs.HCCrossModule.Adapters.alternateFirstAdapter",
        source=alternate_hub.declaration,
        source_representation_node=alternate_hub.representation_node,
    )
    original_gap = next(
        gap
        for gap in observation.gaps
        if gap.source == original_hub.declaration
    )
    alternate_gap = replace(
        original_gap,
        declaration="Benchmark.Hardness.Inputs.HCCrossModule.Specification.alternateGap",
        source=alternate_hub.declaration,
        source_node=alternate_hub.endpoint_node,
    )
    seed = observation.hardness_seeds[0]
    original_route = next(
        edge
        for edge in observation.certified_reductions
        if edge.source_node == seed.endpoint_node
        and edge.target_node == original_hub.endpoint_node
    )
    alternate_route = replace(
        original_route,
        declaration="Benchmark.Hardness.Inputs.HCCrossModule.Adapters.alternateHardnessRoute",
        lean_term="Benchmark.Hardness.Inputs.HCCrossModule.Adapters.alternateHardnessRoute",
        target=alternate_hub.declaration,
        target_node=alternate_hub.endpoint_node,
    )
    ambiguous = plan_np_hard_authoring_from_observation(
        root=ROOT,
        input_module=ENTRY,
        input_problem_declaration=TARGET,
        observation=replace(
            observation,
            problems=(*observation.problems, alternate_hub),
            poly_programs=(*observation.poly_programs, alternate_first),
            gaps=(*observation.gaps, alternate_gap),
            certified_reductions=(
                *observation.certified_reductions,
                alternate_route,
            ),
        ),
    )
    assert ambiguous.status == "BLOCKED"
    assert ambiguous.failure_code == "ambiguous_authoring_hub"
    assert ambiguous.model_calls == 0
    assert ambiguous.ranked_hubs == tuple(sorted(ambiguous.ranked_hubs))
    assert set(ambiguous.ranked_hubs) == {
        original_hub.declaration,
        alternate_hub.declaration,
    }


def test_production_entry_uses_cross_module_plan_without_model_discovery(tmp_path) -> None:
    model = RecommendedBodyModel()
    output = tmp_path / "production"
    result = NPHardOrchestratorV2(
        NPHardOrchestratorConfigV2(
            root=ROOT,
            input_module=ENTRY,
            problem_declaration=TARGET,
            output_dir=output,
            authoring_policy="model-required",
            runtime_prebuilt=False,
        ),
        model_client=model,
    ).run()
    payload = result.to_dict()
    planner = json.loads((output / "planning/plan.json").read_text(encoding="utf-8"))
    assert result.status == "VERIFIED"
    assert result.model_calls == model.calls == 2
    assert planner["model_calls"] == 0
    assert planner["selected_hub"].endswith(".hardnessHub")
    assert payload["artifact"]["endpoint"] == TARGET
    assert payload["independent_replay"]["passed"] is True
    assert payload["axiom_audit"]["passed"] is True
    assert payload["deletion_audit"]["passed"] is True
