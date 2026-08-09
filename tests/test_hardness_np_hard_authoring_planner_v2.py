from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.model_client import ModelResponse
from agent.hardness.np_hard_authoring import (
    NPHardAuthoringContractError,
    build_np_hard_authoring_prompt_v2,
)
from agent.hardness.np_hard_authoring_planner import (
    NPHardAuthoringPlannerV2,
    plan_np_hard_authoring_from_observation,
)
from agent.hardness.np_hard_orchestrator import (
    NPHardOrchestratorConfigV2,
    NPHardOrchestratorV2,
)


ROOT = Path(__file__).resolve().parents[1]
CASES = (
    (
        "Benchmark.Hardness.Inputs.NPHardMVP.ModelAuthoredTaggedThreeSAT",
        "Benchmark.Hardness.Inputs.NPHardMVP.ModelAuthoredTaggedThreeSAT.source",
        "semantic_proof",
        1,
    ),
    (
        "Benchmark.Hardness.Inputs.NPHardGeneralization.GraphProofOnly",
        "Benchmark.Hardness.Inputs.NPHardGeneralization.GraphProofOnly.source",
        "semantic_proof",
        2,
    ),
    (
        "Benchmark.Hardness.Inputs.NPHardGeneralization.SetSystemProgramComposition",
        "Benchmark.Hardness.Inputs.NPHardGeneralization.SetSystemProgramComposition.source",
        "program_composition",
        2,
    ),
    (
        "Benchmark.Hardness.Inputs.NPHardGeneralization.NumericProgramComposition",
        "Benchmark.Hardness.Inputs.NPHardGeneralization.NumericProgramComposition.source",
        "program_composition",
        2,
    ),
    (
        "Benchmark.Hardness.Inputs.NPHardGeneralization.GraphProgramSynthesis",
        "Benchmark.Hardness.Inputs.NPHardGeneralization.GraphProgramSynthesis.source",
        "program_synthesis",
        5,
    ),
)


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
def automatic_plans(tmp_path_factory):
    output = tmp_path_factory.mktemp("np-hard-authoring-planner")
    rows = []
    for index, (module, problem, _, _) in enumerate(CASES):
        rows.append(
            NPHardAuthoringPlannerV2(
                root=ROOT,
                input_module=module,
                input_problem_declaration=problem,
                output_dir=output / f"case-{index}",
            ).plan()
        )
    return tuple(rows)


def test_five_cases_plan_without_suite_authoring_metadata(automatic_plans) -> None:
    assert [plan.status for plan in automatic_plans] == ["PLANNED"] * 5
    assert [plan.task.task_class for plan in automatic_plans] == [
        case[2] for case in CASES
    ]
    assert [len(plan.task.gap_nodes) for plan in automatic_plans] == [
        case[3] for case in CASES
    ]
    assert all(plan.model_calls == 0 for plan in automatic_plans)
    planner_source = (
        ROOT / "agent/hardness/np_hard_authoring_planner.py"
    ).read_text(encoding="utf-8")
    for plan in automatic_plans:
        assert plan.observation.import_closure_sha256.startswith("sha256:")
        assert plan.observation.lake_manifest_sha256.startswith("sha256:")
        assert plan.observation.toolchain == "leanprover/lean4:v4.29.0"
        assert plan.observation.input_module in plan.observation.import_modules
        assert plan.selected_hub is not None
        assert plan.observation.input_declaration not in planner_source
        assert plan.task.target_problem.term == plan.observation.input_declaration
        capabilities = {node.capability for node in plan.capability_dag}
        assert "semantic_forward_implication" in capabilities
        assert "semantic_reverse_implication" in capabilities
        assert "certified_reduction" in capabilities
        assert "native_tm_np_hard" in capabilities


def test_planner_is_content_deterministic_and_prompt_has_no_benchmark_answers(
    automatic_plans, tmp_path
) -> None:
    module, problem, _, _ = CASES[0]
    repeated = NPHardAuthoringPlannerV2(
        root=ROOT,
        input_module=module,
        input_problem_declaration=problem,
        output_dir=tmp_path / "repeat",
    ).plan()
    original = automatic_plans[0]
    assert repeated.observation.observation_id == original.observation.observation_id
    assert repeated.task.request_id == original.task.request_id
    assert repeated.task.to_dict() == original.task.to_dict()
    assert repeated.plan_id == original.plan_id
    prompt = build_np_hard_authoring_prompt_v2(task=repeated.task, root=ROOT).lower()
    for forbidden in ('"case_id"', '"expected"', '"gold"', '"hidden_gold"'):
        assert forbidden not in prompt
    assert ".gold." not in prompt
    assert ".oracles." not in prompt


def test_planner_blocks_reverse_only_missing_prerequisite_and_disconnected_graph(
    automatic_plans,
) -> None:
    graph = automatic_plans[1]
    observation = graph.observation
    direct = next(
        program
        for program in observation.poly_programs
        if program.declaration.endswith(".forwardProgram")
    )
    reverse = replace(
        direct,
        source=direct.target,
        target=direct.source,
        source_representation_node=direct.target_representation_node,
        target_representation_node=direct.source_representation_node,
    )
    reverse_plan = plan_np_hard_authoring_from_observation(
        root=ROOT,
        input_module=CASES[1][0],
        input_problem_declaration=CASES[1][1],
        observation=replace(observation, poly_programs=(reverse,)),
    )
    assert reverse_plan.status == "BLOCKED"
    assert reverse_plan.failure_code == "wrong_direction_only"

    synthesis = automatic_plans[4]
    missing_relation = plan_np_hard_authoring_from_observation(
        root=ROOT,
        input_module=CASES[4][0],
        input_problem_declaration=CASES[4][1],
        observation=replace(synthesis.observation, mapping_relations=()),
    )
    assert missing_relation.status == "BLOCKED"
    assert missing_relation.failure_code == "authoring_plan_missing_capability"
    assert missing_relation.missing_capabilities == ("mapping_invariant",)

    composition = automatic_plans[2]
    disconnected = plan_np_hard_authoring_from_observation(
        root=ROOT,
        input_module=CASES[2][0],
        input_problem_declaration=CASES[2][1],
        observation=replace(composition.observation, poly_programs=()),
    )
    assert disconnected.status == "BLOCKED"
    assert "poly_program" in disconnected.missing_capabilities


def test_task_validation_rejects_cycle_and_dependency_hash_drift(automatic_plans) -> None:
    task = automatic_plans[1].task
    first = task.gap_nodes[0]
    cyclic = replace(first, depends_on=(first.node_id,))
    with pytest.raises(NPHardAuthoringContractError) as raised:
        replace(task, gap_nodes=(cyclic, *task.gap_nodes[1:])).validate()
    assert raised.value.code == "candidate_dependency_stale"

    dependency_name, dependency_hash = task.dependency_hashes[0]
    stale = replace(
        task,
        dependency_hashes=(
            (dependency_name, "sha256:" + "0" * 64),
            *task.dependency_hashes[1:],
        ),
    )
    with pytest.raises(NPHardAuthoringContractError) as raised:
        stale.validate()
    assert raised.value.code == "candidate_dependency_stale"
    assert dependency_hash != "sha256:" + "0" * 64


def test_production_orchestrator_auto_plans_from_module_and_problem(tmp_path) -> None:
    module, problem, _, expected_nodes = CASES[1]
    model = RecommendedBodyModel()
    result = NPHardOrchestratorV2(
        NPHardOrchestratorConfigV2(
            root=ROOT,
            input_module=module,
            problem_declaration=problem,
            output_dir=tmp_path / "production-auto",
            authoring_policy="model-required",
            runtime_prebuilt=False,
        ),
        model_client=model,
    ).run()
    payload = result.to_dict()
    assert result.status == "VERIFIED"
    assert result.model_calls == model.calls == expected_nodes
    assert payload["capability_dag"]["task_class"] == "semantic_proof"
    assert payload["artifact"]["endpoint"] == problem
    assert payload["independent_replay"]["passed"] is True
    assert payload["axiom_audit"]["passed"] is True
    assert payload["deletion_audit"]["passed"] is True
    planner_report = tmp_path / "production-auto/planning/plan.json"
    assert json.loads(planner_report.read_text(encoding="utf-8"))["model_calls"] == 0
