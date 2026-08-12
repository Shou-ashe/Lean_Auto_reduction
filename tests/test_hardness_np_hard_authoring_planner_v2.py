from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.model_client import ModelResponse
from agent.hardness.np_hard_authoring import (
    NPHardAuthoringContractError,
    NPHardAuthoringTaskV2,
    build_np_hard_authoring_prompt_v2,
)
from agent.hardness.np_hard_authoring_planner import (
    NP_HARD_AUTHORING_OBSERVATION_SCHEMA_V1,
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

DEPENDENT_COMPOSITION_CASES = (
    (
        "ComplexityReduction.Presentation.SetSystem",
        "ComplexityReduction.Presentation.SetSystem.hittingSetStructuredProblem",
        "ComplexityReduction.Presentation.SetSystem.setCoveringStructuredProblem",
    ),
    (
        "ComplexityReduction.Presentation.FeedbackArcSet",
        "ComplexityReduction.Presentation.FeedbackArcSet.structuredProblem",
        "ComplexityReduction.Presentation.FeedbackNodeSet.structuredProblem",
    ),
)

H_J_5_CASES = (
    (
        "ComplexityReduction.Presentation.MaxCut",
        "ComplexityReduction.Presentation.MaxCut.structuredProblem",
    ),
    (
        "ComplexityReduction.Presentation.MaxCutBinary",
        "ComplexityReduction.Presentation.MaxCutBinary.binaryStructuredProblem",
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


@pytest.fixture(scope="module")
def dependent_composition_plans(tmp_path_factory):
    output = tmp_path_factory.mktemp("np-hard-dependent-composition-planner")
    return tuple(
        NPHardAuthoringPlannerV2(
            root=ROOT,
            input_module=module,
            input_problem_declaration=problem,
            output_dir=output / f"case-{index}",
        ).plan()
        for index, (module, problem, _) in enumerate(DEPENDENT_COMPOSITION_CASES)
    )


@pytest.fixture(scope="module")
def h_j_5_plans(tmp_path_factory):
    output = tmp_path_factory.mktemp("np-hard-h-j-5-planner")
    return tuple(
        NPHardAuthoringPlannerV2(
            root=ROOT,
            input_module=module,
            input_problem_declaration=problem,
            output_dir=output / f"case-{index}",
        ).plan()
        for index, (module, problem) in enumerate(H_J_5_CASES)
    )


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
        assert (
            plan.observation.schema_version
            == NP_HARD_AUTHORING_OBSERVATION_SCHEMA_V1
        )
        assert plan.selected_hub is not None
        assert plan.observation.input_declaration not in planner_source
        assert plan.task.target_problem.term == plan.observation.input_declaration
        capabilities = {node.capability for node in plan.capability_dag}
        assert "semantic_forward_implication" in capabilities
        assert "semantic_reverse_implication" in capabilities
        assert "certified_reduction" in capabilities
        assert "native_tm_np_hard" in capabilities


def test_h_j_5_plans_exact_gadget_and_successor_only_surfaces(h_j_5_plans) -> None:
    structured, binary = h_j_5_plans
    assert structured.status == binary.status == "PLANNED"
    assert structured.task.task_class == "typed_gadget_indexed_admission_dag"
    assert binary.task.task_class == "typed_tmkarp_dependent_composition_dag"
    assert [len(structured.task.gap_nodes), len(binary.task.gap_nodes)] == [10, 5]
    assert [node.node_id for node in structured.task.gap_nodes] == [
        "gadget-reference-audit",
        "gadget-normalization-audit",
        "gadget-executable",
        "gadget-parameter-audit",
        "gadget-semantic-forward",
        "gadget-semantic-reverse",
        "gadget-direct-tm",
        "gadget-program",
        "gadget-composed-program",
        "gadget-composed-semantic-iff",
    ]
    assert [node.node_id for node in binary.task.gap_nodes] == [
        "tmkarp-primitive",
        "tmkarp-program",
        "tmkarp-semantic-iff",
        "composed-program",
        "composed-semantic-iff",
    ]

    structured_sources = set(structured.task.public_source_files)
    assert structured_sources == {
        "Lean/Reference/ComplexityReduction/Agent/Hardness/GadgetAuthoringSources.lean",
        "Lean/Reference/ComplexityReduction/Presentation/MaxCut.lean",
        "Lean/Reference/ComplexityReduction/Presentation/NAEThreeSAT.lean",
        "Lean/Reference/ComplexityReduction/Problems/Karp21/Satisfiability.lean",
    }
    assert not any("SuccessorAuthoringSources" in path for path in structured_sources)
    assert set(binary.task.public_source_files) == {
        "Lean/Reference/ComplexityReduction/Agent/Hardness/SuccessorAuthoringSources.lean",
        "Lean/Reference/ComplexityReduction/Presentation/MaxCut.lean",
        "Lean/Reference/ComplexityReduction/Presentation/MaxCutBinary.lean",
        "Lean/Reference/ComplexityReduction/Problems/Karp21/Satisfiability.lean",
        "Lean/Reference/ComplexityReduction/Routes/MaxCutToMaxCutBinary/Unified.lean",
    }

    structured_kinds = {
        capability.capability_kind
        for capability in structured.observation.typed_capabilities
    }
    binary_kinds = {
        capability.capability_kind
        for capability in binary.observation.typed_capabilities
    }
    assert "forward_gadget_indexed_admission" in structured_kinds
    assert "forward_successor_only_tmkarp_admission" not in structured_kinds
    assert {
        "forward_successor_only_tmkarp_admission",
        "forward_certified_successor",
    }.issubset(binary_kinds)

    successor = dict(binary.task.observed_capability_terms)["composed-program"]
    successor_module = binary.task.composition_successor_module
    assert successor_module is not None
    owner = successor.rsplit(".", 1)[0]
    assert successor_module == owner + ".Unified"
    assert binary.task.composition_intermediate is not None
    assert (
        binary.task.composition_successor_source
        == binary.task.composition_intermediate.term
    )
    assert (
        binary.task.composition_successor_target
        == binary.task.target_problem.term
    )
    assert dict(binary.task.observed_capability_exact_types)[
        "composed-program"
    ].split() == [
        "ComplexityReduction.Certificate.CertifiedReduction",
        binary.task.composition_successor_source,
        binary.task.composition_successor_target,
    ]
    admission_observation = dict(
        binary.task.composition_admission_observation or ()
    )
    successor_observation = dict(
        binary.task.composition_successor_observation or ()
    )
    assert admission_observation == {
        **next(
            capability.to_dict()
            for capability in binary.observation.typed_capabilities
            if capability.capability_kind
            == "forward_successor_only_tmkarp_admission"
        ),
        "registry_fingerprint": binary.observation.registry_fingerprint,
    }
    observed_successor = next(
        capability.to_dict()
        for capability in binary.observation.typed_capabilities
        if capability.capability_kind == "forward_certified_successor"
        and capability.witness == successor
    )
    assert successor_observation == {
        **observed_successor,
        "exact_type": dict(binary.task.observed_capability_exact_types)[
            "composed-program"
        ],
        "registry_fingerprint": binary.observation.registry_fingerprint,
    }
    dependencies = dict(binary.task.dependency_hashes)
    assert dependencies[
        "content:observed-composition-successor-source"
    ].startswith("sha256:")
    assert dependencies[
        "content:observed-composition-successor-target"
    ].startswith("sha256:")


def test_v3_typed_capability_builds_generic_four_node_dag(automatic_plans) -> None:
    original = automatic_plans[0]
    target_node = original.observation.input_node
    adapters = tuple(
        capability
        for capability in original.observation.typed_capabilities
        if capability.capability_kind == "forward_representation_adapter"
        and capability.target_node == target_node
    )
    assert len(adapters) == 1
    adapter = adapters[0]
    assert "PolyProg.snd" not in adapter.witness
    typed = plan_np_hard_authoring_from_observation(
        root=ROOT,
        input_module=CASES[0][0],
        input_problem_declaration=CASES[0][1],
        observation=replace(
            original.observation,
            poly_programs=(),
            mapping_relations=(),
            gaps=(),
        ),
    )
    assert typed.status == "PLANNED"
    assert typed.task.task_class == "typed_capability_dag"
    assert [node.capability for node in typed.task.gap_nodes] == [
        "representation_adapter",
        "semantic_forward",
        "semantic_reverse",
        "semantic_iff",
    ]
    assert typed.task.terminal_node_id == typed.terminal_node_id == "semantic-iff"
    assert (
        typed.task.final_program_node_id
        == typed.final_program_node_id
        == "representation-adapter"
    )
    assert typed.final_node_id == "native-tm-np-hard"
    assert dict(typed.task.observed_capability_terms) == {
        "representation-adapter": adapter.witness
    }
    payload = typed.task.to_dict()
    assert NPHardAuthoringTaskV2.from_dict(payload) == typed.task
    payload["observed_capability_terms"]["representation-adapter"] = (
        "ComplexityReduction.Program.PolyProg.snd "
        "ComplexityReduction.Encoding.StandardInstances.bool "
        f"{typed.task.source_problem.term}.representation"
    )
    with pytest.raises(NPHardAuthoringContractError) as tampered:
        NPHardAuthoringTaskV2.from_dict(payload)
    assert tampered.value.code in {
        "candidate_dependency_stale",
        "candidate_wrong_direction",
    }
    assert dict(typed.task.dependency_hashes)[
        "content:lean-typed-capability"
    ].startswith("sha256:")
    assert "semantic_forward" in {node.capability for node in typed.capability_dag}
    assert "semantic_reverse" in {node.capability for node in typed.capability_dag}


def test_v3_tmkarp_admission_builds_content_addressed_three_node_dag(
    automatic_plans,
) -> None:
    original = automatic_plans[0]
    adapter = next(
        capability
        for capability in original.observation.typed_capabilities
        if capability.target_node == original.observation.input_node
    )
    source = next(
        problem
        for problem in original.observation.problems
        if problem.endpoint_node == adapter.source_node
    )
    target = next(
        problem
        for problem in original.observation.problems
        if problem.endpoint_node == adapter.target_node
    )
    module = "ComplexityReduction.Agent.Hardness.AuthoringSources"
    witness = module + ".syntheticEndpointExactTMKarpReduction"
    capability = replace(
        adapter,
        capability_kind="forward_tmkarp_admission",
        capability_id="forward_tmkarp_admission:source:target",
        witness=witness,
        exact_type=(
            "ComplexityReduction.TMKarpReduction "
            f"{source.rendered_endpoint}.toEncodedDecisionProblem "
            f"{target.rendered_endpoint}.toEncodedDecisionProblem"
        ),
        module=module,
        authority="lean_exact_tmkarp_public_source",
    )
    plan = plan_np_hard_authoring_from_observation(
        root=ROOT,
        input_module=CASES[0][0],
        input_problem_declaration=CASES[0][1],
        observation=replace(
            original.observation,
            poly_programs=(),
            mapping_relations=(),
            gaps=(),
            typed_capabilities=(capability,),
        ),
    )
    assert plan.status == "PLANNED"
    task = plan.task
    assert task.task_class == "typed_tmkarp_admission_dag"
    assert [node.node_id for node in task.gap_nodes] == [
        "tmkarp-primitive",
        "tmkarp-program",
        "tmkarp-semantic-iff",
    ]
    assert [node.capability for node in task.gap_nodes] == [
        "tmkarp_primitive",
        "tmkarp_program",
        "tmkarp_semantic_iff",
    ]
    assert task.terminal_node_id == plan.terminal_node_id == "tmkarp-semantic-iff"
    assert task.final_program_node_id == plan.final_program_node_id == "tmkarp-program"
    assert dict(task.observed_capability_terms) == {
        "tmkarp-primitive": witness
    }
    assert dict(task.observed_capability_exact_types) == {
        "tmkarp-primitive": capability.exact_type
    }
    dependencies = dict(task.dependency_hashes)
    assert dependencies["content:observed-capability-term:tmkarp-primitive"].startswith(
        "sha256:"
    )
    assert dependencies[
        "content:observed-capability-exact-type:tmkarp-primitive"
    ].startswith("sha256:")
    assert dependencies[f"module:{module}"].startswith("sha256:")
    assert module in task.allowed_imports
    assert all("/Legacy/" not in path for path in task.public_source_files)
    public_node = next(
        node
        for node in plan.capability_dag
        if node.node_id == "public-forward-tmkarp-admission"
    )
    primitive_node = next(
        node for node in plan.capability_dag if node.node_id == "tmkarp-primitive"
    )
    assert public_node.declaration == witness
    assert primitive_node.depends_on == ("public-forward-tmkarp-admission",)
    assert NPHardAuthoringTaskV2.from_dict(task.to_dict()) == task

    payload = task.to_dict()
    payload["observed_capability_exact_types"]["tmkarp-primitive"] = (
        "ComplexityReduction.TMKarpReduction Target.problem Source.problem"
    )
    with pytest.raises(NPHardAuthoringContractError) as tampered:
        NPHardAuthoringTaskV2.from_dict(payload)
    assert tampered.value.code == "candidate_dependency_stale"


def test_v3_dependent_tmkarp_composition_builds_one_strict_five_node_chain(
    dependent_composition_plans,
) -> None:
    planner_source = (
        ROOT / "agent/hardness/np_hard_authoring_planner.py"
    ).read_text(encoding="utf-8")
    assert "HittingSet" not in planner_source
    assert "FeedbackArcSet" not in planner_source
    for plan, (_, _, expected_intermediate) in zip(
        dependent_composition_plans, DEPENDENT_COMPOSITION_CASES
    ):
        assert plan.status == "PLANNED"
        task = plan.task
        assert task.task_class == "typed_tmkarp_dependent_composition_dag"
        assert task.composition_intermediate is not None
        assert task.composition_intermediate.term == expected_intermediate
        assert task.composition_successor_module is not None
        assert task.composition_successor_module in task.allowed_imports
        assert [node.node_id for node in task.gap_nodes] == [
            "tmkarp-primitive",
            "tmkarp-program",
            "tmkarp-semantic-iff",
            "composed-program",
            "composed-semantic-iff",
        ]
        assert [node.capability for node in task.gap_nodes] == [
            "tmkarp_primitive",
            "tmkarp_program",
            "tmkarp_semantic_iff",
            "dependent_composed_program",
            "dependent_composed_semantic_iff",
        ]
        assert task.gap_nodes[-1].depends_on == (
            "tmkarp-semantic-iff",
            "composed-program",
        )
        assert task.terminal_node_id == plan.terminal_node_id == "composed-semantic-iff"
        assert task.final_program_node_id == plan.final_program_node_id == "composed-program"
        assert set(dict(task.observed_capability_terms)) == {
            "tmkarp-primitive",
            "composed-program",
        }
        assert set(dict(task.observed_capability_exact_types)) == {
            "tmkarp-primitive",
            "composed-program",
        }
        dependencies = dict(task.dependency_hashes)
        assert dependencies["content:lean-certified-successor"].startswith("sha256:")
        assert dependencies["content:lean-typed-capability-chain"].startswith("sha256:")
        assert dependencies[
            "content:observed-capability-module:composed-program"
        ].startswith("sha256:")
        assert dependencies[
            f"module:{task.composition_successor_module}"
        ].startswith("sha256:")
        for node_id in ("tmkarp-primitive", "composed-program"):
            assert dependencies[
                f"content:observed-capability-term:{node_id}"
            ].startswith("sha256:")
            assert dependencies[
                f"content:observed-capability-exact-type:{node_id}"
            ].startswith("sha256:")
        assert all("Benchmark/" not in path for path in task.public_source_files)
        assert NPHardAuthoringTaskV2.from_dict(task.to_dict()) == task
        public_successor = next(
            node
            for node in plan.capability_dag
            if node.node_id == "public-forward-certified-successor"
        )
        composed_program = next(
            node for node in plan.capability_dag if node.node_id == "composed-program"
        )
        assert public_successor.capability == "forward_certified_successor"
        assert composed_program.depends_on == (
            "tmkarp-program",
            "public-forward-certified-successor",
        )


def test_v3_dependent_tmkarp_composition_ambiguity_and_endpoint_tamper_fail_closed(
    dependent_composition_plans,
) -> None:
    original = dependent_composition_plans[0]
    successor = next(
        capability
        for capability in original.observation.typed_capabilities
        if capability.capability_kind == "forward_certified_successor"
    )
    ambiguous = plan_np_hard_authoring_from_observation(
        root=ROOT,
        input_module=DEPENDENT_COMPOSITION_CASES[0][0],
        input_problem_declaration=DEPENDENT_COMPOSITION_CASES[0][1],
        observation=replace(
            original.observation,
            typed_capabilities=original.observation.typed_capabilities
            + (replace(successor, capability_id=successor.capability_id + ":alternate"),),
        ),
    )
    assert ambiguous.status == "BLOCKED"
    assert ambiguous.failure_code == "ambiguous_authoring_capability"

    with pytest.raises(NPHardAuthoringContractError) as collapsed:
        replace(
            original.task,
            composition_intermediate=original.task.target_problem,
        ).validate()
    assert collapsed.value.code == "candidate_wrong_endpoint"


def test_typed_capability_ambiguity_fails_closed_but_reverse_uses_open_synthesis(
    automatic_plans,
) -> None:
    original = automatic_plans[0]
    adapter = next(
        capability
        for capability in original.observation.typed_capabilities
        if capability.target_node == original.observation.input_node
    )
    stripped = replace(
        original.observation,
        poly_programs=(),
        mapping_relations=(),
        gaps=(),
    )
    ambiguous = plan_np_hard_authoring_from_observation(
        root=ROOT,
        input_module=CASES[0][0],
        input_problem_declaration=CASES[0][1],
        observation=replace(
            stripped,
            typed_capabilities=(
                adapter,
                replace(adapter, capability_id=adapter.capability_id + ":alternate"),
            ),
        ),
    )
    assert ambiguous.status == "BLOCKED"
    assert ambiguous.failure_code == "ambiguous_authoring_capability"

    reverse = replace(
        adapter,
        source=adapter.target,
        target=adapter.source,
        source_node=adapter.target_node,
        target_node=adapter.source_node,
    )
    reversed_plan = plan_np_hard_authoring_from_observation(
        root=ROOT,
        input_module=CASES[0][0],
        input_problem_declaration=CASES[0][1],
        observation=replace(stripped, typed_capabilities=(reverse,)),
    )
    assert reversed_plan.status == "PLANNED"
    assert reversed_plan.task.task_class == "whole_reduction_synthesis"


def test_hub_aliases_are_deduplicated_by_exact_endpoint_node(automatic_plans) -> None:
    original = automatic_plans[0]
    adapter = next(
        capability
        for capability in original.observation.typed_capabilities
        if capability.target_node == original.observation.input_node
    )
    source_problem = next(
        problem
        for problem in original.observation.problems
        if problem.declaration == adapter.source
    )
    alias = next(
        problem
        for problem in original.observation.problems
        if problem.endpoint_node == source_problem.endpoint_node
        and problem.declaration != source_problem.declaration
    )
    alias_adapter = replace(adapter, source=alias.declaration)
    plan = plan_np_hard_authoring_from_observation(
        root=ROOT,
        input_module=CASES[0][0],
        input_problem_declaration=CASES[0][1],
        observation=replace(
            original.observation,
            typed_capabilities=(alias_adapter,),
        ),
    )
    assert plan.status == "PLANNED"
    assert len(plan.ranked_hubs) == 1
    assert plan.selected_hub == alias.declaration


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


def test_planner_falls_back_to_whole_reduction_when_closed_routes_are_unavailable(
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
    assert reverse_plan.status == "PLANNED"
    assert reverse_plan.task.task_class == "whole_reduction_synthesis"

    synthesis = automatic_plans[4]
    missing_relation = plan_np_hard_authoring_from_observation(
        root=ROOT,
        input_module=CASES[4][0],
        input_problem_declaration=CASES[4][1],
        observation=replace(synthesis.observation, mapping_relations=()),
    )
    assert missing_relation.status == "PLANNED"
    assert missing_relation.task.task_class == "whole_reduction_synthesis"

    composition = automatic_plans[2]
    disconnected = plan_np_hard_authoring_from_observation(
        root=ROOT,
        input_module=CASES[2][0],
        input_problem_declaration=CASES[2][1],
        observation=replace(composition.observation, poly_programs=()),
    )
    assert disconnected.status == "PLANNED"
    assert disconnected.task.task_class == "whole_reduction_synthesis"
    assert all(
        plan.model_calls == 0
        for plan in (reverse_plan, missing_relation, disconnected)
    )


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
