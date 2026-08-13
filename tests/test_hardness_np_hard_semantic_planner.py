from __future__ import annotations

from dataclasses import replace
import json
from pathlib import Path

import pytest

from agent.hardness.np_hard_authoring import (
    NPHardAuthoringContractError,
    NPHardSemanticPlanV1,
)
from agent.hardness.np_hard_authoring_planner import NPHardAuthoringPlannerV2
from agent.hardness.np_hard_semantic_planner import (
    build_semantic_planner_prompt,
    check_semantic_plan_locally,
    semantic_plan_dependency_snapshot,
    split_semantic_plan_for_node,
    validate_semantic_plan,
)


ROOT = Path(__file__).resolve().parents[1]
MODULE = "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3"
SCAFFOLD = "ComplexityReduction.Agent.Hardness.BooleanCSPReductionScaffold"


def _declaration(task, node_id: str) -> str:
    matches = [node for node in task.gap_nodes if node.node_id == node_id]
    assert len(matches) == 1, node_id
    return matches[0].declaration


@pytest.fixture(scope="module")
def semantic_task(tmp_path_factory):
    plan = NPHardAuthoringPlannerV2(
        root=ROOT,
        input_module=MODULE,
        input_problem_declaration=MODULE + ".problem",
        output_dir=tmp_path_factory.mktemp("semantic-planner-task"),
    ).plan()
    assert plan.task is not None
    return plan.task


def _construction_bodies(task) -> dict[str, str]:
    nodes = {node.node_id: node for node in task.gap_nodes}
    candidate = task.candidate_module
    return {
        nodes["clause-constraint"].declaration: (
            "fun (clause : ComplexityReduction.NAEThreeSAT.Clause) =>\n"
            "  match clause with\n"
            "  | ⟨first, second, third⟩ =>\n"
            f"      {SCAFFOLD}.ternaryConstraint\n"
            f"        ({SCAFFOLD}.literalKey first)\n"
            f"        ({SCAFFOLD}.literalKey second)\n"
            f"        ({SCAFFOLD}.literalKey third)\n"
        ),
        nodes["complement-constraint"].declaration: (
            "fun literal =>\n"
            f"  ({SCAFFOLD}.ternaryConstraint\n"
            f"    ({SCAFFOLD}.literalKey literal)\n"
            f"    ({SCAFFOLD}.literalKey ({SCAFFOLD}.complementLiteral literal))\n"
            f"    ({SCAFFOLD}.literalKey literal) :\n"
            "      ComplexityReduction.CSP.Constraint "
            f"{MODULE}.gamma)\n"
        ),
        nodes["clause-gadget"].declaration: (
            "fun (clause : ComplexityReduction.NAEThreeSAT.Clause) =>\n"
            "  match clause with\n"
            "  | ⟨first, second, third⟩ =>\n"
            "      [clauseConstraint ⟨first, second, third⟩,\n"
            "       complementConstraint first,\n"
            "       complementConstraint second,\n"
            "       complementConstraint third]\n"
        ),
        nodes["reference-executable"].declaration: (
            f"{SCAFFOLD}.referenceExecutableFromClauseGadget "
            f"{candidate}.clauseGadget\n"
        ),
        nodes["reduction-executable"].declaration: (
            f"{SCAFFOLD}.executableFromReference "
            f"{candidate}.referenceExecutable\n"
        ),
    }


def _plan(task, bodies) -> NPHardSemanticPlanV1:
    fingerprint = semantic_plan_dependency_snapshot(
        task=task, accepted_bodies=bodies
    ).fingerprint
    candidate = task.candidate_module
    clause = (
        "{ first := ComplexityReduction.SAT.Literal.positive 0, "
        "second := ComplexityReduction.SAT.Literal.positive 1, "
        "third := ComplexityReduction.SAT.Literal.positive 2 }"
    )
    forward = [
        "ComplexityReduction.CSP.Formula.Satisfies "
        f"(List.flatMap {candidate}.clauseGadget "
        "([] : ComplexityReduction.NAEThreeSAT.Formula)) (fun _ => false)",
        "ComplexityReduction.CSP.Formula.Satisfies "
        f"({candidate}.clauseGadget ({clause})) (fun _ => false)",
        "ComplexityReduction.CSP.Constraint.Satisfies "
        f"({candidate}.clauseConstraint ({clause})) (fun _ => false)",
        "ComplexityReduction.CSP.Constraint.Satisfies "
        f"({candidate}.complementConstraint "
        "(ComplexityReduction.SAT.Literal.positive 0)) (fun _ => false)",
        "ComplexityReduction.CSP.Formula.Satisfiable "
        f"(List.flatMap {candidate}.clauseGadget "
        "([] : ComplexityReduction.NAEThreeSAT.Formula))",
    ]
    value = {
        "schema_version": "hardness_np_hard_semantic_plan_v1",
        "dependency_fingerprint": fingerprint,
        "formula_structure": {
            "reference_constructor": "List.flatMap",
            "block_declaration": candidate + ".clauseGadget",
            "introduction_lemma": (
                "ComplexityReduction.CSP.Formula.satisfies_flatMap_intro"
            ),
            "elimination_lemma": (
                "ComplexityReduction.CSP.Formula.satisfies_flatMap_elim"
            ),
        },
        "forward": {
            "target_assignment": SCAFFOLD + ".literalAssignment",
            "literal_value_lemma": SCAFFOLD + ".literalAssignment_literalKey",
            "main_constraint_lemma": SCAFFOLD + ".ternaryConstraint_satisfies_iff",
            "complement_constraint_lemma": (
                SCAFFOLD + ".ternaryConstraint_repeat_satisfies_iff"
            ),
            "block_proof_method": "formula_satisfaction_by_membership",
        },
        "reverse": {
            "source_assignment": SCAFFOLD + ".positiveKeyAssignment",
            "block_extraction_method": "formula_satisfaction_by_membership",
            "main_constraint_lemma": SCAFFOLD + ".ternaryConstraint_satisfies_iff",
            "complement_constraint_lemma": (
                SCAFFOLD + ".ternaryConstraint_repeat_satisfies_iff"
            ),
            "literal_recovery_lemma": (
                SCAFFOLD
                + ".literal_eval_positiveKeyAssignment_of_complement"
            ),
        },
        "language_conversion": {
            "method": "unfold_and_simpa",
            "definitions": [
                MODULE + ".gamma",
                "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common.singletonGamma",
                SCAFFOLD + ".gamma",
            ],
        },
        "ordered_obligations": forward + forward,
        "final_bridge": {
            "source_bridge_theorem": (
                SCAFFOLD + ".threeSATToNAEThreeSATIngress.executableCorrect"
            ),
            "reference_formula_builder": (
                SCAFFOLD + ".threeSATToNAEThreeSATIngress.executable"
            ),
            "application_form": "apply_bridge_at_input_then_project",
            "program_run_declaration": _declaration(task, "program-run-coherence"),
            "synthesized_executable_declaration": _declaration(
                task, "reduction-executable"
            ),
            "reference_executable_declaration": _declaration(
                task, "reference-executable"
            ),
            "reference_forward_declaration": _declaration(
                task, "reference-semantic-forward"
            ),
            "reference_reverse_declaration": _declaration(
                task, "reference-semantic-reverse"
            ),
            "semantic_forward_declaration": _declaration(task, "semantic-forward"),
            "semantic_reverse_declaration": _declaration(task, "semantic-reverse"),
        },
    }
    return NPHardSemanticPlanV1.from_dict(value)


def test_semantic_plan_schema_round_trip_and_stale_rejection(semantic_task) -> None:
    bodies = _construction_bodies(semantic_task)
    plan = _plan(semantic_task, bodies)
    assert NPHardSemanticPlanV1.from_dict(plan.to_dict()) == plan
    snapshot = semantic_plan_dependency_snapshot(
        task=semantic_task, accepted_bodies=bodies
    )
    validate_semantic_plan(plan=plan, task=semantic_task, snapshot=snapshot)
    stale = replace(plan, dependency_fingerprint="sha256:" + "0" * 64)
    with pytest.raises(NPHardAuthoringContractError, match="stale"):
        validate_semantic_plan(
            plan=stale, task=semantic_task, snapshot=snapshot
        )


def test_semantic_plan_rejects_direct_tm_declaration(semantic_task) -> None:
    bodies = _construction_bodies(semantic_task)
    plan = _plan(semantic_task, bodies)
    direct_tm = replace(
        plan.formula_structure,
        introduction_lemma="ComplexityReduction.TMPolyTimeMap.comp",
    )
    with pytest.raises(NPHardAuthoringContractError):
        validate_semantic_plan(
            plan=replace(plan, formula_structure=direct_tm),
            task=semantic_task,
            snapshot=semantic_plan_dependency_snapshot(
                task=semantic_task, accepted_bodies=bodies
            ),
        )


def test_semantic_planner_prompt_excludes_direct_tm_surface(semantic_task) -> None:
    prompt, _ = build_semantic_planner_prompt(
        root=ROOT,
        task=semantic_task,
        accepted_bodies=_construction_bodies(semantic_task),
    )
    for excluded in (
        "TMPolyTimeMap",
        "formulaCode",
        "constraintCode",
        "Primitive",
        "PolyProg",
    ):
        assert excluded not in prompt
    assert "clauseConstraint" in prompt
    assert "ComplexityReduction.NAEThreeSAT.Formula.Satisfiable formula" in prompt
    assert '"forward"' in prompt and '"reverse"' in prompt
    payload = json.loads(prompt)
    assert set(payload) == {"output_contract", "output_template", "planner_context"}
    assert payload["output_contract"]["return_only_output_template_object"] is True


def test_real_echoed_request_shape_is_rejected(semantic_task) -> None:
    bodies = _construction_bodies(semantic_task)
    prompt, snapshot = build_semantic_planner_prompt(
        root=ROOT, task=semantic_task, accepted_bodies=bodies
    )
    from agent.hardness.np_hard_semantic_planner import parse_semantic_plan

    with pytest.raises(NPHardAuthoringContractError):
        parse_semantic_plan(
            content=prompt, task=semantic_task, snapshot=snapshot
        )


def test_semantic_plan_directional_prompt_slices_do_not_leak(semantic_task) -> None:
    plan = _plan(semantic_task, _construction_bodies(semantic_task))
    forward = split_semantic_plan_for_node(
        plan, capability="reference_semantic_forward"
    )
    reverse = split_semantic_plan_for_node(
        plan, capability="reference_semantic_reverse"
    )
    assert "forward" in forward and "reverse" not in forward
    assert "reverse" in reverse and "forward" not in reverse
    assert len(forward["forward"]["ordered_obligations"]) == 5
    assert len(reverse["reverse"]["ordered_obligations"]) == 5


def test_reference_semantic_prompt_makes_membership_route_binding(
    semantic_task,
) -> None:
    from agent.hardness.np_hard_gap_runtime import (
        _CAPABILITY_GUIDANCE,
        _node_allowed_primitives,
    )

    nodes = {node.node_id: node for node in semantic_task.gap_nodes}
    forward = nodes["reference-semantic-forward"]
    reverse = nodes["reference-semantic-reverse"]
    forward_guidance = _CAPABILITY_GUIDANCE[forward.capability]
    reverse_guidance = _CAPABILITY_GUIDANCE[reverse.capability]
    assert "introduction_lemma" in forward_guidance
    assert "do not use CSP.Formula.satisfies_cons" in forward_guidance
    assert "elimination_lemma" in reverse_guidance
    assert "never `cases literal`" in reverse_guidance

    for node in (forward, reverse):
        primitives = _node_allowed_primitives(task=semantic_task, node=node)
        assert "ComplexityReduction.CSP.Formula.satisfies_cons" not in primitives
        assert "ComplexityReduction.CSP.Formula.satisfies_flatMap" not in primitives
        assert (
            "ComplexityReduction.CSP.Formula.satisfies_flatMap_intro"
            in primitives
        )
        assert (
            "ComplexityReduction.CSP.Formula.satisfies_flatMap_elim"
            in primitives
        )


def test_semantic_plan_patch_route_rejects_fixed_list_and_old_reverse_interface(
    semantic_task,
) -> None:
    from agent.hardness.np_hard_gap_runtime import (
        NPHardGapRuntimeError,
        NPHardNodePatchV1,
        _node_request,
        _validate_semantic_plan_patch_route,
    )
    from types import SimpleNamespace

    bodies = _construction_bodies(semantic_task)
    plan = _plan(semantic_task, bodies)
    accepted = tuple(
        SimpleNamespace(node_id=node.node_id, body_sha256="sha256:" + "1" * 64)
        for node in semantic_task.gap_nodes[:11]
    )
    forward_request = _node_request(
        task=semantic_task,
        node_ordinal=12,
        dependency_snapshot=semantic_task.dependency_hashes,
        accepted=accepted,
        total_model_calls=0,
        instance_call_budget=66,
    )
    fixed_list = NPHardNodePatchV1(
        request_id=forward_request.request_id,
        node_id=forward_request.node.node_id,
        declaration=forward_request.node.declaration,
        dependency_fingerprint=forward_request.dependency_fingerprint,
        replacement_body=(
            "by exact ComplexityReduction.CSP.Formula.satisfies_cons"
        ),
    )
    with pytest.raises(NPHardGapRuntimeError, match="fixed-list"):
        _validate_semantic_plan_patch_route(
            request=forward_request, patch=fixed_list, semantic_plan=plan
        )
    rewrite_problem = replace(
        fixed_list,
        replacement_body=(
            f"by rw [{semantic_task.target_problem.term}]\n"
            + "  exact ComplexityReduction.CSP.Formula.satisfies_flatMap_intro "
            + "(fun _ _ => by trivial)"
        ),
    )
    with pytest.raises(NPHardGapRuntimeError, match="do not rewrite"):
        _validate_semantic_plan_patch_route(
            request=forward_request, patch=rewrite_problem, semantic_plan=plan
        )

    reverse_request = _node_request(
        task=semantic_task,
        node_ordinal=13,
        dependency_snapshot=semantic_task.dependency_hashes,
        accepted=accepted
        + (
            SimpleNamespace(
                node_id="reference-semantic-forward",
                body_sha256="sha256:" + "2" * 64,
            ),
        ),
        total_model_calls=0,
        instance_call_budget=66,
    )
    old_reverse = NPHardNodePatchV1(
        request_id=reverse_request.request_id,
        node_id=reverse_request.node.node_id,
        declaration=reverse_request.node.declaration,
        dependency_fingerprint=reverse_request.dependency_fingerprint,
        replacement_body="by cases literal",
    )
    with pytest.raises(NPHardGapRuntimeError, match="cases literal"):
        _validate_semantic_plan_patch_route(
            request=reverse_request, patch=old_reverse, semantic_plan=plan
        )


def test_repeat_position_mismatch_fails_local_lean_check(
    semantic_task, tmp_path: Path
) -> None:
    bodies = _construction_bodies(semantic_task)
    plan = _plan(semantic_task, bodies)
    correct = check_semantic_plan_locally(
        root=ROOT,
        output_dir=tmp_path / "correct",
        task=semantic_task,
        accepted_bodies=bodies,
        plan=plan,
        timeout_seconds=60,
    )
    assert correct.ok, correct.diagnostic
    wrong_lemma = SCAFFOLD + ".ternaryConstraint_repeat_first_satisfies_iff"
    wrong = replace(
        plan,
        forward=replace(plan.forward, complement_constraint_lemma=wrong_lemma),
        reverse=replace(plan.reverse, complement_constraint_lemma=wrong_lemma),
    )
    failed = check_semantic_plan_locally(
        root=ROOT,
        output_dir=tmp_path / "wrong-repeat",
        task=semantic_task,
        accepted_bodies=bodies,
        plan=wrong,
        timeout_seconds=60,
    )
    assert not failed.ok
