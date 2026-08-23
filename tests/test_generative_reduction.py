from __future__ import annotations

from dataclasses import asdict, replace
from pathlib import Path
import json
from types import SimpleNamespace
from typing import Mapping

import pytest

from agent.generative_reduction import boolean_csp_regression
from agent.generative_reduction import construction_basis as construction_basis_module
from agent.generative_reduction import lean_bridge as lean_bridge_module
from agent.generative_reduction.baseline import verify_stable_entrypoints
from agent.generative_reduction.budgets import (
    BudgetExhausted,
    BudgetTracker,
    SearchBudget,
)
from agent.generative_reduction.capability_planner import CapabilityPlanner
from agent.generative_reduction.capability_compilers import (
    compile_direct_tm_candidate,
    compile_semantic_candidate,
)
from agent.generative_reduction.context_capsule import build_context_capsule
from agent.generative_reduction.construction_basis import (
    ConstructionBasisEntry,
    ConstructionBasisReceipt,
    MARKER as CONSTRUCTION_BASIS_MARKER,
    SCHEMA as CONSTRUCTION_BASIS_SCHEMA,
    build_named_probe_source,
    build_probe_source as build_construction_basis_probe_source,
    parse_named_probe_output,
    parse_probe_output as parse_construction_basis_output,
)
from agent.generative_reduction.exact_closure_probe import ClosureCheck
from agent.generative_reduction.finite_synthesis import (
    FiniteCandidateWitness,
    FiniteCapabilityStage,
    parse_finite_counterexample_output,
)
from agent.generative_reduction.goal_kind_adapters import classify_goal
from agent.generative_reduction.models import (
    ActionDisposition,
    ApplicationFrame,
    AuthorshipEvidence,
    BinderSlot,
    CandidateReceipt,
    CandidateRole,
    CandidateAction,
    CapabilityKind,
    CapabilityPlan,
    ContributionClass,
    ContributionReceipt,
    ConstructionContract,
    DirectTMCapabilityPlan,
    ExactClosureResult,
    FrameStatus,
    GeneralNPHardRequest,
    GeneratedCapability,
    GoalKind,
    GeneratorBrief,
    GeneratorResult,
    GeneratorStatus,
    OpenGoal,
    PremiseKind,
    PremiseSlot,
    PlannerEffectReceipt,
    ProofGuidance,
    ProofStep,
    ProviderKind,
    ReusableFragment,
    ResidualObligation,
    RootGoal,
    SlotStatus,
    Strategy,
    StrategyDecision,
    SubstepPlan,
    SemanticCapabilityPlan,
    SemanticDirectionPlan,
    TheoremIndexEntry,
    TheoremApplicationPlan,
    TheoremPremise,
    TypedProgramNode,
)
from agent.generative_reduction.premise_registry import PremiseSolverRegistry
from agent.generative_reduction.plugins.registry import load_plugin
from agent.generative_reduction.proof_frontier import ReadyActionBuckets
from agent.generative_reduction.proof_state import ProofState
from agent.generative_reduction.providers.theorem import TheoremActionProvider
from agent.generative_reduction.providers.structural import StructuralActionProvider
from agent.generative_reduction.providers.synthesis import SynthesisActionProvider
from agent.generative_reduction.model.authoring import (
    implementation_sha256,
    propose_initial_implementation,
    propose_repair,
    render_fixed_declaration,
)
from agent.generative_reduction.model.strategy import propose_strategy
from agent.generative_reduction.orchestrator import GenerativeReductionOrchestrator
from agent.generative_reduction.synthesis.designs import SynthesisDesign
from agent.generative_reduction.synthesis.repair import classify_lean_diagnostic
from agent.hardness.model_client import ModelResponse
from agent.generative_reduction.reconstruction import (
    build_authored_capability_source,
    build_authored_artifact_source,
    build_frame_check_source,
    build_search_artifact_source,
)
from agent.generative_reduction.recursive_runtime import RecursiveSearchRuntime
from agent.generative_reduction.generator_protocol import (
    build_capability_plan,
    generator_result_from_proposal,
    out_of_brief_project_identifiers,
)
from agent.generative_reduction.model.protocol import AuthoringProposal
from agent.generative_reduction.boolean_csp_capability_gate import (
    evaluate_capability_gate,
)
from agent.generative_reduction.capability_gate_policy import CapabilityGatePolicy
from agent.generative_reduction.search import SearchCoordinator
from agent.generative_reduction.lean_bridge import (
    RuleInstantiationReceipt,
    RuleSlotReceipt,
    build_rule_instantiation_probe_source,
    build_type_defeq_probe_source,
    parse_rule_instantiation_output,
    run_lean_file,
)
from agent.generative_reduction.theorem_index import (
    build_probe_source,
    build_typed_goal_probe_source,
    is_runtime_candidate_declaration,
    parse_probe_output,
)


ROOT = Path(__file__).resolve().parents[1]


def _goal() -> OpenGoal:
    return OpenGoal.create(
        goal_id="goal-root",
        exact_type="ComplexityReduction.Certificate.NativeTMNPHard Example.problem",
        import_closure_fingerprint="env",
        kind=GoalKind.HARDNESS,
    )


def _entry(*, premise: str | None = None) -> TheoremIndexEntry:
    premises = (
        ()
        if premise is None
        else (
            TheoremPremise.create(
                ordinal=0, exact_type=premise, kind=PremiseKind.PROPOSITION
            ),
        )
    )
    return TheoremIndexEntry(
        declaration="Example.Rules.hard",
        module="Example.Rules",
        declaration_type="P → NativeTMNPHard Example.problem",
        conclusion_type="NativeTMNPHard Example.problem",
        conclusion_head="ComplexityReduction.Certificate.NativeTMNPHard",
        result_fingerprint="42",
        universe_parameters=("u",),
        premises=premises,
    )


def _contract_for(goal: OpenGoal, *, modes=("typed-witness", "direct-authoring")):
    return ConstructionContract(
        contract_id="contract-test",
        goal_key=goal.key,
        exact_expected_lean_type=goal.exact_type,
        frozen_source_handle=None,
        frozen_target_handle="Example.target",
        available_inputs=goal.local_context,
        reusable_declarations=("Example.Pair.mk",),
        already_closed_fragments=(),
        residual_obligations=(),
        semantic_requirements=(),
        complexity_requirements=(),
        composition_requirements=("preserve endpoints",),
        allowed_construction_modes=tuple(modes),
        forbidden_declarations=("Example.forbidden",),
        forbidden_edits=("input module",),
        validation_commands=(("lake", "env", "lean", "<generated-file>"),),
    )


def test_structural_provider_promotes_lean_typed_generic_constructor() -> None:
    goal = OpenGoal.create(
        goal_id="goal-pair",
        exact_type="Example.Pair",
        kind=GoalKind.DATA,
    )
    residual = ResidualObligation(
        obligation_id="field-left",
        exact_type="Example.Left",
        kind=GoalKind.DATA,
    )
    guidance = ProofGuidance(
        guidance_id="guidance-pair-mk",
        goal_key=goal.key,
        candidate_declaration="Example.Pair.mk",
        declaration_provenance="Example.Pair",
        instantiated_universe_arguments=(),
        application_skeleton="by apply_generative_rule Example.Pair.mk",
        generated_premises=(),
        already_closed_premises=(),
        reusable_fragments=(),
        residual_obligations=(residual,),
        suggested_proof_mode="recursive-premise-search",
        coverage_score=0.0,
        estimated_cost=1.0,
        confidence=0.8,
    )
    contract = _contract_for(goal)
    actions = StructuralActionProvider().actions(
        goal, (guidance,), contract, limit=4
    )
    assert len(actions) == 1
    action = actions[0]
    assert action.provider == ProviderKind.STRUCTURAL
    assert action.declaration == "Example.Pair.mk"
    assert action.metadata["structural_kind"] == "structure-constructor"
    assert action.metadata["field_exact_types"] == ("Example.Left",)
    assert action.metadata["design_id"] == SynthesisDesign.for_contract(
        contract, mode="typed-witness"
    ).design_id


def test_context_capsule_contains_exact_signatures_and_redacts_secrets() -> None:
    goal = OpenGoal.create(
        goal_id="goal-capsule",
        exact_type="Example.Pair",
        local_context=("token = sk-secretvalue123456",),
        kind=GoalKind.DATA,
    )
    entry = replace(
        _entry(),
        declaration="Example.Pair.mk",
        module="Example.Pair",
        declaration_type="Example.Left → Example.Right → Example.Pair",
        conclusion_type="Example.Pair",
        conclusion_head="Example.Pair",
    )
    capsule = build_context_capsule(
        goal=goal,
        candidates=(entry,),
        guidance=(),
        generated_capabilities=(),
        imports=("Example.Pair",),
        environment_fingerprint="env",
        diagnostics="unknown identifier 'Example.Pair.old' Authorization: Bearer secret",
    )
    assert capsule.constructors[0].declaration == "Example.Pair.mk"
    assert capsule.candidate_signatures[0].exact_type.endswith("Example.Pair")
    serialized = json.dumps(capsule.to_dict())
    assert "sk-secretvalue123456" not in serialized
    assert "Bearer secret" not in serialized
    assert capsule.capsule_id.startswith("capsule-")


def test_construction_basis_populates_generation_context_without_exact_candidates() -> None:
    goal = OpenGoal.create(
        goal_id="goal-direct-tm-context",
        exact_type="Example.TMPolyTimeMap Example.source Example.target Example.interpret",
        kind=GoalKind.COMPLEXITY,
    )
    entry = ConstructionBasisEntry(
        declaration="Example.TMPolyTimeMap.comp",
        module="Example.TM",
        declaration_kind="theorem",
        role="lemma",
        dependency_distance=1,
        overlap_count=2,
        exact_type="Example.TMPolyTimeMap A B f → Example.TMPolyTimeMap B C g → Example.TMPolyTimeMap A C (g ∘ f)",
    )
    basis = ConstructionBasisReceipt(
        goal_head="Example.TMPolyTimeMap",
        goal_head_module="Example.TM",
        goal_head_kind="definition",
        goal_head_type="Example.EncodedType → Example.EncodedType → Type",
        goal_head_definition="fun source target => Example.MachineMap source target",
        entries=(entry,),
        receipt_hash="sha256:basis",
    )
    capsule = build_context_capsule(
        goal=goal,
        candidates=(),
        guidance=(),
        generated_capabilities=(),
        imports=("Example.TM",),
        environment_fingerprint="env",
        construction_basis=basis,
    )
    assert capsule.generation_context_ready
    assert capsule.goal_head_type == basis.goal_head_type
    assert capsule.goal_head_definition == basis.goal_head_definition
    assert capsule.relevant_lemmas[0].declaration == entry.declaration
    assert entry.declaration in capsule.allowed_identifier_manifest


def test_construction_basis_parser_preserves_definitions_and_distances() -> None:
    nonce = "basis-test"
    output = "\n".join(
        (
            f"{CONSTRUCTION_BASIS_MARKER}\t{CONSTRUCTION_BASIS_SCHEMA}\t{nonce}\thead\t"
            "Example.Target\tExample.Core\tdefinition\tType\tfun x => x",
            f"{CONSTRUCTION_BASIS_MARKER}\t{CONSTRUCTION_BASIS_SCHEMA}\t{nonce}\tentry\t"
            "Example.Target.mk\tExample.Core\tconstructor\tconstructor\t1\t2\t"
            "Example.Input → Example.Target\t",
        )
    )
    receipt = parse_construction_basis_output(stdout=output, stderr="", nonce=nonce)
    assert receipt.goal_head == "Example.Target"
    assert receipt.goal_head_definition == "fun x => x"
    assert receipt.entries[0].dependency_distance == 1
    assert receipt.entries[0].overlap_count == 2


def test_construction_basis_probe_materializes_job_local_capabilities() -> None:
    capability = GeneratedCapability(
        capability_id="stable-binding-test",
        exact_type="Example.Value",
        declaration="Example.Generated.stable",
        namespace="Example.Generated",
        implementation="noncomputable def stable : Example.Value := Example.value",
        source_hash="sha256:stable",
        action_id="action-stable",
    )
    source = build_construction_basis_probe_source(
        modules=("Example.Input",),
        exact_goal="Example.Predicate\n  Example.Generated.stable",
        nonce="basis-generated",
        generated_capabilities=(capability,),
    )
    assert "namespace Example.Generated" in source
    assert source.index("noncomputable def stable") < source.index(
        "#generative_reduction_probe_construction_basis"
    )
    assert "Example.Predicate Example.Generated.stable" in source


def test_named_construction_lookup_returns_exact_lean_signature(
    tmp_path: Path,
) -> None:
    nonce = "named-basis-test"
    source = build_named_probe_source(
        modules=("ComplexityReduction.Program.List",),
        declarations=("ComplexityReduction.TMPolyTimeMap.list_singleton_of",),
        nonce=nonce,
    )
    path = tmp_path / "NamedConstructionBasis.lean"
    path.write_text(source, encoding="utf-8")
    command = run_lean_file(root=ROOT, path=path, timeout_seconds=120)
    assert command.ok, command.stderr or command.stdout
    entries = parse_named_probe_output(
        stdout=command.stdout, stderr=command.stderr, nonce=nonce
    )
    assert len(entries) == 1
    assert entries[0].declaration.endswith("TMPolyTimeMap.list_singleton_of")
    assert "TMPolyTimeMap" in entries[0].exact_type


def test_capability_plan_brief_and_generator_result_are_fingerprint_bound() -> None:
    entry = _entry()
    receipt = CandidateReceipt.create(
        entry=entry,
        role=CandidateRole.EXACT_CLOSURE,
        exact_closure=True,
        application_skeleton="by exact Example.Rules.hard",
    )
    plan = CapabilityPlan.create(
        capability_kind=CapabilityKind.GENERIC_HELPER,
        goal_id="goal-helper",
        exact_goal="Example.Target",
        selected_route="theorem-guided-helper",
        selected_candidate_ids=(receipt.candidate_id,),
        construction_basis_ids=("basis-1",),
        proof_outline=("apply selected theorem",),
    )
    brief = GeneratorBrief.create(
        plan=plan,
        exact_declaration_name="capability_test",
        exact_declaration_type="Example.Target",
        fixed_declaration_envelope={"header": "noncomputable def capability_test"},
        selected_design={"design_id": "design-test"},
        selected_candidate_ids=(receipt.candidate_id,),
        allowed_identifier_manifest=(entry.declaration,),
    )
    result = GeneratorResult.create(
        brief=brief,
        status=GeneratorStatus.PROPOSED,
        implementation_body=f"exact {entry.declaration}",
        used_candidate_ids=(receipt.candidate_id,),
    )
    assert brief.plan_fingerprint == plan.plan_fingerprint
    assert result.brief_id == brief.brief_id
    assert result.implementation_hash and result.implementation_hash.startswith("sha256:")
    with pytest.raises(ValueError, match="absent from its brief"):
        GeneratorResult.create(
            brief=brief,
            status=GeneratorStatus.PROPOSED,
            implementation_body="exact Example.other",
            used_candidate_ids=("unknown-candidate",),
        )


def test_boolean_csp_regression_can_serialize_typed_receipts() -> None:
    plan = CapabilityPlan.create(
        capability_kind=CapabilityKind.DIRECT_TM,
        goal_id="goal-regression-report",
        exact_goal="ComplexityReduction.TMPolyTimeMap X Y f",
        selected_route="typed-program-dag",
    )
    serialized = boolean_csp_regression.asdict(plan)
    assert serialized["plan_id"] == plan.plan_id
    assert serialized["capability_kind"] == CapabilityKind.DIRECT_TM


def test_planner_generator_protocol_records_round_trip_without_losing_enums() -> None:
    plan = CapabilityPlan.create(
        capability_kind=CapabilityKind.DIRECT_TM,
        goal_id="goal-round-trip",
        exact_goal="ComplexityReduction.TMPolyTimeMap X Y f",
        selected_route="typed-program-dag",
        construction_basis_ids=("primitive-1",),
        proof_outline=("compose", "transport endpoint"),
    )
    brief = GeneratorBrief.create(
        plan=plan,
        exact_declaration_name="generatedDirectTM",
        exact_declaration_type=plan.exact_goal,
        fixed_declaration_envelope={"header": "noncomputable def generatedDirectTM"},
        selected_design={"design_id": "design-round-trip"},
        allowed_identifier_manifest=("ComplexityReduction.TMPolyTimeMap.comp",),
    )
    result = GeneratorResult.create(
        brief=brief,
        status=GeneratorStatus.PROPOSED,
        implementation_body="exact ComplexityReduction.TMPolyTimeMap.id X",
    )
    authorship = AuthorshipEvidence(
        semantic_payload_schema="example_payload_v1",
        semantic_payload_sha256="sha256:semantic",
        model_response_sha256="sha256:model",
        origin="model",
        renderer_name="example-renderer",
        renderer_version="example-renderer-v1",
        renderer_added_semantic_atom_count=0,
        validation_only_steps=("schema", "lean"),
        variable_count=4,
        constraint_count=2,
        output_mapping=(0, 2),
        relation_symbols_used=("target-0",),
        repair_payload_hashes=("sha256:repair",),
    )
    contribution = ContributionReceipt(
        capability_declaration="Generated.generatedDirectTM",
        contribution_class=ContributionClass.DETERMINISTIC_GENERATED_CAPABILITY,
        capability_kind=CapabilityKind.DIRECT_TM,
        plan_id=plan.plan_id,
        brief_id=brief.brief_id,
        generator_result_id=result.result_id,
        authorship_evidence=authorship,
    )
    effect = PlannerEffectReceipt(
        plan_id=plan.plan_id,
        selected_action_id="plugin-direct",
        selected_candidate_ids=(),
        selected_design_id="design-round-trip",
        generated_brief_id=brief.brief_id,
        applied_effect="issued-independent-generator-brief",
    )
    theorem_plan = TheoremApplicationPlan.create(
        candidate_id="candidate-1",
        exact_instantiation="Example.rule",
        application_skeleton="by exact Example.rule",
        solved_premises=(),
        residual_obligations=(),
        expected_result_type="Example.Target",
        contribution_class=ContributionClass.THEOREM_REUSE,
    )
    assert CapabilityPlan.from_dict(asdict(plan)) == plan
    assert GeneratorBrief.from_dict(asdict(brief)) == brief
    assert GeneratorResult.from_dict(asdict(result)) == result
    assert AuthorshipEvidence.from_dict(asdict(authorship)) == authorship
    assert ContributionReceipt.from_dict(asdict(contribution)) == contribution
    assert PlannerEffectReceipt.from_dict(asdict(effect)) == effect
    assert TheoremApplicationPlan.from_dict(asdict(theorem_plan)) == theorem_plan


def test_generator_rejects_project_identifier_outside_frozen_brief() -> None:
    goal = OpenGoal.create(
        goal_id="goal-manifest",
        exact_type="ComplexityReduction.Example.Target",
        kind=GoalKind.PROPOSITION,
    )
    plan = CapabilityPlan.create(
        capability_kind=CapabilityKind.GENERIC_HELPER,
        goal_id=goal.goal_id,
        exact_goal=goal.exact_type,
        selected_route="brief-bound-generation",
    )
    brief = GeneratorBrief.create(
        plan=plan,
        exact_declaration_name="generatedHelper",
        exact_declaration_type=goal.exact_type,
        fixed_declaration_envelope={"header": "noncomputable def generatedHelper"},
        selected_design={"design_id": "design-manifest"},
        allowed_identifier_manifest=("ComplexityReduction.Example.allowed",),
    )
    implementation = "exact ComplexityReduction.Hidden.forbidden"
    assert out_of_brief_project_identifiers(
        brief=brief, implementation=implementation
    ) == ("ComplexityReduction.Hidden.forbidden",)
    proposal = AuthoringProposal(
        implementation=(
            "noncomputable def generatedHelper : ComplexityReduction.Example.Target := by\n"
            f"  {implementation}"
        ),
        implementation_body=implementation,
        reason="attempt an ungrounded declaration",
        raw={},
    )
    substep = SubstepPlan(
        goal_key=goal.key,
        exact_closure_result=ExactClosureResult(goal_key=goal.key, closed=False),
        ranked_proof_guidance=(),
        reusable_fragments=(),
        residual_obligations=(),
        construction_contract=None,
        candidate_actions=(),
        recommended_action_id=None,
        cache_key="manifest-cache",
        plan_fingerprint="manifest-plan",
    )
    result = generator_result_from_proposal(
        brief=brief,
        proposal=proposal,
        substep_plan=substep,
        generated_capabilities=(),
    )
    assert result.status == GeneratorStatus.NEEDS_LOOKUP
    assert result.requested_lookup == ("ComplexityReduction.Hidden.forbidden",)


def test_replan_feedback_changes_plan_id_and_releases_only_requested_action() -> None:
    goal = OpenGoal.create(
        goal_id="goal-replan",
        exact_type="Example.Target",
        kind=GoalKind.PROPOSITION,
    )
    state = replace(_root_state(), open_goals=(goal,))
    action = CandidateAction(
        action_id="synthesis-replan",
        provider=ProviderKind.SYNTHESIS,
        disposition=ActionDisposition.SYNTHESIS_REQUIRED,
        goal_key=goal.key,
        estimated_cost=5.0,
    )
    substep = SubstepPlan(
        goal_key=goal.key,
        exact_closure_result=ExactClosureResult(goal_key=goal.key, closed=False),
        ranked_proof_guidance=(),
        reusable_fragments=(),
        residual_obligations=(),
        construction_contract=None,
        candidate_actions=(action,),
        recommended_action_id=action.action_id,
        cache_key="replan-cache",
        plan_fingerprint="replan-substep",
    )
    capsule = build_context_capsule(
        goal=goal,
        candidates=(_entry(),),
        guidance=(),
        generated_capabilities=(),
        imports=("Example.Input",),
        environment_fingerprint="env",
    )
    first = build_capability_plan(
        goal=goal,
        substep_plan=substep,
        action=action,
        design={"design_id": "design-replan"},
        capsule=capsule,
        forbidden_declarations=(),
        prior_diagnostics=None,
    )
    second = build_capability_plan(
        goal=goal,
        substep_plan=substep,
        action=action,
        design={"design_id": "design-replan"},
        capsule=capsule,
        forbidden_declarations=(),
        prior_diagnostics="program DAG is missing a flatten node",
    )
    assert first.plan_id != second.plan_id
    attempted = state.mark_action_attempted(goal.goal_id, action.action_id)
    replanned = attempted.release_action_for_replan(
        goal_id=goal.goal_id,
        action_id=action.action_id,
        diagnostic="switch to map-plus-flatten DAG",
    )
    assert action.action_id not in replanned.goal(goal.goal_id).attempted_actions
    assert replanned.failure_memory[-1]["blocker_code"] == "generator_requested_replan"


def test_fixed_declaration_envelope_is_owned_by_runtime() -> None:
    rendered = render_fixed_declaration(
        declaration="capability_test",
        exact_type="Example.Target",
        proof_body="exact Example.value",
        helper_declarations=("def helper : Nat := 1",),
    )
    assert rendered.count("noncomputable def capability_test") == 1
    assert rendered.endswith("  exact Example.value")

    goal = OpenGoal.create(
        goal_id="goal-fixed-envelope",
        exact_type="Example.Target",
        kind=GoalKind.DATA,
    )
    contract = _contract_for(goal, modes=("direct-authoring",))
    capsule = build_context_capsule(
        goal=goal,
        candidates=(_entry(),),
        guidance=(),
        generated_capabilities=(),
        imports=("Example.Input",),
        environment_fingerprint="env",
    )

    class EnvelopeModel:
        def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
            assert "runtime owns" in system
            payload = json.loads(prompt)
            assert payload["fixed_declaration_envelope"]["model_may_edit_header"] is False
            return ModelResponse(
                called=True,
                ok=True,
                content=json.dumps(
                    {
                        "helper_declarations": [],
                        "proof_body": "exact Example.value",
                        "reason": "use the selected value",
                    }
                ),
                error=None,
                status_code=200,
                duration_seconds=0.01,
                usage={},
                attempts=1,
            )

    proposal, record = propose_initial_implementation(
        model=EnvelopeModel(),
        contract=contract,
        guidance=(),
        context_capsule=capsule,
        required_declaration="capability_test",
    )
    assert record.ok and proposal is not None
    assert proposal.implementation_body == "exact Example.value"
    assert proposal.implementation == (
        "noncomputable def capability_test : Example.Target := by\n"
        "  exact Example.value"
    )


def test_independent_generator_receives_only_frozen_brief_context() -> None:
    goal = OpenGoal.create(
        goal_id="goal-independent-context",
        exact_type="Example.Target",
        kind=GoalKind.DATA,
    )
    contract = _contract_for(goal, modes=("direct-authoring",))
    selected = _entry()
    hidden = replace(
        selected,
        declaration="Example.Hidden.unselected",
        declaration_type="Example.Target",
        conclusion_type="Example.Target",
    )
    capsule = build_context_capsule(
        goal=goal,
        candidates=(selected, hidden),
        guidance=(),
        generated_capabilities=(),
        imports=("Example.Input",),
        environment_fingerprint="env",
    )
    capability_plan = CapabilityPlan.create(
        capability_kind=CapabilityKind.GENERIC_HELPER,
        goal_id=goal.goal_id,
        exact_goal=goal.exact_type,
        selected_route="brief-bound-generation",
    )
    brief = GeneratorBrief.create(
        plan=capability_plan,
        exact_declaration_name="capability_test",
        exact_declaration_type=goal.exact_type,
        fixed_declaration_envelope={"header": "noncomputable def capability_test"},
        selected_design={"design_id": "design-independent"},
        allowed_identifier_manifest=(selected.declaration,),
        relevant_definitions=(
            {
                "declaration": selected.declaration,
                "exact_type": selected.declaration_type,
            },
        ),
    )

    class BriefOnlyModel:
        def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
            del system
            payload = json.loads(prompt)
            assert "context_capsule" not in payload
            assert "guidance" not in payload
            assert "reusable_declarations" not in payload
            assert hidden.declaration not in prompt
            assert payload["generator_context"]["relevant_definitions"][0][
                "declaration"
            ] == selected.declaration
            return ModelResponse(
                called=True,
                ok=True,
                content=json.dumps(
                    {
                        "helper_declarations": [],
                        "proof_body": f"exact {selected.declaration}",
                        "reason": "use the sole brief-selected declaration",
                    }
                ),
                error=None,
                status_code=200,
                duration_seconds=0.01,
                usage={},
                attempts=1,
            )

    proposal, record = propose_initial_implementation(
        model=BriefOnlyModel(),
        contract=contract,
        guidance=(),
        context_capsule=capsule,
        required_declaration="capability_test",
        generator_brief=brief,
    )
    assert record.ok and proposal is not None


def test_nonexecutable_synthesis_designs_are_prefiltered() -> None:
    goal = OpenGoal.create(
        goal_id="goal-prefilter",
        exact_type="Example.Target",
        kind=GoalKind.DATA,
    )
    contract = _contract_for(
        goal,
        modes=(
            "typed-witness",
            "intermediate-first",
            "apply-existing-theorem",
            "direct-authoring",
        ),
    )
    actions = SynthesisActionProvider().actions(contract, limit=8)
    assert [action.metadata["design_kind"] for action in actions] == [
        "direct-authoring"
    ]


def test_capability_scoped_budget_reserves_a_complete_attempt_without_consuming_it() -> None:
    tracker = BudgetTracker(
        replace(
            SearchBudget(),
            max_lean_checks=2,
            max_generated_files=2,
        )
    )
    receipt = tracker.reserve_capacity(
        scope_id="scope-capability-design-repair",
        hierarchy=(
            "case:Example.Input",
            "route:plugin",
            "capability:plan-1",
            "design:design-1",
            "repair:round-1",
        ),
        requirements={"lean_checks": 2, "generated_files": 2},
    )
    assert receipt["status"] == "reserved-for-immediate-sequential-execution"
    assert tracker.usage.lean_checks == 0
    assert tracker.to_dict()["capacity_reservations"]

    tracker.consume("lean_checks", 1)
    with pytest.raises(BudgetExhausted, match="lean_checks"):
        tracker.reserve_capacity(
            scope_id="scope-second-design",
            hierarchy=("case:x", "route:y", "capability:z", "design:q", "repair:r"),
            requirements={"lean_checks": 2},
        )


def test_repair_protocol_requires_current_base_and_previous_implementation() -> None:
    goal = OpenGoal.create(
        goal_id="goal-repair",
        exact_type="Example.Target",
        kind=GoalKind.DATA,
    )
    contract = _contract_for(goal, modes=("direct-authoring",))
    capsule = build_context_capsule(
        goal=goal,
        candidates=(),
        guidance=(),
        generated_capabilities=(),
        imports=("Example.Input",),
        environment_fingerprint="env",
    )
    previous = "noncomputable def capability_test : Example.Target := by\n  exact Example.old"
    base = implementation_sha256(previous)

    class RepairModel:
        def __init__(self, returned_base: str):
            self.returned_base = returned_base
            self.prompt = ""

        def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
            del system
            self.prompt = prompt
            return ModelResponse(
                called=True,
                ok=True,
                content=json.dumps(
                    {
                        "base_sha256": self.returned_base,
                        "implementation": previous.replace("Example.old", "Example.new"),
                        "changed_reason": "replace the unknown declaration",
                        "addressed_diagnostic_codes": ["unknown_identifier"],
                    }
                ),
                error=None,
                status_code=200,
                duration_seconds=0.01,
                usage={},
                attempts=1,
            )

    stale_model = RepairModel("sha256:stale")
    stale, stale_record = propose_repair(
        model=stale_model,
        contract=contract,
        guidance=(),
        context_capsule=capsule,
        required_declaration="capability_test",
        design={"design_id": "design-test", "design_kind": "direct-authoring"},
        previous_implementation=previous,
        base_sha256=base,
        diagnostic_classification="unknown_identifier",
        normalized_diagnostics="unknown identifier Example.old",
        source_window="1: exact Example.old",
    )
    assert stale is None
    assert "mismatched base_sha256" in (stale_record.error or "")
    assert json.loads(stale_model.prompt)["previous_implementation"] == previous

    valid_model = RepairModel(base)
    repaired, repaired_record = propose_repair(
        model=valid_model,
        contract=contract,
        guidance=(),
        context_capsule=capsule,
        required_declaration="capability_test",
        design={"design_id": "design-test", "design_kind": "direct-authoring"},
        previous_implementation=previous,
        base_sha256=base,
        diagnostic_classification="unknown_identifier",
        normalized_diagnostics="unknown identifier Example.old",
        source_window="1: exact Example.old",
    )
    assert repaired_record.ok
    assert repaired is not None and repaired.base_sha256 == base
    assert repaired.addressed_diagnostic_codes == ("unknown_identifier",)

    with pytest.raises(ValueError, match="base hash"):
        propose_repair(
            model=valid_model,
            contract=contract,
            guidance=(),
            context_capsule=capsule,
            required_declaration="capability_test",
            design={"design_id": "design-test"},
            previous_implementation=previous,
            base_sha256="sha256:not-current",
            diagnostic_classification="unknown_identifier",
            normalized_diagnostics="unknown identifier Example.old",
            source_window="1: exact Example.old",
        )


def test_synthesis_modes_map_to_distinct_executable_design_kinds() -> None:
    goal = OpenGoal.create(
        goal_id="goal-design",
        exact_type="Example.Target",
        kind=GoalKind.DATA,
    )
    contract = _contract_for(goal)
    constructor = SynthesisDesign.for_contract(
        contract, mode="typed-witness", parent_goal_id=goal.goal_id
    )
    helper = SynthesisDesign.for_contract(
        contract, mode="intermediate-first", parent_goal_id=goal.goal_id
    )
    direct = SynthesisDesign.for_contract(
        contract, mode="direct-authoring", parent_goal_id=goal.goal_id
    )
    assert (constructor.design_kind, helper.design_kind, direct.design_kind) == (
        "constructor-first",
        "helper-first",
        "direct-authoring",
    )
    assert len({constructor.design_id, helper.design_id, direct.design_id}) == 3
    assert direct.transition("context-ready").stage == "context-ready"


@pytest.mark.parametrize(
    ("message", "code"),
    (
        ("error: unknown identifier 'Example.missing'", "unknown_identifier"),
        ("error: failed to synthesize Example.Instance", "typeclass_synthesis_failed"),
        ("error: type mismatch", "type_mismatch"),
        ("error: unsolved goals", "unsolved_goals"),
    ),
)
def test_lean_diagnostics_have_stable_repair_classes(message: str, code: str) -> None:
    diagnostic = classify_lean_diagnostic(message)
    assert diagnostic.code == code
    assert diagnostic.fingerprint.startswith("sha256:")


def test_stable_boolean_csp_entrypoints_remain_byte_identical() -> None:
    actual = verify_stable_entrypoints(ROOT)
    assert set(actual) == {
        "scripts/prove_np_hard.py",
        "agent/hardness/boolean_csp_np_hard_benchmark.py",
    }


def test_request_schema_round_trip_and_goal_key_are_stable() -> None:
    request = GeneralNPHardRequest(
        input_module="Example.Input",
        problem_declaration="Example.Input.problem",
        strategy=Strategy.BALANCED,
        plugins=("graph",),
        forbidden_declarations=("Example.Rules.forbidden",),
    )
    assert GeneralNPHardRequest.from_dict(request.canonical_dict()) == request
    assert _goal().key == _goal().key
    assert request.fingerprint.startswith("sha256:")


def test_authored_source_rejects_forbidden_declaration_reference() -> None:
    implementation = """theorem problemIsNPHard :
    ComplexityReduction.Certificate.NativeTMNPHard Example.Input.problem := by
  exact Example.Rules.forbidden
"""
    with pytest.raises(ValueError, match="referenced forbidden declaration"):
        build_authored_artifact_source(
            input_module="Example.Input",
            problem_declaration="Example.Input.problem",
            implementation=implementation,
            forbidden_declarations=("Example.Rules.forbidden",),
        )


def test_lean_data_slot_overrides_arrow_shaped_goal_heuristic() -> None:
    exact_type = "(symbol : Example.Core.Symbol) → Example.Gadget symbol"
    assert classify_goal(exact_type, premise_kind="data") == GoalKind.DATA


def test_authored_child_capability_uses_data_safe_definition() -> None:
    exact_type = "(symbol : Example.Core.Symbol) → Example.Gadget symbol"
    implementation = f"""noncomputable def capability_test : {exact_type} := by
  exact Example.gadget
"""
    source, declaration = build_authored_capability_source(
        input_module="Example.Input",
        exact_type=exact_type,
        namespace="Example.Generated",
        declaration_name="capability_test",
        implementation=implementation,
    )
    assert "noncomputable def capability_test" in source
    assert declaration == "Example.Generated.capability_test"


def test_rule_probe_materializes_instantiated_proof_with_declaration_provenance() -> None:
    fragment = ReusableFragment(
        exact_type="Example.Target",
        proof_term="by\n  apply Example.rule\n  exact Example.premise",
        declaration="Example.rule",
        module="Example.Rules",
    )
    source = build_rule_instantiation_probe_source(
        modules=("Example.Input",),
        declaration="Example.parent",
        exact_target="Example.ParentTarget",
        assignments={0: fragment},
        nonce="abc",
    )
    assert "noncomputable def bound0 : Example.Target :=" in source
    assert "set_option maxHeartbeats 10000000" in source
    assert "0=Example.rule" not in source
    assert "0=ComplexityReduction.Agent.GenerativeReduction.RuleInstantiationProbe.Nabc.bound0" in source


def test_rule_probe_materializes_zero_premise_application_wrapper() -> None:
    fragment = ReusableFragment(
        exact_type="Example.Target",
        proof_term="by\n  apply_generative_rule Example.value",
        declaration="Example.value",
        module="Example.Values",
    )
    source = build_rule_instantiation_probe_source(
        modules=("Example.Input",),
        declaration="Example.parent",
        exact_target="Example.ParentTarget",
        assignments={0: fragment},
        nonce="def",
    )
    assert "noncomputable def bound0 : Example.Target :=" in source
    assert "apply_generative_rule Example.value" in source
    assert "0=ComplexityReduction.Agent.GenerativeReduction.RuleInstantiationProbe.Ndef.bound0" in source


def test_rule_probe_reuses_literal_stable_declaration() -> None:
    fragment = ReusableFragment(
        exact_type="Example.Target",
        proof_term="Example.value",
        declaration="Example.value",
        module="Example.Values",
    )
    source = build_rule_instantiation_probe_source(
        modules=("Example.Input",),
        declaration="Example.parent",
        exact_target="Example.ParentTarget",
        assignments={0: fragment},
        nonce="ghi",
    )
    assert "noncomputable def bound0" not in source
    assert "0=Example.value" in source


def test_strategy_cache_key_invalidates_after_new_repair_diagnostic() -> None:
    state = _root_state()
    goal = state.select_open_goal()
    action = CandidateAction(
        action_id="synthesis-stable",
        provider=ProviderKind.SYNTHESIS,
        disposition=ActionDisposition.SYNTHESIS_REQUIRED,
        goal_key=goal.key,
        estimated_cost=1.0,
        contract_id="contract-stable",
        metadata={"construction_mode": "direct-authoring"},
    )
    plan = SubstepPlan(
        goal_key=goal.key,
        exact_closure_result=ExactClosureResult(goal_key=goal.key, closed=False),
        ranked_proof_guidance=(),
        reusable_fragments=(),
        residual_obligations=(),
        construction_contract=None,
        candidate_actions=(action,),
        recommended_action_id=action.action_id,
        cache_key="cache",
        plan_fingerprint="plan",
    )
    first = RecursiveSearchRuntime._strategy_cache_key(
        state=state,
        goal=goal,
        actions=(action,),
        plan=plan,
    )
    repaired = RecursiveSearchRuntime._strategy_cache_key(
        state=replace(state, normalized_failure_fingerprints=("repair",)),
        goal=goal,
        actions=(action,),
        plan=plan,
    )
    assert first != repaired


def test_strategy_prompt_contains_only_current_executable_actions() -> None:
    goal = _goal()
    first = CandidateAction(
        action_id="already-attempted",
        provider=ProviderKind.THEOREM,
        disposition=ActionDisposition.DECOMPOSED,
        goal_key=goal.key,
        estimated_cost=1.0,
    )
    second = replace(first, action_id="currently-executable")
    plan = SubstepPlan(
        goal_key=goal.key,
        exact_closure_result=ExactClosureResult(goal_key=goal.key, closed=False),
        ranked_proof_guidance=(),
        reusable_fragments=(),
        residual_obligations=(),
        construction_contract=None,
        candidate_actions=(first, second),
        recommended_action_id=first.action_id,
        cache_key="strategy-executable-cache",
        plan_fingerprint="strategy-executable-plan",
    )

    class Model:
        prompt = ""

        def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
            del system
            self.prompt = prompt
            return ModelResponse(
                called=True,
                ok=True,
                content=json.dumps(
                    {
                        "decision": "select_action",
                        "action_id": second.action_id,
                        "design_id": None,
                        "confidence": 1.0,
                        "reason": "only executable action",
                    }
                ),
                error=None,
                status_code=200,
                duration_seconds=0.01,
                usage={},
                attempts=1,
            )

    model = Model()
    proposal, record = propose_strategy(
        model=model,
        goal=goal,
        plan=plan,
        actions=(second,),
    )

    payload = json.loads(model.prompt)
    assert [item["action_id"] for item in payload["actions"]] == [second.action_id]
    assert first.action_id not in model.prompt
    assert proposal is not None and proposal.action_id == second.action_id
    assert record.ok


def test_theorem_residual_recreating_an_ancestor_is_cycle_pruned() -> None:
    root = _root_state()
    frame = _frame(root)
    child = OpenGoal.create(
        goal_id="goal-frame-test-cycle",
        exact_type="Example.Child",
        import_closure_fingerprint="env",
        parent_rule=frame.declaration,
        producer_frame_id=frame.frame_id,
        producer_slot_id=frame.premise_slots[0].slot_id,
        dependency_slot_ids=frame.premise_slots[0].dependency_slot_ids,
        kind=GoalKind.DATA,
    )
    state = replace(root, open_goals=(child,), application_frames=(frame,))
    residual = ResidualObligation(
        obligation_id="residual-ancestor",
        exact_type=frame.parent_exact_type,
        kind=GoalKind.HARDNESS,
    )
    action = CandidateAction(
        action_id="cyclic-accessor",
        provider=ProviderKind.THEOREM,
        disposition=ActionDisposition.DECOMPOSED,
        goal_key=child.key,
        estimated_cost=0.1,
        declaration="Example.Parent.child",
        residual_obligation_ids=(residual.obligation_id,),
    )
    plan = SubstepPlan(
        goal_key=child.key,
        exact_closure_result=ExactClosureResult(goal_key=child.key, closed=False),
        ranked_proof_guidance=(),
        reusable_fragments=(),
        residual_obligations=(residual,),
        construction_contract=None,
        candidate_actions=(action,),
        recommended_action_id=action.action_id,
        cache_key="ancestor-cycle-cache",
        plan_fingerprint="ancestor-cycle-plan",
    )

    reason = SearchCoordinator._ancestor_cycle_reason(state, child, plan, action)

    assert reason is not None
    assert residual.obligation_id in reason
    assert frame.frame_id in reason
    direct_authoring = replace(
        action,
        action_id="direct-authoring",
        provider=ProviderKind.SYNTHESIS,
        disposition=ActionDisposition.SYNTHESIS_REQUIRED,
    )
    assert (
        SearchCoordinator._ancestor_cycle_reason(
            state, child, plan, direct_authoring
        )
        is None
    )


def test_boolean_csp_plugin_exposes_reflection_declaration_owner() -> None:
    plugin = load_plugin("boolean_csp")
    assert "ComplexityReduction.Agent.Reduction.Reflection" in plugin.lean_imports
    assert (
        "ComplexityReduction.Agent.GenerativeReduction.Plugins."
        "BooleanCSPFiniteGadget"
    ) in plugin.lean_imports


def test_boolean_csp_explicit_finite_gadget_precedes_canonical_database() -> None:
    plugin = load_plugin("boolean_csp")
    names = tuple(item.name for item in plugin.finite_synthesis_plugins)
    assert names == (
        "boolean-csp-direct-tm-compiler",
        "boolean-csp-semantic-compiler",
        "boolean-csp-explicit-finite-gadget",
        "boolean-csp-canonical-database",
    )


def test_boolean_csp_explicit_finite_gadget_avoids_canonical_route() -> None:
    plugin = next(
        item
        for item in load_plugin("boolean_csp").finite_synthesis_plugins
        if item.name == "boolean-csp-explicit-finite-gadget"
    )
    goal = OpenGoal.create(
        goal_id="goal-explicit-one-in-three-gadget",
        exact_type=(
            "(symbol : ComplexityReduction.Domain.BooleanCSP.Hardness.oneInThreeCore.Symbol) → "
            "ComplexityReduction.Domain.BooleanCSP.Hardness.Gadget Example.gamma "
            "(ComplexityReduction.Domain.BooleanCSP.Hardness.oneInThreeCore.relationOf symbol)"
        ),
        kind=GoalKind.DATA,
    )
    assert plugin.supports(goal).supported
    candidates = plugin.enumerate(
        goal,
        declaration_name="Example.generated",
        limit=2,
    )
    assert len(candidates) == 2
    assert tuple(
        candidate.check_receipt["grammar_variant"] for candidate in candidates
    ) == (
        "planner-base-grammar",
        "dual-cardinality-arity-4",
    )
    combined = "\n".join(candidate.implementation for candidate in candidates)
    assert "BooleanCSPFiniteGadget.gadgetOfPlannedSearch" in combined
    assert "Finset.univ.toList" in candidates[0].implementation
    assert "intro symbol" in candidates[0].implementation
    assert "Classical.choice" in candidates[0].implementation
    assert "fin_cases symbol" in candidates[0].implementation
    assert "CanonicalDatabase.gadget" not in combined
    assert "exactlyOne_closed_of_notSchaeferTractable" not in combined
    assert "nae_closed_of_notSchaeferTractable" not in combined


def test_generic_constant_parity_clause_seed_materializes_one_in_three(
    tmp_path: Path,
) -> None:
    plugin = next(
        item
        for item in load_plugin("boolean_csp").finite_synthesis_plugins
        if item.name == "boolean-csp-explicit-finite-gadget"
    )
    exact_type = (
        "(symbol : ComplexityReduction.Domain.BooleanCSP.Hardness.oneInThreeCore.Symbol) → "
        "ComplexityReduction.Domain.BooleanCSP.Hardness.Gadget "
        "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case05OR2EvenParity3.gamma "
        "(ComplexityReduction.Domain.BooleanCSP.Hardness.oneInThreeCore.relationOf symbol)"
    )
    goal = OpenGoal.create(
        goal_id="goal-generic-constant-parity-clause",
        exact_type=exact_type,
        kind=GoalKind.DATA,
    )
    candidate = plugin.enumerate(
        goal,
        declaration_name="generatedOneInThreeGadget",
        limit=1,
    )[0]
    source, declaration = build_authored_capability_source(
        input_module=(
            "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case05OR2EvenParity3"
        ),
        exact_type=exact_type,
        namespace="GeneratedGenericBooleanCSPSeedTest",
        declaration_name="generatedOneInThreeGadget",
        implementation=candidate.implementation,
        extra_imports=candidate.imports,
        generated_capabilities=(),
        forbidden_declarations=(
            "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalDatabase.gadget",
        ),
    )
    path = tmp_path / "GenericConstantParityClauseSeed.lean"
    path.write_text(source, encoding="utf-8")
    command = run_lean_file(root=ROOT, path=path, timeout_seconds=180)
    assert command.ok, command.stderr or command.stdout
    assert declaration.endswith("generatedOneInThreeGadget")
    grammar_source = (
        ROOT
        / "Lean/Reference/ComplexityReduction/Agent/GenerativeReduction/Plugins/BooleanCSPFiniteGadget.lean"
    ).read_text(encoding="utf-8")
    plugin_source = (
        ROOT / "agent/generative_reduction/plugins/boolean_csp.py"
    ).read_text(encoding="utf-8")
    assert "Case05OR2EvenParity3" not in grammar_source
    assert "Case05OR2EvenParity3" not in plugin_source
    assert "CanonicalDatabase.gadget" not in candidate.implementation


def test_boolean_csp_gadget_cegis_expands_bounds_and_grammar_from_feedback() -> None:
    plugin = next(
        item
        for item in load_plugin("boolean_csp").finite_synthesis_plugins
        if item.name == "boolean-csp-explicit-finite-gadget"
    )
    goal = OpenGoal.create(
        goal_id="goal-cegis-gadget",
        exact_type=(
            "(symbol : ComplexityReduction.Domain.BooleanCSP.Hardness.nae3Core.Symbol) → "
            "ComplexityReduction.Domain.BooleanCSP.Hardness.Gadget Example.gamma "
            "(ComplexityReduction.Domain.BooleanCSP.Hardness.nae3Core.relationOf symbol)"
        ),
        kind=GoalKind.DATA,
    )
    initial = plugin.enumerate(
        goal, declaration_name="generatedGadget", limit=1, counterexamples=()
    )[0]
    feedback = ({"kind": "lean-truth-table-rejection", "witness_id": initial.witness_id},)
    expanded = plugin.enumerate(
        goal,
        declaration_name="generatedGadget",
        limit=1,
        counterexamples=feedback,
    )[0]
    assert expanded.check_receipt["cegis_round"] == 2
    assert expanded.check_receipt["variable_bound"] > initial.check_receipt["variable_bound"]
    assert expanded.check_receipt["constraint_bound"] > initial.check_receipt["constraint_bound"]
    assert expanded.check_receipt["expanded_template_count"] > 0
    assert "templates ++" in expanded.implementation
    assert expanded.generator_brief is not None
    assert expanded.generator_brief.prior_counterexamples == feedback
    assert expanded.typed_plan_receipt["design_kind"] == "cegis-finite-spec"


def test_boolean_csp_counterexample_probe_returns_exact_truth_table_row(
    tmp_path: Path,
) -> None:
    source = """import ComplexityReduction.Agent.GenerativeReduction.Plugins.BooleanCSPFiniteGadget
import ComplexityReduction.Agent.Hardness.BooleanCSPAuthoringSources
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case02PositiveNAE4

open ComplexityReduction.Agent.GenerativeReduction.Plugins.BooleanCSPFiniteGadget

#reduce firstPlannedCounterexample?
  ComplexityReduction.Agent.Hardness.BooleanCSPAuthoringSources.PositiveNAE3CSP.gamma
  Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case02PositiveNAE4.gamma
  6 (by decide) (by intro symbol; fin_cases symbol <;> decide) [[]]
"""
    path = tmp_path / "CounterexampleProbe.lean"
    path.write_text(source, encoding="utf-8")
    command = run_lean_file(root=ROOT, path=path, timeout_seconds=120)
    assert command.ok, command.stderr or command.stdout
    parsed = parse_finite_counterexample_output(
        stdout=command.stdout,
        stderr=command.stderr,
        schema="finite-truth-table-counterexample-v1",
    )
    assert parsed == {
        "kind": "finite-truth-table-counterexample",
        "source_tuple": (False, False, False),
        "expected_source_relation_value": False,
        "formula_satisfiability": True,
        "schema_version": "finite-truth-table-counterexample-v1",
    }


def test_boolean_csp_counterexample_probe_reduces_with_stable_core_declaration(
    tmp_path: Path,
) -> None:
    source = """import ComplexityReduction.Agent.GenerativeReduction.Plugins.BooleanCSPFiniteGadget
import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case10PositiveExactlyThree4

open ComplexityReduction.Agent.GenerativeReduction.Plugins.BooleanCSPFiniteGadget

#reduce firstPlannedCounterexample?
  ComplexityReduction.Domain.BooleanCSP.Hardness.oneInThreeCore
  Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case10PositiveExactlyThree4.gamma
  6 (by decide) (by intro symbol; fin_cases symbol <;> decide) [[]]
"""
    path = tmp_path / "StableCoreCounterexampleProbe.lean"
    path.write_text(source, encoding="utf-8")
    command = run_lean_file(root=ROOT, path=path, timeout_seconds=120)
    assert command.ok, command.stderr or command.stdout
    parsed = parse_finite_counterexample_output(
        stdout=command.stdout,
        stderr=command.stderr,
        schema="finite-truth-table-counterexample-v1",
    )
    assert parsed == {
        "kind": "finite-truth-table-counterexample",
        "source_tuple": (False, False, False),
        "expected_source_relation_value": False,
        "formula_satisfiability": True,
        "schema_version": "finite-truth-table-counterexample-v1",
    }


@pytest.mark.parametrize(
    ("case_name", "arity"),
    (
        ("Case10PositiveExactlyThree4", 4),
        ("Case14PositiveExactlyFour5", 5),
        ("Case19PositiveExactlyFive6", 6),
    ),
)
def test_boolean_csp_dual_cardinality_seed_is_generic_and_lean_verified(
    tmp_path: Path, case_name: str, arity: int
) -> None:
    plugin = next(
        item
        for item in load_plugin("boolean_csp").finite_synthesis_plugins
        if item.name == "boolean-csp-explicit-finite-gadget"
    )
    target = f"Benchmark.Hardness.Inputs.BooleanCSPNPHard.{case_name}.gamma"
    exact_type = (
        "(symbol : ComplexityReduction.Domain.BooleanCSP.Hardness.oneInThreeCore.Symbol) → "
        "ComplexityReduction.Domain.BooleanCSP.Hardness.Gadget "
        f"{target} "
        "(ComplexityReduction.Domain.BooleanCSP.Hardness.oneInThreeCore.relationOf symbol)"
    )
    goal = OpenGoal.create(
        goal_id=f"goal-generic-dual-cardinality-{arity}",
        exact_type=exact_type,
        kind=GoalKind.DATA,
    )
    candidates = plugin.enumerate(
        goal,
        declaration_name="generatedDualCardinalityGadget",
        limit=4,
    )
    assert candidates[0].check_receipt["grammar_variant"] == "planner-base-grammar"
    candidate = next(
        item
        for item in candidates
        if item.check_receipt["grammar_variant"]
        == f"dual-cardinality-arity-{arity}"
    )
    assert candidate.check_receipt["variable_bound"] == 8
    assert candidate.check_receipt["constraint_bound"] == 5
    source, declaration = build_authored_capability_source(
        input_module=f"Benchmark.Hardness.Inputs.BooleanCSPNPHard.{case_name}",
        exact_type=exact_type,
        namespace="GeneratedGenericDualCardinalitySeedTest",
        declaration_name="generatedDualCardinalityGadget",
        implementation=candidate.implementation,
        extra_imports=candidate.imports,
        generated_capabilities=(),
        forbidden_declarations=(
            "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalDatabase.gadget",
        ),
    )
    path = tmp_path / f"GenericDualCardinalitySeed{arity}.lean"
    path.write_text(source, encoding="utf-8")
    command = run_lean_file(root=ROOT, path=path, timeout_seconds=180)
    assert command.ok, command.stderr or command.stdout
    assert declaration.endswith("generatedDualCardinalityGadget")
    assert "CanonicalDatabase.gadget" not in candidate.implementation
    grammar_source = (
        ROOT
        / "Lean/Reference/ComplexityReduction/Agent/GenerativeReduction/Plugins/BooleanCSPFiniteGadget.lean"
    ).read_text(encoding="utf-8")
    plugin_source = (
        ROOT / "agent/generative_reduction/plugins/boolean_csp.py"
    ).read_text(encoding="utf-8")
    assert case_name not in grammar_source
    assert case_name not in plugin_source


def _check_compiled_boolean_csp_capability(
    *,
    tmp_path: Path,
    exact_type: str,
    compiler,
    declaration_name: str,
    forbidden_declarations: tuple[str, ...],
    input_module: str = (
        "ComplexityReduction.Domain.BooleanCSP.Hardness.CoreReductions"
    ),
) -> FiniteCandidateWitness:
    goal = OpenGoal.create(
        goal_id=f"goal-{declaration_name}",
        exact_type=exact_type,
        kind=GoalKind.PROPOSITION,
    )
    candidate = compiler(goal, declaration_name=declaration_name)
    assert candidate is not None
    namespace = "GeneratedCapabilityCompilerTest"
    generated: list[GeneratedCapability] = []
    for ordinal, stage in enumerate(candidate.stages, start=1):
        stage_source, stage_declaration = build_authored_capability_source(
            input_module=input_module,
            exact_type=stage.exact_type,
            namespace=namespace,
            declaration_name=stage.declaration_name,
            implementation=stage.implementation,
            extra_imports=(*candidate.imports, *stage.imports),
            generated_capabilities=tuple(generated),
            forbidden_declarations=forbidden_declarations,
        )
        stage_path = tmp_path / f"{declaration_name}-stage-{ordinal}.lean"
        stage_path.write_text(stage_source, encoding="utf-8")
        stage_command = run_lean_file(root=ROOT, path=stage_path, timeout_seconds=120)
        assert stage_command.ok, stage_command.stderr or stage_command.stdout
        generated.append(
            GeneratedCapability(
                capability_id=f"test-stage-{ordinal}",
                exact_type=stage.exact_type,
                declaration=stage_declaration,
                namespace=namespace,
                implementation=stage.implementation,
                source_hash=f"test-stage-hash-{ordinal}",
                action_id="test-compiler",
            )
        )
    source, _ = build_authored_capability_source(
        input_module=input_module,
        exact_type=exact_type,
        namespace=namespace,
        declaration_name=declaration_name,
        implementation=candidate.implementation,
        extra_imports=candidate.imports,
        generated_capabilities=tuple(generated),
        forbidden_declarations=forbidden_declarations,
    )
    path = tmp_path / f"{declaration_name}.lean"
    path.write_text(source, encoding="utf-8")
    command = run_lean_file(root=ROOT, path=path, timeout_seconds=120)
    assert command.ok, command.stderr or command.stdout
    return candidate


def test_boolean_csp_gadget_compiler_handles_arbitrary_symbol_without_large_elim(
    tmp_path: Path,
) -> None:
    hardness = "ComplexityReduction.Domain.BooleanCSP.Hardness"
    case = "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case02PositiveNAE4"
    exact_type = (
        f"(symbol : {hardness}.nae3Core.Symbol) → "
        f"{hardness}.Gadget {case}.gamma "
        f"({hardness}.nae3Core.relationOf symbol)"
    )
    plugin = next(
        item
        for item in load_plugin("boolean_csp").finite_synthesis_plugins
        if item.name == "boolean-csp-explicit-finite-gadget"
    )

    def compile_gadget(goal, *, declaration_name):
        candidates = plugin.enumerate(
            goal,
            declaration_name=declaration_name,
            limit=1,
            counterexamples=(),
        )
        return candidates[0] if candidates else None

    candidate = _check_compiled_boolean_csp_capability(
        tmp_path=tmp_path,
        exact_type=exact_type,
        compiler=compile_gadget,
        declaration_name="compiledGadget",
        forbidden_declarations=(
            f"{hardness}.CanonicalDatabase.gadget",
            f"{hardness}.CanonicalHardCores.exactlyOne_closed_of_notSchaeferTractable",
        ),
        input_module=case,
    )
    assert candidate.check_receipt["target_symbol_enumeration"] == (
        "Finset.univ.toList"
    )
    assert "apply Classical.choice" in candidate.implementation


def test_type_defeq_probe_detects_presented_problem_alias(
    tmp_path: Path,
) -> None:
    case = "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case02PositiveNAE4"
    first = f"ComplexityReduction.Certificate.NativeTMNPHard {case}.problem"
    second = (
        "ComplexityReduction.Certificate.NativeTMNPHard "
        f"(ComplexityReduction.Domain.BooleanCSP.cspOf {case}.gamma)"
    )
    source = build_type_defeq_probe_source(
        modules=(case,),
        first_type=first,
        second_type=second,
    )
    path = tmp_path / "TypeDefeqProbe.lean"
    path.write_text(source, encoding="utf-8")
    command = run_lean_file(root=ROOT, path=path, timeout_seconds=120)
    assert command.ok, command.stderr or command.stdout


def test_boolean_csp_direct_tm_compiler_generates_kernel_checked_dag(
    tmp_path: Path,
) -> None:
    hardness = "ComplexityReduction.Domain.BooleanCSP.Hardness"
    presentation = "ComplexityReduction.Presentation.FiniteDomainCSPTable"
    source = f"{hardness}.oneInThreeCore"
    target = f"{hardness}.exactlyTwo3Core"
    interpretation = f"{hardness}.exactlyTwo3InterpretsOneInThree"
    exact_type = (
        "ComplexityReduction.TMPolyTimeMap "
        f"({presentation}.encodedType {source}) "
        f"({presentation}.encodedType {target}) "
        f"(@{hardness}.interpret {source} {target} {interpretation})"
    )
    candidate = _check_compiled_boolean_csp_capability(
        tmp_path=tmp_path,
        exact_type=exact_type,
        compiler=compile_direct_tm_candidate,
        declaration_name="compiledDirectTM",
        forbidden_declarations=(f"{hardness}.interpretation_tmPolyTime",),
    )
    assert candidate.authoritative_typed_compiler
    assert candidate.typed_plan_receipt is not None
    assert len(candidate.typed_plan_receipt["nodes"]) == 4
    restored = DirectTMCapabilityPlan.from_dict(candidate.typed_plan_receipt)
    assert restored.plan_id == candidate.typed_plan_receipt["plan_id"]
    assert restored.nodes[-1].node_id == restored.final_node_id
    assert f"{hardness}.interpretation_tmPolyTime" not in candidate.implementation


def test_boolean_csp_semantic_compiler_generates_both_kernel_checked_directions(
    tmp_path: Path,
) -> None:
    hardness = "ComplexityReduction.Domain.BooleanCSP.Hardness"
    source = f"{hardness}.oneInThreeCore"
    target = f"{hardness}.exactlyTwo3Core"
    interpretation = f"{hardness}.exactlyTwo3InterpretsOneInThree"
    interpreted = (
        f"(@{hardness}.interpret {source} {target} {interpretation} formula)"
    )
    exact_type = (
        f"∀ (formula : ComplexityReduction.CSP.Formula {source}), "
        "Iff "
        f"(@ComplexityReduction.CSP.Formula.Satisfiable {target} {interpreted}) "
        f"(@ComplexityReduction.CSP.Formula.Satisfiable {source} formula)"
    )
    forbidden = (
        f"{hardness}.interpret_satisfiable_iff",
        f"{hardness}.interpret_satisfies_forward",
        f"{hardness}.interpret_satisfies_reverse",
    )
    candidate = _check_compiled_boolean_csp_capability(
        tmp_path=tmp_path,
        exact_type=exact_type,
        compiler=compile_semantic_candidate,
        declaration_name="compiledSemantic",
        forbidden_declarations=forbidden,
    )
    assert candidate.authoritative_typed_compiler
    assert candidate.typed_plan_receipt is not None
    assert candidate.check_receipt["direction_count"] == 2
    restored = SemanticCapabilityPlan.from_dict(candidate.typed_plan_receipt)
    assert restored.forward.direction == "forward"
    assert restored.reverse.direction == "reverse"
    assert all(item not in candidate.implementation for item in forbidden)


def test_non_boolean_held_out_direct_semantic_and_graph_generation_use_shared_protocol(
    tmp_path: Path,
) -> None:
    source = """import ComplexityReduction.Program.List

namespace HeldOutCapabilityGeneration

open ComplexityReduction

private theorem generatedIdentity (X : EncodedType) :
    TMPolyTimeMap X X id :=
  TMPolyTimeMap.id X

private theorem generatedSingleton (X : EncodedType) :
    TMPolyTimeMap X (EncodedType.list X) (fun input => [input]) :=
  TMPolyTimeMap.list_singleton_of (generatedIdentity X)

theorem generatedDirectTM (X : EncodedType) :
    TMPolyTimeMap X (EncodedType.list X) (fun input => [input]) :=
  generatedSingleton X

def sourceAccepts (input : Nat) : Prop :=
  ∃ witness : Nat, witness = input + 1

def targetAccepts (input : Nat) : Prop :=
  ∃ witness : Nat, input = witness

private theorem generatedForward (input : Nat) :
    sourceAccepts input → targetAccepts input := by
  intro _
  exact ⟨input, rfl⟩

private theorem generatedReverse (input : Nat) :
    targetAccepts input → sourceAccepts input := by
  intro _
  exact ⟨input + 1, rfl⟩

theorem generatedSemanticIff (input : Nat) :
    sourceAccepts input ↔ targetAccepts input :=
  ⟨generatedForward input, generatedReverse input⟩

structure GraphGadget where
  map : Fin 2 → Fin 2
  injective : Function.Injective map
  preserves : ∀ left right, left ≠ right ↔ map left ≠ map right

def generatedGraphGadget : GraphGadget where
  map := id
  injective := fun _ _ equality => equality
  preserves := by intro left right; rfl

theorem finalUsesAllGeneratedCapabilities :
    Nonempty GraphGadget ∧
      (∀ input, sourceAccepts input ↔ targetAccepts input) := by
  exact ⟨⟨generatedGraphGadget⟩, generatedSemanticIff⟩

end HeldOutCapabilityGeneration
"""
    path = tmp_path / "HeldOutCapabilityGeneration.lean"
    path.write_text(source, encoding="utf-8")
    command = run_lean_file(root=ROOT, path=path, timeout_seconds=120)
    assert command.ok, command.stderr or command.stdout

    identity = TypedProgramNode.create(
        operation="identity",
        input_encoded_type="X",
        output_encoded_type="X",
        function_term="id",
        primitive_declaration="ComplexityReduction.TMPolyTimeMap.id",
        generated_helper_name="generatedIdentity",
        status="generator-required",
    )
    singleton = TypedProgramNode.create(
        operation="list-singleton",
        input_encoded_type="X",
        output_encoded_type="ComplexityReduction.EncodedType.list X",
        function_term="fun input => [input]",
        primitive_declaration="ComplexityReduction.TMPolyTimeMap.list_singleton_of",
        dependency_node_ids=(identity.node_id,),
        generated_helper_name="generatedDirectTM",
        status="deterministic-compiler",
    )
    direct_plan = DirectTMCapabilityPlan.create(
        exact_goal="TMPolyTimeMap X (EncodedType.list X) (fun input => [input])",
        source_language="held-out-list-source",
        target_language="held-out-list-target",
        interpretation_term="fun input => [input]",
        nodes=(identity, singleton),
        final_node_id=singleton.node_id,
        missing_node_ids=(identity.node_id,),
        endpoint_goal="∀ input, (fun value => [value]) input = [input]",
        normalization_receipt={"domain": "non-Boolean-list", "acyclic": True},
    )
    forward = SemanticDirectionPlan.create(
        direction="forward",
        exact_helper_type="∀ input, sourceAccepts input → targetAccepts input",
        witness_schema={"target_witness": "input"},
        invariant_specs=({"name": "target-witness-equality"},),
        primitive_declarations=("Exists.intro",),
    )
    reverse = SemanticDirectionPlan.create(
        direction="reverse",
        exact_helper_type="∀ input, targetAccepts input → sourceAccepts input",
        witness_schema={"source_witness": "input + 1"},
        invariant_specs=({"name": "source-witness-equality"},),
        primitive_declarations=("Exists.intro",),
    )
    semantic_plan = SemanticCapabilityPlan.create(
        exact_goal="∀ input, sourceAccepts input ↔ targetAccepts input",
        source_language="held-out-source-predicate",
        target_language="held-out-target-predicate",
        interpretation_term="id",
        forward=forward,
        reverse=reverse,
        final_helper_type="∀ input, sourceAccepts input ↔ targetAccepts input",
        residual_goal_dag=(
            {"goal_id": forward.direction_id, "dependencies": ()},
            {"goal_id": reverse.direction_id, "dependencies": ()},
        ),
    )
    capability_plan = CapabilityPlan.create(
        capability_kind=CapabilityKind.SEMANTIC,
        goal_id="held-out-semantic",
        exact_goal=semantic_plan.exact_goal,
        selected_route="semantic-direction-helper-dag/final-iff-assembly",
        construction_basis_ids=("Exists.intro",),
        helper_specs=(
            {"helper_id": forward.direction_id, "exact_type": forward.exact_helper_type},
            {"helper_id": reverse.direction_id, "exact_type": reverse.exact_helper_type},
        ),
    )
    brief = GeneratorBrief.create(
        plan=capability_plan,
        exact_declaration_name="generatedSemanticIff",
        exact_declaration_type=semantic_plan.exact_goal,
        fixed_declaration_envelope={"header": "theorem generatedSemanticIff"},
        selected_design={"design_id": "held-out-semantic-dag"},
        helper_contracts=capability_plan.helper_specs,
        allowed_identifier_manifest=("Exists.intro",),
    )
    contribution = ContributionReceipt(
        capability_declaration="HeldOutCapabilityGeneration.generatedSemanticIff",
        contribution_class=ContributionClass.DETERMINISTIC_GENERATED_CAPABILITY,
        capability_kind=CapabilityKind.SEMANTIC,
        plan_id=capability_plan.plan_id,
        brief_id=brief.brief_id,
        generated_helpers=("generatedForward", "generatedReverse"),
        final_artifact_used=True,
        forbidden_audit_passed=True,
        independent_lean_passed=True,
    )
    serialized = json.dumps(
        {
            "direct": asdict(direct_plan),
            "semantic": asdict(semantic_plan),
            "brief": asdict(brief),
            "contribution": asdict(contribution),
        },
        default=str,
    )
    assert "BooleanCSP" not in serialized
    assert "Case" not in serialized
    assert contribution.final_artifact_used


def test_capability_gate_requires_full_verified_plan_context_and_final_use_coverage(
    tmp_path: Path,
) -> None:
    case_ids = tuple(f"SyntheticCase{ordinal + 1:02d}" for ordinal in range(20))
    policy = CapabilityGatePolicy(
        name="direct-tm",
        policy_version="test-policy-v1",
        required_case_ids=case_ids[3:],
        anchor_case_ids=case_ids[:3],
        required_capability_kind=CapabilityKind.DIRECT_TM,
        required_contribution_classes=(
            ContributionClass.DETERMINISTIC_GENERATED_CAPABILITY,
        ),
    )
    rows = []
    for ordinal in range(20):
        case = case_ids[ordinal]
        row = {
            "case": case,
            "proof_status": "VERIFIED",
            "artifact": None,
            "generated_capabilities": [],
            "typed_capability_plans": [],
            "context_capsules": [],
            "contribution_receipts": [],
            "capability_budget_reservations": [],
        }
        if ordinal >= 3:
            declaration = f"Generated.{case}.directTM"
            exact_goal = "ComplexityReduction.TMPolyTimeMap X Y generatedMap"
            artifact = tmp_path / f"{case}.lean"
            artifact.write_text(f"#check {declaration}\n", encoding="utf-8")
            node_id = f"node-{ordinal}"
            row.update(
                {
                    "artifact": str(artifact),
                    "generated_capabilities": [
                        {"declaration": declaration, "exact_type": exact_goal}
                    ],
                    "typed_capability_plans": [
                        {
                            "plan_id": f"direct-tm-plan-{ordinal}",
                            "exact_goal": exact_goal,
                            "nodes": [
                                {
                                    "node_id": node_id,
                                    "dependency_node_ids": [],
                                }
                            ],
                            "final_node_id": node_id,
                        }
                    ],
                    "context_capsules": [
                        {
                            "exact_goal": exact_goal,
                            "generation_context_ready": True,
                        }
                    ],
                    "contribution_receipts": [
                        {
                            "capability_kind": "direct-tm",
                            "capability_declaration": declaration,
                            "plan_id": f"capability-plan-{ordinal}",
                            "brief_id": f"brief-{ordinal}",
                            "final_artifact_used": True,
                            "forbidden_audit_passed": True,
                            "independent_lean_passed": True,
                            "contribution_class": "DETERMINISTIC_GENERATED_CAPABILITY",
                        }
                    ],
                    "capability_budget_reservations": [
                        {
                            "scope_id": f"scope-{ordinal}",
                            "hierarchy": [
                                f"case:{case}",
                                "route:plugin",
                                f"capability:direct-tm-plan-{ordinal}",
                                f"design:design-{ordinal}",
                                "repair:round-1",
                            ],
                            "requirements": {"lean_checks": 1},
                            "status": (
                                "reserved-for-immediate-sequential-execution"
                            ),
                        }
                    ],
                }
            )
        rows.append(row)
    report = {
        "suite": {"completed_case_count": 20},
        "results": {"verified_case_count": 20},
        "real_api": {"total_calls": 17},
        "validation": {
            "all_called_requests_http_200": True,
            "forbidden_direct_or_transitive_dependency_count": 0,
            "unresolved_probe_handle_count_is_zero": True,
            "empty_context_generator_call_count_is_zero": True,
        },
        "cases": rows,
    }
    evaluation = evaluate_capability_gate(report, "direct-tm", policy)
    assert evaluation["gate_passed"]
    assert evaluation["verified_case_count_with_final_used_match"] == 17
    incomplete = {
        **report,
        "results": {"verified_case_count": 3},
    }
    assert not evaluate_capability_gate(
        incomplete, "direct-tm", policy
    )["gate_passed"]


def test_capability_dag_preserves_verified_stage_when_later_stage_fails(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    class Store:
        def write_text(self, relative: str, source: str) -> Path:
            path = tmp_path / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source, encoding="utf-8")
            return path

    class Command:
        def __init__(self, ok: bool):
            self.ok = ok
            self.stdout = ""
            self.stderr = "" if ok else "error: second stage rejected"

        def to_dict(self):
            return {"ok": self.ok, "stdout": self.stdout, "stderr": self.stderr}

    checks = iter((Command(True), Command(False)))
    monkeypatch.setattr(
        "agent.generative_reduction.recursive_runtime.run_lean_file",
        lambda **_kwargs: next(checks),
    )
    monkeypatch.setattr(
        "agent.generative_reduction.recursive_runtime.build_authored_capability_source",
        lambda **kwargs: (
            f"source for {kwargs['declaration_name']}",
            f"{kwargs['namespace']}.{kwargs['declaration_name']}",
        ),
    )
    runtime = object.__new__(RecursiveSearchRuntime)
    runtime.root = ROOT
    runtime.store = Store()
    runtime.input_module = "Example.Input"
    runtime.plugin_imports = ()
    runtime.forbidden_declarations = ()
    runtime.tracker = BudgetTracker(SearchBudget())
    runtime.lean_timeout_seconds = 30
    runtime.commands = []
    runtime._verified_plugin_stage_sources = set()
    runtime.event_sink = lambda name, details: events.append((name, details))
    runtime.planner = SimpleNamespace(invalidate_for_new_capability=lambda _value: None)
    events: list[tuple[str, object]] = []
    state = _root_state()
    goal = state.select_open_goal()
    action = CandidateAction(
        action_id="plugin-stage-test",
        provider=ProviderKind.PLUGIN,
        disposition=ActionDisposition.SYNTHESIS_REQUIRED,
        goal_key=goal.key,
        estimated_cost=1.0,
    )
    first = FiniteCapabilityStage(
        stage_id="stage-first",
        declaration_name="firstStage",
        exact_type="Example.First",
        implementation="noncomputable def firstStage : Example.First := by exact Example.first",
    )
    second = FiniteCapabilityStage(
        stage_id="stage-second",
        declaration_name="secondStage",
        exact_type="Example.Second",
        implementation="noncomputable def secondStage : Example.Second := by exact Example.second",
        dependency_stage_ids=(first.stage_id,),
    )
    candidate = SimpleNamespace(stages=(first, second), imports=())
    progressed, diagnostic = runtime._materialize_plugin_stages(
        state=state,
        goal=goal,
        action=action,
        candidate=candidate,
        namespace="Generated.Stages",
        digest="stage-test",
        plugin_name="stage-test-plugin",
    )
    assert diagnostic == "error: second stage rejected"
    assert [item.declaration for item in progressed.generated_capabilities] == [
        "Generated.Stages.firstStage"
    ]
    assert any(name == "CAPABILITY_STAGE_REGISTERED" for name, _ in events)
    assert any(name == "CAPABILITY_STAGE_FAILED" for name, _ in events)


def test_boolean_csp_plugin_selects_complement_polarity() -> None:
    plugin = load_plugin("boolean_csp")
    registry = PremiseSolverRegistry()
    plugin.register(registry)
    positive = TheoremPremise.create(
        ordinal=0,
        exact_type="Example.SchaeferAlgebra.PreservesComplement Example.gamma",
        kind=PremiseKind.PROPOSITION,
    )
    negative = TheoremPremise.create(
        ordinal=0,
        exact_type="¬Example.SchaeferAlgebra.PreservesComplement Example.gamma",
        kind=PremiseKind.PROPOSITION,
    )
    positive_solution = registry.propose(positive)
    negative_solution = registry.propose(negative)
    assert positive_solution is not None
    assert negative_solution is not None
    assert "gammaPreservesComplement_of_decide_eq_true" in "\n".join(
        positive_solution.proof_lines
    )
    assert "gammaNotPreservesComplement_of_decide_eq_false" in "\n".join(
        negative_solution.proof_lines
    )


@pytest.mark.parametrize(
    "exact_type",
    (
        "Decidable.decide Example.gamma.IsSchaeferTractable = Bool.false",
        "@Eq Bool (@Decidable.decide Example.gamma.IsSchaeferTractable Example.inst) Bool.false",
        "@decide Example.gamma.IsSchaeferTractable Example.inst = Bool.false",
    ),
)
def test_boolean_csp_plugin_closes_reflection_decision_equalities(
    exact_type: str,
) -> None:
    plugin = load_plugin("boolean_csp")
    registry = PremiseSolverRegistry()
    plugin.register(registry)
    premise = TheoremPremise.create(
        ordinal=0,
        exact_type=exact_type,
        kind=PremiseKind.PROPOSITION,
    )
    solution = registry.propose(premise)
    assert solution is not None
    assert solution.solver.endswith(":decision-equality")
    assert solution.proof_lines == ("  · decide",)
    assert solution.proof_term == "by decide"


def test_exact_closure_requires_lean_checker() -> None:
    tracker = BudgetTracker(SearchBudget())
    planner = CapabilityPlanner(
        solver_registry=PremiseSolverRegistry(),
        tracker=tracker,
        checker=None,
    )
    plan = planner.plan(
        goal=_goal(),
        candidates=(_entry(),),
        environment_fingerprint="env",
        capability_fingerprint="caps",
        failure_memory_fingerprint="failures",
        strategy=Strategy.REUSE_FIRST,
        is_root=True,
        target_handle="Example.problem",
    )
    assert not plan.exact_closure_result.closed
    assert any(
        action.disposition == ActionDisposition.DECOMPOSED
        for action in plan.candidate_actions
    )
    assert not any(
        action.provider == ProviderKind.SYNTHESIS
        for action in plan.candidate_actions
    )
    scaffold = next(
        action
        for action in plan.candidate_actions
        if action.disposition == ActionDisposition.DECOMPOSED
    )
    fallback = planner.plan(
        goal=replace(_goal(), attempted_actions=(scaffold.action_id,)),
        candidates=(_entry(),),
        environment_fingerprint="env",
        capability_fingerprint="caps",
        failure_memory_fingerprint="failures-after-scaffold",
        strategy=Strategy.REUSE_FIRST,
        is_root=True,
        target_handle="Example.problem",
    )
    assert any(
        action.provider == ProviderKind.SYNTHESIS
        for action in fallback.candidate_actions
    )


def test_checked_zero_premise_candidate_closes_without_model() -> None:
    planner = CapabilityPlanner(
        solver_registry=PremiseSolverRegistry(),
        tracker=BudgetTracker(SearchBudget()),
        checker=lambda _goal, entry, _solved: ClosureCheck(
            ok=True, proof_term=entry.declaration
        ),
    )
    plan = planner.plan(
        goal=_goal(),
        candidates=(_entry(),),
        environment_fingerprint="env",
        capability_fingerprint="caps",
        failure_memory_fingerprint="failures",
        strategy=Strategy.BALANCED,
        is_root=True,
        target_handle="Example.problem",
    )
    assert plan.exact_closure_result.closed
    assert [action.provider for action in plan.candidate_actions] == [ProviderKind.REUSE]
    assert plan.construction_contract is None


def test_exact_closure_advances_to_next_candidate_after_rebind_attempt() -> None:
    planner = CapabilityPlanner(
        solver_registry=PremiseSolverRegistry(),
        tracker=BudgetTracker(SearchBudget()),
        checker=lambda _goal, entry, _solved: ClosureCheck(
            ok=True, proof_term=entry.declaration
        ),
    )
    first = replace(_entry(), declaration="Example.first")
    second = replace(_entry(), declaration="Example.second")
    goal = _goal()
    initial = planner.plan(
        goal=goal,
        candidates=(first, second),
        environment_fingerprint="env",
        capability_fingerprint="caps",
        failure_memory_fingerprint="failures-a",
        strategy=Strategy.BALANCED,
        is_root=False,
    )
    first_action = initial.candidate_actions[0]
    assert first_action.declaration == "Example.first"
    rebound_goal = replace(goal, attempted_actions=(first_action.action_id,))
    rebound = planner.plan(
        goal=rebound_goal,
        candidates=(first, second),
        environment_fingerprint="env",
        capability_fingerprint="caps",
        failure_memory_fingerprint="failures-b",
        strategy=Strategy.BALANCED,
        is_root=False,
    )
    assert rebound.candidate_actions[0].declaration == "Example.second"


def test_synthesis_required_filters_direct_root_closure_but_keeps_contract() -> None:
    planner = CapabilityPlanner(
        solver_registry=PremiseSolverRegistry(),
        tracker=BudgetTracker(SearchBudget()),
        checker=lambda _goal, entry, _solved: ClosureCheck(
            ok=True, proof_term=entry.declaration
        ),
    )
    plan = planner.plan(
        goal=_goal(),
        candidates=(_entry(),),
        environment_fingerprint="env",
        capability_fingerprint="caps",
        failure_memory_fingerprint="failures",
        strategy=Strategy.SYNTHESIS_REQUIRED,
        is_root=True,
        target_handle="Example.problem",
    )
    assert plan.exact_closure_result.closed
    assert not any(action.disposition == ActionDisposition.CLOSED for action in plan.candidate_actions)
    assert plan.construction_contract is not None
    assert any(action.provider == ProviderKind.SYNTHESIS for action in plan.candidate_actions)


def test_ready_action_buckets_are_views_and_enforce_activation_deadline() -> None:
    goal = _goal()
    theorem = CandidateAction(
        action_id="theorem",
        provider=ProviderKind.THEOREM,
        disposition=ActionDisposition.DECOMPOSED,
        goal_key=goal.key,
        estimated_cost=1.0,
    )
    synthesis = CandidateAction(
        action_id="synthesis",
        provider=ProviderKind.SYNTHESIS,
        disposition=ActionDisposition.SYNTHESIS_REQUIRED,
        goal_key=goal.key,
        estimated_cost=9.0,
    )
    buckets = ReadyActionBuckets((theorem, synthesis))
    assert not hasattr(buckets, "proof_state")
    selected = buckets.choose(
        strategy=Strategy.BALANCED,
        non_synthesis_expansions=12,
        synthesis_activation_deadline=12,
    )
    assert selected == synthesis


def test_general_typed_index_parser_preserves_universes_and_premise_kinds() -> None:
    output = "\n".join(
        (
            "GENERAL_REDUCTION_THEOREM_INDEX\tgeneral_reduction_theorem_index_v1\tn\tgoal\t"
            "Example.problem\tNativeTMNPHard Example.problem\t1\t1",
            "GENERAL_REDUCTION_THEOREM_INDEX\tgeneral_reduction_theorem_index_v1\tn\tcandidate\t"
            "Example.Rules.hard\tExample.Rules\tu,v\t2\tP → C → NativeTMNPHard p\t"
            "proposition=>P || typeclass=>C\tNativeTMNPHard Example.problem\t2\t"
            "ComplexityReduction.Certificate.NativeTMNPHard\tExample.Rules",
        )
    )
    entries = parse_probe_output(stdout=output, stderr="", nonce="n")
    assert entries[0].universe_parameters == ("u", "v")
    assert [premise.kind for premise in entries[0].premises] == [
        PremiseKind.PROPOSITION,
        PremiseKind.TYPECLASS,
    ]


def test_typed_index_v2_preserves_lean_constructor_kind_and_pi_shape() -> None:
    output = "\n".join(
        (
            "GENERAL_REDUCTION_THEOREM_INDEX\tgeneral_reduction_theorem_index_v2\tn\tgoal\t"
            "<typed-goal>\t(x : Example.A) → Example.Pair x\t1\t1\t1\tExample.A\t"
            "Example.Pair x",
            "GENERAL_REDUCTION_THEOREM_INDEX\tgeneral_reduction_theorem_index_v2\tn\tcandidate\t"
            "Example.Pair.mk\tExample.Pair\t\t1\t(x : Example.A) → Example.Pair x\t"
            "data=>Example.A\t(x : Example.A) → Example.Pair x\t2\tExample.Pair\t"
            "Example.Pair\tconstructor",
        )
    )
    entries = parse_probe_output(stdout=output, stderr="", nonce="n")
    assert entries[0].declaration_kind == "constructor"
    assert entries[0].target_binders == ("Example.A",)
    assert entries[0].target_body == "Example.Pair x"


def test_typed_index_skips_unrenderable_unicode_declaration_names() -> None:
    output = "\n".join(
        (
            "GENERAL_REDUCTION_THEOREM_INDEX\tgeneral_reduction_theorem_index_v1\tn\tgoal\t"
            "<typed-goal>\tNot P\t1\t2",
            "GENERAL_REDUCTION_THEOREM_INDEX\tgeneral_reduction_theorem_index_v1\tn\tcandidate\t"
            "Example.Rules.valid\tExample.Rules\t\t1\tP → Not P\tproposition=>P\t"
            "Not P\t1\tNot\tExample.Rules",
            "GENERAL_REDUCTION_THEOREM_INDEX\tgeneral_reduction_theorem_index_v1\tn\tcandidate\t"
            "Example.Rules.asymmetric₃\tExample.Rules\t\t1\tP → Not P\tproposition=>P\t"
            "Not P\t1\tNot\tExample.Rules",
        )
    )
    entries = parse_probe_output(stdout=output, stderr="", nonce="n")
    assert [entry.declaration for entry in entries] == ["Example.Rules.valid"]


def test_typed_index_skips_compiler_and_tactic_internal_declarations() -> None:
    assert is_runtime_candidate_declaration("Example.Rules.valid")
    assert not is_runtime_candidate_declaration("Classical.typeDecidable._proof_1")
    assert not is_runtime_candidate_declaration("Aesop.BuiltinRules.not_intro")
    assert not is_runtime_candidate_declaration("Example.Rule._flat_ctor")

    output = "\n".join(
        (
            "GENERAL_REDUCTION_THEOREM_INDEX\tgeneral_reduction_theorem_index_v1\tn\tgoal\t"
            "<typed-goal>\tNot P\t1\t2",
            "GENERAL_REDUCTION_THEOREM_INDEX\tgeneral_reduction_theorem_index_v1\tn\tcandidate\t"
            "Classical.typeDecidable._proof_1\tInit.Classical\t\t1\tP → Not P\t"
            "proposition=>P\tNot P\t1\tNot\tInit.Classical",
            "GENERAL_REDUCTION_THEOREM_INDEX\tgeneral_reduction_theorem_index_v1\tn\tcandidate\t"
            "Example.Rules.valid\tExample.Rules\t\t1\tP → Not P\t"
            "proposition=>P\tNot P\t1\tNot\tExample.Rules",
        )
    )
    entries = parse_probe_output(stdout=output, stderr="", nonce="n")
    assert [entry.declaration for entry in entries] == ["Example.Rules.valid"]


def test_internal_typed_goal_probe_supports_non_hardness_heads() -> None:
    source = build_typed_goal_probe_source(
        modules=("Example.Input",),
        exact_goal="ComplexityReduction.Certificate.CertifiedReduction source target",
        nonce="n",
    )
    assert "#generative_reduction_probe_typed_goal" in source
    assert "CertifiedReduction source target" in source


def test_typed_goal_probe_materializes_generated_handles_and_multiline_goal() -> None:
    capability = GeneratedCapability(
        capability_id="typed-index-stable-binding",
        exact_type="Example.Value",
        declaration="Example.Generated.stable",
        namespace="Example.Generated",
        implementation="noncomputable def stable : Example.Value := Example.value",
        source_hash="sha256:typed-index-stable",
        action_id="action-typed-index-stable",
    )
    source = build_typed_goal_probe_source(
        modules=("Example.Input",),
        exact_goal="Example.Predicate\n  Example.Generated.stable",
        nonce="typed-generated",
        generated_capabilities=(capability,),
    )
    assert "namespace Example.Generated" in source
    assert source.index("noncomputable def stable") < source.index(
        "#generative_reduction_probe_typed_goal"
    )
    assert "Example.Predicate Example.Generated.stable" in source


def test_np_hard_probe_source_is_materialized_and_binds_requested_problem() -> None:
    source = build_probe_source(
        input_module="Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case02PositiveNAE4",
        problem_declaration=(
            "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case02PositiveNAE4.problem"
        ),
        modules=("ComplexityReduction.Domain.BooleanCSP.Hardness",),
        nonce="probe-nonce",
    )
    assert isinstance(source, str)
    assert "import ComplexityReduction.Domain.BooleanCSP.Hardness" in source
    assert "#generative_reduction_probe_np_hard_theorems" in source
    assert '"probe-nonce"' in source
    assert source.rstrip().endswith(
        "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case02PositiveNAE4.problem"
    )


def test_core_does_not_import_boolean_csp_plugin_or_benchmark_scorer() -> None:
    core_lean = ROOT / "Lean/Reference/ComplexityReduction/Agent/GenerativeReduction"
    for path in core_lean.glob("*.lean"):
        source = path.read_text(encoding="utf-8")
        assert "Plugins.BooleanCSPReflection" not in source
    cli = (ROOT / "scripts/prove_np_hard_general.py").read_text(encoding="utf-8")
    assert "boolean_csp_np_hard_benchmark" not in cli
    assert "Evaluation" not in cli


def _root_state() -> ProofState:
    return ProofState.initial(
        RootGoal.for_problem(
            input_module="Example.Input",
            problem_declaration="Example.problem",
            endpoint_fingerprint="endpoint",
        ),
        import_closure_fingerprint="env",
    )


def test_final_used_generated_capabilities_follow_root_dependency_graph() -> None:
    child = GeneratedCapability(
        capability_id="child",
        exact_type="Example.Child",
        declaration="Example.Generated.child",
        namespace="Example.Generated",
        implementation="noncomputable def child : Example.Child := Example.childProof",
        source_hash="sha256:child",
        action_id="generate-child",
    )
    parent = GeneratedCapability(
        capability_id="parent",
        exact_type="Example.Parent",
        declaration="Example.Generated.parent",
        namespace="Example.Generated",
        implementation=(
            "noncomputable def parent : Example.Parent := "
            "Example.wrap Example.Generated.child"
        ),
        source_hash="sha256:parent",
        action_id="generate-parent",
    )
    abandoned = GeneratedCapability(
        capability_id="abandoned",
        exact_type="Example.Other",
        declaration="Example.Generated.abandoned",
        namespace="Example.Generated",
        implementation="noncomputable def abandoned : Example.Other := Example.otherProof",
        source_hash="sha256:abandoned",
        action_id="generate-abandoned",
    )
    state = SimpleNamespace(
        root_fragment=ReusableFragment(
            exact_type="Example.Root",
            proof_term="Example.finish Example.Generated.parent",
        ),
        generated_capabilities=(child, parent, abandoned),
    )

    reachable = GenerativeReductionOrchestrator._reachable_generated_declarations(state)

    assert reachable == frozenset(
        {"Example.Generated.parent", "Example.Generated.child"}
    )


def test_search_artifact_emits_kernel_dependency_assertions() -> None:
    root_goal = RootGoal(
        input_module="Example.Input",
        problem_declaration="Example.problem",
        exact_type="Example.Root",
        endpoint_fingerprint="example-root",
    )
    capability = GeneratedCapability(
        capability_id="child",
        exact_type="Example.Child",
        declaration="Example.Generated.child",
        namespace="Example.Generated",
        implementation="noncomputable def child : Example.Child := Example.childProof",
        source_hash="sha256:child",
        action_id="generate-child",
    )
    completed = SimpleNamespace(
        complete=True,
        root_goal=root_goal,
        root_fragment=ReusableFragment(
            exact_type=root_goal.exact_type,
            proof_term="Example.finish Example.Generated.child",
        ),
        application_frames=(),
        completed_fragments=(),
        generated_capabilities=(capability,),
    )

    source = build_search_artifact_source(
        completed_state=completed,
        input_module=root_goal.input_module,
        problem_declaration=root_goal.problem_declaration,
        required_declarations=(capability.declaration,),
    )

    assert (
        "#generative_reduction_assert_transitive_dependency "
        "ComplexityReduction.Agent.GenerativeReduction.Generated.problemIsNPHard "
        '"Example.Generated.child"'
    ) in source


def test_route_audit_kernel_dependency_command_accepts_used_and_rejects_unused(
    tmp_path: Path,
) -> None:
    passing = tmp_path / "RouteAuditDependencyPass.lean"
    passing.write_text(
        """import ComplexityReduction.Agent.GenerativeReduction.RouteAudit

namespace RouteAuditDependencySmoke

def child : Nat := 7
def root : Nat := child

#generative_reduction_assert_transitive_dependency RouteAuditDependencySmoke.root "RouteAuditDependencySmoke.child"

end RouteAuditDependencySmoke
""",
        encoding="utf-8",
    )
    passing_command = run_lean_file(root=ROOT, path=passing, timeout_seconds=120)
    assert passing_command.ok, passing_command.stderr or passing_command.stdout

    failing = tmp_path / "RouteAuditDependencyFail.lean"
    failing.write_text(
        """import ComplexityReduction.Agent.GenerativeReduction.RouteAudit

namespace RouteAuditDependencySmoke

def child : Nat := 7
def unused : Nat := 11
def root : Nat := child

#generative_reduction_assert_transitive_dependency RouteAuditDependencySmoke.root "RouteAuditDependencySmoke.unused"

end RouteAuditDependencySmoke
""",
        encoding="utf-8",
    )
    failing_command = run_lean_file(root=ROOT, path=failing, timeout_seconds=120)
    assert not failing_command.ok
    assert "missing dependency RouteAuditDependencySmoke.unused" in (
        failing_command.stderr or failing_command.stdout
    )


def test_closing_verified_fragment_propagates_owner_imports() -> None:
    state = _root_state()
    goal = state.select_open_goal()
    action = CandidateAction(
        action_id="reuse-owner",
        provider=ProviderKind.REUSE,
        disposition=ActionDisposition.CLOSED,
        goal_key=goal.key,
        estimated_cost=0.0,
        declaration="Example.Owner.proof",
        proof_term="Example.Owner.proof",
        lean_verified=True,
    )
    fragment = ReusableFragment(
        exact_type=goal.exact_type,
        proof_term="Example.Owner.proof",
        declaration="Example.Owner.proof",
        module="Example.Owner",
        imports=("Example.Dependency",),
        provenance="test",
        lean_verified=True,
    )
    closed = state.close_goal(
        goal_id=goal.goal_id,
        action=action,
        fragment=fragment,
        step=ProofStep(
            action_id=action.action_id,
            provider=action.provider,
            disposition=action.disposition,
            goal_id=goal.goal_id,
            exact_type=goal.exact_type,
            declaration=action.declaration,
        ),
    )
    assert closed.imports == ("Example.Owner", "Example.Dependency")


def test_rule_probe_uses_capability_scoped_import_envelope(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    runtime = object.__new__(RecursiveSearchRuntime)
    runtime.root = ROOT
    runtime.input_module = "Example.Input"
    runtime.modules = ("Example.Unrelated", "Example.Input")
    runtime.plugin_imports = ("Example.Plugin",)
    runtime.lean_timeout_seconds = 10
    runtime.tracker = SimpleNamespace(consume=lambda _resource: None)
    runtime.store = SimpleNamespace(path=lambda relative: tmp_path / relative)
    entry = _entry()
    runtime._candidate_entries = {entry.declaration: entry}
    captured: dict[str, object] = {}

    def fake_probe(**kwargs):
        captured.update(kwargs)
        return SimpleNamespace(receipt_hash="receipt"), SimpleNamespace(
            to_dict=lambda: {}
        )

    monkeypatch.setattr(
        "agent.generative_reduction.recursive_runtime.run_rule_instantiation_probe",
        fake_probe,
    )
    state = replace(_root_state(), imports=("Example.State",))
    runtime._run_rule_probe(
        state=state,
        declaration=entry.declaration,
        exact_target=state.root_goal.exact_type,
        assignments={
            0: ReusableFragment(
                exact_type="Example.Source",
                proof_term="Example.source",
                declaration="Example.source",
                module="Example.Fragment",
                imports=("Example.Dependency",),
                provenance="test",
                lean_verified=True,
            )
        },
        purpose="test",
    )
    assert captured["modules"] == (
        "Example.Input",
        "Example.Rules",
        "Example.Fragment",
        "Example.Dependency",
        "Example.State",
        "Example.Plugin",
    )
    assert "Example.Unrelated" not in captured["modules"]


def test_generator_context_uses_goal_scoped_import_envelope() -> None:
    runtime = object.__new__(RecursiveSearchRuntime)
    runtime.input_module = "Example.Input"
    runtime.modules = ("Example.Unrelated", "Example.Input")
    runtime.plugin_imports = ("Example.Plugin",)
    entry = _entry()
    state = replace(_root_state(), imports=("Example.State",))
    goal = state.select_open_goal()
    runtime._last_candidates_by_goal = {goal.goal_id: (entry,)}
    runtime._requested_lookup_entries_by_goal = {}
    runtime._candidate_entries = {entry.declaration: entry}
    runtime._construction_basis_cache = {}

    modules = runtime._context_probe_modules(state=state, goal=goal)

    assert modules == (
        "Example.Input",
        "Example.Rules",
        "Example.State",
        "Example.Plugin",
    )
    assert "Example.Unrelated" not in modules


def test_construction_basis_timeout_has_actionable_diagnostic(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    command = SimpleNamespace(
        ok=False,
        stderr="",
        stdout="",
        exit_code=-9,
        timed_out=True,
        duration_seconds=10.0,
    )
    monkeypatch.setattr(
        construction_basis_module, "run_lean_file", lambda **_kwargs: command
    )
    with pytest.raises(RuntimeError, match="timed_out=True"):
        construction_basis_module.query_construction_basis(
            root=ROOT,
            exact_goal="Example.Target",
            modules=("Example.Input",),
            output_path=tmp_path / "TimedOutConstructionBasis.lean",
            timeout_seconds=10,
        )


def test_finite_counterexample_timeout_has_actionable_diagnostic(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    state = _root_state()
    goal = state.select_open_goal()
    action = CandidateAction(
        action_id="finite-counterexample",
        provider=ProviderKind.PLUGIN,
        disposition=ActionDisposition.CLOSED,
        goal_key=goal.key,
        estimated_cost=1.0,
    )
    runtime = object.__new__(RecursiveSearchRuntime)
    runtime.root = ROOT
    runtime.input_module = "Example.Input"
    runtime.plugin_imports = ()
    runtime.lean_timeout_seconds = 10
    runtime.tracker = SimpleNamespace(consume=lambda _resource: None)

    def write_text(relative: str, source: str) -> Path:
        path = tmp_path / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")
        return path

    runtime.store = SimpleNamespace(write_text=write_text)
    runtime._record_command = lambda _command: None
    events: list[tuple[str, Mapping[str, object]]] = []
    runtime.event_sink = lambda name, details: events.append((name, details))
    command = SimpleNamespace(
        ok=False,
        stderr="",
        stdout="",
        exit_code=-9,
        timed_out=True,
        duration_seconds=10.0,
    )
    monkeypatch.setattr(
        "agent.generative_reduction.recursive_runtime.run_lean_file",
        lambda **_kwargs: command,
    )
    candidate = SimpleNamespace(
        witness_id="finite-witness",
        imports=(),
        check_receipt={
            "counterexample_probe_schema": "finite-truth-table-counterexample-v1",
            "counterexample_probe_term": "Example.firstCounterexample?",
        },
    )

    result = runtime._extract_finite_counterexample(
        state=state,
        goal=goal,
        action=action,
        candidate=candidate,
        round_index=0,
    )

    assert result is None
    assert events[-1][0] == "FINITE_COUNTEREXAMPLE_PROBE_FAILED"
    assert "timed_out=True" in str(events[-1][1]["diagnostic"])


def test_rule_probe_timeout_has_actionable_diagnostic(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    command = SimpleNamespace(
        ok=False,
        stderr="",
        stdout="",
        exit_code=-9,
        timed_out=True,
        duration_seconds=10.0,
    )
    monkeypatch.setattr(lean_bridge_module, "run_lean_file", lambda **_kwargs: command)
    with pytest.raises(RuntimeError, match="timed_out=True"):
        lean_bridge_module.run_rule_instantiation_probe(
            root=ROOT,
            modules=("Example.Input",),
            declaration="Example.Rules.transport",
            exact_target="Example.Target",
            assignments={},
            generated_capabilities=(),
            output_path=tmp_path / "TimedOutRuleProbe.lean",
            timeout_seconds=10,
        )


def test_frame_refresh_failure_rolls_back_instead_of_crashing() -> None:
    state = _root_state()
    root_goal = state.select_open_goal()
    action = CandidateAction(
        action_id="theorem-refresh",
        provider=ProviderKind.THEOREM,
        disposition=ActionDisposition.DECOMPOSED,
        goal_key=root_goal.key,
        estimated_cost=1.0,
        declaration="Example.Rules.transport",
    )
    frame = ApplicationFrame(
        frame_id="frame-refresh",
        parent_goal_id=root_goal.goal_id,
        parent_exact_type=root_goal.exact_type,
        parent_local_context=(),
        parent_import_closure_fingerprint="env",
        parent_kind=root_goal.kind,
        parent_attempted_actions=(),
        parent_depth=0,
        action_id=action.action_id,
        declaration="Example.Rules.transport",
        declaration_module="Example.Rules",
        guidance_id="guidance-refresh",
        application_skeleton="by apply_generative_rule Example.Rules.transport",
        premise_slots=(
            PremiseSlot(
                slot_id="frame-refresh:slot:0",
                ordinal=0,
                premise_kind=PremiseKind.PROPOSITION,
                type_template_receipt="receipt",
                dependency_slot_ids=(),
                instantiated_exact_type="Example.Child",
                child_goal_id="goal-child",
                status=SlotStatus.READY,
            ),
        ),
        status=FrameStatus.ACTIVE,
    )
    state = replace(state, open_goals=(), application_frames=(frame,))
    events: list[tuple[str, Mapping[str, object]]] = []
    runtime = object.__new__(RecursiveSearchRuntime)
    runtime._frame_actions = {frame.frame_id: action}
    runtime.event_sink = lambda name, details: events.append((name, details))
    runtime._run_rule_probe = lambda **_kwargs: (_ for _ in ()).throw(
        RuntimeError(
            "Lean rule instantiation probe failed without output "
            "(exit_code=-9, timed_out=True)"
        )
    )
    rolled_back = runtime._fill_frame_slot(
        state,
        frame_id=frame.frame_id,
        slot_id="frame-refresh:slot:0",
        fragment=ReusableFragment(
            exact_type="Example.Child",
            proof_term="Example.child",
            declaration="Example.child",
            provenance="test",
            lean_verified=True,
        ),
    )
    assert not rolled_back.application_frames
    assert rolled_back.select_open_goal().goal_id == root_goal.goal_id
    assert rolled_back.failure_memory[-1]["blocker_code"] == "frame_refresh_failed"
    assert events[-1][0] == "FRAME_REFRESH_FAILED"


def _frame(state: ProofState, *, bound_term: str | None = None) -> ApplicationFrame:
    status = SlotStatus.BOUND if bound_term else SlotStatus.READY
    return ApplicationFrame(
        frame_id="frame-test",
        parent_goal_id="goal-root",
        parent_exact_type=state.root_goal.exact_type,
        parent_local_context=(),
        parent_import_closure_fingerprint="env",
        parent_kind=GoalKind.HARDNESS,
        parent_attempted_actions=("theorem-test",),
        parent_depth=0,
        action_id="theorem-test",
        declaration="Example.Rules.transport",
        declaration_module="Example.Rules",
        guidance_id="guidance-test",
        application_skeleton="by apply_generative_rule Example.Rules.transport",
        binder_slots=(
            BinderSlot(
                slot_id="frame-test:slot:0",
                ordinal=0,
                binder_name="source",
                binder_kind=PremiseKind.DATA,
                exact_type="Example.Source",
                bound_term=bound_term,
                bound_declaration=bound_term,
                status=status,
            ),
        ),
        premise_slots=(
            PremiseSlot(
                slot_id="frame-test:slot:1",
                ordinal=1,
                premise_kind=PremiseKind.PROPOSITION,
                type_template_receipt="receipt",
                dependency_slot_ids=("frame-test:slot:0",),
                instantiated_exact_type=("Example.P " + bound_term if bound_term else None),
                child_goal_id="goal-frame-test-1",
                status=(SlotStatus.READY if bound_term else SlotStatus.DORMANT),
            ),
        ),
        status=FrameStatus.ACTIVE,
    )


def test_failure_memory_and_attempted_action_change_state_fingerprint() -> None:
    state = _root_state()
    goal = state.select_open_goal()
    action = CandidateAction(
        action_id="first",
        provider=ProviderKind.THEOREM,
        disposition=ActionDisposition.DECOMPOSED,
        goal_key=goal.key,
        estimated_cost=1.0,
    )
    failed = state.mark_action_attempted(goal.goal_id, action.action_id).remember_failure(
        action=action,
        diagnostic="Lean rejected the first route",
        blocker_code="lean_rejected",
        goal_id=goal.goal_id,
    )
    assert failed.fingerprint != state.fingerprint
    assert failed.goal(goal.goal_id).attempted_actions == ("first",)
    assert failed.normalized_failure_fingerprints


def test_search_requeues_failure_and_selects_alternative_action() -> None:
    state = _root_state()
    goal = state.select_open_goal()
    first = CandidateAction(
        action_id="first",
        provider=ProviderKind.REUSE,
        disposition=ActionDisposition.CLOSED,
        goal_key=goal.key,
        estimated_cost=1.0,
        proof_term="Example.first",
        declaration="Example.first",
        lean_verified=True,
    )
    second = CandidateAction(
        action_id="second",
        provider=ProviderKind.REUSE,
        disposition=ActionDisposition.CLOSED,
        goal_key=goal.key,
        estimated_cost=2.0,
        proof_term="Example.proof",
        declaration="Example.proof",
        lean_verified=True,
    )
    plan = SubstepPlan(
        goal_key=goal.key,
        exact_closure_result=ExactClosureResult(goal_key=goal.key, closed=False),
        ranked_proof_guidance=(),
        reusable_fragments=(),
        residual_obligations=(),
        construction_contract=None,
        candidate_actions=(first, second),
        recommended_action_id="first",
        cache_key="cache",
        plan_fingerprint="plan",
    )

    class Planner:
        def plan(self, **_kwargs):
            return plan

    expanded: list[str] = []

    def execute(current, selected_goal, _plan, action):
        expanded.append(action.action_id)
        if action.action_id == "first":
            return (
                current.mark_action_attempted(selected_goal.goal_id, action.action_id)
                .remember_failure(
                    action=action,
                    diagnostic="first failed",
                    blocker_code="first_failed",
                    goal_id=selected_goal.goal_id,
                ),
            )
        fragment = ReusableFragment(
            exact_type=selected_goal.exact_type,
            proof_term="Example.proof",
            declaration="Example.proof",
        )
        return (
            current.close_goal(
                goal_id=selected_goal.goal_id,
                action=action,
                fragment=fragment,
                step=ProofStep(
                    action_id=action.action_id,
                    provider=action.provider,
                    disposition=action.disposition,
                    goal_id=selected_goal.goal_id,
                    exact_type=selected_goal.exact_type,
                ),
            ),
        )

    outcome = SearchCoordinator(
        planner=Planner(),
        tracker=BudgetTracker(SearchBudget(max_search_rounds=6)),
        strategy=Strategy.BALANCED,
        environment_fingerprint="env",
        capability_fingerprint=lambda current: current.capability_fingerprint,
        candidate_lookup=lambda _state, _goal: (),
        action_executor=execute,
    ).run(state)
    assert outcome.status == "VERIFIED"
    assert expanded == ["first", "second"]
    assert outcome.requeued_failure_states == 1


def test_strategy_selects_second_typed_action_and_effect_matches_expansion() -> None:
    state = _root_state()
    goal = state.select_open_goal()
    first = CandidateAction(
        action_id="first",
        provider=ProviderKind.THEOREM,
        disposition=ActionDisposition.DECOMPOSED,
        goal_key=goal.key,
        estimated_cost=1.0,
    )
    second = replace(first, action_id="second", estimated_cost=2.0)
    plan = SubstepPlan(
        goal_key=goal.key,
        exact_closure_result=ExactClosureResult(goal_key=goal.key, closed=False),
        ranked_proof_guidance=(),
        reusable_fragments=(),
        residual_obligations=(),
        construction_contract=None,
        candidate_actions=(first, second),
        recommended_action_id="first",
        cache_key="cache-strategy",
        plan_fingerprint="plan-strategy",
    )

    class Planner:
        def plan(self, **_kwargs):
            return plan

    expanded: list[str] = []

    def decide(current, selected_goal, _plan, _actions):
        return StrategyDecision(
            decision_id="decision-second",
            goal_id=selected_goal.goal_id,
            state_fingerprint=current.fingerprint,
            decision_kind="select_action",
            selected_action_id="second",
            rationale="second has the useful residual shape",
            confidence=0.9,
            proposal_hash="sha256:proposal",
            applicable=True,
        )

    def execute(current, selected_goal, _plan, action):
        expanded.append(action.action_id)
        fragment = ReusableFragment(
            exact_type=selected_goal.exact_type,
            proof_term="Example.proof",
            declaration="Example.proof",
        )
        return (
            current.close_goal(
                goal_id=selected_goal.goal_id,
                action=action,
                fragment=fragment,
                step=ProofStep(
                    action_id=action.action_id,
                    provider=action.provider,
                    disposition=ActionDisposition.CLOSED,
                    goal_id=selected_goal.goal_id,
                    exact_type=selected_goal.exact_type,
                ),
            ),
        )

    outcome = SearchCoordinator(
        planner=Planner(),
        tracker=BudgetTracker(SearchBudget(max_search_rounds=4)),
        strategy=Strategy.BALANCED,
        environment_fingerprint="env",
        capability_fingerprint=lambda current: current.capability_fingerprint,
        candidate_lookup=lambda _state, _goal: (),
        action_executor=execute,
        strategy_decider=decide,
    ).run(state)
    assert outcome.status == "VERIFIED"
    assert expanded == ["second"]
    assert outcome.strategy_applied_decisions == 1
    assert outcome.strategy_effect_receipts[0].applied_action_id == "second"
    assert outcome.strategy_effect_receipts[0].next_state_fingerprint


def test_invalid_strategy_action_falls_back_deterministically() -> None:
    state = _root_state()
    goal = state.select_open_goal()
    first = CandidateAction(
        action_id="first",
        provider=ProviderKind.THEOREM,
        disposition=ActionDisposition.DECOMPOSED,
        goal_key=goal.key,
        estimated_cost=1.0,
    )
    second = replace(first, action_id="second", estimated_cost=2.0)
    plan = SubstepPlan(
        goal_key=goal.key,
        exact_closure_result=ExactClosureResult(goal_key=goal.key, closed=False),
        ranked_proof_guidance=(),
        reusable_fragments=(),
        residual_obligations=(),
        construction_contract=None,
        candidate_actions=(first, second),
        recommended_action_id="first",
        cache_key="cache-invalid-strategy",
        plan_fingerprint="plan-invalid-strategy",
    )

    class Planner:
        def plan(self, **_kwargs):
            return plan

    expanded: list[str] = []

    def decide(current, selected_goal, _plan, _actions):
        return StrategyDecision(
            decision_id="decision-invalid",
            goal_id=selected_goal.goal_id,
            state_fingerprint=current.fingerprint,
            decision_kind="select_action",
            selected_action_id="invented",
            rationale="invalid test proposal",
            proposal_hash="sha256:invalid",
            applicable=False,
        )

    def execute(current, selected_goal, _plan, action):
        expanded.append(action.action_id)
        fragment = ReusableFragment(
            exact_type=selected_goal.exact_type,
            proof_term="Example.proof",
        )
        return (
            current.close_goal(
                goal_id=selected_goal.goal_id,
                action=action,
                fragment=fragment,
                step=ProofStep(
                    action_id=action.action_id,
                    provider=action.provider,
                    disposition=ActionDisposition.CLOSED,
                    goal_id=selected_goal.goal_id,
                    exact_type=selected_goal.exact_type,
                ),
            ),
        )

    outcome = SearchCoordinator(
        planner=Planner(),
        tracker=BudgetTracker(SearchBudget(max_search_rounds=4)),
        strategy=Strategy.BALANCED,
        environment_fingerprint="env",
        capability_fingerprint=lambda current: current.capability_fingerprint,
        candidate_lookup=lambda _state, _goal: (),
        action_executor=execute,
        strategy_decider=decide,
    ).run(state)
    assert outcome.status == "VERIFIED"
    assert expanded == ["first"]
    assert outcome.strategy_rejections == 1
    assert outcome.strategy_effect_receipts[0].effect == (
        "deterministic-fallback-invalid-proposal"
    )


def test_single_action_does_not_call_strategy() -> None:
    state = _root_state()
    goal = state.select_open_goal()
    action = CandidateAction(
        action_id="only",
        provider=ProviderKind.THEOREM,
        disposition=ActionDisposition.DECOMPOSED,
        goal_key=goal.key,
        estimated_cost=1.0,
    )
    plan = SubstepPlan(
        goal_key=goal.key,
        exact_closure_result=ExactClosureResult(goal_key=goal.key, closed=False),
        ranked_proof_guidance=(),
        reusable_fragments=(),
        residual_obligations=(),
        construction_contract=None,
        candidate_actions=(action,),
        recommended_action_id=action.action_id,
        cache_key="cache-single-action",
        plan_fingerprint="plan-single-action",
    )

    class Planner:
        def plan(self, **_kwargs):
            return plan

    strategy_calls = 0

    def decide(*_args):
        nonlocal strategy_calls
        strategy_calls += 1
        raise AssertionError("single action must not call strategy")

    def execute(current, selected_goal, _plan, selected_action):
        fragment = ReusableFragment(
            exact_type=selected_goal.exact_type,
            proof_term="Example.proof",
        )
        return (
            current.close_goal(
                goal_id=selected_goal.goal_id,
                action=selected_action,
                fragment=fragment,
                step=ProofStep(
                    action_id=selected_action.action_id,
                    provider=selected_action.provider,
                    disposition=ActionDisposition.CLOSED,
                    goal_id=selected_goal.goal_id,
                    exact_type=selected_goal.exact_type,
                ),
            ),
        )

    outcome = SearchCoordinator(
        planner=Planner(),
        tracker=BudgetTracker(SearchBudget(max_search_rounds=4)),
        strategy=Strategy.BALANCED,
        environment_fingerprint="env",
        capability_fingerprint=lambda current: current.capability_fingerprint,
        candidate_lookup=lambda _state, _goal: (),
        action_executor=execute,
        strategy_decider=decide,
    ).run(state)
    assert outcome.status == "VERIFIED"
    assert strategy_calls == 0


def test_budget_stop_reports_the_most_progressed_frontier_state() -> None:
    state = _root_state()
    goal = state.select_open_goal()
    action = CandidateAction(
        action_id="progress",
        provider=ProviderKind.THEOREM,
        disposition=ActionDisposition.DECOMPOSED,
        goal_key=goal.key,
        estimated_cost=1.0,
    )
    plan = SubstepPlan(
        goal_key=goal.key,
        exact_closure_result=ExactClosureResult(goal_key=goal.key, closed=False),
        ranked_proof_guidance=(),
        reusable_fragments=(),
        residual_obligations=(),
        construction_contract=None,
        candidate_actions=(action,),
        recommended_action_id=action.action_id,
        cache_key="cache-progress",
        plan_fingerprint="plan-progress",
    )

    class Planner:
        def plan(self, **_kwargs):
            return plan

    def execute(current, selected_goal, _plan, selected_action):
        progressed = current.mark_action_attempted(
            selected_goal.goal_id, selected_action.action_id
        )
        return (replace(progressed, data_binding_count=1),)

    outcome = SearchCoordinator(
        planner=Planner(),
        tracker=BudgetTracker(SearchBudget(max_search_rounds=1)),
        strategy=Strategy.BALANCED,
        environment_fingerprint="env",
        capability_fingerprint=lambda current: current.capability_fingerprint,
        candidate_lookup=lambda _state, _goal: (),
        action_executor=execute,
    ).run(state)
    assert outcome.status == "BUDGET_EXHAUSTED"
    assert outcome.best_state.data_binding_count == 1


def test_branch_binding_is_fingerprinted_and_frame_round_trips() -> None:
    state = _root_state()
    first = replace(state, application_frames=(_frame(state, bound_term="Example.sourceA"),))
    second = replace(state, application_frames=(_frame(state, bound_term="Example.sourceB"),))
    assert first.fingerprint != second.fingerprint
    restored = ProofState.from_dict(first.to_dict())
    assert restored.fingerprint == first.fingerprint
    assert restored.application_frames[0].binder_slots[0].bound_term == "Example.sourceA"


def test_exhausted_dependent_branch_reopens_only_its_data_witness() -> None:
    state = _root_state()
    frame = _frame(state, bound_term="Example.sourceA")
    binder = replace(frame.binder_slots[0], attempted_actions=("reuse-source-a",))
    frame = replace(frame, binder_slots=(binder,))
    dependent = OpenGoal.create(
        goal_id="goal-frame-test-1",
        exact_type="Example.P Example.sourceA",
        import_closure_fingerprint="env",
        parent_rule=frame.declaration,
        producer_frame_id=frame.frame_id,
        producer_slot_id=frame.premise_slots[0].slot_id,
        dependency_slot_ids=(binder.slot_id,),
        kind=GoalKind.PROPOSITION,
    )
    active = replace(state, open_goals=(dependent,), application_frames=(frame,))
    rebound = active.reopen_dependent_data_slot(
        frame_id=frame.frame_id,
        dependent_slot_id=dependent.producer_slot_id or "",
    )
    assert rebound is not None
    rebound_frame = rebound.frame(frame.frame_id)
    assert rebound_frame.binder_slots[0].status == SlotStatus.READY
    assert rebound_frame.binder_slots[0].bound_term is None
    assert rebound_frame.premise_slots[0].status == SlotStatus.DORMANT
    restored_goal = rebound.select_open_goal()
    assert restored_goal.producer_slot_id == binder.slot_id
    assert restored_goal.attempted_actions == ("reuse-source-a",)


def test_dead_end_uses_the_reopened_ready_binder_not_stale_goal_dependencies() -> None:
    state = _root_state()
    frame = _frame(state, bound_term="Example.sourceA")
    dependent = OpenGoal.create(
        goal_id="goal-frame-test-1",
        exact_type="Example.P Example.sourceA",
        import_closure_fingerprint="env",
        parent_rule=frame.declaration,
        producer_frame_id=frame.frame_id,
        producer_slot_id=frame.premise_slots[0].slot_id,
        dependency_slot_ids=(),
        kind=GoalKind.PROPOSITION,
    )
    active = replace(state, open_goals=(dependent,), application_frames=(frame,))
    events: list[tuple[str, object]] = []
    runtime = object.__new__(RecursiveSearchRuntime)
    runtime._frame_actions = {}
    runtime.event_sink = lambda name, details: events.append((name, details))

    rebound = runtime.dead_end(active, dependent, "all child actions exhausted")

    assert rebound is not None
    restored_goal = rebound.select_open_goal()
    assert restored_goal.producer_slot_id == frame.binder_slots[0].slot_id
    assert any(name == "DATA_BINDING_REOPENED" for name, _ in events)


@pytest.mark.parametrize("lean_ok", (False, True))
def test_finite_data_witness_lookahead_requires_lean_verification(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, lean_ok: bool
) -> None:
    goal = OpenGoal.create(
        goal_id="finite-lookahead-goal",
        exact_type="Example.Target",
        import_closure_fingerprint="env",
        kind=GoalKind.DATA,
    )

    class Plugin:
        name = "finite-test"

        def enumerate(
            self,
            _goal,
            *,
            declaration_name,
            limit,
            counterexamples=(),
        ):
            assert limit == 4
            assert not counterexamples
            return (
                FiniteCandidateWitness(
                    witness_id="finite-test-witness",
                    implementation=(
                        f"noncomputable def {declaration_name} : Example.Target := "
                        "by exact Example.target"
                    ),
                    imports=(),
                    executable_status="accepted",
                    check_receipt={},
                ),
            )

    class Store:
        def write_text(self, relative: str, source: str) -> Path:
            path = tmp_path / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(source, encoding="utf-8")
            return path

    class Command:
        ok = lean_ok
        stderr = "" if lean_ok else "error: type mismatch"
        stdout = ""

        def to_dict(self):
            return {"ok": self.ok, "stderr": self.stderr}

    calls: list[Path] = []

    def fake_run_lean_file(*, root, path, timeout_seconds):
        assert root == ROOT
        assert timeout_seconds == 30
        calls.append(path)
        return Command()

    monkeypatch.setattr(
        "agent.generative_reduction.recursive_runtime.run_lean_file",
        fake_run_lean_file,
    )
    events: list[tuple[str, object]] = []
    runtime = object.__new__(RecursiveSearchRuntime)
    runtime.root = ROOT
    runtime.store = Store()
    runtime.input_module = "Example.Input"
    runtime.plugin_imports = ()
    runtime.forbidden_declarations = ()
    runtime.tracker = BudgetTracker(SearchBudget())
    runtime.lean_timeout_seconds = 30
    runtime.commands = []
    runtime.event_sink = lambda name, details: events.append((name, details))
    runtime._finite_lookahead_cache = {}

    first = runtime._finite_lookahead_closes(
        state=_root_state(),
        parent_goal=_goal(),
        goal=goal,
        plugin=Plugin(),
        extra_imports=("Example.Witness",),
    )
    second = runtime._finite_lookahead_closes(
        state=_root_state(),
        parent_goal=_goal(),
        goal=goal,
        plugin=Plugin(),
        extra_imports=("Example.Witness",),
    )

    assert first is lean_ok
    assert second is lean_ok
    assert len(calls) == 1
    assert "import Example.Witness" in calls[0].read_text(encoding="utf-8")
    assert runtime.tracker.usage.lean_checks == 1
    assert any(
        name == "data_witness_lookahead_finite_check"
        and details["verified"] is lean_ok
        for name, details in events
    )


def test_dependent_binding_reuses_lean_typed_stable_declaration() -> None:
    state = _root_state()
    entry = replace(
        _entry(),
        declaration="Example.source",
        module="Example.Source",
        declaration_type="Example.Source",
        conclusion_type="Example.Source",
        conclusion_head="Example.Source",
        result_fingerprint="source",
    )
    runtime = object.__new__(RecursiveSearchRuntime)
    runtime._candidate_entries = {entry.declaration: entry}
    events: list[tuple[str, Mapping[str, object]]] = []
    runtime.event_sink = lambda name, details: events.append((name, details))
    fragment = ReusableFragment(
        exact_type="Example.Source",
        proof_term="by apply_generative_rule Example.source",
        declaration="Example.source",
        module="Example.Source",
        lean_verified=True,
    )

    unchanged, stable = runtime._stabilize_dependent_fragment(
        state=state,
        fragment=fragment,
        parent_action_id="bind-source",
    )

    assert unchanged is state
    assert stable.proof_term == "Example.source"
    assert stable.declaration == "Example.source"
    assert not stable.proof_term.startswith("by apply_generative_rule")
    assert events == [
        (
            "DEPENDENT_BINDING_REUSED",
            {
                "declaration": "Example.source",
                "exact_type": "Example.Source",
                "reason": "verified-declaration-exact-type-match",
            },
        )
    ]


def test_data_witness_ranking_requires_every_ready_sibling_to_close() -> None:
    state = _root_state()
    base_frame = _frame(state)
    frame = replace(
        base_frame,
        premise_slots=(
            base_frame.premise_slots[0],
            PremiseSlot(
                slot_id="frame-test:slot:2",
                ordinal=2,
                premise_kind=PremiseKind.PROPOSITION,
                type_template_receipt="receipt-2",
                dependency_slot_ids=("frame-test:slot:0",),
                status=SlotStatus.DORMANT,
            ),
        ),
    )
    data_goal = OpenGoal.create(
        goal_id="goal-data-rank",
        exact_type="Example.Source",
        import_closure_fingerprint="env",
        producer_frame_id=frame.frame_id,
        producer_slot_id=frame.binder_slots[0].slot_id,
        kind=GoalKind.DATA,
    )
    state = replace(state, application_frames=(frame,), open_goals=(data_goal,))
    bad = replace(
        _entry(),
        declaration="Example.BadSource",
        module="Example.Bad",
        result_fingerprint="bad",
    )
    good = replace(
        _entry(),
        declaration="Example.GoodSource",
        module="Example.Good",
        result_fingerprint="good",
    )

    class FinitePlugin:
        name = "finite-sibling"

        def supports(self, goal):
            return SimpleNamespace(supported=goal.exact_type == "Example.FiniteSibling")

    def probe(*, fragment, **_kwargs):
        theorem_type = (
            "Example.TheoremGood"
            if fragment.declaration == good.declaration
            else "Example.TheoremBad"
        )
        return RuleInstantiationReceipt(
            declaration=frame.declaration,
            target_exact_type=frame.parent_exact_type,
            slots=(
                RuleSlotReceipt(
                    ordinal=0,
                    kind=PremiseKind.DATA,
                    dependency_ordinals=(),
                    status="bound",
                    exact_type="Example.Source",
                    bound_declaration=fragment.declaration,
                    type_hash="source",
                ),
                RuleSlotReceipt(
                    ordinal=1,
                    kind=PremiseKind.PROPOSITION,
                    dependency_ordinals=(0,),
                    status="ready",
                    exact_type="Example.FiniteSibling",
                    bound_declaration=None,
                    type_hash="finite",
                ),
                RuleSlotReceipt(
                    ordinal=2,
                    kind=PremiseKind.PROPOSITION,
                    dependency_ordinals=(0,),
                    status="ready",
                    exact_type=theorem_type,
                    bound_declaration=None,
                    type_hash="theorem",
                ),
            ),
            receipt_hash="receipt-rank",
        )

    runtime = object.__new__(RecursiveSearchRuntime)
    runtime.input_module = "Example.Input"
    runtime.forbidden_declarations = ()
    runtime.tracker = BudgetTracker(SearchBudget())
    runtime._data_witness_rank_cache = {}
    runtime._finite_plugins = {"finite-sibling": FinitePlugin()}
    runtime._probe_with_temporary_binding = probe
    runtime._finite_lookahead_closes = lambda **_kwargs: True
    theorem_candidate = _entry()
    runtime._query_index = lambda _state, exact_type, purpose: (
        (theorem_candidate,) if exact_type.startswith("Example.Theorem") else ()
    )
    runtime._lookahead_candidate_closes = lambda *, exact_type, **_kwargs: (
        exact_type == "Example.TheoremGood"
    )
    runtime.event_sink = lambda _name, _details: None

    ranked = runtime._rank_data_witnesses(state, data_goal, (bad, good))

    assert ranked[0].declaration == good.declaration


def test_state_is_not_complete_until_every_frame_is_verified() -> None:
    state = _root_state()
    root_fragment = ReusableFragment(
        exact_type=state.root_goal.exact_type,
        proof_term="Example.proof",
    )
    active = replace(
        state,
        open_goals=(),
        root_fragment=root_fragment,
        application_frames=(_frame(state, bound_term="Example.source"),),
    )
    assert not active.complete
    verified_frame = replace(active.application_frames[0], status=FrameStatus.VERIFIED)
    assert replace(active, application_frames=(verified_frame,)).complete


def test_frame_reconstruction_binds_every_slot_in_one_lean_application() -> None:
    state = _root_state()
    frame = _frame(state, bound_term="Example.source")
    premise = replace(
        frame.premise_slots[0],
        proof_term="Example.proof",
        declaration="Example.proof",
        status=SlotStatus.BOUND,
    )
    frame = replace(frame, premise_slots=(premise,), status=FrameStatus.SATURATED)
    source, proof_term = build_frame_check_source(
        input_module="Example.Input",
        frame=frame,
        slot_fragments={
            0: ReusableFragment(
                exact_type="Example.Source",
                proof_term="Example.source",
                declaration="Example.source",
            ),
            1: ReusableFragment(
                exact_type="Example.P Example.source",
                proof_term="Example.proof",
                declaration="Example.proof",
            ),
        },
    )
    assert "apply_generative_rule_exact Example.Rules.transport [" in proof_term
    assert "· exact" not in proof_term
    assert "set_option maxHeartbeats 10000000" in source
    assert "Example.source" in source
    assert "Example.proof" in source


def test_theorem_action_id_is_stable_across_guidance_receipts() -> None:
    goal = _goal()

    def guidance(guidance_id: str) -> ProofGuidance:
        return ProofGuidance(
            guidance_id=guidance_id,
            goal_key=goal.key,
            candidate_declaration="Example.Rules.transport",
            declaration_provenance="Example.Rules",
            instantiated_universe_arguments=(),
            application_skeleton="by apply_generative_rule Example.Rules.transport",
            generated_premises=(),
            already_closed_premises=(),
            reusable_fragments=(),
            residual_obligations=(),
            suggested_proof_mode="recursive-premise-search",
            coverage_score=0.0,
            estimated_cost=1.0,
            confidence=0.5,
        )

    provider = TheoremActionProvider()
    assert provider.actions((guidance("receipt-a"),))[0].action_id == provider.actions(
        (guidance("receipt-b"),)
    )[0].action_id


def test_rule_instantiation_parser_preserves_dormant_dependencies() -> None:
    nonce = "n"
    output = "\n".join(
        (
            "GENERAL_REDUCTION_RULE_INSTANTIATION\tgeneral_reduction_rule_instantiation_v1\tn\tframe\tExample.rule\tExample.Target\t2",
            "GENERAL_REDUCTION_RULE_INSTANTIATION\tgeneral_reduction_rule_instantiation_v1\tn\tslot\t0\tdata\t\tready\tExample.Source\t\t1",
            "GENERAL_REDUCTION_RULE_INSTANTIATION\tgeneral_reduction_rule_instantiation_v1\tn\tslot\t1\tproposition\t0\tdormant\tExample.P ?source\t\t2",
        )
    )
    receipt = parse_rule_instantiation_output(
        stdout=output, stderr="", nonce=nonce
    )
    assert receipt.slots[0].status == "ready"
    assert receipt.slots[1].status == "dormant"
    assert receipt.slots[1].dependency_ordinals == (0,)
