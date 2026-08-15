from __future__ import annotations

from dataclasses import replace
from pathlib import Path
import json

import pytest

from agent.generative_reduction.baseline import verify_stable_entrypoints
from agent.generative_reduction.budgets import BudgetTracker, SearchBudget
from agent.generative_reduction.capability_planner import CapabilityPlanner
from agent.generative_reduction.context_capsule import build_context_capsule
from agent.generative_reduction.exact_closure_probe import ClosureCheck
from agent.generative_reduction.finite_synthesis import FiniteCandidateWitness
from agent.generative_reduction.goal_kind_adapters import classify_goal
from agent.generative_reduction.models import (
    ActionDisposition,
    ApplicationFrame,
    BinderSlot,
    CandidateAction,
    ConstructionContract,
    ExactClosureResult,
    FrameStatus,
    GeneralNPHardRequest,
    GoalKind,
    OpenGoal,
    PremiseKind,
    PremiseSlot,
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
    TheoremIndexEntry,
    TheoremPremise,
)
from agent.generative_reduction.premise_registry import PremiseSolverRegistry
from agent.generative_reduction.plugins.registry import load_plugin
from agent.generative_reduction.proof_frontier import ReadyActionBuckets
from agent.generative_reduction.proof_state import ProofState
from agent.generative_reduction.providers.theorem import TheoremActionProvider
from agent.generative_reduction.providers.structural import StructuralActionProvider
from agent.generative_reduction.model.authoring import (
    implementation_sha256,
    propose_repair,
)
from agent.generative_reduction.model.strategy import propose_strategy
from agent.generative_reduction.synthesis.designs import SynthesisDesign
from agent.generative_reduction.synthesis.repair import classify_lean_diagnostic
from agent.hardness.model_client import ModelResponse
from agent.generative_reduction.reconstruction import (
    build_authored_capability_source,
    build_authored_artifact_source,
    build_frame_check_source,
)
from agent.generative_reduction.recursive_runtime import RecursiveSearchRuntime
from agent.generative_reduction.search import SearchCoordinator
from agent.generative_reduction.lean_bridge import (
    build_rule_instantiation_probe_source,
    parse_rule_instantiation_output,
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


def test_rule_probe_reuses_stable_declaration_for_zero_premise_closure() -> None:
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
    assert any(
        action.disposition == ActionDisposition.SYNTHESIS_REQUIRED
        for action in plan.candidate_actions
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
            assert limit == 1
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
    )
    second = runtime._finite_lookahead_closes(
        state=_root_state(),
        parent_goal=_goal(),
        goal=goal,
        plugin=Plugin(),
    )

    assert first is lean_ok
    assert second is lean_ok
    assert len(calls) == 1
    assert runtime.tracker.usage.lean_checks == 1
    assert any(
        name == "data_witness_lookahead_finite_check"
        and details["verified"] is lean_ok
        for name, details in events
    )


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
