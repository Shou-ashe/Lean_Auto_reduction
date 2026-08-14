from __future__ import annotations

from pathlib import Path

import pytest

from agent.generative_reduction.baseline import verify_stable_entrypoints
from agent.generative_reduction.budgets import BudgetTracker, SearchBudget
from agent.generative_reduction.capability_planner import CapabilityPlanner
from agent.generative_reduction.exact_closure_probe import ClosureCheck
from agent.generative_reduction.models import (
    ActionDisposition,
    CandidateAction,
    GeneralNPHardRequest,
    GoalKind,
    OpenGoal,
    PremiseKind,
    ProviderKind,
    Strategy,
    TheoremIndexEntry,
    TheoremPremise,
)
from agent.generative_reduction.premise_registry import PremiseSolverRegistry
from agent.generative_reduction.proof_frontier import ReadyActionBuckets
from agent.generative_reduction.reconstruction import build_authored_artifact_source
from agent.generative_reduction.theorem_index import (
    build_probe_source,
    build_typed_goal_probe_source,
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
