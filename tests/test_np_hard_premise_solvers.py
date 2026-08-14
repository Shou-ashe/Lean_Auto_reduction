from __future__ import annotations

from agent.reduction.models import TheoremCandidate
from agent.reduction.premise_solvers import plans_for


def _candidate(premises: tuple[str, ...]) -> TheoremCandidate:
    return TheoremCandidate(
        declaration="Example.hardSide",
        module="Example",
        premise_count=len(premises),
        declaration_type="schema",
        premises=premises,
        result_type="NativeTMNPHard Example.problem",
        result_fingerprint="lean:example",
    )


def test_schaefer_reflection_solver_follows_telescope_order() -> None:
    candidate = _candidate(
        (
            "¬ ComplexityReduction.Domain.BooleanCSP.IsSchaeferTractable Γ",
            "∀ relation ∈ Γ.relations, relation.Nonempty",
        )
    )
    plans = plans_for(candidate)
    assert [plan.solver for plan in plans] == [
        "finite-reflection:not-schaefer-tractable",
        "finite-reflection:relations-nonempty",
    ]


def test_unknown_open_premise_is_not_claimed_solved() -> None:
    assert plans_for(_candidate(("Example.UnknownPremise",))) == ()


def test_schema_detection_does_not_depend_on_theorem_name() -> None:
    candidate = _candidate(
        (
            "∀ symbol : Γ.Symbol, (Γ.relationOf symbol).Nonempty",
            "¬ Γ.IsSchaeferTractable",
        )
    )
    assert candidate.declaration == "Example.hardSide"
    assert candidate.is_schaefer_schema is True
    assert len(plans_for(candidate)) == 2
