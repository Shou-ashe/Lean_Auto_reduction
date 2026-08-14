"""Problem-family-independent rules derived from certificate types."""

from __future__ import annotations

from dataclasses import dataclass

from .models import GoalKind


@dataclass(frozen=True)
class Rule:
    name: str
    conclusion_kind: GoalKind
    premise_kinds: tuple[GoalKind, ...]
    lean_declaration: str | None
    base_cost: float


RULES = (
    Rule("exact-hardness", GoalKind.HARDNESS, (), None, 0.0),
    Rule(
        "completeness-projection",
        GoalKind.HARDNESS,
        (GoalKind.COMPLETENESS,),
        "ComplexityReduction.Certificate.NativeTMNPComplete.nativeHardness",
        0.25,
    ),
    Rule(
        "hardness-along-path",
        GoalKind.HARDNESS,
        (GoalKind.HARDNESS, GoalKind.PATH),
        "ComplexityReduction.Certificate.NativeTMNPHard.alongPath",
        1.0,
    ),
    Rule(
        "completeness-along-path",
        GoalKind.HARDNESS,
        (GoalKind.COMPLETENESS, GoalKind.PATH),
        "ComplexityReduction.Certificate.NativeTMNPHard.ofCompleteAlongPath",
        1.0,
    ),
    Rule(
        "reduction-step",
        GoalKind.PATH,
        (GoalKind.REDUCTION,),
        "ComplexityReduction.Certificate.CertifiedPath.step",
        0.5,
    ),
    Rule(
        "path-composition",
        GoalKind.PATH,
        (GoalKind.PATH, GoalKind.PATH),
        "ComplexityReduction.Certificate.CertifiedPath.append",
        1.0,
    ),
    Rule(
        "reduction-composition",
        GoalKind.REDUCTION,
        (GoalKind.REDUCTION, GoalKind.REDUCTION),
        "ComplexityReduction.Certificate.CertifiedReduction.comp",
        1.0,
    ),
    Rule(
        "equivalence-forward",
        GoalKind.REDUCTION,
        (GoalKind.EQUIVALENCE,),
        "ComplexityReduction.Certificate.CertifiedEquiv.forwardReduction",
        0.5,
    ),
    Rule(
        "presentation-forward",
        GoalKind.REDUCTION,
        (GoalKind.PRESENTATION,),
        "ComplexityReduction.Certificate.CertifiedPresentationChange.forwardReduction",
        0.5,
    ),
    Rule(
        "reduction-assembly",
        GoalKind.REDUCTION,
        (GoalKind.PROGRAM, GoalKind.SEMANTICS),
        None,
        3.0,
    ),
)


def rules_for(kind: GoalKind) -> tuple[Rule, ...]:
    return tuple(rule for rule in RULES if rule.conclusion_kind == kind)


__all__ = ["RULES", "Rule", "rules_for"]
