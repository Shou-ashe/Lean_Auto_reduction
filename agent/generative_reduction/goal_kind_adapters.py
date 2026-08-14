"""Type-driven goal classification and construction-contract defaults."""

from __future__ import annotations

from .models import GoalKind


HEADS: tuple[tuple[str, GoalKind], ...] = (
    ("NativeTMNPHard", GoalKind.HARDNESS),
    ("NativeTMNPComplete", GoalKind.COMPLETENESS),
    ("CertifiedReduction", GoalKind.REDUCTION),
    ("CertifiedPath", GoalKind.PATH),
    ("CertifiedEquiv", GoalKind.EQUIVALENCE),
    ("CertifiedPresentationChange", GoalKind.PRESENTATION),
    ("LocalReductionComponent", GoalKind.COMPONENT),
    ("TMPolyTimeMap", GoalKind.COMPLEXITY),
    ("PolyProg", GoalKind.PROGRAM),
    ("Program.Primitive", GoalKind.PROGRAM),
)


def classify_goal(exact_type: str, *, premise_kind: str | None = None) -> GoalKind:
    if premise_kind == "typeclass":
        return GoalKind.TYPECLASS
    for marker, kind in HEADS:
        if marker in exact_type:
            return kind
    if "↔" in exact_type or "accepts" in exact_type or "Semantic" in exact_type:
        return GoalKind.SEMANTICS
    if exact_type.lstrip().startswith(("∀", "∃", "¬")) or any(
        token in exact_type for token in (" = ", " → ", " ∧ ", " ∨ ")
    ):
        return GoalKind.PROPOSITION
    return GoalKind.UNKNOWN


def construction_modes(kind: GoalKind) -> tuple[str, ...]:
    return {
        GoalKind.HARDNESS: ("intermediate-first", "direct-authoring"),
        GoalKind.REDUCTION: (
            "direct-synthesis",
            "component-first",
            "intermediate-first",
            "presentation-first",
        ),
        GoalKind.PATH: ("compose-path", "direct-synthesis", "intermediate-first"),
        GoalKind.PROGRAM: ("program-first", "compose-program"),
        GoalKind.SEMANTICS: ("spec-first", "program-first", "directional-proof"),
        GoalKind.COMPLEXITY: ("combinator-first", "direct-authoring"),
        GoalKind.COMPONENT: ("component-first", "direct-synthesis"),
        GoalKind.PRESENTATION: ("presentation-first", "direct-authoring"),
        GoalKind.PROPOSITION: ("apply-existing-theorem", "direct-authoring"),
    }.get(kind, ("open-candidate-module",))


def is_generation_eligible(kind: GoalKind) -> bool:
    return kind in {
        GoalKind.HARDNESS,
        GoalKind.REDUCTION,
        GoalKind.PATH,
        GoalKind.PROGRAM,
        GoalKind.SEMANTICS,
        GoalKind.COMPLEXITY,
        GoalKind.COMPONENT,
        GoalKind.PRESENTATION,
        GoalKind.PROPOSITION,
        GoalKind.UNKNOWN,
    }


__all__ = ["HEADS", "classify_goal", "construction_modes", "is_generation_eligible"]
