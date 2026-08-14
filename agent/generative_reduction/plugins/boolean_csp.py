"""Optional finite-reflection capabilities for Boolean CSP premises."""

from __future__ import annotations

from typing import Sequence

from ..models import PremiseKind, TheoremPremise
from ..premise_registry import PremiseSolution, PremiseSolverRegistry
from .registry import Plugin


def _is_decision_equality(text: str) -> bool:
    return (
        ("Decidable.decide" in text or "@decide" in text)
        and ("Bool.true" in text or "Bool.false" in text)
    )


def _is_negative_goal(text: str) -> bool:
    normalized = " ".join(text.split())
    return normalized.startswith(("¬", "Not ", "Not(")) or normalized.endswith(
        ("→ False", "-> False")
    )


class BooleanCSPFiniteReflectionSolver:
    name = "boolean-csp-finite-reflection"

    def supports(self, premise: TheoremPremise, local_context: Sequence[str]) -> float:
        if premise.kind != PremiseKind.PROPOSITION:
            return 0.0
        text = premise.exact_type
        if _is_decision_equality(text):
            return 1.0
        if ".Nonempty" in text:
            return 1.0
        if "IsSchaeferTractable" in text and _is_negative_goal(text):
            return 1.0
        if "PreservesComplement" in text:
            return 1.0
        return 0.0

    def propose(
        self, premise: TheoremPremise, local_context: Sequence[str]
    ) -> PremiseSolution | None:
        text = premise.exact_type
        if _is_decision_equality(text):
            return PremiseSolution(
                solver=self.name + ":decision-equality",
                proof_lines=("  · decide",),
                proof_term="by decide",
                confidence=1.0,
            )
        if ".Nonempty" in text:
            return PremiseSolution(
                solver=self.name + ":relations-nonempty",
                proof_lines=(
                    "  · apply ComplexityReduction.Agent.Reduction.Reflection."
                    "gammaRelationsNonempty_of_decide_eq_true",
                    "    decide",
                ),
                proof_term=None,
                confidence=1.0,
            )
        if "IsSchaeferTractable" in text and _is_negative_goal(text):
            return PremiseSolution(
                solver=self.name + ":hard-side",
                proof_lines=(
                    "  · apply ComplexityReduction.Agent.Reduction.Reflection."
                    "gammaNotSchaeferTractable_of_decide_eq_false",
                    "    decide",
                ),
                proof_term=None,
                confidence=1.0,
            )
        if "PreservesComplement" in text:
            negative = _is_negative_goal(text)
            theorem = (
                "gammaNotPreservesComplement_of_decide_eq_false"
                if negative
                else "gammaPreservesComplement_of_decide_eq_true"
            )
            return PremiseSolution(
                solver=self.name + (":not-complement" if negative else ":complement"),
                proof_lines=(
                    "  · apply ComplexityReduction.Agent.Reduction.Reflection." + theorem,
                    "    decide",
                ),
                proof_term=None,
                confidence=1.0,
            )
        return None


def _register(registry: PremiseSolverRegistry) -> None:
    registry.register(BooleanCSPFiniteReflectionSolver())


PLUGIN = Plugin(
    name="boolean_csp",
    register=_register,
    public_capabilities=(
        "finite relation nonemptiness reflection",
        "finite tractability-side reflection",
        "finite complement-closure reflection",
    ),
    lean_imports=(
        "ComplexityReduction.Agent.GenerativeReduction.Plugins.BooleanCSPReflection",
        # The wrapper exports the declarations for authored source, while the
        # typed index filters by declaration-owning module.  Include both so
        # exact open goals can retrieve and recursively apply the reflection
        # theorems instead of falling through to model synthesis.
        "ComplexityReduction.Agent.Reduction.Reflection",
    ),
)


__all__ = ["BooleanCSPFiniteReflectionSolver", "PLUGIN"]
