"""Optional finite-reflection capabilities for Boolean CSP premises."""

from __future__ import annotations

from typing import Sequence

from ..models import PremiseKind, TheoremPremise
from ..premise_registry import PremiseSolution, PremiseSolverRegistry
from .registry import Plugin


class BooleanCSPFiniteReflectionSolver:
    name = "boolean-csp-finite-reflection"

    def supports(self, premise: TheoremPremise, local_context: Sequence[str]) -> float:
        if premise.kind != PremiseKind.PROPOSITION:
            return 0.0
        text = premise.exact_type
        if ".Nonempty" in text:
            return 1.0
        if "IsSchaeferTractable" in text:
            return 1.0
        return 0.0

    def propose(
        self, premise: TheoremPremise, local_context: Sequence[str]
    ) -> PremiseSolution | None:
        text = premise.exact_type
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
        if "IsSchaeferTractable" in text:
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
        return None


def _register(registry: PremiseSolverRegistry) -> None:
    registry.register(BooleanCSPFiniteReflectionSolver())


PLUGIN = Plugin(
    name="boolean_csp",
    register=_register,
    public_capabilities=(
        "finite relation nonemptiness reflection",
        "finite tractability-side reflection",
    ),
    lean_imports=(
        "ComplexityReduction.Agent.GenerativeReduction.Plugins.BooleanCSPReflection",
    ),
)


__all__ = ["BooleanCSPFiniteReflectionSolver", "PLUGIN"]
