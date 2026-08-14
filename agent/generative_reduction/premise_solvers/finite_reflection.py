from __future__ import annotations

import re
from typing import Sequence

from ..models import GoalKind, PremiseKind, TheoremPremise
from ..premise_registry import PremiseSolution, goal_kind_for_premise


class GenericFiniteReflectionSolver:
    name = "generic-finite-reflection"

    def supports(self, premise: TheoremPremise, local_context: Sequence[str]) -> float:
        if premise.kind not in {PremiseKind.PROPOSITION, PremiseKind.TYPECLASS}:
            return 0.0
        text = premise.exact_type
        if re.search(r"\b(?:Decidable|Fintype|Finite)\b", text):
            return 0.6
        if goal_kind_for_premise(premise) == GoalKind.PROPOSITION and "decide" in text:
            return 0.4
        return 0.0

    def propose(
        self, premise: TheoremPremise, local_context: Sequence[str]
    ) -> PremiseSolution | None:
        if self.supports(premise, local_context) <= 0:
            return None
        return PremiseSolution(self.name, ("  · decide",), "by decide", 0.6)
