from __future__ import annotations

from typing import Sequence

from ..models import GoalKind, PremiseKind, TheoremPremise
from ..premise_registry import PremiseSolution, goal_kind_for_premise


class BoundedLeanTacticSolver:
    name = "bounded-lean-tactic"

    def supports(self, premise: TheoremPremise, local_context: Sequence[str]) -> float:
        if premise.kind != PremiseKind.PROPOSITION:
            return 0.0
        return 0.15 if goal_kind_for_premise(premise) == GoalKind.PROPOSITION else 0.0

    def propose(
        self, premise: TheoremPremise, local_context: Sequence[str]
    ) -> PremiseSolution | None:
        if self.supports(premise, local_context) <= 0:
            return None
        return PremiseSolution(self.name, ("  · aesop",), "by aesop", 0.15)
