from __future__ import annotations

from typing import Sequence

from ..models import GoalKind, TheoremPremise
from ..premise_registry import PremiseSolution, goal_kind_for_premise


class PolynomialCombinatorSolver:
    name = "polynomial-combinator"

    def supports(self, premise: TheoremPremise, local_context: Sequence[str]) -> float:
        return 0.45 if goal_kind_for_premise(premise) == GoalKind.COMPLEXITY else 0.0

    def propose(
        self, premise: TheoremPremise, local_context: Sequence[str]
    ) -> PremiseSolution | None:
        # Combinator retrieval is represented as theorem guidance, not an unchecked tactic.
        return None
