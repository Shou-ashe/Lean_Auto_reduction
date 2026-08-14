from __future__ import annotations

from typing import Sequence

from ..models import GoalKind, TheoremPremise
from ..premise_registry import PremiseSolution, goal_kind_for_premise


class ReductionGraphSolver:
    name = "reduction-graph"

    def supports(self, premise: TheoremPremise, local_context: Sequence[str]) -> float:
        return (
            0.35
            if goal_kind_for_premise(premise)
            in {GoalKind.HARDNESS, GoalKind.COMPLETENESS, GoalKind.REDUCTION, GoalKind.PATH}
            else 0.0
        )

    def propose(
        self, premise: TheoremPremise, local_context: Sequence[str]
    ) -> PremiseSolution | None:
        # A graph subgoal must re-enter the global planner; it is not closed here.
        return None
