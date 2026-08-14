from __future__ import annotations

from typing import Sequence

from ..models import TheoremPremise
from ..premise_registry import PremiseSolution


class RecursiveTheoremSolver:
    name = "recursive-theorem"

    def supports(self, premise: TheoremPremise, local_context: Sequence[str]) -> float:
        return 0.1

    def propose(
        self, premise: TheoremPremise, local_context: Sequence[str]
    ) -> PremiseSolution | None:
        # Returning None deliberately keeps the exact proposition as a global open goal.
        return None
