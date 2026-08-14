from __future__ import annotations

from typing import Sequence

from ..models import TheoremPremise
from ..premise_registry import PremiseSolution


class LocalContextSolver:
    name = "local-context"

    def supports(self, premise: TheoremPremise, local_context: Sequence[str]) -> float:
        return 1.0 if premise.exact_type in local_context else 0.0

    def propose(
        self, premise: TheoremPremise, local_context: Sequence[str]
    ) -> PremiseSolution | None:
        if self.supports(premise, local_context) <= 0:
            return None
        return PremiseSolution(self.name, ("  · assumption",), "by assumption", 1.0)
