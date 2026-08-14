from __future__ import annotations

import re
from typing import Sequence

from ..models import TheoremPremise
from ..premise_registry import PremiseSolution


REFLEXIVE_RE = re.compile(r"^\s*(.+?)\s*=\s*\1\s*$")


class DefinitionalSolver:
    name = "definitional"

    def supports(self, premise: TheoremPremise, local_context: Sequence[str]) -> float:
        return 0.95 if REFLEXIVE_RE.match(premise.exact_type) else 0.0

    def propose(
        self, premise: TheoremPremise, local_context: Sequence[str]
    ) -> PremiseSolution | None:
        if self.supports(premise, local_context) <= 0:
            return None
        return PremiseSolution(self.name, ("  · rfl",), "by rfl", 0.95)
