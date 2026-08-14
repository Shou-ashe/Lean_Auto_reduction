from __future__ import annotations

from typing import Sequence

from ..models import PremiseKind, TheoremPremise
from ..premise_registry import PremiseSolution


class TypeclassSolver:
    name = "typeclass"

    def supports(self, premise: TheoremPremise, local_context: Sequence[str]) -> float:
        return 0.9 if premise.kind == PremiseKind.TYPECLASS else 0.0

    def propose(
        self, premise: TheoremPremise, local_context: Sequence[str]
    ) -> PremiseSolution | None:
        if self.supports(premise, local_context) <= 0:
            return None
        return PremiseSolution(
            self.name, ("  · infer_instance",), "by infer_instance", 0.9
        )
