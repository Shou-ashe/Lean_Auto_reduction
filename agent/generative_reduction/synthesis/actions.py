from __future__ import annotations

from ..models import ConstructionContract
from .designs import SynthesisDesign


def designs_for(contract: ConstructionContract, *, limit: int) -> tuple[SynthesisDesign, ...]:
    return tuple(
        SynthesisDesign.for_contract(contract, mode=mode)
        for mode in contract.allowed_construction_modes[:limit]
    )


__all__ = ["designs_for"]
