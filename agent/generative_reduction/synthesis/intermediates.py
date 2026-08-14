from __future__ import annotations

from dataclasses import replace

from .designs import SynthesisDesign


def with_intermediate(design: SynthesisDesign, declaration: str) -> SynthesisDesign:
    return replace(
        design,
        mode="intermediate-first",
        declarations=(*design.declarations, declaration),
        status="designed",
        estimated_cost=design.estimated_cost + 2.5,
    )


__all__ = ["with_intermediate"]
