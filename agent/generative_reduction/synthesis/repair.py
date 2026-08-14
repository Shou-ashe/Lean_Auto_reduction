from __future__ import annotations

from dataclasses import replace

from .designs import SynthesisDesign


def record_diagnostic(design: SynthesisDesign, diagnostic: str) -> SynthesisDesign:
    return replace(
        design,
        diagnostics=(*design.diagnostics, diagnostic[-4000:]),
        status="repair-required",
        estimated_cost=design.estimated_cost + 0.5,
    )


__all__ = ["record_diagnostic"]
