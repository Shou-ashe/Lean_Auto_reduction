from __future__ import annotations

from dataclasses import replace

from .designs import SynthesisDesign


def direct_program_design(design: SynthesisDesign, *, declaration: str) -> SynthesisDesign:
    return replace(
        design,
        mode="direct-synthesis",
        design_kind="direct-authoring",
        declarations=(*design.declarations, declaration),
        stage="designed",
        status="designed",
        estimated_cost=design.estimated_cost + 1.0,
    )


__all__ = ["direct_program_design"]
