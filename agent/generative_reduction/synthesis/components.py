from __future__ import annotations

from dataclasses import dataclass, replace

from ..models import stable_sha256
from .designs import SynthesisDesign


@dataclass(frozen=True)
class LocalReductionComponent:
    component_id: str
    source_fragment: str
    target_fragment: str
    constructor: str | None
    interface: tuple[str, ...]
    local_invariant: str
    soundness_goal: str
    completeness_goal: str
    size_bound_goal: str
    composition_contract: str

    @classmethod
    def create(
        cls,
        *,
        source_fragment: str,
        target_fragment: str,
        local_invariant: str,
        soundness_goal: str,
        completeness_goal: str,
        size_bound_goal: str,
        composition_contract: str,
        constructor: str | None = None,
        interface: tuple[str, ...] = (),
    ) -> "LocalReductionComponent":
        digest = stable_sha256(
            {
                "source": source_fragment,
                "target": target_fragment,
                "invariant": local_invariant,
            }
        )
        return cls(
            component_id=f"component-{digest.removeprefix('sha256:')[:20]}",
            source_fragment=source_fragment,
            target_fragment=target_fragment,
            constructor=constructor,
            interface=interface,
            local_invariant=local_invariant,
            soundness_goal=soundness_goal,
            completeness_goal=completeness_goal,
            size_bound_goal=size_bound_goal,
            composition_contract=composition_contract,
        )


def attach_component(
    design: SynthesisDesign, component: LocalReductionComponent
) -> SynthesisDesign:
    return replace(
        design,
        mode="component-first",
        design_kind="helper-first",
        declarations=(*design.declarations, component.component_id),
        stage="designed",
        status="designed",
        estimated_cost=design.estimated_cost + 2.0,
    )


__all__ = ["LocalReductionComponent", "attach_component"]
