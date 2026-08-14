from __future__ import annotations

from dataclasses import dataclass

from .observations import SourceObservation


@dataclass(frozen=True)
class ForwardSemanticState:
    source_observation: SourceObservation
    proposed_projections: tuple[str, ...] = ()
    preserved_invariants: tuple[str, ...] = ()
    candidate_intermediates: tuple[str, ...] = ()
    reusable_primitives: tuple[str, ...] = ()
    estimated_program_cost: float = 0.0


def expand_forward(
    state: ForwardSemanticState,
    *,
    invariant: str | None = None,
    intermediate: str | None = None,
) -> ForwardSemanticState:
    return ForwardSemanticState(
        source_observation=state.source_observation,
        proposed_projections=state.proposed_projections,
        preserved_invariants=(
            state.preserved_invariants
            if invariant is None
            else (*state.preserved_invariants, invariant)
        ),
        candidate_intermediates=(
            state.candidate_intermediates
            if intermediate is None
            else (*state.candidate_intermediates, intermediate)
        ),
        reusable_primitives=state.reusable_primitives,
        estimated_program_cost=state.estimated_program_cost + 1.0,
    )


__all__ = ["ForwardSemanticState", "expand_forward"]
