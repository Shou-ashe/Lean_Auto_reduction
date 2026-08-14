from __future__ import annotations

from dataclasses import dataclass

from .backward import BackwardSemanticState
from .forward import ForwardSemanticState
from .invariants import InvariantCandidate


@dataclass(frozen=True)
class SemanticMeeting:
    invariant: InvariantCandidate
    intermediate_representation: str | None
    forward_construction: tuple[str, ...]
    backward_decoding: tuple[str, ...]
    local_obligations: tuple[str, ...]
    global_obligations: tuple[str, ...]
    complexity_obligations: tuple[str, ...]


def meet(
    forward: ForwardSemanticState,
    backward: BackwardSemanticState,
    invariant: InvariantCandidate,
) -> SemanticMeeting | None:
    forward_known = set(forward.preserved_invariants) | set(
        forward.source_observation.computable_features
    )
    backward_needed = set(backward.soundness_requirements) | set(
        backward.completeness_requirements
    )
    if invariant.statement not in forward_known and backward_needed:
        return None
    intermediate = (
        forward.candidate_intermediates[0]
        if forward.candidate_intermediates
        else None
    )
    return SemanticMeeting(
        invariant=invariant,
        intermediate_representation=intermediate,
        forward_construction=forward.proposed_projections,
        backward_decoding=backward.witness_recovery,
        local_obligations=tuple(sorted(backward_needed - forward_known)),
        global_obligations=backward.invalid_output_exclusions,
        complexity_obligations=("prove the selected construction is polynomial",),
    )


__all__ = ["SemanticMeeting", "meet"]
