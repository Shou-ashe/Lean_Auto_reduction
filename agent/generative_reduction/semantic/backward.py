from __future__ import annotations

from dataclasses import dataclass

from .observations import TargetObservation


@dataclass(frozen=True)
class BackwardSemanticState:
    target_observation: TargetObservation
    soundness_requirements: tuple[str, ...] = ()
    completeness_requirements: tuple[str, ...] = ()
    witness_recovery: tuple[str, ...] = ()
    representation_requirements: tuple[str, ...] = ()
    invalid_output_exclusions: tuple[str, ...] = ()
    candidate_invariants: tuple[str, ...] = ()


__all__ = ["BackwardSemanticState"]
