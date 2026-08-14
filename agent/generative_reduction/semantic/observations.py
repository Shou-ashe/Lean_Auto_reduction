from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class SourceObservation:
    endpoint: str
    constructors: tuple[str, ...] = ()
    computable_features: tuple[str, ...] = ()
    available_witnesses: tuple[str, ...] = ()
    representation_constraints: tuple[str, ...] = ()


@dataclass(frozen=True)
class TargetObservation:
    endpoint: str
    acceptance_requirements: tuple[str, ...] = ()
    witness_requirements: tuple[str, ...] = ()
    representation_constraints: tuple[str, ...] = ()


__all__ = ["SourceObservation", "TargetObservation"]
