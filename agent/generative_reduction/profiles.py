"""Orthogonal proof-search strategies and verification profiles."""

from __future__ import annotations

from dataclasses import dataclass


PROFILE_NAMES = ("research", "strict-release", "benchmark")


@dataclass(frozen=True)
class VerificationProfile:
    name: str
    independent_replay: bool
    dependency_receipts: bool
    full_axiom_provenance: bool
    benchmark_qualification: bool
    mutation_qualification: bool


PROFILES = {
    "research": VerificationProfile(
        name="research",
        independent_replay=False,
        dependency_receipts=False,
        full_axiom_provenance=False,
        benchmark_qualification=False,
        mutation_qualification=False,
    ),
    "strict-release": VerificationProfile(
        name="strict-release",
        independent_replay=True,
        dependency_receipts=True,
        full_axiom_provenance=True,
        benchmark_qualification=False,
        mutation_qualification=False,
    ),
    "benchmark": VerificationProfile(
        name="benchmark",
        independent_replay=True,
        dependency_receipts=True,
        full_axiom_provenance=True,
        benchmark_qualification=True,
        mutation_qualification=True,
    ),
}


def get_profile(name: str) -> VerificationProfile:
    try:
        return PROFILES[name]
    except KeyError as error:
        raise ValueError(f"unsupported general reduction profile: {name!r}") from error


__all__ = ["PROFILE_NAMES", "PROFILES", "VerificationProfile", "get_profile"]
