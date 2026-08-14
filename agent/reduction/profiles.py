"""Validation profiles for the NP-hard-first core."""

from __future__ import annotations

from dataclasses import dataclass


PROFILE_NAMES = ("research", "strict-release", "benchmark")


@dataclass(frozen=True)
class ReductionProfile:
    name: str
    independent_replay: bool
    dependency_receipts: bool
    benchmark_audits: bool


PROFILES = {
    "research": ReductionProfile(
        name="research",
        independent_replay=False,
        dependency_receipts=False,
        benchmark_audits=False,
    ),
    "strict-release": ReductionProfile(
        name="strict-release",
        independent_replay=True,
        dependency_receipts=True,
        benchmark_audits=False,
    ),
    "benchmark": ReductionProfile(
        name="benchmark",
        independent_replay=True,
        dependency_receipts=True,
        benchmark_audits=True,
    ),
}


def get_profile(name: str) -> ReductionProfile:
    try:
        return PROFILES[name]
    except KeyError as error:
        raise ValueError(f"unsupported reduction profile: {name!r}") from error

