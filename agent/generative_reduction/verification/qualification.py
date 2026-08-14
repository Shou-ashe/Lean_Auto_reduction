"""Layer C: optional release/benchmark qualification."""

from __future__ import annotations

from ..models import QualificationStatus
from ..profiles import VerificationProfile


def initial_qualification_status(profile: VerificationProfile) -> QualificationStatus:
    if profile.name == "research":
        return QualificationStatus.NOT_REQUESTED
    return QualificationStatus.NOT_RUN


__all__ = ["initial_qualification_status"]
