from __future__ import annotations

from ..models import QualificationStatus


def mutation_not_run() -> QualificationStatus:
    return QualificationStatus.NOT_RUN


__all__ = ["mutation_not_run"]
