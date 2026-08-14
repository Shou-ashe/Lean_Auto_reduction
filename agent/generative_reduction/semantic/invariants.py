from __future__ import annotations

from dataclasses import dataclass

from ..models import stable_sha256


@dataclass(frozen=True)
class InvariantCandidate:
    invariant_id: str
    statement: str
    forward_coverage: tuple[str, ...] = ()
    backward_coverage: tuple[str, ...] = ()
    estimated_cost: float = 1.0

    @classmethod
    def create(cls, statement: str, *, estimated_cost: float = 1.0) -> "InvariantCandidate":
        digest = stable_sha256({"statement": statement})
        return cls(
            invariant_id=f"invariant-{digest.removeprefix('sha256:')[:20]}",
            statement=statement,
            estimated_cost=estimated_cost,
        )


__all__ = ["InvariantCandidate"]
