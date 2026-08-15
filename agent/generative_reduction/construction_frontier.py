"""Nested beam frontier for one scheduled synthesis action."""

from __future__ import annotations

import heapq
from itertools import count

from .synthesis.designs import SynthesisDesign


class ConstructionFrontier:
    def __init__(self, *, contract_id: str, beam_width: int):
        if beam_width < 1:
            raise ValueError("construction beam width must be positive")
        self.contract_id = contract_id
        self.beam_width = beam_width
        self._counter = count()
        self._heap: list[tuple[tuple[object, ...], int, SynthesisDesign]] = []
        self._ids: set[str] = set()

    def __len__(self) -> int:
        return len(self._heap)

    @staticmethod
    def _cost(design: SynthesisDesign) -> tuple[object, ...]:
        progress_rank = {
            "verified": 0,
            "materializing": 1,
            "context-ready": 2,
            "designed": 2,
            "planned": 3,
            "repairing": 4,
            "lean-failed": 4,
            "failed": 5,
            "abandoned": 6,
        }.get(design.status, 6)
        return (
            progress_rank,
            len(design.residual_obligations),
            design.estimated_cost,
            design.materialization_attempts,
            design.repair_attempts,
            design.design_id,
        )

    def push(self, design: SynthesisDesign) -> bool:
        if design.contract_id != self.contract_id:
            raise ValueError("design belongs to a different construction contract")
        if design.design_id in self._ids:
            return False
        self._ids.add(design.design_id)
        heapq.heappush(self._heap, (self._cost(design), next(self._counter), design))
        if len(self._heap) > self.beam_width:
            worst = max(range(len(self._heap)), key=lambda index: self._heap[index][:2])
            _, _, removed = self._heap.pop(worst)
            self._ids.discard(removed.design_id)
            heapq.heapify(self._heap)
        return True

    def pop(self) -> SynthesisDesign:
        if not self._heap:
            raise LookupError("construction frontier is empty")
        _, _, design = heapq.heappop(self._heap)
        self._ids.discard(design.design_id)
        return design

    def snapshot(self) -> tuple[SynthesisDesign, ...]:
        return tuple(item[2] for item in sorted(self._heap))


__all__ = ["ConstructionFrontier"]
