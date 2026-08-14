"""Global best-first frontier and provider-aware action scheduling."""

from __future__ import annotations

import heapq
from itertools import count
from typing import Iterable

from .models import ActionDisposition, CandidateAction, ProviderKind, Strategy
from .proof_state import ProofState
from .ranking import action_cost, proof_state_cost


class GlobalProofFrontier:
    def __init__(self, *, max_width: int):
        if max_width < 1:
            raise ValueError("frontier width must be positive")
        self.max_width = max_width
        self._counter = count()
        self._heap: list[tuple[tuple[object, ...], int, ProofState]] = []
        self._fingerprints: set[str] = set()
        self._seen_fingerprints: set[str] = set()

    def __len__(self) -> int:
        return len(self._heap)

    def push(self, state: ProofState) -> bool:
        fingerprint = state.fingerprint
        if fingerprint in self._seen_fingerprints:
            return False
        self._fingerprints.add(fingerprint)
        self._seen_fingerprints.add(fingerprint)
        heapq.heappush(self._heap, (proof_state_cost(state), next(self._counter), state))
        if len(self._heap) > self.max_width:
            worst = max(range(len(self._heap)), key=lambda index: self._heap[index][:2])
            _, _, removed = self._heap.pop(worst)
            self._fingerprints.discard(removed.fingerprint)
            heapq.heapify(self._heap)
        return True

    def pop(self) -> ProofState:
        if not self._heap:
            raise LookupError("global proof frontier is empty")
        _, _, state = heapq.heappop(self._heap)
        self._fingerprints.discard(state.fingerprint)
        return state

    def snapshot(self) -> tuple[ProofState, ...]:
        return tuple(item[2] for item in sorted(self._heap))


class ReadyActionBuckets:
    """Scheduling views over actions from one SubstepPlan.

    These buckets intentionally contain no ProofState, checkpoint, backtracking
    stack, or success flag.
    """

    def __init__(self, actions: Iterable[CandidateAction] = ()):
        self._buckets: dict[ProviderKind, list[CandidateAction]] = {
            kind: [] for kind in ProviderKind
        }
        self._cursor = 0
        for action in actions:
            self.add(action)

    def add(self, action: CandidateAction) -> None:
        bucket = self._buckets[action.provider]
        if any(existing.action_id == action.action_id for existing in bucket):
            return
        bucket.append(action)
        bucket.sort(key=action_cost)

    def counts(self) -> dict[str, int]:
        return {kind.value: len(bucket) for kind, bucket in self._buckets.items()}

    def _take(self, provider: ProviderKind) -> CandidateAction | None:
        bucket = self._buckets[provider]
        return bucket.pop(0) if bucket else None

    def choose(
        self,
        *,
        strategy: Strategy,
        non_synthesis_expansions: int,
        synthesis_activation_deadline: int,
    ) -> CandidateAction | None:
        closed = sorted(
            (
                action
                for bucket in self._buckets.values()
                for action in bucket
                if action.disposition == ActionDisposition.CLOSED
                and action.lean_verified
            ),
            key=action_cost,
        )
        if closed:
            selected = closed[0]
            self._buckets[selected.provider].remove(selected)
            return selected

        synthesis_ready = bool(self._buckets[ProviderKind.SYNTHESIS])
        if strategy == Strategy.SYNTHESIS_REQUIRED and synthesis_ready:
            return self._take(ProviderKind.SYNTHESIS)
        if synthesis_ready and non_synthesis_expansions >= synthesis_activation_deadline:
            return self._take(ProviderKind.SYNTHESIS)

        schedule = (
            (ProviderKind.REUSE, ProviderKind.THEOREM, ProviderKind.SYNTHESIS)
            if strategy == Strategy.BALANCED
            else (
                ProviderKind.REUSE,
                ProviderKind.THEOREM,
                ProviderKind.THEOREM,
                ProviderKind.SYNTHESIS,
            )
        )
        for offset in range(len(schedule)):
            index = (self._cursor + offset) % len(schedule)
            provider = schedule[index]
            action = self._take(provider)
            if action is not None:
                self._cursor = (index + 1) % len(schedule)
                return action
        return None


__all__ = ["GlobalProofFrontier", "ReadyActionBuckets"]
