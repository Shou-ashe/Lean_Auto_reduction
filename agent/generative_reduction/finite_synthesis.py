"""Typed protocol for proof-producing finite witness synthesis plugins.

Executable checks are search filters, never proof authority.  A materialized
candidate becomes a capability only after the generic runtime independently
elaborates it with Lean and applies the normal axiom/source/route fences.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping, Protocol, Sequence

from .models import OpenGoal, stable_sha256


@dataclass(frozen=True)
class FiniteSupportReceipt:
    plugin: str
    supported: bool
    confidence: float
    reason: str
    goal_fingerprint: str
    witness_grammar: str
    receipt_hash: str

    @classmethod
    def create(
        cls,
        *,
        plugin: str,
        goal: OpenGoal,
        supported: bool,
        confidence: float,
        reason: str,
        witness_grammar: str,
    ) -> "FiniteSupportReceipt":
        payload = {
            "plugin": plugin,
            "goal": goal.key.fingerprint,
            "supported": supported,
            "confidence": confidence,
            "reason": reason,
            "witness_grammar": witness_grammar,
        }
        return cls(
            plugin=plugin,
            supported=supported,
            confidence=max(0.0, min(1.0, confidence)),
            reason=reason,
            goal_fingerprint=goal.key.fingerprint,
            witness_grammar=witness_grammar,
            receipt_hash=stable_sha256(payload),
        )


@dataclass(frozen=True)
class FiniteCandidateWitness:
    witness_id: str
    implementation: str
    imports: tuple[str, ...]
    executable_status: str
    check_receipt: Mapping[str, object]
    counterexample: Mapping[str, object] | None = None


class FiniteSynthesisPlugin(Protocol):
    name: str

    def supports(self, goal: OpenGoal) -> FiniteSupportReceipt: ...

    def enumerate(
        self,
        goal: OpenGoal,
        *,
        declaration_name: str,
        limit: int,
        counterexamples: Sequence[Mapping[str, object]] = (),
    ) -> Sequence[FiniteCandidateWitness]: ...


__all__ = [
    "FiniteCandidateWitness",
    "FiniteSupportReceipt",
    "FiniteSynthesisPlugin",
]
