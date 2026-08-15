from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Protocol


class JSONModel(Protocol):
    def complete_json(self, *, system: str, prompt: str): ...


@dataclass(frozen=True)
class StrategyProposal:
    decision: str
    action_id: str | None
    design_id: str | None
    confidence: float
    reason: str
    raw: Mapping[str, Any]

    @property
    def action(self) -> str:
        """Compatibility alias for older callers and serialized fixtures."""

        return self.decision


@dataclass(frozen=True)
class AuthoringProposal:
    implementation: str | None
    reason: str
    raw: Mapping[str, Any]
    base_sha256: str | None = None
    changed_reason: str | None = None
    addressed_diagnostic_codes: tuple[str, ...] = ()


__all__ = ["AuthoringProposal", "JSONModel", "StrategyProposal"]
