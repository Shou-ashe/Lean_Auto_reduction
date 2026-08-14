from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping, Protocol


class JSONModel(Protocol):
    def complete_json(self, *, system: str, prompt: str): ...


@dataclass(frozen=True)
class StrategyProposal:
    action: str
    action_id: str | None
    reason: str
    raw: Mapping[str, Any]


@dataclass(frozen=True)
class AuthoringProposal:
    implementation: str | None
    reason: str
    raw: Mapping[str, Any]


__all__ = ["AuthoringProposal", "JSONModel", "StrategyProposal"]
