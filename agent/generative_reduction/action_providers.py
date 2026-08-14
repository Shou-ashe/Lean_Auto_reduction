"""Merge the three action-provider views for one global proof state."""

from __future__ import annotations

from .models import ConstructionContract, ExactClosureResult, ProofGuidance
from .providers import ReuseActionProvider, SynthesisActionProvider, TheoremActionProvider
from .ranking import action_cost


class ActionProviders:
    def __init__(self) -> None:
        self.reuse = ReuseActionProvider()
        self.theorem = TheoremActionProvider()
        self.synthesis = SynthesisActionProvider()

    def collect(
        self,
        *,
        closure: ExactClosureResult,
        guidance: tuple[ProofGuidance, ...],
        contract: ConstructionContract | None,
        max_actions_per_provider: int,
    ):
        actions = (
            *self.reuse.actions(closure)[:max_actions_per_provider],
            *self.theorem.actions(guidance)[:max_actions_per_provider],
            *self.synthesis.actions(
                contract, limit=max_actions_per_provider
            ),
        )
        unique = {action.action_id: action for action in actions}
        return tuple(sorted(unique.values(), key=action_cost))


__all__ = ["ActionProviders"]
