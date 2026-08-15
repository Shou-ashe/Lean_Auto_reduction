"""Merge the three action-provider views for one global proof state."""

from __future__ import annotations

from .finite_synthesis import FiniteSynthesisPlugin
from .models import ConstructionContract, ExactClosureResult, OpenGoal, ProofGuidance
from .providers import (
    PluginActionProvider,
    ReuseActionProvider,
    StructuralActionProvider,
    SynthesisActionProvider,
    TheoremActionProvider,
)
from .ranking import action_cost


class ActionProviders:
    def __init__(self, finite_plugins: tuple[FiniteSynthesisPlugin, ...] = ()) -> None:
        self.reuse = ReuseActionProvider()
        self.structural = StructuralActionProvider()
        self.plugin = PluginActionProvider(finite_plugins)
        self.theorem = TheoremActionProvider()
        self.synthesis = SynthesisActionProvider()

    def collect(
        self,
        *,
        goal: OpenGoal,
        closure: ExactClosureResult,
        guidance: tuple[ProofGuidance, ...],
        contract: ConstructionContract | None,
        max_actions_per_provider: int,
    ):
        structural = self.structural.actions(
            goal, guidance, contract, limit=max_actions_per_provider
        )
        structural_declarations = {
            action.declaration for action in structural if action.declaration
        }
        theorem = tuple(
            action
            for action in self.theorem.actions(guidance)[:max_actions_per_provider]
            if action.declaration not in structural_declarations
        )
        plugin = (
            ()
            if structural
            else self.plugin.actions(
                goal, contract, limit=max_actions_per_provider
            )
        )
        actions = (
            *self.reuse.actions(closure)[:max_actions_per_provider],
            *structural,
            *plugin,
            *theorem,
            *self.synthesis.actions(
                contract,
                limit=max_actions_per_provider,
                structural_available=bool(structural),
            ),
        )
        unique = {action.action_id: action for action in actions}
        return tuple(sorted(unique.values(), key=action_cost))


__all__ = ["ActionProviders"]
