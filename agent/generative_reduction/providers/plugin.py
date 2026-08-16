from __future__ import annotations

from typing import Sequence

from ..finite_synthesis import FiniteSynthesisPlugin
from ..models import (
    ActionDisposition,
    CandidateAction,
    ConstructionContract,
    OpenGoal,
    ProviderKind,
    stable_sha256,
)


class PluginActionProvider:
    kind = ProviderKind.PLUGIN

    def __init__(self, plugins: Sequence[FiniteSynthesisPlugin] = ()) -> None:
        self.plugins = tuple(plugins)

    def actions(
        self,
        goal: OpenGoal,
        contract: ConstructionContract | None,
        *,
        limit: int,
    ) -> tuple[CandidateAction, ...]:
        actions: list[CandidateAction] = []
        for plugin in self.plugins:
            receipt = plugin.supports(goal)
            if not receipt.supported:
                continue
            digest = stable_sha256(
                {
                    "goal": goal.key.fingerprint,
                    "plugin": plugin.name,
                    "support": receipt.receipt_hash,
                }
            )
            design_id = (
                "design-plugin-" + digest.removeprefix("sha256:")[:16]
            )
            candidate_class = str(
                getattr(plugin, "candidate_class", "finite-enumeration")
            )
            authoritative = bool(
                getattr(plugin, "authoritative_typed_compiler", False)
            )
            actions.append(
                CandidateAction(
                    action_id="plugin-" + digest.removeprefix("sha256:")[:20],
                    provider=self.kind,
                    disposition=ActionDisposition.SYNTHESIS_REQUIRED,
                    goal_key=goal.key,
                    estimated_cost=max(0.25, 1.25 - receipt.confidence),
                    contract_id=(contract.contract_id if contract else None),
                    provenance=f"capability-synthesis-plugin:{plugin.name}",
                    metadata={
                        "plugin_name": plugin.name,
                        "design_id": design_id,
                        "design_kind": candidate_class,
                        "candidate_class": candidate_class,
                        "authoritative_typed_compiler": authoritative,
                        "constructibility_score": receipt.confidence,
                        "support_receipt": {
                            "plugin": receipt.plugin,
                            "supported": receipt.supported,
                            "confidence": receipt.confidence,
                            "reason": receipt.reason,
                            "goal_fingerprint": receipt.goal_fingerprint,
                            "witness_grammar": receipt.witness_grammar,
                            "receipt_hash": receipt.receipt_hash,
                        },
                    },
                )
            )
        return tuple(actions[:limit])


__all__ = ["PluginActionProvider"]
