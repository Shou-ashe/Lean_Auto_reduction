from __future__ import annotations

from ..models import (
    ActionDisposition,
    CandidateAction,
    ConstructionContract,
    ProviderKind,
    stable_sha256,
)


class SynthesisActionProvider:
    kind = ProviderKind.SYNTHESIS

    def actions(
        self, contract: ConstructionContract | None, *, limit: int
    ) -> tuple[CandidateAction, ...]:
        if contract is None:
            return ()
        actions: list[CandidateAction] = []
        for ordinal, mode in enumerate(contract.allowed_construction_modes[:limit]):
            digest = stable_sha256(
                {
                    "goal": contract.goal_key.fingerprint,
                    "mode": mode,
                    "ordinal": ordinal,
                }
            )
            actions.append(
                CandidateAction(
                    action_id=f"synthesis-{digest.removeprefix('sha256:')[:20]}",
                    provider=self.kind,
                    disposition=ActionDisposition.SYNTHESIS_REQUIRED,
                    goal_key=contract.goal_key,
                    estimated_cost=5.0 + ordinal,
                    contract_id=contract.contract_id,
                    residual_obligation_ids=tuple(
                        item.obligation_id for item in contract.residual_obligations
                    ),
                    provenance="job-local-planned",
                    metadata={"construction_mode": mode},
                )
            )
        return tuple(actions)


__all__ = ["SynthesisActionProvider"]
