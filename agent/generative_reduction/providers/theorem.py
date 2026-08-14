from __future__ import annotations

from typing import Sequence

from ..models import (
    ActionDisposition,
    CandidateAction,
    ProofGuidance,
    ProviderKind,
    stable_sha256,
)


class TheoremActionProvider:
    kind = ProviderKind.THEOREM

    def actions(self, guidance: Sequence[ProofGuidance]) -> tuple[CandidateAction, ...]:
        actions: list[CandidateAction] = []
        for plan in guidance:
            digest = stable_sha256(
                {"goal": plan.goal_key.fingerprint, "guidance": plan.guidance_id}
            )
            actions.append(
                CandidateAction(
                    action_id=f"theorem-{digest.removeprefix('sha256:')[:20]}",
                    provider=self.kind,
                    disposition=ActionDisposition.DECOMPOSED,
                    goal_key=plan.goal_key,
                    estimated_cost=plan.estimated_cost,
                    declaration=plan.candidate_declaration,
                    guidance_id=plan.guidance_id,
                    residual_obligation_ids=tuple(
                        item.obligation_id for item in plan.residual_obligations
                    ),
                    provenance=plan.declaration_provenance,
                    lean_verified=False,
                )
            )
        return tuple(actions)


__all__ = ["TheoremActionProvider"]
