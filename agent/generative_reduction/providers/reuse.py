from __future__ import annotations

from ..models import (
    ActionDisposition,
    CandidateAction,
    ExactClosureResult,
    ProviderKind,
    stable_sha256,
)


class ReuseActionProvider:
    kind = ProviderKind.REUSE

    def actions(self, closure: ExactClosureResult) -> tuple[CandidateAction, ...]:
        if not closure.closed:
            return ()
        digest = stable_sha256(
            {
                "goal": closure.goal_key.fingerprint,
                "declaration": closure.declaration,
                "proof_term": closure.proof_term,
            }
        )
        return (
            CandidateAction(
                action_id=f"reuse-{digest.removeprefix('sha256:')[:20]}",
                provider=self.kind,
                disposition=ActionDisposition.CLOSED,
                goal_key=closure.goal_key,
                estimated_cost=0.0,
                declaration=closure.declaration,
                proof_term=closure.proof_term,
                provenance=closure.provenance or "environment",
                lean_verified=closure.lean_verified,
            ),
        )


__all__ = ["ReuseActionProvider"]
