from __future__ import annotations

from ..models import (
    ActionDisposition,
    CandidateAction,
    ExactClosureResult,
    ProviderKind,
    stable_sha256,
)


def reuse_action_id(closure: ExactClosureResult) -> str:
    digest = stable_sha256(
        {
            "goal": closure.goal_key.fingerprint,
            "identity": (
                {"declaration": closure.declaration}
                if closure.declaration
                else {"proof_term": closure.proof_term}
            ),
        }
    )
    return f"reuse-{digest.removeprefix('sha256:')[:20]}"


class ReuseActionProvider:
    kind = ProviderKind.REUSE

    def actions(self, closure: ExactClosureResult) -> tuple[CandidateAction, ...]:
        if not closure.closed:
            return ()
        return (
            CandidateAction(
                action_id=reuse_action_id(closure),
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


__all__ = ["ReuseActionProvider", "reuse_action_id"]
