"""Model strategy proposals over opaque, typed planner actions."""

from __future__ import annotations

import hashlib
import json
from typing import Sequence

from agent.hardness.model_client import extract_json_object

from ..models import CandidateAction, ModelCallRecord, OpenGoal, SubstepPlan
from .protocol import JSONModel, StrategyProposal


ALLOWED_ACTIONS = {
    "select_action",
    "retrieve",
    "propose_helper",
    "propose_intermediate",
    "propose_invariant",
    "backtrack",
    "stop_with_blocker",
}


def propose_strategy(
    *, model: JSONModel, goal: OpenGoal, plan: SubstepPlan
) -> tuple[StrategyProposal | None, ModelCallRecord]:
    allowed = {action.action_id: action for action in plan.candidate_actions}
    prompt = json.dumps(
        {
            "exact_goal": goal.exact_type,
            "actions": [
                {
                    "action_id": action.action_id,
                    "provider": action.provider.value,
                    "disposition": action.disposition.value,
                    "residual_obligation_count": len(action.residual_obligation_ids),
                    "construction_mode": action.metadata.get("construction_mode"),
                }
                for action in allowed.values()
            ],
            "required_output": {
                "action": "select_action|retrieve|propose_helper|propose_intermediate|"
                "propose_invariant|backtrack|stop_with_blocker",
                "action_id": "one supplied opaque ID or null",
                "reason": "short explanation",
            },
        },
        ensure_ascii=False,
    )
    response = model.complete_json(
        system=(
            "Choose only among typed opaque actions supplied by the caller. "
            "Never invent a theorem or claim a proof. Return one compact JSON object."
        ),
        prompt=prompt,
    )
    parsed = extract_json_object(response.content) if response.ok else None
    proposal = None
    error = response.error
    if isinstance(parsed, dict):
        action = parsed.get("action")
        action_id = parsed.get("action_id")
        reason = parsed.get("reason")
        valid_id = action_id is None or (
            isinstance(action_id, str) and action_id in allowed
        )
        if action in ALLOWED_ACTIONS and valid_id and isinstance(reason, str):
            proposal = StrategyProposal(action, action_id, reason, parsed)
        else:
            error = "model strategy proposal violated the opaque action protocol"
    elif response.ok:
        error = "model strategy response did not contain one JSON object"
    record = ModelCallRecord(
        purpose="strategy-proposal",
        called=response.called,
        ok=response.ok and proposal is not None,
        status_code=response.status_code,
        duration_seconds=response.duration_seconds,
        usage=response.usage,
        attempts=response.attempts,
        response_sha256=hashlib.sha256(response.content.encode("utf-8")).hexdigest(),
        error=error,
        proposal_id=(proposal.action_id if proposal else None),
    )
    return proposal, record


__all__ = ["ALLOWED_ACTIONS", "propose_strategy"]
