"""Model strategy proposals over exact, typed planner consequences."""

from __future__ import annotations

import hashlib
import json
from typing import Sequence

from agent.hardness.model_client import extract_json_object

from ..models import (
    CandidateAction,
    ModelCallRecord,
    OpenGoal,
    StrategyDecision,
    SubstepPlan,
    stable_sha256,
)
from .protocol import JSONModel, StrategyProposal


ALLOWED_DECISIONS = {
    "select_action",
    "select_design",
    "backtrack",
}
# Compatibility export retained for callers that imported the old constant.
ALLOWED_ACTIONS = ALLOWED_DECISIONS


def _residual_types(plan: SubstepPlan, action: CandidateAction) -> list[str]:
    by_id = {item.obligation_id: item.exact_type for item in plan.residual_obligations}
    return [by_id[item] for item in action.residual_obligation_ids if item in by_id]


def propose_strategy(
    *,
    model: JSONModel,
    goal: OpenGoal,
    plan: SubstepPlan,
    actions: Sequence[CandidateAction] | None = None,
) -> tuple[StrategyProposal | None, ModelCallRecord]:
    executable = tuple(plan.candidate_actions if actions is None else actions)
    allowed = {action.action_id: action for action in executable}
    prompt = json.dumps(
        {
            "exact_goal": goal.exact_type,
            "goal_kind": goal.kind.value,
            "local_context": list(goal.local_context),
            "actions": [
                {
                    "action_id": action.action_id,
                    "provider": action.provider.value,
                    "disposition": action.disposition.value,
                    "declaration": action.declaration,
                    "exact_result_type": goal.exact_type,
                    "residual_obligation_types": _residual_types(plan, action),
                    "construction_mode": action.metadata.get("construction_mode"),
                    "design_id": action.metadata.get("design_id"),
                    "constructibility_score": action.metadata.get(
                        "constructibility_score"
                    ),
                    "estimated_cost": action.estimated_cost,
                    "cycle_risk": action.metadata.get("cycle_risk", "unknown"),
                    "prior_failure_code": action.metadata.get("prior_failure_code"),
                }
                for action in allowed.values()
            ],
            "required_output": {
                "decision": "select_action|select_design|backtrack",
                "action_id": "one supplied action ID or null",
                "design_id": "one supplied design ID or null",
                "confidence": "number from 0.0 to 1.0",
                "reason": "short explanation",
            },
        },
        ensure_ascii=False,
    )
    response = model.complete_json(
        system=(
            "Choose only among typed actions and designs supplied by the caller. "
            "Never invent a theorem, action, design, or proof. Backtrack only abandons "
            "the current branch. Return one compact JSON object."
        ),
        prompt=prompt,
    )
    parsed = extract_json_object(response.content) if response.ok else None
    proposal = None
    error = response.error
    if isinstance(parsed, dict):
        decision = parsed.get("decision", parsed.get("action"))
        action_id = parsed.get("action_id")
        design_id = parsed.get("design_id")
        confidence = parsed.get("confidence", 0.0)
        reason = parsed.get("reason")
        ids_well_formed = (
            (action_id is None or isinstance(action_id, str))
            and (design_id is None or isinstance(design_id, str))
        )
        confidence_well_formed = isinstance(confidence, (int, float)) and not isinstance(
            confidence, bool
        )
        if (
            decision in ALLOWED_DECISIONS
            and ids_well_formed
            and confidence_well_formed
            and isinstance(reason, str)
        ):
            proposal = StrategyProposal(
                decision=str(decision),
                action_id=action_id,
                design_id=design_id,
                confidence=max(0.0, min(1.0, float(confidence))),
                reason=reason,
                raw=parsed,
            )
        else:
            error = "model strategy proposal violated the typed decision protocol"
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
        proposal_id=(
            stable_sha256(proposal.raw).removeprefix("sha256:")[:24]
            if proposal
            else None
        ),
    )
    return proposal, record


def validate_strategy_proposal(
    *,
    proposal: StrategyProposal | None,
    state_fingerprint: str,
    goal: OpenGoal,
    actions: Sequence[CandidateAction],
    error: str | None = None,
) -> StrategyDecision:
    """Map a model response to one state-bound executable decision."""

    action_by_id = {action.action_id: action for action in actions}
    design_to_action = {
        str(action.metadata["design_id"]): action.action_id
        for action in actions
        if action.metadata.get("design_id")
    }
    proposal_hash = stable_sha256(proposal.raw if proposal else {"error": error})
    decision_id = "strategy-" + stable_sha256(
        {
            "state": state_fingerprint,
            "goal": goal.goal_id,
            "proposal": proposal_hash,
            "actions": sorted(action_by_id),
            "designs": sorted(design_to_action),
        }
    ).removeprefix("sha256:")[:20]
    if proposal is None:
        return StrategyDecision(
            decision_id=decision_id,
            goal_id=goal.goal_id,
            state_fingerprint=state_fingerprint,
            decision_kind="invalid",
            rationale=error or "strategy response did not yield a proposal",
            proposal_hash=proposal_hash,
            applicable=False,
        )

    selected_action_id = proposal.action_id
    selected_design_id = proposal.design_id
    applicable = False
    rationale = proposal.reason
    requested_backtrack = proposal.decision == "backtrack"
    if proposal.decision == "select_action":
        applicable = selected_action_id in action_by_id
        if not applicable:
            rationale = "strategy selected an unavailable action_id: " + rationale
    elif proposal.decision == "select_design":
        selected_action_id = design_to_action.get(selected_design_id or "")
        applicable = selected_action_id is not None
        if not applicable:
            rationale = "strategy selected an unavailable design_id: " + rationale
    elif requested_backtrack:
        applicable = True
        selected_action_id = None
        selected_design_id = None

    return StrategyDecision(
        decision_id=decision_id,
        goal_id=goal.goal_id,
        state_fingerprint=state_fingerprint,
        decision_kind=proposal.decision,
        selected_action_id=selected_action_id,
        selected_design_id=selected_design_id,
        requested_backtrack=requested_backtrack,
        rationale=rationale,
        confidence=proposal.confidence,
        proposal_hash=proposal_hash,
        applicable=applicable,
    )


__all__ = [
    "ALLOWED_ACTIONS",
    "ALLOWED_DECISIONS",
    "propose_strategy",
    "validate_strategy_proposal",
]
