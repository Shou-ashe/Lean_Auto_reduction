"""Stable ranking functions for proof states, guidance, and actions."""

from __future__ import annotations

from .models import ActionDisposition, CandidateAction, ProofGuidance, ProviderKind
from .proof_state import ProofState


def proof_state_cost(state: ProofState) -> tuple[object, ...]:
    unresolved_weight = sum(max(0.0, goal.estimated_cost) for goal in state.open_goals)
    residuals = sum(
        len(plan.residual_obligations) for plan in state.substep_plans[-4:]
    )
    return (
        len(state.open_goals),
        unresolved_weight,
        residuals,
        state.depth,
        state.total_cost,
        state.model_call_count,
        state.lean_check_count,
        len(state.generated_modules),
        state.state_id,
    )


def guidance_cost(guidance: ProofGuidance) -> tuple[object, ...]:
    return (
        len(guidance.residual_obligations),
        -guidance.coverage_score,
        guidance.estimated_cost,
        -guidance.confidence,
        guidance.candidate_declaration,
        guidance.guidance_id,
    )


def action_cost(action: CandidateAction) -> tuple[object, ...]:
    disposition_rank = {
        ActionDisposition.CLOSED: 0,
        ActionDisposition.DECOMPOSED: 1,
        ActionDisposition.SYNTHESIS_REQUIRED: 2,
        ActionDisposition.BLOCKED: 3,
    }[action.disposition]
    provider_rank = {
        ProviderKind.REUSE: 0,
        ProviderKind.THEOREM: 1,
        ProviderKind.SYNTHESIS: 2,
    }[action.provider]
    return (
        disposition_rank,
        action.estimated_cost,
        len(action.residual_obligation_ids),
        provider_rank,
        action.declaration or "",
        action.action_id,
    )


__all__ = ["action_cost", "guidance_cost", "proof_state_cost"]
