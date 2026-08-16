"""Bounded best-first search over one global AND/OR proof frontier."""

from __future__ import annotations

from dataclasses import dataclass, replace
import time
from typing import Callable, Mapping, Sequence

from .budgets import BudgetExhausted, BudgetTracker
from .capability_planner import CapabilityPlanner
from .models import (
    CandidateAction,
    OpenGoal,
    ProviderKind,
    ProviderStatistics,
    Strategy,
    StrategyDecision,
    StrategyEffectReceipt,
    SubstepPlan,
    TheoremIndexEntry,
    stable_sha256,
)
from .proof_frontier import GlobalProofFrontier, ReadyActionBuckets
from .proof_state import ProofState


CandidateLookup = Callable[[ProofState, OpenGoal], Sequence[TheoremIndexEntry]]
ActionExecutor = Callable[
    [ProofState, OpenGoal, SubstepPlan, CandidateAction], Sequence[ProofState]
]
EventSink = Callable[[str, Mapping[str, object]], None]
DeadEndHandler = Callable[[ProofState, OpenGoal, str], ProofState | None]
StrategyDecider = Callable[
    [ProofState, OpenGoal, SubstepPlan, Sequence[CandidateAction]],
    StrategyDecision | None,
]


@dataclass(frozen=True)
class SearchOutcome:
    status: str
    best_state: ProofState
    completed_state: ProofState | None
    expanded_states: int
    blocker: str | None
    provider_statistics: Mapping[str, ProviderStatistics]
    requeued_failure_states: int = 0
    pruned_cycles: int = 0
    max_observed_depth: int = 0
    final_frontier_size: int = 0
    frontier_exhaustion_receipt: Mapping[str, object] | None = None
    strategy_valid_proposals: int = 0
    strategy_applied_decisions: int = 0
    strategy_fallbacks: int = 0
    strategy_rejections: int = 0
    strategy_effect_receipts: tuple[StrategyEffectReceipt, ...] = ()
    finite_candidate_count: int = 0
    finite_counterexample_count: int = 0
    finite_certificate_count: int = 0
    capability_compiler_candidate_count: int = 0
    capability_compiler_certificate_count: int = 0
    generated_lean_check_count: int = 0
    generated_lean_success_count: int = 0
    capability_registration_count: int = 0
    synthesis_design_count: int = 0
    context_expansion_count: int = 0
    duplicate_candidate_rejection_count: int = 0
    repeated_diagnostic_count: int = 0
    context_insufficient_count: int = 0
    unresolved_probe_handle_count: int = 0
    rejected_nonexecutable_design_count: int = 0


class SearchCoordinator:
    def __init__(
        self,
        *,
        planner: CapabilityPlanner,
        tracker: BudgetTracker,
        strategy: Strategy,
        environment_fingerprint: str,
        capability_fingerprint: Callable[[ProofState], str],
        candidate_lookup: CandidateLookup,
        action_executor: ActionExecutor,
        forbidden_declarations: Sequence[str] = (),
        event_sink: EventSink | None = None,
        dead_end_handler: DeadEndHandler | None = None,
        strategy_decider: StrategyDecider | None = None,
    ):
        self.planner = planner
        self.tracker = tracker
        self.strategy = strategy
        self.environment_fingerprint = environment_fingerprint
        self.capability_fingerprint = capability_fingerprint
        self.candidate_lookup = candidate_lookup
        self.action_executor = action_executor
        self.forbidden_declarations = tuple(forbidden_declarations)
        self.event_sink = event_sink
        self.dead_end_handler = dead_end_handler
        self.strategy_decider = strategy_decider
        self.statistics = {
            kind.value: ProviderStatistics() for kind in ProviderKind
        }
        self.requeued_failure_states = 0
        self.max_observed_depth = 0
        self.strategy_valid_proposals = 0
        self.strategy_applied_decisions = 0
        self.strategy_fallbacks = 0
        self.strategy_rejections = 0
        self.strategy_effect_receipts: list[StrategyEffectReceipt] = []

    @staticmethod
    def _progress_key(state: ProofState) -> tuple[object, ...]:
        return (
            int(state.complete),
            sum(frame.status.value == "verified" for frame in state.application_frames),
            len(state.generated_capabilities),
            len(state.verified_frame_fragments),
            state.data_binding_count,
            state.dependent_goal_activation_count,
            len(state.completed_fragments),
            state.depth,
            -len(state.open_goals),
        )

    def _more_progressed(self, candidate: ProofState, current: ProofState) -> ProofState:
        return (
            candidate
            if self._progress_key(candidate) > self._progress_key(current)
            else current
        )

    def _event(self, name: str, **details: object) -> None:
        if self.event_sink is not None:
            self.event_sink(name, details)

    @staticmethod
    def _ancestor_cycle_reason(
        state: ProofState,
        goal: OpenGoal,
        plan: SubstepPlan,
        action: CandidateAction,
    ) -> str | None:
        """Reject an action whose open residual recreates this ancestor chain."""

        if action.provider not in {ProviderKind.THEOREM, ProviderKind.STRUCTURAL}:
            return None

        def normalized(exact_type: str) -> str:
            return " ".join(exact_type.split())

        ancestor_types = {normalized(goal.exact_type): goal.goal_id}
        frame_id = goal.producer_frame_id
        seen: set[str] = set()
        while frame_id and frame_id not in seen:
            seen.add(frame_id)
            try:
                frame = state.frame(frame_id)
            except KeyError:
                break
            ancestor_types[normalized(frame.parent_exact_type)] = frame.frame_id
            frame_id = frame.parent_producer_frame_id
        residual_by_id = {
            item.obligation_id: item.exact_type for item in plan.residual_obligations
        }
        for obligation_id in action.residual_obligation_ids:
            exact_type = residual_by_id.get(obligation_id)
            if exact_type is None:
                continue
            owner = ancestor_types.get(normalized(exact_type))
            if owner is not None:
                return (
                    f"residual obligation {obligation_id} recreates active ancestor "
                    f"{owner}"
                )
        return None

    def run(self, initial: ProofState) -> SearchOutcome:
        frontier = GlobalProofFrontier(max_width=self.tracker.budget.max_frontier_width)
        frontier.push(initial)
        self._event("STATE_PUSHED", state_id=initial.state_id, fingerprint=initial.fingerprint)
        best = initial
        non_synthesis_expansions: dict[str, int] = {}
        exhausted_goals: list[Mapping[str, object]] = []
        try:
            while len(frontier):
                self.tracker.consume("search_rounds")
                state = frontier.pop()
                self._event("STATE_POPPED", state_id=state.state_id, fingerprint=state.fingerprint)
                best = self._more_progressed(state, best)
                self.max_observed_depth = max(self.max_observed_depth, state.depth)
                if state.complete:
                    self._event("STATE_COMPLETED", state_id=state.state_id)
                    return self._outcome("VERIFIED", state, state, None, len(frontier), None)
                if state.depth >= self.tracker.budget.max_search_depth:
                    try:
                        depth_goal = state.select_open_goal()
                    except LookupError:
                        depth_goal = None
                    if depth_goal is not None and self.dead_end_handler is not None:
                        backtracked = self.dead_end_handler(
                            state, depth_goal, "maximum search depth reached"
                        )
                        if backtracked is not None and frontier.push(backtracked):
                            best = self._more_progressed(backtracked, best)
                            self._event(
                                "ACTION_FAILED_REQUEUED",
                                state_id=backtracked.state_id,
                                goal_id=depth_goal.goal_id,
                                action_id="depth-backtrack",
                            )
                            continue
                    exhausted_goals.append(
                        {
                            "state_id": state.state_id,
                            "reason": "max_search_depth",
                            "open_goals": [goal.goal_id for goal in state.open_goals],
                        }
                    )
                    continue
                self.tracker.consume("expanded_states")
                try:
                    goal = state.select_open_goal()
                except LookupError:
                    exhausted_goals.append(
                        {
                            "state_id": state.state_id,
                            "reason": "no_ready_goal",
                            "dormant_frames": [
                                frame.frame_id
                                for frame in state.application_frames
                                if frame.status.value != "verified"
                            ],
                        }
                    )
                    continue
                self._event(
                    "GOAL_SELECTED",
                    state_id=state.state_id,
                    goal_id=goal.goal_id,
                    exact_type=goal.exact_type,
                )
                action_started = time.monotonic()
                lean_checks_before = self.tracker.usage.lean_checks
                model_calls_before = self.tracker.usage.model_calls
                candidates = tuple(self.candidate_lookup(state, goal))
                failure_fingerprint = stable_sha256(
                    {
                        "failures": state.normalized_failure_fingerprints,
                        "attempted_actions": goal.attempted_actions,
                    }
                )
                self.tracker.consume("recursive_substep_plans")
                plan = self.planner.plan(
                    goal=goal,
                    candidates=candidates,
                    fragments=(
                        *state.completed_fragments,
                        *state.verified_frame_fragments,
                    ),
                    environment_fingerprint=self.environment_fingerprint,
                    capability_fingerprint=self.capability_fingerprint(state),
                    failure_memory_fingerprint=failure_fingerprint,
                    strategy=self.strategy,
                    is_root=goal.goal_id == "goal-root",
                    target_handle=state.root_goal.problem_declaration,
                    forbidden_declarations=self.forbidden_declarations,
                )
                self._event(
                    "PLAN_COMPUTED",
                    goal_id=goal.goal_id,
                    plan_fingerprint=plan.plan_fingerprint,
                )
                state = state.record_plan(plan)
                eligible_actions: list[CandidateAction] = []
                for candidate in plan.candidate_actions:
                    if candidate.action_id in goal.attempted_actions:
                        continue
                    if candidate.disposition.value == "BLOCKED":
                        continue
                    cycle_reason = self._ancestor_cycle_reason(
                        state, goal, plan, candidate
                    )
                    if cycle_reason is not None:
                        self._event(
                            "ACTION_PRUNED_ANCESTOR_CYCLE",
                            state_id=state.state_id,
                            goal_id=goal.goal_id,
                            action_id=candidate.action_id,
                            declaration=candidate.declaration,
                            reason=cycle_reason,
                        )
                        continue
                    eligible_actions.append(candidate)
                unattempted = tuple(eligible_actions)
                buckets = ReadyActionBuckets(unattempted)
                for provider, count in buckets.counts().items():
                    self.statistics[provider].candidate_count += count
                counter = non_synthesis_expansions.get(goal.key.fingerprint, 0)
                deterministic_action = buckets.choose(
                    strategy=self.strategy,
                    non_synthesis_expansions=counter,
                    synthesis_activation_deadline=(
                        self.tracker.budget.synthesis_activation_deadline
                    ),
                )
                action = deterministic_action
                applied_decision: StrategyDecision | None = None
                receipt_index: int | None = None
                exact_actions = tuple(
                    candidate
                    for candidate in unattempted
                    if candidate.disposition.value == "CLOSED"
                    and candidate.lean_verified
                )
                if (
                    not exact_actions
                    and len(unattempted) >= 2
                    and self.strategy_decider is not None
                ):
                    decision = self.strategy_decider(state, goal, plan, unattempted)
                    if decision is not None:
                        self._event(
                            "STRATEGY_DECISION_PROPOSED",
                            decision_id=decision.decision_id,
                            state_id=state.state_id,
                            goal_id=goal.goal_id,
                            decision_kind=decision.decision_kind,
                            selected_action_id=decision.selected_action_id,
                            selected_design_id=decision.selected_design_id,
                            applicable=decision.applicable,
                        )
                        stale_reason = None
                        if decision.state_fingerprint != state.fingerprint:
                            stale_reason = "strategy decision state fingerprint is stale"
                        elif decision.goal_id != goal.goal_id:
                            stale_reason = "strategy decision goal is stale"
                        action_by_id = {
                            candidate.action_id: candidate for candidate in unattempted
                        }
                        selected = action_by_id.get(decision.selected_action_id or "")
                        if stale_reason is not None:
                            self.strategy_fallbacks += 1
                            receipt = StrategyEffectReceipt(
                                decision_id=decision.decision_id,
                                proposal_status="stale",
                                proposed_action_id=decision.selected_action_id,
                                applied_action_id=(
                                    deterministic_action.action_id
                                    if deterministic_action is not None
                                    else None
                                ),
                                applied_design_id=None,
                                effect="deterministic-fallback-stale-proposal",
                                override_reason=stale_reason,
                            )
                            self._event(
                                "STRATEGY_DECISION_REJECTED",
                                decision_id=decision.decision_id,
                                reason=stale_reason,
                            )
                        elif decision.applicable and decision.requested_backtrack:
                            backtracked = (
                                self.dead_end_handler(
                                    state,
                                    goal,
                                    "strategy requested current-branch backtrack",
                                )
                                if self.dead_end_handler is not None
                                else None
                            )
                            if backtracked is not None and frontier.push(backtracked):
                                self.strategy_valid_proposals += 1
                                self.strategy_applied_decisions += 1
                                self.tracker.consume("requeues")
                                self.requeued_failure_states += 1
                                receipt = StrategyEffectReceipt(
                                    decision_id=decision.decision_id,
                                    proposal_status="valid",
                                    proposed_action_id=None,
                                    applied_action_id=None,
                                    applied_design_id=None,
                                    effect="backtracked-current-branch",
                                    next_state_fingerprint=backtracked.fingerprint,
                                )
                                self.strategy_effect_receipts.append(receipt)
                                self._event(
                                    "STRATEGY_DECISION_APPLIED",
                                    decision_id=decision.decision_id,
                                    effect=receipt.effect,
                                    next_state_fingerprint=backtracked.fingerprint,
                                )
                                continue
                            self.strategy_fallbacks += 1
                            receipt = StrategyEffectReceipt(
                                decision_id=decision.decision_id,
                                proposal_status="valid-but-not-applicable",
                                proposed_action_id=None,
                                applied_action_id=(
                                    deterministic_action.action_id
                                    if deterministic_action is not None
                                    else None
                                ),
                                applied_design_id=None,
                                effect="deterministic-fallback-invalid-proposal",
                                override_reason=(
                                    "current state has no valid parent branch to backtrack"
                                ),
                            )
                        elif decision.applicable and selected is not None:
                            self.strategy_valid_proposals += 1
                            self.strategy_applied_decisions += 1
                            action = selected
                            applied_decision = decision
                            effect = (
                                "selected-design"
                                if decision.selected_design_id
                                else "selected-action"
                            )
                            receipt = StrategyEffectReceipt(
                                decision_id=decision.decision_id,
                                proposal_status="valid",
                                proposed_action_id=decision.selected_action_id,
                                applied_action_id=selected.action_id,
                                applied_design_id=decision.selected_design_id,
                                effect=effect,
                            )
                            self._event(
                                "STRATEGY_DECISION_APPLIED",
                                decision_id=decision.decision_id,
                                applied_action_id=selected.action_id,
                                applied_design_id=decision.selected_design_id,
                                effect=effect,
                            )
                        else:
                            self.strategy_rejections += 1
                            reason = decision.rationale or "strategy proposal is not executable"
                            receipt = StrategyEffectReceipt(
                                decision_id=decision.decision_id,
                                proposal_status="invalid",
                                proposed_action_id=decision.selected_action_id,
                                applied_action_id=(
                                    deterministic_action.action_id
                                    if deterministic_action is not None
                                    else None
                                ),
                                applied_design_id=None,
                                effect="deterministic-fallback-invalid-proposal",
                                override_reason=reason,
                            )
                            self._event(
                                "STRATEGY_DECISION_REJECTED",
                                decision_id=decision.decision_id,
                                reason=reason,
                            )
                        self.strategy_effect_receipts.append(receipt)
                        receipt_index = len(self.strategy_effect_receipts) - 1
                if action is None:
                    if self.dead_end_handler is not None:
                        backtracked = self.dead_end_handler(
                            state, goal, "all actions for child goal were exhausted"
                        )
                        if backtracked is not None:
                            self.tracker.consume("requeues")
                            self.requeued_failure_states += 1
                            if frontier.push(backtracked):
                                best = self._more_progressed(backtracked, best)
                                self._event(
                                    "ACTION_FAILED_REQUEUED",
                                    state_id=backtracked.state_id,
                                    goal_id=goal.goal_id,
                                    action_id="child-dead-end-backtrack",
                                )
                                continue
                    exhausted_goals.append(
                        {
                            "state_id": state.state_id,
                            "goal_id": goal.goal_id,
                            "exact_type": goal.exact_type,
                            "attempted_actions": list(goal.attempted_actions),
                            "candidate_count": len(candidates),
                            "reason": "all_actions_exhausted",
                        }
                    )
                    continue
                if applied_decision is not None:
                    action = replace(
                        action,
                        metadata={
                            **action.metadata,
                            "strategy_decision_id": applied_decision.decision_id,
                            "strategy_selected_design_id": (
                                applied_decision.selected_design_id
                            ),
                        },
                    )
                stats = self.statistics[action.provider.value]
                stats.expanded_action_count += 1
                self._event(
                    "ACTION_EXPANDED",
                    state_id=state.state_id,
                    goal_id=goal.goal_id,
                    action_id=action.action_id,
                    provider=action.provider.value,
                    declaration=action.declaration,
                    strategy_decision_id=(
                        applied_decision.decision_id if applied_decision else None
                    ),
                )
                if action.provider == ProviderKind.SYNTHESIS:
                    self.tracker.consume("synthesis_action_expansions")
                    non_synthesis_expansions[goal.key.fingerprint] = 0
                else:
                    non_synthesis_expansions[goal.key.fingerprint] = counter + 1
                children = tuple(self.action_executor(state, goal, plan, action))
                if receipt_index is not None and children:
                    self.strategy_effect_receipts[receipt_index] = replace(
                        self.strategy_effect_receipts[receipt_index],
                        next_state_fingerprint=children[0].fingerprint,
                    )
                stats.lean_checks += (
                    self.tracker.usage.lean_checks - lean_checks_before
                )
                stats.model_calls += (
                    self.tracker.usage.model_calls - model_calls_before
                )
                stats.wall_clock_seconds += time.monotonic() - action_started
                if not children:
                    # An executor may prune a branch entirely, but this never
                    # maps directly to a top-level BLOCKED result.
                    stats.failed_actions += 1
                    continue
                for child in children:
                    attempted_child = child
                    try:
                        child_goal = child.goal(goal.goal_id)
                    except KeyError:
                        child_goal = None
                    if child_goal is not None and action.action_id not in child_goal.attempted_actions:
                        attempted_child = child.mark_action_attempted(goal.goal_id, action.action_id)
                    failed = len(attempted_child.failure_memory) > len(state.failure_memory)
                    if failed:
                        stats.failed_actions += 1
                        self.tracker.consume("requeues")
                        self.requeued_failure_states += 1
                        self._event(
                            "ACTION_FAILED_REQUEUED",
                            state_id=attempted_child.state_id,
                            goal_id=goal.goal_id,
                            action_id=action.action_id,
                        )
                    if attempted_child.complete:
                        stats.successful_closures += 1
                    best = self._more_progressed(attempted_child, best)
                    if attempted_child.depth <= self.tracker.budget.max_search_depth:
                        if frontier.push(attempted_child):
                            self._event(
                                "STATE_PUSHED",
                                state_id=attempted_child.state_id,
                                fingerprint=attempted_child.fingerprint,
                            )
                if (
                    action.disposition.value == "CLOSED"
                    and not any(
                        child_goal.goal_id == goal.goal_id
                        for child in children
                        for child_goal in child.open_goals
                    )
                    and not any(child.complete for child in children)
                ):
                    stats.successful_closures += 1
            receipt: Mapping[str, object] = {
                "reason": "global proof frontier exhausted",
                "expanded_states": self.tracker.usage.expanded_states,
                "search_rounds": self.tracker.usage.search_rounds,
                "last_or_exhausted_goals": exhausted_goals[-64:],
                "remaining_budget": self.tracker.to_dict()["remaining"],
                "provider_statistics": {
                    key: vars(value) for key, value in self.statistics.items()
                },
            }
            self._event("FRONTIER_EXHAUSTED", **receipt)
            return self._outcome(
                "BLOCKED",
                best,
                None,
                "global proof frontier exhausted",
                0,
                receipt,
            )
        except BudgetExhausted as error:
            return self._outcome(
                "BUDGET_EXHAUSTED", best, None, str(error), len(frontier), None
            )

    def _outcome(
        self,
        status: str,
        best: ProofState,
        completed: ProofState | None,
        blocker: str | None,
        final_frontier_size: int,
        exhaustion_receipt: Mapping[str, object] | None,
    ) -> SearchOutcome:
        return SearchOutcome(
            status=status,
            best_state=best,
            completed_state=completed,
            expanded_states=self.tracker.usage.expanded_states,
            blocker=blocker,
            provider_statistics=self.statistics,
            requeued_failure_states=self.requeued_failure_states,
            pruned_cycles=best.pruned_cycle_count,
            max_observed_depth=self.max_observed_depth,
            final_frontier_size=final_frontier_size,
            frontier_exhaustion_receipt=exhaustion_receipt,
            strategy_valid_proposals=self.strategy_valid_proposals,
            strategy_applied_decisions=self.strategy_applied_decisions,
            strategy_fallbacks=self.strategy_fallbacks,
            strategy_rejections=self.strategy_rejections,
            strategy_effect_receipts=tuple(self.strategy_effect_receipts),
            finite_candidate_count=self.tracker.usage.finite_candidates,
            finite_counterexample_count=self.tracker.usage.finite_counterexamples,
            finite_certificate_count=self.tracker.usage.finite_certificates,
            capability_compiler_candidate_count=(
                self.tracker.usage.capability_compiler_candidates
            ),
            capability_compiler_certificate_count=(
                self.tracker.usage.capability_compiler_certificates
            ),
            generated_lean_check_count=self.tracker.usage.generated_lean_checks,
            generated_lean_success_count=self.tracker.usage.generated_lean_successes,
            capability_registration_count=self.tracker.usage.capability_registrations,
            synthesis_design_count=self.tracker.usage.synthesis_designs,
            context_expansion_count=self.tracker.usage.context_expansions,
            duplicate_candidate_rejection_count=(
                self.tracker.usage.duplicate_candidate_rejections
            ),
            repeated_diagnostic_count=self.tracker.usage.repeated_diagnostics,
            context_insufficient_count=self.tracker.usage.context_insufficient,
            unresolved_probe_handle_count=self.tracker.usage.unresolved_probe_handles,
            rejected_nonexecutable_design_count=(
                self.tracker.usage.rejected_nonexecutable_designs
            ),
        )


__all__ = [
    "ActionExecutor",
    "CandidateLookup",
    "DeadEndHandler",
    "SearchCoordinator",
    "SearchOutcome",
    "StrategyDecider",
]
