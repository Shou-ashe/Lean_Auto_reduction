"""Bounded best-first search over one global AND/OR proof frontier."""

from __future__ import annotations

from dataclasses import dataclass
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
        self.statistics = {
            kind.value: ProviderStatistics() for kind in ProviderKind
        }
        self.requeued_failure_states = 0
        self.max_observed_depth = 0

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
                unattempted = tuple(
                    action
                    for action in plan.candidate_actions
                    if action.action_id not in goal.attempted_actions
                )
                buckets = ReadyActionBuckets(unattempted)
                for provider, count in buckets.counts().items():
                    self.statistics[provider].candidate_count += count
                counter = non_synthesis_expansions.get(goal.key.fingerprint, 0)
                action = buckets.choose(
                    strategy=self.strategy,
                    non_synthesis_expansions=counter,
                    synthesis_activation_deadline=(
                        self.tracker.budget.synthesis_activation_deadline
                    ),
                )
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
                stats = self.statistics[action.provider.value]
                stats.expanded_action_count += 1
                self._event(
                    "ACTION_EXPANDED",
                    state_id=state.state_id,
                    goal_id=goal.goal_id,
                    action_id=action.action_id,
                    provider=action.provider.value,
                    declaration=action.declaration,
                )
                if action.provider == ProviderKind.SYNTHESIS:
                    self.tracker.consume("synthesis_action_expansions")
                    non_synthesis_expansions[goal.key.fingerprint] = 0
                else:
                    non_synthesis_expansions[goal.key.fingerprint] = counter + 1
                children = tuple(self.action_executor(state, goal, plan, action))
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
        )


__all__ = [
    "ActionExecutor",
    "CandidateLookup",
    "DeadEndHandler",
    "SearchCoordinator",
    "SearchOutcome",
]
