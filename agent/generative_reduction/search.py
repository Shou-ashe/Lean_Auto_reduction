"""Bounded best-first search over one global AND/OR proof frontier."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Mapping, Sequence

from .budgets import BudgetExhausted, BudgetTracker
from .capability_planner import CapabilityPlanner
from .models import (
    CandidateAction,
    OpenGoal,
    ProviderKind,
    ProviderStatistics,
    ReusableFragment,
    Strategy,
    SubstepPlan,
    TheoremIndexEntry,
    stable_sha256,
)
from .proof_frontier import GlobalProofFrontier, ReadyActionBuckets
from .proof_state import ProofState


CandidateLookup = Callable[[OpenGoal], Sequence[TheoremIndexEntry]]
ActionExecutor = Callable[
    [ProofState, OpenGoal, SubstepPlan, CandidateAction], Sequence[ProofState]
]


@dataclass(frozen=True)
class SearchOutcome:
    status: str
    best_state: ProofState
    completed_state: ProofState | None
    expanded_states: int
    blocker: str | None
    provider_statistics: Mapping[str, ProviderStatistics]


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
    ):
        self.planner = planner
        self.tracker = tracker
        self.strategy = strategy
        self.environment_fingerprint = environment_fingerprint
        self.capability_fingerprint = capability_fingerprint
        self.candidate_lookup = candidate_lookup
        self.action_executor = action_executor
        self.statistics = {
            kind.value: ProviderStatistics() for kind in ProviderKind
        }

    def run(self, initial: ProofState) -> SearchOutcome:
        frontier = GlobalProofFrontier(max_width=self.tracker.budget.max_frontier_width)
        frontier.push(initial)
        best = initial
        non_synthesis_expansions: dict[str, int] = {}
        try:
            while len(frontier):
                self.tracker.consume("search_rounds")
                state = frontier.pop()
                best = state
                if state.complete:
                    return self._outcome("VERIFIED", state, state, None)
                if state.depth >= self.tracker.budget.max_search_depth:
                    continue
                self.tracker.consume("expanded_states")
                goal = state.select_open_goal()
                candidates = tuple(self.candidate_lookup(goal))
                failure_fingerprint = stable_sha256(state.failure_memory)
                plan = self.planner.plan(
                    goal=goal,
                    candidates=candidates,
                    fragments=state.completed_fragments,
                    environment_fingerprint=self.environment_fingerprint,
                    capability_fingerprint=self.capability_fingerprint(state),
                    failure_memory_fingerprint=failure_fingerprint,
                    strategy=self.strategy,
                    is_root=goal.goal_id == "goal-root",
                    target_handle=state.root_goal.problem_declaration,
                )
                state = state.record_plan(plan)
                buckets = ReadyActionBuckets(plan.candidate_actions)
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
                    continue
                stats = self.statistics[action.provider.value]
                stats.expanded_action_count += 1
                if action.provider == ProviderKind.SYNTHESIS:
                    self.tracker.consume("synthesis_action_expansions")
                    non_synthesis_expansions[goal.key.fingerprint] = 0
                else:
                    non_synthesis_expansions[goal.key.fingerprint] = counter + 1
                children = tuple(self.action_executor(state, goal, plan, action))
                if not children:
                    stats.failed_actions += 1
                    continue
                stats.successful_closures += sum(child.complete for child in children)
                for child in children:
                    if child.depth <= self.tracker.budget.max_search_depth:
                        frontier.push(child)
            return self._outcome(
                "BLOCKED", best, None, "global proof frontier exhausted"
            )
        except BudgetExhausted as error:
            return self._outcome(
                "BUDGET_EXHAUSTED", best, None, str(error)
            )

    def _outcome(
        self,
        status: str,
        best: ProofState,
        completed: ProofState | None,
        blocker: str | None,
    ) -> SearchOutcome:
        return SearchOutcome(
            status=status,
            best_state=best,
            completed_state=completed,
            expanded_states=self.tracker.usage.expanded_states,
            blocker=blocker,
            provider_statistics=self.statistics,
        )


__all__ = ["ActionExecutor", "CandidateLookup", "SearchCoordinator", "SearchOutcome"]
