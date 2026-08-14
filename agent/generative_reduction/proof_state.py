"""One reconstructible AND/OR proof state.

Lean metavariable identifiers are intentionally absent.  Every node is keyed
by exact rendered type plus stable environment/context fingerprints.
"""

from __future__ import annotations

from dataclasses import dataclass, field, replace
from typing import Any, Mapping, Sequence

from .goal_kind_adapters import classify_goal
from .models import (
    CandidateAction,
    ConstructionContract,
    GoalKey,
    OpenGoal,
    ProofGuidance,
    ProofStep,
    ReusableFragment,
    RootGoal,
    SubstepPlan,
    stable_sha256,
)


@dataclass(frozen=True)
class ProofState:
    state_id: str
    root_goal: RootGoal
    open_goals: tuple[OpenGoal, ...]
    proof_skeleton: tuple[ProofStep, ...] = ()
    planner_decisions: tuple[Mapping[str, Any], ...] = ()
    substep_plans: tuple[SubstepPlan, ...] = ()
    completed_fragments: tuple[ReusableFragment, ...] = ()
    verified_paths: tuple[str, ...] = ()
    construction_contracts: tuple[ConstructionContract, ...] = ()
    generated_modules: tuple[str, ...] = ()
    imports: tuple[str, ...] = ()
    depth: int = 0
    total_cost: float = 0.0
    lean_check_count: int = 0
    model_call_count: int = 0
    synthesis_round_count: int = 0
    cycle_fingerprints: frozenset[str] = field(default_factory=frozenset)
    failure_memory: tuple[Mapping[str, Any], ...] = ()

    @classmethod
    def initial(
        cls, root_goal: RootGoal, *, import_closure_fingerprint: str = ""
    ) -> "ProofState":
        open_goal = OpenGoal.create(
            goal_id="goal-root",
            exact_type=root_goal.exact_type,
            import_closure_fingerprint=import_closure_fingerprint,
            kind=classify_goal(root_goal.exact_type),
        )
        fingerprint = stable_sha256(
            {"root": root_goal.exact_type, "endpoint": root_goal.endpoint_fingerprint}
        )
        return cls(
            state_id=f"state-{fingerprint.removeprefix('sha256:')[:16]}",
            root_goal=root_goal,
            open_goals=(open_goal,),
            cycle_fingerprints=frozenset({fingerprint}),
        )

    @property
    def complete(self) -> bool:
        return not self.open_goals

    @property
    def fingerprint(self) -> str:
        return stable_sha256(
            {
                "root": self.root_goal.exact_type,
                "open": [goal.key.fingerprint for goal in self.open_goals],
                "skeleton": self.proof_skeleton,
                "generated_modules": self.generated_modules,
            }
        )

    def goal(self, goal_id: str) -> OpenGoal:
        for goal in self.open_goals:
            if goal.goal_id == goal_id:
                return goal
        raise KeyError(goal_id)

    def select_open_goal(self) -> OpenGoal:
        if not self.open_goals:
            raise LookupError("proof state has no open goals")
        return min(
            self.open_goals,
            key=lambda goal: (goal.estimated_cost, goal.goal_id, goal.exact_type),
        )

    def record_plan(self, plan: SubstepPlan) -> "ProofState":
        return replace(
            self,
            substep_plans=(*self.substep_plans, plan),
            planner_decisions=(
                *self.planner_decisions,
                {
                    "goal_key": plan.goal_key.fingerprint,
                    "plan_fingerprint": plan.plan_fingerprint,
                    "recommended_action_id": plan.recommended_action_id,
                },
            ),
            construction_contracts=(
                self.construction_contracts
                if plan.construction_contract is None
                else (*self.construction_contracts, plan.construction_contract)
            ),
        )

    def close_goal(
        self,
        *,
        goal_id: str,
        action: CandidateAction,
        fragment: ReusableFragment,
        step: ProofStep,
    ) -> "ProofState":
        remaining = tuple(goal for goal in self.open_goals if goal.goal_id != goal_id)
        if len(remaining) == len(self.open_goals):
            raise KeyError(goal_id)
        return replace(
            self,
            state_id=_next_state_id(self.state_id, action.action_id, remaining),
            open_goals=remaining,
            proof_skeleton=(*self.proof_skeleton, step),
            completed_fragments=(*self.completed_fragments, fragment),
            depth=self.depth + 1,
            total_cost=self.total_cost + action.estimated_cost,
        )

    def decompose_goal(
        self,
        *,
        goal_id: str,
        action: CandidateAction,
        residual_types: Sequence[str],
        guidance: ProofGuidance,
        step: ProofStep,
    ) -> "ProofState":
        parent = self.goal(goal_id)
        remaining = [goal for goal in self.open_goals if goal.goal_id != goal_id]
        for ordinal, exact_type in enumerate(residual_types):
            remaining.append(
                OpenGoal.create(
                    goal_id=f"{goal_id}.{ordinal + 1}",
                    exact_type=exact_type,
                    local_context=parent.local_context,
                    import_closure_fingerprint=parent.key.import_closure_fingerprint,
                    parent_rule=guidance.candidate_declaration,
                    kind=classify_goal(exact_type),
                )
            )
        return replace(
            self,
            state_id=_next_state_id(self.state_id, action.action_id, tuple(remaining)),
            open_goals=tuple(remaining),
            proof_skeleton=(*self.proof_skeleton, step),
            depth=self.depth + 1,
            total_cost=self.total_cost + action.estimated_cost,
        )

    def remember_failure(
        self, *, action: CandidateAction, diagnostic: str
    ) -> "ProofState":
        return replace(
            self,
            failure_memory=(
                *self.failure_memory,
                {
                    "action_id": action.action_id,
                    "diagnostic": diagnostic[-4000:],
                },
            ),
        )


def _next_state_id(
    previous: str, action_id: str, open_goals: Sequence[OpenGoal]
) -> str:
    digest = stable_sha256(
        {
            "previous": previous,
            "action": action_id,
            "open": [goal.key.fingerprint for goal in open_goals],
        }
    )
    return f"state-{digest.removeprefix('sha256:')[:16]}"


__all__ = ["ProofState"]
