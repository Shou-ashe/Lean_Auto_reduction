"""Two-phase capability planning for every new typed subgoal."""

from __future__ import annotations

from dataclasses import replace
from typing import Sequence

from .action_providers import ActionProviders
from .budgets import BudgetTracker
from .construction_contract import build_construction_contract
from .exact_closure_probe import ClosureChecker, ExactClosureProbe
from .finite_synthesis import FiniteSynthesisPlugin
from .goal_kind_adapters import is_generation_eligible
from .guided_proof_planner import GuidedProofPlanner
from .models import (
    ActionDisposition,
    CandidateReceipt,
    CandidateRole,
    ExactClosureResult,
    GoalKind,
    OpenGoal,
    ProviderKind,
    ReusableFragment,
    Strategy,
    SubstepPlan,
    TheoremIndexEntry,
    stable_sha256,
)
from .premise_registry import PremiseSolverRegistry
from .ranking import action_cost
from .synthesis.designs import design_kind_for_mode


class CapabilityPlanner:
    def __init__(
        self,
        *,
        solver_registry: PremiseSolverRegistry,
        tracker: BudgetTracker,
        checker: ClosureChecker | None = None,
        finite_plugins: Sequence[FiniteSynthesisPlugin] = (),
    ):
        self.solver_registry = solver_registry
        self.tracker = tracker
        budget = tracker.budget
        self.exact_probe = ExactClosureProbe(
            solver_registry=solver_registry,
            max_candidates=budget.max_exact_closure_candidates,
            checker=checker,
        )
        self.guided = GuidedProofPlanner(
            solver_registry=solver_registry,
            max_candidates=budget.max_guidance_candidates_per_goal,
            max_plans=budget.max_guidance_plans_per_goal,
        )
        self.providers = ActionProviders(tuple(finite_plugins))
        self._closure_cache: dict[str, ExactClosureResult] = {}
        self._plan_cache: dict[str, SubstepPlan] = {}

    @staticmethod
    def closure_cache_key(
        *, goal: OpenGoal, environment_fingerprint: str, capability_fingerprint: str
    ) -> str:
        return stable_sha256(
            {
                "goal": goal.key.fingerprint,
                "attempted_actions": goal.attempted_actions,
                "environment": environment_fingerprint,
                "capabilities": capability_fingerprint,
            }
        )

    @staticmethod
    def plan_cache_key(
        *,
        goal: OpenGoal,
        environment_fingerprint: str,
        capability_fingerprint: str,
        failure_memory_fingerprint: str,
        strategy: Strategy,
        is_root: bool,
    ) -> str:
        return stable_sha256(
            {
                "goal": goal.key.fingerprint,
                "environment": environment_fingerprint,
                "capabilities": capability_fingerprint,
                "failure_memory": failure_memory_fingerprint,
                "strategy": strategy.value,
                "is_root": is_root,
            }
        )

    def invalidate_for_new_capability(self, capability_fingerprint: str) -> None:
        # Cache keys are content-addressed.  A changed capability fingerprint
        # naturally selects fresh entries; clearing avoids unbounded stale data.
        del capability_fingerprint
        self._closure_cache.clear()
        self._plan_cache.clear()

    def plan(
        self,
        *,
        goal: OpenGoal,
        candidates: Sequence[TheoremIndexEntry],
        fragments: Sequence[ReusableFragment] = (),
        environment_fingerprint: str,
        capability_fingerprint: str,
        failure_memory_fingerprint: str,
        strategy: Strategy,
        is_root: bool,
        source_handle: str | None = None,
        target_handle: str | None = None,
        forbidden_declarations: Sequence[str] = (),
    ) -> SubstepPlan:
        cache_key = self.plan_cache_key(
            goal=goal,
            environment_fingerprint=environment_fingerprint,
            capability_fingerprint=capability_fingerprint,
            failure_memory_fingerprint=failure_memory_fingerprint,
            strategy=strategy,
            is_root=is_root,
        )
        cached = self._plan_cache.get(cache_key)
        if cached is not None:
            return cached

        self.tracker.consume("capability_plans")
        closure_key = self.closure_cache_key(
            goal=goal,
            environment_fingerprint=environment_fingerprint,
            capability_fingerprint=capability_fingerprint,
        )
        closure = self._closure_cache.get(closure_key)
        if closure is None:
            closure = self.exact_probe.run(
                goal=goal, fragments=fragments, candidates=candidates
            )
            self._closure_cache[closure_key] = closure

        root_reuse_filtered = (
            is_root
            and strategy == Strategy.SYNTHESIS_REQUIRED
            and closure.closed
        )
        if closure.closed and not root_reuse_filtered:
            guidance = ()
            contract = None
            residuals = ()
            reusable = tuple(fragments)
        else:
            guidance = self.guided.run(
                goal=goal, fragments=fragments, candidates=candidates
            )
            reusable_by_key = {
                (fragment.exact_type, fragment.proof_term): fragment
                for fragment in fragments
            }
            for plan in guidance:
                for fragment in plan.reusable_fragments:
                    reusable_by_key.setdefault(
                        (fragment.exact_type, fragment.proof_term), fragment
                    )
            reusable = tuple(reusable_by_key.values())
            residual_by_id = {
                item.obligation_id: item
                for plan in guidance
                for item in plan.residual_obligations
            }
            residuals = tuple(residual_by_id.values())
            contract = (
                build_construction_contract(
                    goal=goal,
                    guidance=guidance,
                    reusable_fragments=reusable,
                    source_handle=source_handle,
                    target_handle=target_handle,
                    forbidden_declarations=forbidden_declarations,
                )
                if is_generation_eligible(goal.kind)
                else None
            )

        provider_closure = closure
        if root_reuse_filtered:
            provider_closure = replace(
                closure,
                closed=False,
                diagnostics=(
                    *closure.diagnostics,
                    "synthesis-required filtered direct root closure",
                ),
            )
        actions = self.providers.collect(
            goal=goal,
            closure=provider_closure,
            guidance=guidance,
            contract=contract,
            max_actions_per_provider=self.tracker.budget.max_actions_per_provider,
        )
        # A root hardness goal with a Lean-typed scaffold is already
        # decomposable into exact child capabilities.  Keep monolithic/helper
        # synthesis as a genuine fallback instead of exposing it alongside an
        # untried scaffold, where a model may author an arbitrary data binder
        # (for example a bare source language) that says nothing about whether
        # the downstream DAG closes.  Explicit synthesis-required research
        # mode intentionally retains the synthesis actions.
        if (
            is_root
            and goal.kind == GoalKind.HARDNESS
            and strategy != Strategy.SYNTHESIS_REQUIRED
            and any(
                action.provider == ProviderKind.THEOREM
                and action.disposition == ActionDisposition.DECOMPOSED
                and action.action_id not in goal.attempted_actions
                for action in actions
            )
        ):
            actions = tuple(
                action
                for action in actions
                if action.provider != ProviderKind.SYNTHESIS
            )
        if contract is not None:
            structural_available = any(
                action.provider == ProviderKind.STRUCTURAL for action in actions
            )
            rejected_nonexecutable = 0
            for mode in contract.allowed_construction_modes:
                kind = design_kind_for_mode(mode)
                if kind == "constructor-first" and not structural_available:
                    rejected_nonexecutable += 1
                elif (
                    kind in {"helper-first", "theorem-composition"}
                    and not contract.residual_obligations
                ):
                    rejected_nonexecutable += 1
                elif kind == "theorem-composition" and not contract.reusable_declarations:
                    rejected_nonexecutable += 1
            if rejected_nonexecutable:
                self.tracker.consume(
                    "rejected_nonexecutable_designs", rejected_nonexecutable
                )
        entries_by_declaration = {entry.declaration: entry for entry in candidates}
        receipts: list[CandidateReceipt] = []
        if closure.closed and closure.declaration in entries_by_declaration:
            entry = entries_by_declaration[closure.declaration]
            receipts.append(
                CandidateReceipt.create(
                    entry=entry,
                    role=CandidateRole.EXACT_CLOSURE,
                    exact_closure=True,
                    application_skeleton=closure.proof_term,
                    estimated_cost=0.1,
                )
            )
        recorded = {receipt.candidate_id for receipt in receipts}
        for item in guidance:
            entry = entries_by_declaration.get(item.candidate_declaration)
            if entry is None or entry.candidate_id in recorded:
                continue
            residual_types = tuple(
                obligation.exact_type for obligation in item.residual_obligations
            )
            if not residual_types:
                role = CandidateRole.EXACT_CLOSURE
            elif entry.declaration_kind == "constructor":
                role = CandidateRole.CONSTRUCTOR
            else:
                role = CandidateRole.CONDITIONAL_CLOSURE
            receipt = CandidateReceipt.create(
                entry=entry,
                role=role,
                exact_closure=not residual_types,
                residual_obligations=residual_types,
                application_skeleton=item.application_skeleton,
                estimated_cost=item.estimated_cost,
            )
            receipts.append(receipt)
            recorded.add(receipt.candidate_id)
        recommended = min(actions, key=action_cost).action_id if actions else None
        fingerprint = stable_sha256(
            {
                "cache_key": cache_key,
                "closure": closure,
                "guidance": guidance,
                "contract": contract,
                "actions": actions,
                "candidate_receipts": receipts,
            }
        )
        plan = SubstepPlan(
            goal_key=goal.key,
            exact_closure_result=closure,
            ranked_proof_guidance=guidance,
            reusable_fragments=reusable,
            residual_obligations=residuals,
            construction_contract=contract,
            candidate_actions=actions,
            recommended_action_id=recommended,
            cache_key=cache_key,
            plan_fingerprint=fingerprint,
            candidate_receipts=tuple(receipts),
        )
        self._plan_cache[cache_key] = plan
        return plan


__all__ = ["CapabilityPlanner"]
