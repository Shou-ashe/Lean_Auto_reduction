"""Phase A: exact, fully checked closure of one typed goal."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

from .models import (
    ExactClosureResult,
    OpenGoal,
    ReusableFragment,
    TheoremIndexEntry,
    TheoremPremise,
)
from .premise_registry import PremiseSolution, PremiseSolverRegistry
from .providers.reuse import reuse_action_id


@dataclass(frozen=True)
class ClosureCheck:
    ok: bool
    proof_term: str | None = None
    diagnostic: str | None = None


ClosureChecker = Callable[
    [
        OpenGoal,
        TheoremIndexEntry,
        tuple[tuple[TheoremPremise, PremiseSolution], ...],
    ],
    ClosureCheck,
]


class ExactClosureProbe:
    def __init__(
        self,
        *,
        solver_registry: PremiseSolverRegistry,
        max_candidates: int,
        checker: ClosureChecker | None = None,
    ):
        self.solver_registry = solver_registry
        self.max_candidates = max_candidates
        self.checker = checker

    def run(
        self,
        *,
        goal: OpenGoal,
        fragments: Sequence[ReusableFragment],
        candidates: Sequence[TheoremIndexEntry],
    ) -> ExactClosureResult:
        diagnostics: list[str] = []
        for fragment in fragments:
            if (
                fragment.lean_verified
                and fragment.exact_type.strip() == goal.exact_type.strip()
            ):
                result = ExactClosureResult(
                    goal_key=goal.key,
                    closed=True,
                    proof_term=fragment.proof_term,
                    declaration=fragment.declaration,
                    provenance=fragment.provenance,
                    lean_verified=True,
                    checked_candidate_count=0,
                )
                if reuse_action_id(result) in goal.attempted_actions:
                    diagnostics.append("verified fragment closure was already attempted")
                    continue
                return result

        checked = 0
        for candidate in candidates[: self.max_candidates]:
            predicted = ExactClosureResult(
                goal_key=goal.key,
                closed=True,
                proof_term=candidate.declaration,
                declaration=candidate.declaration,
                provenance=candidate.provenance,
                lean_verified=True,
            )
            if reuse_action_id(predicted) in goal.attempted_actions:
                diagnostics.append(
                    f"{candidate.declaration}: exact closure action was already attempted"
                )
                continue
            solved, residual = self.solver_registry.coverage(
                candidate.premises, goal.local_context
            )
            if residual:
                diagnostics.append(
                    f"{candidate.declaration}: {len(residual)} residual obligation(s)"
                )
                continue
            checked += 1
            if self.checker is None:
                diagnostics.append(
                    f"{candidate.declaration}: exact application not Lean-checked"
                )
                continue
            check = self.checker(goal, candidate, solved)
            if check.ok:
                result = ExactClosureResult(
                    goal_key=goal.key,
                    closed=True,
                    proof_term=check.proof_term or candidate.declaration,
                    declaration=candidate.declaration,
                    provenance=candidate.provenance,
                    lean_verified=True,
                    diagnostics=tuple(diagnostics),
                    checked_candidate_count=checked,
                )
                if reuse_action_id(result) in goal.attempted_actions:
                    diagnostics.append(
                        f"{candidate.declaration}: checked closure action was already attempted"
                    )
                    continue
                return result
            diagnostics.append(
                f"{candidate.declaration}: {check.diagnostic or 'Lean rejected candidate'}"
            )

        return ExactClosureResult(
            goal_key=goal.key,
            closed=False,
            lean_verified=False,
            diagnostics=tuple(diagnostics),
            checked_candidate_count=checked,
        )


__all__ = ["ClosureCheck", "ClosureChecker", "ExactClosureProbe"]
