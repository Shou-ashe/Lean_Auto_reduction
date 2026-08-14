"""Phase B: top-k theorem/constructor/combinator proof guidance."""

from __future__ import annotations

from typing import Sequence

from .goal_kind_adapters import classify_goal
from .models import (
    OpenGoal,
    ProofGuidance,
    ResidualObligation,
    ReusableFragment,
    TheoremIndexEntry,
    stable_sha256,
)
from .premise_registry import PremiseSolverRegistry
from .proof_guidance import guidance_id
from .ranking import guidance_cost


class GuidedProofPlanner:
    def __init__(
        self,
        *,
        solver_registry: PremiseSolverRegistry,
        max_candidates: int,
        max_plans: int,
    ):
        self.solver_registry = solver_registry
        self.max_candidates = max_candidates
        self.max_plans = max_plans

    def run(
        self,
        *,
        goal: OpenGoal,
        fragments: Sequence[ReusableFragment],
        candidates: Sequence[TheoremIndexEntry],
    ) -> tuple[ProofGuidance, ...]:
        plans: list[ProofGuidance] = []
        verified_by_type = {
            fragment.exact_type.strip(): fragment
            for fragment in fragments
            if fragment.lean_verified
        }
        for candidate in candidates[: self.max_candidates]:
            closed: list[ReusableFragment] = []
            residuals: list[ResidualObligation] = []
            suggested = 0
            for premise in candidate.premises:
                fragment = verified_by_type.get(premise.exact_type.strip())
                if fragment is not None:
                    closed.append(fragment)
                    continue
                proposal = self.solver_registry.propose(premise, goal.local_context)
                if proposal is not None:
                    suggested += 1
                obligation_digest = stable_sha256(
                    {
                        "goal": goal.key.fingerprint,
                        "candidate": candidate.declaration,
                        "premise": premise.fingerprint,
                    }
                )
                residuals.append(
                    ResidualObligation(
                        obligation_id=(
                            "obligation-"
                            + obligation_digest.removeprefix("sha256:")[:20]
                        ),
                        exact_type=premise.exact_type,
                        kind=classify_goal(
                            premise.exact_type, premise_kind=premise.kind.value
                        ),
                        suggested_solver=(proposal.solver if proposal else None),
                        estimated_cost=(
                            max(0.1, 1.0 - proposal.confidence)
                            if proposal
                            else 1.0
                        ),
                    )
                )
            denominator = max(1, len(candidate.premises))
            coverage = (len(closed) + 0.5 * suggested) / denominator
            residual_types = tuple(item.exact_type for item in residuals)
            plan_id = guidance_id(
                goal_fingerprint=goal.key.fingerprint,
                declaration=candidate.declaration,
                residuals=residual_types,
            )
            proof_mode = (
                "apply-existing-theorem"
                if not candidate.premises
                else "recursive-premise-search"
            )
            plans.append(
                ProofGuidance(
                    guidance_id=plan_id,
                    goal_key=goal.key,
                    candidate_declaration=candidate.declaration,
                    declaration_provenance=candidate.provenance,
                    instantiated_universe_arguments=candidate.universe_parameters,
                    application_skeleton=(
                        f"by\n  apply_generative_rule {candidate.declaration}"
                    ),
                    generated_premises=candidate.premises,
                    already_closed_premises=tuple(closed),
                    reusable_fragments=tuple(closed),
                    residual_obligations=tuple(residuals),
                    suggested_proof_mode=proof_mode,
                    coverage_score=min(1.0, coverage),
                    estimated_cost=(
                        0.25
                        + sum(item.estimated_cost for item in residuals)
                        + 0.1 * len(candidate.universe_parameters)
                    ),
                    confidence=max(0.05, 1.0 - 0.15 * len(residuals)),
                    diagnostics=(),
                )
            )
        return tuple(sorted(plans, key=guidance_cost)[: self.max_plans])


__all__ = ["GuidedProofPlanner"]
