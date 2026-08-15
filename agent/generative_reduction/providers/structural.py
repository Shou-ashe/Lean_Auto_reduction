"""Generic constructor actions promoted from Lean-typed theorem guidance."""

from __future__ import annotations

from typing import Sequence

from ..context_capsule import classify_structural_declaration
from ..models import (
    ActionDisposition,
    CandidateAction,
    ConstructionContract,
    OpenGoal,
    ProofGuidance,
    ProviderKind,
    stable_sha256,
)
from ..synthesis.designs import design_kind_for_mode


class StructuralActionProvider:
    """Expose constructor decompositions as their own typed action family.

    Candidates come from the Lean theorem index and are still re-instantiated
    by Lean before a frame is accepted.  The provider contains no domain or
    benchmark-specific name tests.
    """

    kind = ProviderKind.STRUCTURAL

    def actions(
        self,
        goal: OpenGoal,
        guidance: Sequence[ProofGuidance],
        contract: ConstructionContract | None,
        *,
        limit: int,
    ) -> tuple[CandidateAction, ...]:
        structural: list[CandidateAction] = []
        constructor_mode = next(
            (
                mode
                for mode in (contract.allowed_construction_modes if contract else ())
                if design_kind_for_mode(mode) == "constructor-first"
            ),
            "constructor-first",
        )
        design_id = None
        if contract is not None:
            design_digest = stable_sha256(
                {
                    "contract": contract.contract_id,
                    "mode": constructor_mode,
                    "kind": "constructor-first",
                }
            )
            design_id = f"design-{design_digest.removeprefix('sha256:')[:20]}"
        for item in guidance:
            structural_kind = (
                "lean-environment-constructor"
                if item.candidate_kind == "constructor"
                else classify_structural_declaration(item.candidate_declaration)
            )
            if structural_kind is None:
                continue
            digest = stable_sha256(
                {
                    "goal": goal.key.fingerprint,
                    "declaration": item.candidate_declaration,
                    "provider": self.kind.value,
                }
            )
            structural.append(
                CandidateAction(
                    action_id=f"structural-{digest.removeprefix('sha256:')[:20]}",
                    provider=self.kind,
                    disposition=ActionDisposition.DECOMPOSED,
                    goal_key=goal.key,
                    estimated_cost=max(0.05, item.estimated_cost - 0.5),
                    declaration=item.candidate_declaration,
                    guidance_id=item.guidance_id,
                    contract_id=(contract.contract_id if contract else None),
                    residual_obligation_ids=tuple(
                        obligation.obligation_id
                        for obligation in item.residual_obligations
                    ),
                    provenance=item.declaration_provenance,
                    metadata={
                        "structural_kind": structural_kind,
                        "constructor_skeleton": item.application_skeleton,
                        "field_exact_types": tuple(
                            obligation.exact_type
                            for obligation in item.residual_obligations
                        ),
                        "progress_fingerprint": stable_sha256(
                            {
                                "parent_goal": goal.key.fingerprint,
                                "constructor": item.candidate_declaration,
                                "fields": tuple(
                                    obligation.exact_type
                                    for obligation in item.residual_obligations
                                ),
                                "local_context": goal.local_context,
                            }
                        ),
                        "design_id": design_id,
                        "design_kind": "constructor-first",
                        "construction_mode": constructor_mode,
                        "lean_typed_candidate": True,
                        "constructibility_score": min(
                            1.0,
                            0.55
                            + 0.1 * item.coverage_score
                            - 0.03 * len(item.residual_obligations),
                        ),
                    },
                )
            )
        return tuple(structural[:limit])


__all__ = ["StructuralActionProvider"]
