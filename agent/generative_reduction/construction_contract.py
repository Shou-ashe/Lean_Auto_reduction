"""Build exact authoring contracts from open typed goals."""

from __future__ import annotations

from typing import Sequence

from .goal_kind_adapters import construction_modes
from .models import (
    ConstructionContract,
    OpenGoal,
    ProofGuidance,
    ResidualObligation,
    ReusableFragment,
    stable_sha256,
)


def build_construction_contract(
    *,
    goal: OpenGoal,
    guidance: Sequence[ProofGuidance],
    reusable_fragments: Sequence[ReusableFragment],
    source_handle: str | None,
    target_handle: str | None,
    forbidden_declarations: Sequence[str] = (),
) -> ConstructionContract:
    residual_by_id: dict[str, ResidualObligation] = {}
    for plan in guidance:
        for obligation in plan.residual_obligations:
            residual_by_id.setdefault(obligation.obligation_id, obligation)
    digest = stable_sha256(
        {
            "goal": goal.key.fingerprint,
            "residuals": sorted(residual_by_id),
            "modes": construction_modes(goal.kind),
        }
    )
    return ConstructionContract(
        contract_id=f"contract-{digest.removeprefix('sha256:')[:20]}",
        goal_key=goal.key,
        exact_expected_lean_type=goal.exact_type,
        frozen_source_handle=source_handle,
        frozen_target_handle=target_handle,
        available_inputs=goal.local_context,
        reusable_declarations=tuple(
            dict.fromkeys(
                plan.candidate_declaration for plan in guidance
            )
        ),
        already_closed_fragments=tuple(reusable_fragments),
        residual_obligations=tuple(residual_by_id.values()),
        semantic_requirements=(
            ("preserve source acceptance iff target acceptance",)
            if goal.kind.value in {"certified-reduction", "semantics"}
            else ()
        ),
        complexity_requirements=(
            ("use the same indexed program as the semantic proof",)
            if goal.kind.value
            in {"certified-reduction", "program", "complexity", "component"}
            else ()
        ),
        composition_requirements=("preserve exact source and target endpoints",),
        allowed_construction_modes=construction_modes(goal.kind),
        forbidden_declarations=tuple(forbidden_declarations),
        forbidden_edits=(
            "request.json",
            "environment.json",
            "input module",
            "frozen declaration signature",
            "production library",
        ),
        validation_commands=(("lake", "env", "lean", "<generated-file>"),),
    )


__all__ = ["build_construction_contract"]
