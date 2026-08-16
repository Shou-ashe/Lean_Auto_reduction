from __future__ import annotations

from ..models import (
    ActionDisposition,
    CandidateAction,
    ConstructionContract,
    ProviderKind,
    stable_sha256,
)
from ..synthesis.designs import design_kind_for_mode


class SynthesisActionProvider:
    kind = ProviderKind.SYNTHESIS

    def actions(
        self,
        contract: ConstructionContract | None,
        *,
        limit: int,
        structural_available: bool = False,
    ) -> tuple[CandidateAction, ...]:
        if contract is None:
            return ()
        del structural_available
        actions: list[CandidateAction] = []
        for ordinal, mode in enumerate(contract.allowed_construction_modes[:limit]):
            design_kind = design_kind_for_mode(mode)
            # Constructor designs are executable only through the typed
            # structural provider.  If that provider emitted an action it will
            # be collected separately; otherwise no constructor has been
            # confirmed and this synthesis design must not consume budget.
            if design_kind == "constructor-first":
                continue
            if (
                design_kind in {"helper-first", "theorem-composition"}
                and not contract.residual_obligations
            ):
                continue
            if (
                design_kind == "theorem-composition"
                and not contract.reusable_declarations
            ):
                continue
            design_digest = stable_sha256(
                {
                    "contract": contract.contract_id,
                    "mode": mode,
                    "kind": design_kind,
                }
            )
            design_id = f"design-{design_digest.removeprefix('sha256:')[:20]}"
            digest = stable_sha256(
                {
                    "goal": contract.goal_key.fingerprint,
                    "mode": mode,
                    "ordinal": ordinal,
                }
            )
            actions.append(
                CandidateAction(
                    action_id=f"synthesis-{digest.removeprefix('sha256:')[:20]}",
                    provider=self.kind,
                    disposition=ActionDisposition.SYNTHESIS_REQUIRED,
                    goal_key=contract.goal_key,
                    estimated_cost=5.0 + ordinal,
                    contract_id=contract.contract_id,
                    residual_obligation_ids=tuple(
                        item.obligation_id for item in contract.residual_obligations
                    ),
                    provenance="job-local-planned",
                    metadata={
                        "construction_mode": mode,
                        "design_id": design_id,
                        "design_kind": design_kind,
                        "execution_semantics": {
                            "constructor-first": "delegate-to-typed-structural-frame",
                            "helper-first": "author-and-register-minimal-residual-helper",
                            "direct-authoring": "author-exact-parent-capability",
                        }.get(design_kind, "author-exact-parent-capability"),
                        "constructibility_score": max(0.0, 0.35 - 0.05 * ordinal),
                    },
                )
            )
        return tuple(actions)


__all__ = ["SynthesisActionProvider"]
