from __future__ import annotations

from dataclasses import dataclass, replace

from ..models import ConstructionContract, stable_sha256


_MODE_TO_KIND = {
    "typed-witness": "constructor-first",
    "constructor-first": "constructor-first",
    "intermediate-first": "helper-first",
    "helper-first": "helper-first",
    "direct-authoring": "direct-authoring",
    "direct-synthesis": "direct-authoring",
    "finite-enumeration": "finite-enumeration",
    "cegis-witness": "cegis-witness",
    "apply-existing-theorem": "theorem-composition",
    "compose-path": "theorem-composition",
    "compose-program": "theorem-composition",
}


def design_kind_for_mode(mode: str) -> str:
    if mode in _MODE_TO_KIND:
        return _MODE_TO_KIND[mode]
    if mode.endswith("-first"):
        return "helper-first"
    return "direct-authoring"


@dataclass(frozen=True)
class SynthesisDesign:
    design_id: str
    contract_id: str
    mode: str
    design_kind: str
    exact_expected_type: str
    parent_goal_id: str | None = None
    stage: str = "planned"
    staged_goal_ids: tuple[str, ...] = ()
    helper_declarations: tuple[str, ...] = ()
    constructor_skeleton: str | None = None
    previous_implementation: str | None = None
    previous_source_hash: str | None = None
    diagnostic_history: tuple[str, ...] = ()
    diagnostic_fingerprints: tuple[str, ...] = ()
    candidate_implementation_hashes: tuple[str, ...] = ()
    candidate_source_hashes: tuple[str, ...] = ()
    counterexamples: tuple[str, ...] = ()
    context_capsule_id: str | None = None
    strategy_decision_id: str | None = None
    declarations: tuple[str, ...] = ()
    residual_obligations: tuple[str, ...] = ()
    verified_capabilities: tuple[str, ...] = ()
    generated_files: tuple[str, ...] = ()
    diagnostics: tuple[str, ...] = ()
    materialization_attempts: int = 0
    repair_attempts: int = 0
    estimated_cost: float = 5.0
    status: str = "planned"
    terminal_reason: str | None = None

    @classmethod
    def for_contract(
        cls,
        contract: ConstructionContract,
        *,
        mode: str,
        parent_goal_id: str | None = None,
    ) -> "SynthesisDesign":
        kind = design_kind_for_mode(mode)
        digest = stable_sha256(
            {"contract": contract.contract_id, "mode": mode, "kind": kind}
        )
        return cls(
            design_id=f"design-{digest.removeprefix('sha256:')[:20]}",
            contract_id=contract.contract_id,
            mode=mode,
            design_kind=kind,
            exact_expected_type=contract.exact_expected_lean_type,
            parent_goal_id=parent_goal_id,
            residual_obligations=tuple(
                item.obligation_id for item in contract.residual_obligations
            ),
        )

    def transition(
        self,
        stage: str,
        *,
        status: str | None = None,
        terminal_reason: str | None = None,
        **changes,
    ) -> "SynthesisDesign":
        return replace(
            self,
            stage=stage,
            status=status or stage,
            terminal_reason=terminal_reason,
            **changes,
        )


__all__ = ["SynthesisDesign", "design_kind_for_mode"]
