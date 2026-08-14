from __future__ import annotations

from dataclasses import dataclass

from ..models import ConstructionContract, stable_sha256


@dataclass(frozen=True)
class SynthesisDesign:
    design_id: str
    contract_id: str
    mode: str
    exact_expected_type: str
    declarations: tuple[str, ...] = ()
    residual_obligations: tuple[str, ...] = ()
    verified_capabilities: tuple[str, ...] = ()
    generated_files: tuple[str, ...] = ()
    diagnostics: tuple[str, ...] = ()
    materialization_attempts: int = 0
    estimated_cost: float = 5.0
    status: str = "planned"

    @classmethod
    def for_contract(cls, contract: ConstructionContract, *, mode: str) -> "SynthesisDesign":
        digest = stable_sha256({"contract": contract.contract_id, "mode": mode})
        return cls(
            design_id=f"design-{digest.removeprefix('sha256:')[:20]}",
            contract_id=contract.contract_id,
            mode=mode,
            exact_expected_type=contract.exact_expected_lean_type,
            residual_obligations=tuple(
                item.obligation_id for item in contract.residual_obligations
            ),
        )


__all__ = ["SynthesisDesign"]
