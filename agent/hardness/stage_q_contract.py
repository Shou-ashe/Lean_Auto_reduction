"""Versioned Stage-Q request and ``prove_in_p`` finish contracts.

The historical benchmark-v1 objective vocabulary remains unchanged.  Stage Q
uses this separate contract so deterministic-P evidence cannot be confused
with the frozen ``prove_in_np`` payload or silently widen older manifests.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence, TypeVar

from .in_p import InPCertificate, InPValidationReceipt, validate_in_p_certificate


InstanceT = TypeVar("InstanceT")

STAGE_Q_REQUEST_SCHEMA = "hardness_stage_q_request_v1"
STAGE_Q_PROVE_IN_P_FINISH_ABI = "hardness_stage_q_prove_in_p_finish_v1"
STAGE_Q_OBJECTIVES = frozenset({"prove_in_p"})


class StageQContractError(ValueError):
    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


@dataclass(frozen=True)
class StageQRequest:
    class_fingerprint: str
    source_declaration: str
    objective: str = "prove_in_p"
    direction: str = "identity"
    target_declaration: None = None
    schema_version: str = STAGE_Q_REQUEST_SCHEMA

    def __post_init__(self) -> None:
        if self.schema_version != STAGE_Q_REQUEST_SCHEMA:
            raise StageQContractError("wrong_schema", "unsupported Stage-Q request schema")
        if self.objective not in STAGE_Q_OBJECTIVES:
            raise StageQContractError("wrong_objective", "Stage-Q v1 supports prove_in_p only")
        if self.direction != "identity" or self.target_declaration is not None:
            raise StageQContractError(
                "endpoint_mutation", "prove_in_p is bound to its exact source and identity direction"
            )
        if not isinstance(self.source_declaration, str) or not self.source_declaration.strip():
            raise StageQContractError("missing_source", "source declaration is required")
        if (
            not isinstance(self.class_fingerprint, str)
            or not self.class_fingerprint.startswith("sha256:")
            or len(self.class_fingerprint) != 71
        ):
            raise StageQContractError(
                "invalid_class_fingerprint", "a canonical SHA-256 class fingerprint is required"
            )

    def assert_same(self, other: "StageQRequest") -> None:
        if self != other:
            raise StageQContractError(
                "exact_task_binding", "source, class fingerprint, objective, or direction changed"
            )


@dataclass(frozen=True)
class StageQInPFinishPayload:
    request: StageQRequest
    receipt: InPValidationReceipt
    algorithm_lean_term: str
    schema_version: str = STAGE_Q_PROVE_IN_P_FINISH_ABI

    def __post_init__(self) -> None:
        if self.schema_version != STAGE_Q_PROVE_IN_P_FINISH_ABI:
            raise StageQContractError("wrong_finish_schema", "unsupported finish payload")
        if self.receipt.problem_fingerprint != self.request.class_fingerprint:
            raise StageQContractError(
                "predicate_mismatch", "receipt is indexed by another problem class"
            )
        if not isinstance(self.algorithm_lean_term, str) or not self.algorithm_lean_term.strip():
            raise StageQContractError(
                "missing_algorithm", "finish payload requires exact NativeTMInP Lean evidence"
            )


def close_prove_in_p(
    request: StageQRequest,
    certificate: InPCertificate[InstanceT],
    *,
    predicate: Callable[[InstanceT], bool],
    validation_instances: Sequence[InstanceT],
    algorithm_lean_term: str,
) -> StageQInPFinishPayload:
    if certificate.problem_fingerprint != request.class_fingerprint:
        raise StageQContractError(
            "class_fingerprint_mismatch", "certificate is bound to another class"
        )
    receipt = validate_in_p_certificate(
        certificate,
        predicate=predicate,
        validation_instances=validation_instances,
    )
    return StageQInPFinishPayload(request, receipt, algorithm_lean_term)


__all__ = [
    "STAGE_Q_OBJECTIVES",
    "STAGE_Q_PROVE_IN_P_FINISH_ABI",
    "STAGE_Q_REQUEST_SCHEMA",
    "StageQContractError",
    "StageQInPFinishPayload",
    "StageQRequest",
    "close_prove_in_p",
]
