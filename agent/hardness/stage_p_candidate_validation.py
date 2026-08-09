"""Exact, content-addressed candidate validation receipts for Stage P."""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Any

from .models import sha256_id
from .stage_p_contract import CAPABILITY_HEADS, SHA256_RE, StagePContractError
from .stage_p_runtime import StagePImmutableRequest, StagePRuntimeGap


STAGE_P_CANDIDATE_EXPECTATION_SCHEMA = "hardness_stage_p_candidate_expectation_v1"
STAGE_P_CANDIDATE_OBSERVATION_SCHEMA = "hardness_stage_p_candidate_observation_v1"
STAGE_P_CANDIDATE_RECEIPT_SCHEMA = "hardness_stage_p_candidate_validation_receipt_v1"


def _require_hash(value: str, *, label: str, code: str) -> None:
    if not isinstance(value, str) or not SHA256_RE.fullmatch(value):
        raise StagePContractError(code, f"{label} is not a content hash")


@dataclass(frozen=True)
class StagePCandidateExpectation:
    request_id: str
    gap_id: str
    candidate_declaration: str
    candidate_source_sha256: str
    exact_type_sha256: str
    capability_head: str
    source_endpoint_id: str
    target_endpoint_id: str
    direction: str
    dependency_fingerprint: str
    expected_program_index_sha256: str | None
    schema_version: str = STAGE_P_CANDIDATE_EXPECTATION_SCHEMA

    @classmethod
    def from_gap(
        cls,
        *,
        request: StagePImmutableRequest,
        gap: StagePRuntimeGap,
        candidate_declaration: str,
        candidate_source_sha256: str,
        expected_program_index_sha256: str | None = None,
    ) -> "StagePCandidateExpectation":
        gap.validate(request)
        value = cls(
            request_id=request.request_id,
            gap_id=gap.gap_id,
            candidate_declaration=candidate_declaration,
            candidate_source_sha256=candidate_source_sha256,
            exact_type_sha256=sha256_id(gap.declaration_signature),
            capability_head=gap.capability_head,
            source_endpoint_id=request.source_endpoint_id,
            target_endpoint_id=request.target_endpoint_id,
            direction=request.direction,
            dependency_fingerprint=gap.dependency_hash,
            expected_program_index_sha256=expected_program_index_sha256,
        )
        value.validate()
        return value

    def validate(self) -> None:
        if self.schema_version != STAGE_P_CANDIDATE_EXPECTATION_SCHEMA:
            raise StagePContractError(
                "candidate_dependency_stale", "candidate expectation schema drifted"
            )
        if not self.candidate_declaration.strip():
            raise StagePContractError(
                "candidate_exact_type_mismatch", "candidate declaration is empty"
            )
        if self.capability_head not in CAPABILITY_HEADS:
            raise StagePContractError(
                "candidate_canonical_head_mismatch", "expected capability head is unsupported"
            )
        if self.direction != "source_to_target":
            raise StagePContractError(
                "candidate_wrong_direction", "expected direction is not canonical"
            )
        for label, value in {
            "request_id": self.request_id,
            "gap_id": self.gap_id,
            "candidate_source_sha256": self.candidate_source_sha256,
            "exact_type_sha256": self.exact_type_sha256,
            "source_endpoint_id": self.source_endpoint_id,
            "target_endpoint_id": self.target_endpoint_id,
            "dependency_fingerprint": self.dependency_fingerprint,
        }.items():
            _require_hash(value, label=label, code="candidate_dependency_stale")
        if self.expected_program_index_sha256 is not None:
            _require_hash(
                self.expected_program_index_sha256,
                label="expected_program_index_sha256",
                code="candidate_program_index_mismatch",
            )


@dataclass(frozen=True)
class StagePCandidateObservation:
    request_id: str
    gap_id: str
    candidate_declaration: str
    candidate_source_sha256: str
    diagnostics_sha256: str
    observed_exact_type_sha256: str
    observed_capability_head: str
    observed_source_endpoint_id: str
    observed_target_endpoint_id: str
    observed_direction: str
    observed_dependency_fingerprint: str
    observed_program_index_sha256: str | None
    axiom_audit_sha256: str
    bundle_sha256: str
    static_policy_verified: bool
    lean_verified: bool
    axiom_verified: bool
    bundle_verified: bool
    compiler_inserted_math_token_count: int = 0
    schema_version: str = STAGE_P_CANDIDATE_OBSERVATION_SCHEMA

    def validate_shape(self) -> None:
        if self.schema_version != STAGE_P_CANDIDATE_OBSERVATION_SCHEMA:
            raise StagePContractError(
                "candidate_dependency_stale", "candidate observation schema drifted"
            )
        if not self.candidate_declaration.strip():
            raise StagePContractError(
                "candidate_exact_type_mismatch", "observed candidate declaration is empty"
            )
        for label, value in {
            "request_id": self.request_id,
            "gap_id": self.gap_id,
            "candidate_source_sha256": self.candidate_source_sha256,
            "diagnostics_sha256": self.diagnostics_sha256,
            "observed_exact_type_sha256": self.observed_exact_type_sha256,
            "observed_source_endpoint_id": self.observed_source_endpoint_id,
            "observed_target_endpoint_id": self.observed_target_endpoint_id,
            "observed_dependency_fingerprint": self.observed_dependency_fingerprint,
            "axiom_audit_sha256": self.axiom_audit_sha256,
            "bundle_sha256": self.bundle_sha256,
        }.items():
            _require_hash(value, label=label, code="candidate_dependency_stale")
        if self.observed_program_index_sha256 is not None:
            _require_hash(
                self.observed_program_index_sha256,
                label="observed_program_index_sha256",
                code="candidate_program_index_mismatch",
            )
        if self.compiler_inserted_math_token_count != 0:
            raise StagePContractError(
                "compiler_math_insertion_detected", "candidate compiler inserted mathematics"
            )


@dataclass(frozen=True)
class StagePCandidateValidationReceipt:
    request_id: str
    gap_id: str
    candidate_declaration: str
    candidate_source_sha256: str
    diagnostics_sha256: str
    exact_type_sha256: str
    capability_head: str
    source_endpoint_id: str
    target_endpoint_id: str
    direction: str
    dependency_fingerprint: str
    program_index_sha256: str | None
    axiom_audit_sha256: str
    bundle_sha256: str
    compiler_inserted_math_token_count: int
    schema_version: str = STAGE_P_CANDIDATE_RECEIPT_SCHEMA

    @property
    def receipt_sha256(self) -> str:
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})

    def to_dict(self) -> dict[str, Any]:
        return {**asdict(self), "receipt_sha256": self.receipt_sha256}


def validate_stage_p_candidate(
    *,
    expectation: StagePCandidateExpectation,
    observation: StagePCandidateObservation,
) -> StagePCandidateValidationReceipt:
    expectation.validate()
    observation.validate_shape()
    if not observation.static_policy_verified:
        raise StagePContractError(
            "candidate_static_policy_failed", "candidate failed the static source policy"
        )
    if not observation.lean_verified:
        raise StagePContractError(
            "candidate_lean_compile_failed", "candidate failed Lean elaboration"
        )
    if (
        observation.request_id != expectation.request_id
        or observation.gap_id != expectation.gap_id
    ):
        raise StagePContractError(
            "request_or_endpoint_mutation", "candidate observation belongs to another task"
        )
    if observation.candidate_declaration != expectation.candidate_declaration:
        raise StagePContractError(
            "candidate_exact_type_mismatch", "candidate declaration identity changed"
        )
    if observation.candidate_source_sha256 != expectation.candidate_source_sha256:
        raise StagePContractError(
            "candidate_dependency_stale", "candidate source differs from the accepted patch"
        )
    if observation.observed_exact_type_sha256 != expectation.exact_type_sha256:
        raise StagePContractError(
            "candidate_exact_type_mismatch", "candidate declaration has the wrong exact type"
        )
    if observation.observed_capability_head != expectation.capability_head:
        raise StagePContractError(
            "candidate_canonical_head_mismatch", "candidate has the wrong canonical head"
        )
    if observation.observed_source_endpoint_id != expectation.source_endpoint_id:
        raise StagePContractError(
            "candidate_wrong_endpoint", "candidate has the wrong exact source endpoint"
        )
    if observation.observed_target_endpoint_id != expectation.target_endpoint_id:
        raise StagePContractError(
            "candidate_wrong_endpoint", "candidate has the wrong exact target endpoint"
        )
    if observation.observed_direction != expectation.direction:
        raise StagePContractError(
            "candidate_wrong_direction", "candidate direction differs from the request"
        )
    if observation.observed_dependency_fingerprint != expectation.dependency_fingerprint:
        raise StagePContractError(
            "candidate_dependency_stale", "candidate dependency state is stale"
        )
    if observation.observed_program_index_sha256 != expectation.expected_program_index_sha256:
        raise StagePContractError(
            "candidate_program_index_mismatch", "candidate components use different programs"
        )
    if not observation.axiom_verified:
        raise StagePContractError(
            "sorry_axiom_or_unsafe_candidate", "candidate failed the standard-axiom gate"
        )
    if not observation.bundle_verified:
        raise StagePContractError(
            "fresh_core_resolve_failed", "candidate bundle failed dependent validation"
        )
    return StagePCandidateValidationReceipt(
        request_id=expectation.request_id,
        gap_id=expectation.gap_id,
        candidate_declaration=expectation.candidate_declaration,
        candidate_source_sha256=observation.candidate_source_sha256,
        diagnostics_sha256=observation.diagnostics_sha256,
        exact_type_sha256=expectation.exact_type_sha256,
        capability_head=expectation.capability_head,
        source_endpoint_id=expectation.source_endpoint_id,
        target_endpoint_id=expectation.target_endpoint_id,
        direction=expectation.direction,
        dependency_fingerprint=expectation.dependency_fingerprint,
        program_index_sha256=expectation.expected_program_index_sha256,
        axiom_audit_sha256=observation.axiom_audit_sha256,
        bundle_sha256=observation.bundle_sha256,
        compiler_inserted_math_token_count=observation.compiler_inserted_math_token_count,
    )
