from __future__ import annotations

from dataclasses import replace

import pytest

from agent.hardness.models import sha256_id
from agent.hardness.stage_p_candidate_validation import (
    StagePCandidateExpectation,
    StagePCandidateObservation,
    validate_stage_p_candidate,
)
from agent.hardness.stage_p_contract import StagePContractError
from agent.hardness.stage_p_runtime import StagePImmutableRequest, StagePRuntimeGap


def digest(label: str) -> str:
    return sha256_id(label)


def request_and_gap() -> tuple[StagePImmutableRequest, StagePRuntimeGap]:
    request = StagePImmutableRequest(
        source_declaration="StageP.Source",
        target_declaration="StageP.Target",
        source_endpoint_id=digest("source"),
        target_endpoint_id=digest("target"),
        objective="reduce_to",
        direction="source_to_target",
        request_policy_sha256=digest("policy"),
        resolved_parameters_sha256=digest("parameters"),
        base_registry_fingerprint=digest("registry"),
        max_gap_count=1,
    )
    gap = StagePRuntimeGap(
        request_id=request.request_id,
        ordinal=1,
        task_class="semantic_correctness",
        capability_head=(
            "ComplexityReduction.Agent.Hardness.Authoring.ExecutableSemanticProof"
        ),
        declaration_signature="StageP.ExpectedType",
        source_endpoint_id=request.source_endpoint_id,
        target_endpoint_id=request.target_endpoint_id,
        registry_fingerprint=request.base_registry_fingerprint,
        dependency_hash=digest("dependency"),
        parent_checkpoint_hash=request.initial_checkpoint_hash,
    )
    return request, gap


def valid_pair() -> tuple[StagePCandidateExpectation, StagePCandidateObservation]:
    request, gap = request_and_gap()
    expectation = StagePCandidateExpectation.from_gap(
        request=request,
        gap=gap,
        candidate_declaration="StageP.Generated.capability",
        candidate_source_sha256=digest("source-body"),
        expected_program_index_sha256=digest("program"),
    )
    observation = StagePCandidateObservation(
        request_id=request.request_id,
        gap_id=gap.gap_id,
        candidate_declaration=expectation.candidate_declaration,
        candidate_source_sha256=expectation.candidate_source_sha256,
        diagnostics_sha256=digest("diagnostics"),
        observed_exact_type_sha256=expectation.exact_type_sha256,
        observed_capability_head=expectation.capability_head,
        observed_source_endpoint_id=expectation.source_endpoint_id,
        observed_target_endpoint_id=expectation.target_endpoint_id,
        observed_direction=expectation.direction,
        observed_dependency_fingerprint=expectation.dependency_fingerprint,
        observed_program_index_sha256=expectation.expected_program_index_sha256,
        axiom_audit_sha256=digest("axiom"),
        bundle_sha256=digest("bundle"),
        static_policy_verified=True,
        lean_verified=True,
        axiom_verified=True,
        bundle_verified=True,
    )
    return expectation, observation


def test_valid_candidate_produces_a_content_addressed_receipt() -> None:
    expectation, observation = valid_pair()
    receipt = validate_stage_p_candidate(
        expectation=expectation, observation=observation
    )
    assert receipt.candidate_source_sha256 == observation.candidate_source_sha256
    assert receipt.receipt_sha256.startswith("sha256:")
    assert receipt.to_dict()["receipt_sha256"] == receipt.receipt_sha256


@pytest.mark.parametrize(
    ("changes", "code"),
    [
        ({"static_policy_verified": False}, "candidate_static_policy_failed"),
        ({"lean_verified": False}, "candidate_lean_compile_failed"),
        ({"request_id": digest("foreign-request")}, "request_or_endpoint_mutation"),
        ({"candidate_declaration": "StageP.Other"}, "candidate_exact_type_mismatch"),
        ({"candidate_source_sha256": digest("wrong-source-body")}, "candidate_dependency_stale"),
        ({"observed_exact_type_sha256": digest("wrong-type")}, "candidate_exact_type_mismatch"),
        ({"observed_capability_head": "ComplexityReduction.Certificate.CertifiedReduction"}, "candidate_canonical_head_mismatch"),
        ({"observed_source_endpoint_id": digest("wrong-source")}, "candidate_wrong_endpoint"),
        ({"observed_target_endpoint_id": digest("wrong-target")}, "candidate_wrong_endpoint"),
        ({"observed_direction": "target_to_source"}, "candidate_wrong_direction"),
        ({"observed_dependency_fingerprint": digest("stale")}, "candidate_dependency_stale"),
        ({"observed_program_index_sha256": digest("other-program")}, "candidate_program_index_mismatch"),
        ({"axiom_verified": False}, "sorry_axiom_or_unsafe_candidate"),
        ({"bundle_verified": False}, "fresh_core_resolve_failed"),
        ({"compiler_inserted_math_token_count": 1}, "compiler_math_insertion_detected"),
    ],
)
def test_candidate_validation_fails_at_the_exact_trust_gate(
    changes: dict[str, object], code: str
) -> None:
    expectation, observation = valid_pair()
    with pytest.raises(StagePContractError) as captured:
        validate_stage_p_candidate(
            expectation=expectation,
            observation=replace(observation, **changes),
        )
    assert captured.value.code == code
