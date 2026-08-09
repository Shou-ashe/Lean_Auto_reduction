from dataclasses import replace

import pytest

from agent.hardness.stage_p_contract import StagePContractError
from agent.hardness.stage_p_runtime import (
    STAGE_P_CHECKPOINT_SCHEMA,
    STAGE_P_RUNTIME_TRACE_SCHEMA,
    StagePImmutableRequest,
    StagePRuntimeGap,
    StagePSequentialAuthoringSession,
)


TASKS = (
    (
        "lawful_presentation",
        "ComplexityReduction.Encoding.StructuralRepresentationCertificate",
    ),
    (
        "program_definition",
        "ComplexityReduction.Agent.Hardness.Authoring.ProgramIndexedReductionTemplate",
    ),
    (
        "semantic_correctness",
        "ComplexityReduction.Agent.Hardness.Authoring.ExecutableSemanticProof",
    ),
    (
        "polytime_or_direct_tm",
        "ComplexityReduction.Agent.Hardness.Authoring.ExecutableDirectTMEvidence",
    ),
)


def digest(value: int) -> str:
    return f"sha256:{value:064x}"


def request(*, max_gap_count: int = 4) -> StagePImmutableRequest:
    return StagePImmutableRequest(
        source_declaration="Benchmark.Source.problem",
        target_declaration="Benchmark.Target.problem",
        source_endpoint_id=digest(1),
        target_endpoint_id=digest(2),
        objective="reduce_to",
        direction="source_to_target",
        request_policy_sha256=digest(3),
        resolved_parameters_sha256=digest(4),
        base_registry_fingerprint=digest(5),
        max_gap_count=max_gap_count,
    )


def gap(
    session: StagePSequentialAuthoringSession,
    ordinal: int,
    *,
    task_class: str | None = None,
    capability_head: str | None = None,
    registry_fingerprint: str | None = None,
    dependency_hash: str | None = None,
    parent_checkpoint_hash: str | None = None,
) -> StagePRuntimeGap:
    default_task, default_head = TASKS[min(ordinal, len(TASKS)) - 1]
    return StagePRuntimeGap(
        request_id=session.request.request_id,
        ordinal=ordinal,
        task_class=task_class or default_task,
        capability_head=capability_head or default_head,
        declaration_signature=f"Benchmark.Generated.gap{ordinal}",
        source_endpoint_id=session.request.source_endpoint_id,
        target_endpoint_id=session.request.target_endpoint_id,
        registry_fingerprint=registry_fingerprint or digest(10 + ordinal),
        dependency_hash=dependency_hash or digest(20 + ordinal),
        parent_checkpoint_hash=(
            parent_checkpoint_hash or session.expected_parent_checkpoint_hash
        ),
        public_preconditions=(digest(30 + ordinal),),
    )


def validate_and_publish(
    session: StagePSequentialAuthoringSession, *, ordinal: int
):
    session.record_transport_attempt(retry=False)
    session.record_model_turn(token_count=1_000 * ordinal)
    session.record_candidate_attempt()
    checkpoint = session.validate_candidate(
        model_response_sha256=digest(100 + ordinal),
        patch_sha256=digest(110 + ordinal),
        candidate_source_sha256=digest(120 + ordinal),
        diagnostics_sha256=digest(130 + ordinal),
        bundle_sha256=digest(140 + ordinal),
        axiom_audit_sha256=digest(150 + ordinal),
    )
    assert checkpoint.schema_version == STAGE_P_CHECKPOINT_SCHEMA
    return session.publish_active(publication_hash=digest(160 + ordinal))


def test_request_identity_is_content_addressed_and_immutable() -> None:
    original = request(max_gap_count=3)
    assert original.request_id.startswith("sha256:")
    assert original.initial_checkpoint_hash.startswith("sha256:")
    original.assert_same(request(max_gap_count=3))
    with pytest.raises(StagePContractError) as captured:
        original.assert_same(replace(original, objective="prove_in_np"))
    assert captured.value.code == "request_or_endpoint_mutation"


def test_stage_p_runtime_completes_four_dynamic_gaps_with_chained_checkpoints() -> None:
    session = StagePSequentialAuthoringSession(request())
    previous_checkpoint_hash = session.request.initial_checkpoint_hash
    for ordinal in range(1, 5):
        active = gap(session, ordinal, parent_checkpoint_hash=previous_checkpoint_hash)
        session.begin_gap(active)
        published = validate_and_publish(session, ordinal=ordinal)
        assert published.parent_checkpoint_hash == previous_checkpoint_hash
        previous_checkpoint_hash = published.checkpoint_hash
        if ordinal < 4:
            next_gap = gap(session, ordinal + 1)
            session.record_fresh_core_resolution(verified=False, next_gap=next_gap)
        else:
            session.record_fresh_core_resolution(verified=True)

    session.record_final_combined_lean(verified=True)
    session.record_standard_axiom_audit(verified=True, audit_sha256=digest(200))
    session.record_release_replay(verified=True)

    report = session.to_dict()
    assert report["schema_version"] == STAGE_P_RUNTIME_TRACE_SCHEMA
    assert report["state"] == "RELEASE_REPLAY"
    assert report["complete"] is True
    assert report["semantic_model_call_count"] == 4
    assert report["http_attempt_count"] == 4
    assert report["transport_retry_count"] == 0
    assert report["fresh_core_resolve_count"] == 4
    assert len(report["checkpoints"]) == 4
    assert len({row["task_class"] for row in report["checkpoints"]}) == 4
    assert report["trace_sha256"].startswith("sha256:")


def test_gap_two_cannot_start_before_publication_and_fresh_core_reveal() -> None:
    session = StagePSequentialAuthoringSession(request(max_gap_count=2))
    session.begin_gap(gap(session, 1))
    with pytest.raises(StagePContractError) as captured:
        session.begin_gap(gap(session, 2))
    assert captured.value.code == "gap_sequence_cycle"


def test_fresh_core_rejects_stale_parent_checkpoint() -> None:
    session = StagePSequentialAuthoringSession(request(max_gap_count=2))
    session.begin_gap(gap(session, 1))
    validate_and_publish(session, ordinal=1)
    stale = gap(session, 2, parent_checkpoint_hash=digest(999))
    with pytest.raises(StagePContractError) as captured:
        session.record_fresh_core_resolution(verified=False, next_gap=stale)
    assert captured.value.code == "candidate_dependency_stale"


@pytest.mark.parametrize("repeat", ["task_class", "dependency_hash"])
def test_fresh_core_rejects_repeated_gap_state(repeat: str) -> None:
    session = StagePSequentialAuthoringSession(request(max_gap_count=2))
    first = gap(session, 1)
    session.begin_gap(first)
    validate_and_publish(session, ordinal=1)
    changes = {repeat: getattr(first, repeat)}
    repeated = gap(session, 2, **changes)
    with pytest.raises(StagePContractError) as captured:
        session.record_fresh_core_resolution(verified=False, next_gap=repeated)
    assert captured.value.code == "gap_sequence_cycle"


def test_fresh_core_requires_registry_change_after_publication() -> None:
    session = StagePSequentialAuthoringSession(request(max_gap_count=2))
    first = gap(session, 1)
    session.begin_gap(first)
    validate_and_publish(session, ordinal=1)
    unchanged = gap(session, 2, registry_fingerprint=first.registry_fingerprint)
    with pytest.raises(StagePContractError) as captured:
        session.record_fresh_core_resolution(verified=False, next_gap=unchanged)
    assert captured.value.code == "published_capability_not_visible"


def test_pending_gap_binding_cannot_be_replaced_before_authoring() -> None:
    session = StagePSequentialAuthoringSession(request(max_gap_count=2))
    session.begin_gap(gap(session, 1))
    validate_and_publish(session, ordinal=1)
    revealed = gap(session, 2)
    session.record_fresh_core_resolution(verified=False, next_gap=revealed)
    replacement = replace(revealed, declaration_signature="Benchmark.Generated.changed")
    with pytest.raises(StagePContractError) as captured:
        session.begin_gap(replacement)
    assert captured.value.code == "request_or_endpoint_mutation"


def test_fifth_gap_is_rejected_even_when_core_returns_an_object() -> None:
    session = StagePSequentialAuthoringSession(request(max_gap_count=4))
    for ordinal in range(1, 5):
        session.begin_gap(gap(session, ordinal))
        validate_and_publish(session, ordinal=ordinal)
        if ordinal < 4:
            session.record_fresh_core_resolution(
                verified=False,
                next_gap=gap(session, ordinal + 1),
            )
    fifth = replace(
        gap(session, 4),
        ordinal=5,
        declaration_signature="Benchmark.Generated.gap5",
        registry_fingerprint=digest(99),
        dependency_hash=digest(1000),
    )
    with pytest.raises(StagePContractError) as captured:
        session.record_fresh_core_resolution(verified=False, next_gap=fifth)
    assert captured.value.code == "gap_count_exceeded"


def test_transport_retries_do_not_consume_semantic_turn_budget() -> None:
    session = StagePSequentialAuthoringSession(
        request(max_gap_count=1),
        max_semantic_turns_per_gap=1,
        max_total_tokens=100,
        max_transport_retries=2,
    )
    session.begin_gap(gap(session, 1))
    session.record_transport_attempt(retry=False)
    session.record_transport_attempt(retry=True)
    session.record_transport_attempt(retry=True)
    assert session.semantic_model_call_count == 0
    assert session.transport_retry_count == 2
    session.record_model_turn(token_count=100)
    assert session.semantic_model_call_count == 1
    with pytest.raises(StagePContractError) as semantic_error:
        session.record_model_turn(token_count=0)
    assert semantic_error.value.code == "authoring_budget_exhausted"
    with pytest.raises(StagePContractError) as transport_error:
        session.record_transport_attempt(retry=True)
    assert transport_error.value.code == "authoring_budget_exhausted"


def test_candidate_validation_requires_a_recorded_compile_attempt() -> None:
    session = StagePSequentialAuthoringSession(request(max_gap_count=1))
    session.begin_gap(gap(session, 1))
    with pytest.raises(StagePContractError) as captured:
        session.validate_candidate(
            model_response_sha256=digest(1),
            patch_sha256=digest(2),
            candidate_source_sha256=digest(3),
            diagnostics_sha256=digest(4),
            bundle_sha256=digest(5),
            axiom_audit_sha256=digest(6),
        )
    assert captured.value.code == "candidate_lean_compile_failed"


def test_final_validation_order_is_fail_closed() -> None:
    session = StagePSequentialAuthoringSession(request(max_gap_count=1))
    session.begin_gap(gap(session, 1))
    validate_and_publish(session, ordinal=1)
    session.record_fresh_core_resolution(verified=True)
    with pytest.raises(StagePContractError) as captured:
        session.record_release_replay(verified=True)
    assert captured.value.code == "gap_sequence_cycle"
    session.record_final_combined_lean(verified=True)
    with pytest.raises(StagePContractError) as axiom_error:
        session.record_standard_axiom_audit(verified=False, audit_sha256=digest(9))
    assert axiom_error.value.code == "sorry_axiom_or_unsafe_candidate"


def test_gap_endpoint_mutation_is_rejected_before_authoring() -> None:
    session = StagePSequentialAuthoringSession(request(max_gap_count=1))
    mutated = replace(gap(session, 1), target_endpoint_id=digest(777))
    with pytest.raises(StagePContractError) as captured:
        session.begin_gap(mutated)
    assert captured.value.code == "request_or_endpoint_mutation"
