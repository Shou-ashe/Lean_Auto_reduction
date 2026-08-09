import json
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.benchmark import load_benchmark_suite
from agent.hardness.stage_o_contract import (
    EXPECTED_NEGATIVE_FAILURES,
    STAGE_O_ACTION_SCHEMA,
    STAGE_O_CONTRACT_REPORT_SCHEMA,
    STAGE_O_FAILURE_CODES,
    STAGE_O_OFFLINE_REPORT_SCHEMA,
    STAGE_O_REPORT_SCHEMA,
    CapabilityPromotionManifest,
    LeanValidationCacheKey,
    SequentialAuthoringTrace,
    StageOContractError,
    audit_stage_o_prompt,
    build_contract_candidate_set,
    build_stage_o_contract_prompt,
    candidate_rejection_reasons,
    globally_valid_candidate,
    inspect_packet,
    load_lean_service_microbenchmark,
    locally_valid_candidate,
    parse_stage_o_action,
    stable_gap_id,
    stability_aggregate_skeleton,
    stage_o_report_skeleton,
    validate_stage_o_suites,
    validate_stage_o_terminal_action,
)
from agent.hardness.models import sha256_id


ROOT = Path(__file__).resolve().parents[1]
POSITIVE_SUITE = ROOT / "Benchmark" / "Hardness" / "Suites" / "stage_o_multi_gap.json"
NEGATIVE_SUITE = ROOT / "Benchmark" / "Hardness" / "Suites" / "stage_o_adversarial.json"
MICROBENCHMARK = (
    ROOT
    / "Benchmark"
    / "Hardness"
    / "Suites"
    / "stage_o_lean_service_microbenchmark.json"
)


def stage_o_cases():
    positives = load_benchmark_suite(POSITIVE_SUITE)
    negatives = load_benchmark_suite(NEGATIVE_SUITE)
    return validate_stage_o_suites(positives, negatives)


def test_stage_o_freezes_exact_8_plus_8_matrix_and_public_boundaries() -> None:
    cases = stage_o_cases()
    assert len(cases) == 16
    assert sum(case.is_positive for case in cases) == 8
    assert sum(not case.is_positive for case in cases) == 8
    assert {case.expected.final_failure_code for case in cases if not case.is_positive} == set(
        EXPECTED_NEGATIVE_FAILURES.values()
    )
    assert all(case.evaluation_lane == "stage_o" for case in cases)
    assert all("expected" not in case.stage_o for case in cases)
    assert all("coverage" not in case.stage_o for case in cases)
    assert all("case_id" not in case.stage_o for case in cases)


def test_stage_o_competitive_contract_has_real_local_choice_and_one_global_winner() -> None:
    positives = [case for case in stage_o_cases() if case.is_positive]
    for case in positives:
        candidate_set = build_contract_candidate_set(case)
        assert 3 <= len(candidate_set.candidates) <= 8
        assert sum(
            locally_valid_candidate(candidate, candidate_set)
            for candidate in candidate_set.candidates
        ) >= 2
        assert sum(
            globally_valid_candidate(candidate, candidate_set)
            for candidate in candidate_set.candidates
        ) == 1


def test_stage_o_negative_contracts_have_precise_deterministic_reasons() -> None:
    negatives = [case for case in stage_o_cases() if not case.is_positive]
    for case in negatives:
        candidate_set = build_contract_candidate_set(case)
        assert not any(
            globally_valid_candidate(candidate, candidate_set)
            for candidate in candidate_set.candidates
        )
        reasons = {
            reason
            for candidate in candidate_set.candidates
            for reason in candidate_rejection_reasons(candidate, candidate_set)
        }
        assert case.expected.final_failure_code in reasons
        assert case.expected.final_failure_code in STAGE_O_FAILURE_CODES


def test_stage_o_prompt_contains_only_public_contract_and_no_case_id() -> None:
    for case in stage_o_cases():
        candidate_set = build_contract_candidate_set(case)
        inspected = [candidate.packet_id for candidate in candidate_set.candidates[:3]]
        prompt = build_stage_o_contract_prompt(
            candidate_set=candidate_set,
            inspected_packet_ids=inspected,
        )
        assert case.id not in prompt
        assert "final_status" not in prompt
        assert "final_failure_code" not in prompt
        payload = json.loads(prompt)
        assert "inspect_packet" not in payload["return_one_of"]
        audit_stage_o_prompt(payload, forbidden_values=(case.id,))

        uninspected_payload = json.loads(
            build_stage_o_contract_prompt(
                candidate_set=candidate_set,
                inspected_packet_ids=[],
            )
        )
        assert uninspected_payload["return_one_of"]["inspect_packet"]["action"] == "inspect_packet"
        terminal_payload = json.loads(
            build_stage_o_contract_prompt(
                candidate_set=candidate_set,
                inspected_packet_ids=[],
                remaining_model_turns=1,
            )
        )
        assert "inspect_packet" not in terminal_payload["return_one_of"]
        assert terminal_payload["limits"]["must_terminate_this_turn"] is True


def test_inspect_packet_requires_retrieval_and_enforces_three_packet_budget() -> None:
    case = next(case for case in stage_o_cases() if case.is_positive)
    candidate_set = build_contract_candidate_set(case)
    packet_ids = [candidate.packet_id for candidate in candidate_set.candidates]
    inspected = inspect_packet(
        candidate_set,
        packet_ids[0],
        retrieved_packet_ids=packet_ids,
    )
    assert inspected["packet_id"] == packet_ids[0]
    with pytest.raises(StageOContractError) as unknown:
        inspect_packet(
            candidate_set,
            packet_ids[0],
            retrieved_packet_ids=packet_ids[1:],
        )
    assert unknown.value.code == "unknown_packet"
    with pytest.raises(StageOContractError) as exhausted:
        inspect_packet(
            candidate_set,
            packet_ids[3],
            retrieved_packet_ids=packet_ids,
            already_inspected=packet_ids[:3],
        )
    assert exhausted.value.code == "inspect_budget_exhausted"


def test_select_packet_preserves_model_choice_and_immutable_bindings() -> None:
    case = next(case for case in stage_o_cases() if case.is_positive)
    candidate_set = build_contract_candidate_set(case)
    candidate = next(
        candidate
        for candidate in candidate_set.candidates
        if globally_valid_candidate(candidate, candidate_set)
    )
    payload = {
        "schema_version": STAGE_O_ACTION_SCHEMA,
        "action": "select_packet",
        "session_id": candidate_set.session_id,
        "packet_id": candidate.packet_id,
        "candidate_kind": candidate.candidate_kind,
        "typed_bindings": {
            "input_endpoint_id": candidate.input_endpoint_id,
            "output_endpoint_id": candidate.output_endpoint_id,
            "direction": candidate.direction,
            "capability_kind": candidate.capability_kind,
        },
        "dependencies": list(candidate.dependencies),
        "explanation": "The packet preserves the exact endpoints and all public dependencies exist.",
    }
    action = parse_stage_o_action(json.dumps(payload), candidate_set=candidate_set)
    validate_stage_o_terminal_action(action, candidate_set=candidate_set)
    assert action.packet_id == candidate.packet_id
    bad = json.loads(json.dumps(payload))
    bad["typed_bindings"]["direction"] = "identity"
    with pytest.raises(StageOContractError) as mismatch:
        parse_stage_o_action(json.dumps(bad), candidate_set=candidate_set)
    assert mismatch.value.code == "packet_binding_mismatch"


def test_stop_authoring_is_allowed_only_when_no_global_candidate_exists() -> None:
    negative = next(case for case in stage_o_cases() if case.id == "o-unsupported-checker")
    candidate_set = build_contract_candidate_set(negative)
    payload = {
        "schema_version": STAGE_O_ACTION_SCHEMA,
        "action": "stop_authoring",
        "session_id": candidate_set.session_id,
        "checked_packet_ids": [candidate.packet_id for candidate in candidate_set.candidates],
        "missing_conditions": ["No packet has the required supported capability kind."],
        "explanation": "All retrieved packets expose an unsupported checker capability.",
    }
    action = parse_stage_o_action(json.dumps(payload), candidate_set=candidate_set)
    validate_stage_o_terminal_action(action, candidate_set=candidate_set)

    positive = next(case for case in stage_o_cases() if case.is_positive)
    positive_set = build_contract_candidate_set(positive)
    bad = replace(action, session_id=positive_set.session_id)
    with pytest.raises(StageOContractError) as stopped:
        validate_stage_o_terminal_action(bad, candidate_set=positive_set)
    assert stopped.value.code == "model_stopped_with_valid_candidate"


def test_two_gap_state_machine_requires_every_fresh_resolve_and_distinct_gap() -> None:
    request_id = sha256_id({"request": "stage-o-two-gap"})
    gap1 = stable_gap_id(
        request_id=request_id,
        ordinal=1,
        registry_fingerprint=sha256_id({"registry": 0}),
        source_endpoint_id=sha256_id({"source": 0}),
        target_endpoint_id=sha256_id({"target": 0}),
        capability_head="ComplexityReduction.Encoding.StructuralRepresentationCertificate",
        dependency_hash=sha256_id({"dependency": 0}),
    )
    gap2 = stable_gap_id(
        request_id=request_id,
        ordinal=2,
        registry_fingerprint=sha256_id({"registry": 1}),
        source_endpoint_id=sha256_id({"source": 0}),
        target_endpoint_id=sha256_id({"target": 0}),
        capability_head="ComplexityReduction.Certificate.CertifiedReduction",
        dependency_hash=sha256_id({"dependency": 1}),
    )
    assert gap1 != gap2
    trace = SequentialAuthoringTrace(request_id=request_id)
    trace = trace.advance("AUTHORING_GAP_1", gap_id=gap1)
    trace = trace.advance("GAP_1_BUNDLE_VALIDATED")
    trace = trace.advance("GAP_1_CASE_LOCAL_PUBLISHED")
    trace = trace.advance("FRESH_CORE_RESOLVE_1")
    trace = trace.advance("CORE_BLOCKED_GAP_2")
    trace = trace.advance("AUTHORING_GAP_2", gap_id=gap2)
    trace = trace.advance("GAP_2_BUNDLE_VALIDATED")
    trace = trace.advance("FRESH_CORE_RESOLVE_2")
    trace = trace.advance("CORE_VERIFIED")
    trace = trace.advance("FINAL_COMBINED_LEAN")
    trace = trace.advance("RELEASE_REPLAY")
    assert trace.complete

    with pytest.raises(StageOContractError) as skipped:
        SequentialAuthoringTrace(request_id=request_id).advance("GAP_1_BUNDLE_VALIDATED")
    assert skipped.value.code == "gap_sequence_mismatch"


def test_gap1_dependency_change_changes_gap2_identity() -> None:
    fields = {
        "request_id": sha256_id({"request": 1}),
        "ordinal": 2,
        "registry_fingerprint": sha256_id({"registry": 1}),
        "source_endpoint_id": sha256_id({"source": 1}),
        "target_endpoint_id": sha256_id({"target": 1}),
        "capability_head": "ComplexityReduction.Certificate.NativeTMInNP",
    }
    first = stable_gap_id(**fields, dependency_hash=sha256_id({"gap1": "first"}))
    second = stable_gap_id(**fields, dependency_hash=sha256_id({"gap1": "changed"}))
    assert first != second


def test_promotion_manifest_is_content_addressed_and_hash_complete() -> None:
    digest = lambda label: sha256_id({"hash": label})
    manifest = CapabilityPromotionManifest(
        toolchain="leanprover/lean4:v4.29.0",
        lake_manifest_sha256=digest("lake"),
        base_registry_fingerprint=digest("registry"),
        source_sha256=digest("source"),
        dependency_sha256=(digest("dependency"),),
        declaration="StageO.Published.capability",
        source_endpoint_id=digest("source-endpoint"),
        target_endpoint_id=digest("target-endpoint"),
        direction="source_to_target",
        capability_head="ComplexityReduction.Certificate.CertifiedReduction",
        axiom_audit_sha256=digest("axiom"),
        candidate_sha256=digest("candidate"),
        bundle_sha256=digest("bundle"),
        final_request_precheck_sha256=digest("precheck"),
        producer_run_id=digest("run"),
    )
    manifest.validate()
    changed = replace(manifest, source_sha256=digest("changed-source"))
    changed.validate()
    assert changed.capability_hash != manifest.capability_hash
    with pytest.raises(StageOContractError) as invalid:
        replace(manifest, source_sha256="missing-prefix").validate()
    assert invalid.value.code == "capability_promotion_failed"


def test_lean_cache_key_covers_content_namespace_allowlist_and_profile() -> None:
    digest = lambda label: sha256_id({"hash": label})
    key = LeanValidationCacheKey(
        toolchain="leanprover/lean4:v4.29.0",
        lake_manifest_sha256=digest("lake"),
        base_registry_fingerprint=digest("registry"),
        complete_source_sha256=digest("source"),
        dependency_sha256=(digest("dependency"),),
        namespace="StageO.Session.A",
        editable_allowlist=("Generated/StageO/SessionA.lean",),
        validation_profile="candidate_precheck",
    )
    first = key.cache_key
    assert replace(key, namespace="StageO.Session.B").cache_key != first
    assert replace(key, dependency_sha256=(digest("changed"),)).cache_key != first
    with pytest.raises(StageOContractError) as incomplete:
        replace(key, editable_allowlist=()).cache_key
    assert incomplete.value.code == "lean_cache_key_incomplete"


def test_lean_service_microbenchmark_and_report_contracts_are_frozen() -> None:
    benchmark = load_lean_service_microbenchmark(MICROBENCHMARK)
    assert benchmark["repeat_count"] == 20
    assert benchmark["gates"]["warm_p50_over_cold_p50_max"] == 0.5
    assert stage_o_report_skeleton(offline=True)["schema_version"] == STAGE_O_OFFLINE_REPORT_SCHEMA
    assert stage_o_report_skeleton(offline=False)["schema_version"] == STAGE_O_REPORT_SCHEMA
    assert (
        stage_o_report_skeleton(offline=False, contract_only=True)["schema_version"]
        == STAGE_O_CONTRACT_REPORT_SCHEMA
    )
    assert stability_aggregate_skeleton()["run_reports"] == []
