from __future__ import annotations

import hashlib
import json
import threading
import time
from dataclasses import replace
from pathlib import Path

import pytest

import agent.hardness.lean_validation_service as lean_service_module
import agent.hardness.stage_o_benchmark as stage_o_benchmark_module
from agent.hardness.benchmark import load_benchmark_suite
from agent.hardness.capability_promotion import (
    PromotionWaveBarrier,
    RunLocalPublishedRegistry,
)
from agent.hardness.lean_validation_service import LeanValidationService, sha256_text
from agent.hardness.models import CommandResult, sha256_id
from agent.hardness.model_client import ModelResponse
from agent.hardness.sequential_authoring import (
    ImmutableStageORequest,
    RuntimeGap,
    SequentialAuthoringSession,
)
from agent.hardness.stage_o_artifact import (
    build_final_artifact_source,
    build_producer_capability_source,
)
from agent.hardness.stage_o_contract import (
    CapabilityPromotionManifest,
    LeanValidationCacheKey,
    StageOContractError,
    candidate_rejection_reasons,
    globally_valid_candidate,
)
from agent.hardness.stage_o_runtime import (
    RuntimeCandidateContext,
    SimulatedStageOClient,
    build_runtime_candidate_set,
    drive_candidate_selection,
)


ROOT = Path(__file__).resolve().parents[1]
POSITIVE = load_benchmark_suite(ROOT / "Gate/Suites/stage_o_multi_gap.json")
NEGATIVE = load_benchmark_suite(ROOT / "Gate/Suites/stage_o_adversarial.json")


def _hash(label: str) -> str:
    return sha256_id({"label": label})


def _case(suite: object, case_id: str):
    return next(case for case in suite.cases if case.id == case_id)


def test_runtime_candidates_have_two_real_global_choices_and_preserve_model_selection() -> None:
    case = _case(POSITIVE, "o-core-ambiguous-fixed-target")
    candidate_set = build_runtime_candidate_set(case)
    valid = [
        candidate
        for candidate in candidate_set.candidates
        if globally_valid_candidate(candidate, candidate_set)
    ]
    assert 3 <= len(candidate_set.candidates) <= 8
    assert len(valid) == 2

    outcome = drive_candidate_selection(
        client=SimulatedStageOClient(candidate_set),
        candidate_set=candidate_set,
    )
    assert outcome.selected_packet_id in {candidate.packet_id for candidate in valid}
    assert outcome.model_choice_preserved
    assert outcome.inspected_packet_ids == (outcome.selected_packet_id,)


def test_runtime_rejects_invalid_model_choice_then_exposes_public_feedback() -> None:
    case = _case(POSITIVE, "o-core-ambiguous-fixed-target")
    candidate_set = build_runtime_candidate_set(case)
    invalid = next(candidate for candidate in candidate_set.candidates if candidate.direction == "identity")
    valid = next(
        candidate
        for candidate in candidate_set.candidates
        if globally_valid_candidate(candidate, candidate_set)
    )

    def selection(candidate):
        return {
            "schema_version": "hardness_stage_o_action_v1",
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
            "explanation": "Exercise public rejection feedback.",
        }

    class SequenceClient:
        config = SimulatedStageOClient(candidate_set).config

        def __init__(self) -> None:
            self.responses = [selection(invalid), selection(valid)]
            self.prompts: list[str] = []

        def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
            del system
            self.prompts.append(prompt)
            content = json.dumps(self.responses.pop(0), sort_keys=True)
            return ModelResponse(
                called=True,
                ok=True,
                content=content,
                error=None,
                status_code=200,
                duration_seconds=0.01,
                usage={"total_tokens": 100},
                attempts=1,
            )

    client = SequenceClient()
    observed = []
    outcome = drive_candidate_selection(
        client=client,
        candidate_set=candidate_set,
        on_turn=observed.append,
    )
    assert outcome.selected_packet_id == valid.packet_id
    assert len(observed) == 2
    assert not observed[0].ok
    assert "wrong_direction" in (observed[0].error or "")
    assert "wrong_direction" in json.loads(client.prompts[1])["previous_rejection"]
    assert observed[1].ok
    assert outcome.real_model_call_count == 2
    assert outcome.http_ok_count == 2
    assert not observed[0].ok and observed[0].http_ok


def test_ablation_reports_missing_original_selection_instead_of_crashing(tmp_path: Path) -> None:
    case = _case(POSITIVE, "o-core-ambiguous-fixed-target")
    outcome = stage_o_benchmark_module.StageOCaseOutcome(case=case, row={}, selections=[])
    rows = stage_o_benchmark_module._run_ablations(
        outcomes=[outcome],
        output_root=tmp_path,
        real=False,
        deepseek_config=None,
    )
    assert rows[0]["outcome"] == "source_selection_unavailable"
    assert not rows[0]["success"]


def test_duplicate_inspection_is_rejected_with_a_terminal_correction_turn() -> None:
    case = _case(POSITIVE, "o-capability-consumer")
    candidate_set = build_runtime_candidate_set(
        case,
        context=RuntimeCandidateContext(published_capability_hash=_hash("published")),
    )
    inspected_candidates = list(candidate_set.candidates[:3])
    valid = next(
        candidate
        for candidate in candidate_set.candidates
        if globally_valid_candidate(candidate, candidate_set)
    )

    def inspect(candidate):
        return {
            "schema_version": "hardness_stage_o_action_v1",
            "action": "inspect_packet",
            "session_id": candidate_set.session_id,
            "packet_id": candidate.packet_id,
            "explanation": "Inspect bounded public metadata.",
        }

    select = {
        "schema_version": "hardness_stage_o_action_v1",
        "action": "select_packet",
        "session_id": candidate_set.session_id,
        "packet_id": valid.packet_id,
        "candidate_kind": valid.candidate_kind,
        "typed_bindings": {
            "input_endpoint_id": valid.input_endpoint_id,
            "output_endpoint_id": valid.output_endpoint_id,
            "direction": valid.direction,
            "capability_kind": valid.capability_kind,
        },
        "dependencies": list(valid.dependencies),
        "explanation": "Select after bounded inspection.",
    }

    class SequenceClient:
        config = SimulatedStageOClient(candidate_set).config

        def __init__(self) -> None:
            self.responses = [
                *(inspect(candidate) for candidate in inspected_candidates),
                inspect(inspected_candidates[-1]),
                select,
            ]
            self.prompts: list[str] = []

        def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
            del system
            self.prompts.append(prompt)
            content = json.dumps(self.responses.pop(0), sort_keys=True)
            return ModelResponse(
                called=True,
                ok=True,
                content=content,
                error=None,
                status_code=200,
                duration_seconds=0.01,
                usage={"total_tokens": 100},
                attempts=1,
            )

    client = SequenceClient()
    outcome = drive_candidate_selection(
        client=client,
        candidate_set=candidate_set,
        max_turns=5,
    )
    assert outcome.selected_packet_id == valid.packet_id
    assert len(outcome.turns) == 5
    assert "already inspected" in (outcome.turns[3].error or "")
    final_prompt = json.loads(client.prompts[-1])
    assert final_prompt["limits"]["must_terminate_this_turn"] is True
    assert "inspect_packet" not in final_prompt["return_one_of"]


def test_case_model_call_budget_is_enforced_for_offline_negative(tmp_path: Path) -> None:
    case = _case(NEGATIVE, "o-cycle-dag-blocked")
    outcome = stage_o_benchmark_module._run_case_safely(
        case=case,
        case_root=tmp_path / case.id,
        real=False,
        deepseek_config=None,
    )
    assert outcome.row["status"] == "BLOCKED"
    assert len(outcome.selections[0].turns) <= int(case.resources["max_model_calls"])


def test_ablation_uses_same_registry_and_selects_a_fresh_alternative() -> None:
    case = _case(POSITIVE, "o-core-ambiguous-auto-target")
    original = build_runtime_candidate_set(case)
    first = drive_candidate_selection(
        client=SimulatedStageOClient(original, choice_salt="paired"),
        candidate_set=original,
    )
    ablated = build_runtime_candidate_set(
        case,
        context=RuntimeCandidateContext(
            registry_fingerprint=original.registry_fingerprint,
            removed_packet_ids=frozenset({first.selected_packet_id or ""}),
        ),
    )
    second = drive_candidate_selection(
        client=SimulatedStageOClient(ablated, choice_salt="paired"),
        candidate_set=ablated,
    )
    assert ablated.registry_fingerprint == original.registry_fingerprint
    assert second.selected_packet_id != first.selected_packet_id
    assert second.action.action == "select_packet"
    assert first.turns[-1].response_sha256 != second.turns[-1].response_sha256


def test_negative_runtime_profiles_keep_precise_public_blockers() -> None:
    for case in NEGATIVE.cases:
        candidate_set = build_runtime_candidate_set(case)
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
        outcome = drive_candidate_selection(
            client=SimulatedStageOClient(candidate_set),
            candidate_set=candidate_set,
        )
        assert outcome.action.action == "stop_authoring"


def test_sequential_session_enforces_two_fresh_resolves_and_stale_parent_rejection() -> None:
    request = ImmutableStageORequest(
        input_declaration="StageO.source",
        input_kind="predicate",
        objective="reduce_to",
        target_declaration="StageO.target",
        capability_head="ComplexityReduction.Certificate.CertifiedReduction",
    )
    session = SequentialAuthoringSession(request)
    gap1 = RuntimeGap(
        request_id=request.request_id,
        ordinal=1,
        registry_fingerprint=_hash("registry-0"),
        source_endpoint_id=_hash("source-0"),
        target_endpoint_id=_hash("presentation"),
        capability_head="ComplexityReduction.Encoding.StructuralRepresentationCertificate",
        dependency_hash=_hash("dependency-0"),
    )
    session.begin_gap(gap1)
    session.record_model_call(token_count=1200)
    session.attempt_candidate()
    checkpoint1 = session.validate_active_bundle(
        candidate_hash=_hash("candidate-1"), bundle_hash=_hash("bundle-1")
    )
    checkpoint1 = session.publish_gap_one(publication_hash=_hash("publication-1"))
    gap2 = RuntimeGap(
        request_id=request.request_id,
        ordinal=2,
        registry_fingerprint=_hash("registry-1"),
        source_endpoint_id=_hash("presentation"),
        target_endpoint_id=_hash("target"),
        capability_head="ComplexityReduction.Certificate.CertifiedReduction",
        dependency_hash=checkpoint1.checkpoint_hash,
    )
    session.resolve_after_gap_one(gap2)
    session.begin_gap(gap2)
    session.record_model_call(token_count=1400)
    session.attempt_candidate()
    checkpoint2 = session.validate_active_bundle(
        candidate_hash=_hash("candidate-2"), bundle_hash=_hash("bundle-2")
    )
    session.validate_gap_two_checkpoint(checkpoint2)
    with pytest.raises(StageOContractError, match="stale_gap_dependency"):
        session.validate_gap_two_checkpoint(
            replace(checkpoint2, previous_checkpoint_hash=_hash("stale-parent"))
        )
    session.resolve_after_gap_two(verified=True)
    session.record_final_combined_lean(verified=True)
    session.record_release_replay(verified=True)
    assert session.trace.complete
    assert session.fresh_core_resolve_count == 2
    assert len(set(session.trace.gap_ids)) == 2


def test_sequential_session_rejects_parallel_active_gap_and_budget_overflow() -> None:
    request = ImmutableStageORequest("S", "predicate", "reduce_to", "T", "Head")
    session = SequentialAuthoringSession(request, max_model_calls=1, max_total_tokens=10)
    gap = RuntimeGap(
        request.request_id,
        1,
        _hash("r"),
        _hash("s"),
        _hash("t"),
        "Head",
        _hash("d"),
    )
    session.begin_gap(gap)
    with pytest.raises(StageOContractError, match="two authoring nodes"):
        session.begin_gap(gap)
    session.record_model_call(token_count=10)
    with pytest.raises(StageOContractError, match="budget exhausted"):
        session.record_model_call(token_count=1)


def test_wave_barrier_forbids_early_consumer_and_seals_at_zero_active_jobs() -> None:
    barrier = PromotionWaveBarrier()
    barrier.start(job_id="producer", wave="producer")
    with pytest.raises(StageOContractError, match="producer wave"):
        barrier.start(job_id="consumer", wave="consumer")
    barrier.finish(job_id="producer")
    barrier.seal_producer_wave()
    barrier.start(job_id="consumer", wave="consumer")
    barrier.finish(job_id="consumer")
    assert not barrier.active_jobs
    assert barrier.producer_wave_sealed


def test_promotion_is_content_addressed_read_only_and_excludable(tmp_path: Path) -> None:
    source = tmp_path / "Candidate.lean"
    source.write_text("import ComplexityReduction.Agent.Hardness.Runtime\n\ndef capability : True := True.intro\n")
    source_hash = "sha256:" + hashlib.sha256(source.read_bytes()).hexdigest()
    run_id = _hash("run")
    manifest = CapabilityPromotionManifest(
        toolchain="leanprover/lean4:v4.29.0",
        lake_manifest_sha256=_hash("lake"),
        base_registry_fingerprint=_hash("registry"),
        source_sha256=source_hash,
        dependency_sha256=(_hash("dependency"),),
        declaration="Benchmark.Hardness.PublishedCapabilities.Habc.Capability.capability",
        source_endpoint_id=_hash("source"),
        target_endpoint_id=_hash("target"),
        direction="source_to_target",
        capability_head="ComplexityReduction.Certificate.CertifiedReduction",
        axiom_audit_sha256=_hash("axiom"),
        candidate_sha256=source_hash,
        bundle_sha256=_hash("bundle"),
        final_request_precheck_sha256=_hash("precheck"),
        producer_run_id=run_id,
    )
    registry = RunLocalPublishedRegistry(tmp_path / "published", run_id=run_id)
    registry.register_job_local_candidate(source_hash)
    registry.assert_unpublished_isolation(source_hash)
    published = registry.publish(
        manifest=manifest,
        module="Benchmark.Hardness.PublishedCapabilities.Habc.Capability",
        candidate_source=source,
    )
    registry.require_visible(published.capability_hash)
    with pytest.raises(StageOContractError, match="does not contain"):
        registry.require_visible(
            published.capability_hash, excluded=frozenset({published.capability_hash})
        )
    assert published.source_file.stat().st_mode & 0o222 == 0
    for path in (published.pack_root, published.pack_root / "src", published.source_file.parent):
        path.chmod(0o755)
    published.source_file.chmod(0o644)
    published.manifest_file.chmod(0o644)


def test_lean_validation_service_owns_sessions_and_reuses_only_exact_key(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    def fake_run_command(*args: object, **kwargs: object) -> CommandResult:
        del args, kwargs
        return CommandResult(
            command=("lake", "env", "lean", "Validation.lean"),
            exit_code=0,
            stdout="",
            stderr="",
            duration_seconds=0.01,
        )

    monkeypatch.setattr(lean_service_module, "run_command", fake_run_command)
    service = LeanValidationService(
        lean_root=ROOT / "Lean",
        service_root=tmp_path / "service",
    )
    source = "import Benchmark.Hardness.Inputs.StageO.Inputs\n#check Benchmark.Hardness.Inputs.StageO.Inputs.coreAmbiguousFixedSource\n"
    namespace = "Benchmark.Hardness.StageO.SessionA"
    key = LeanValidationCacheKey(
        toolchain="leanprover/lean4:v4.29.0",
        lake_manifest_sha256=_hash("lake"),
        base_registry_fingerprint=_hash("registry"),
        complete_source_sha256=sha256_text(source),
        dependency_sha256=(_hash("dependency"),),
        namespace=namespace,
        editable_allowlist=("readonly-import-check",),
        validation_profile="stage_o_strict_v1",
    )
    session_id = service.start_session(owner="case-a", namespace=namespace)
    first = service.validate(
        session_id=session_id,
        owner="case-a",
        key=key,
        source=source,
        dependency_sha256=key.dependency_sha256,
    )
    second = service.validate(
        session_id=session_id,
        owner="case-a",
        key=key,
        source=source,
        dependency_sha256=key.dependency_sha256,
    )
    assert first.verified and not first.cache_hit
    assert second.verified and second.cache_hit
    with pytest.raises(StageOContractError, match="another case"):
        service.validate(
            session_id=session_id,
            owner="case-b",
            key=key,
            source=source,
            dependency_sha256=key.dependency_sha256,
        )
    with pytest.raises(StageOContractError, match="source differs"):
        service.validate(
            session_id=session_id,
            owner="case-a",
            key=key,
            source=source + "\n#check True\n",
            dependency_sha256=key.dependency_sha256,
        )


def test_lean_microbenchmark_runs_twenty_real_cold_checks_with_four_way_bound(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    lock = threading.Lock()
    active = 0
    max_active = 0
    call_count = 0

    def fake_run_command(*args: object, **kwargs: object) -> CommandResult:
        nonlocal active, max_active, call_count
        del args, kwargs
        with lock:
            active += 1
            call_count += 1
            max_active = max(max_active, active)
        time.sleep(0.01)
        with lock:
            active -= 1
        return CommandResult(
            command=("lake", "env", "lean", "Validation.lean"),
            exit_code=0,
            stdout="",
            stderr="",
            duration_seconds=0.01,
        )

    monkeypatch.setattr(lean_service_module, "run_command", fake_run_command)
    service = LeanValidationService(
        lean_root=ROOT / "Lean",
        service_root=tmp_path / "parallel-service",
    )
    source = "namespace StageOValidation.Parallel\n#check True\nend StageOValidation.Parallel\n"
    namespace = "StageOValidation.Parallel"
    key = LeanValidationCacheKey(
        toolchain="leanprover/lean4:v4.29.0",
        lake_manifest_sha256=_hash("parallel-lake"),
        base_registry_fingerprint=_hash("parallel-registry"),
        complete_source_sha256=sha256_text(source),
        dependency_sha256=(_hash("parallel-dependency"),),
        namespace=namespace,
        editable_allowlist=("readonly-import-check",),
        validation_profile="stage_o_strict_v1",
    )
    result = service.microbenchmark(
        owner="parallel-owner",
        namespace=namespace,
        key=key,
        source=source,
        dependency_sha256=key.dependency_sha256,
    )
    assert result["repeat_count"] == 20
    assert result["cold_process_jobs"] == 4
    assert len(result["cold_seconds"]) == 20
    assert call_count == 21
    assert 2 <= max_active <= 4


def test_stage_o_final_artifact_source_imports_and_audits_promoted_pack(tmp_path: Path) -> None:
    module = "StageOPublished.Htest.Capability"
    declaration = "StageOPublished.Htest.capability"
    source_root = tmp_path / "published-src"
    source_file = source_root / Path(*module.split(".")).with_suffix(".lean")
    source_file.parent.mkdir(parents=True)
    source_file.write_text(build_producer_capability_source(module=module), encoding="utf-8")
    final_source = build_final_artifact_source(
        published_module=module,
        published_declaration=declaration,
        namespace="Benchmark.Hardness.StageO.TestFinal",
    )
    assert f"import {module}" in final_source
    assert declaration in final_source
    assert "consumerCompleteness" in final_source
    assert "capabilityConsumerProblem,\n       policy := policy," in final_source
    assert "assert_standard_axioms" in final_source
    assert "StageO.Regression" in final_source
