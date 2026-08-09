import json
from dataclasses import replace

import pytest

from agent.hardness.stage_p_contract import StagePContractError
from agent.hardness.stage_p_model_authoring import (
    STAGE_P_MAX_LOCAL_CONTEXT_CHARS,
    STAGE_P_MAX_PRIMARY_DIAGNOSTIC_CHARS,
    StagePBoundAuthoringTask,
    StagePCandidateSource,
    StagePRepairSession,
    summarize_stage_p_diagnostics,
)
from agent.hardness.stage_p_runtime import (
    StagePImmutableRequest,
    StagePRuntimeGap,
)


PUBLIC_MODULE = "Benchmark.Hardness.Inputs.StageP.ContractProbes"


def digest(value: int) -> str:
    return f"sha256:{value:064x}"


def immutable_request() -> StagePImmutableRequest:
    return StagePImmutableRequest(
        source_declaration="Benchmark.Public.source",
        target_declaration="Benchmark.Public.target",
        source_endpoint_id=digest(1),
        target_endpoint_id=digest(2),
        objective="reduce_to",
        direction="source_to_target",
        request_policy_sha256=digest(3),
        resolved_parameters_sha256=digest(4),
        base_registry_fingerprint=digest(5),
        max_gap_count=1,
    )


def runtime_gap(request: StagePImmutableRequest) -> StagePRuntimeGap:
    return StagePRuntimeGap(
        request_id=request.request_id,
        ordinal=1,
        task_class="semantic_correctness",
        capability_head=(
            "ComplexityReduction.Agent.Hardness.Authoring.ExecutableSemanticProof"
        ),
        declaration_signature="Generated.StageP.capability : True",
        source_endpoint_id=request.source_endpoint_id,
        target_endpoint_id=request.target_endpoint_id,
        registry_fingerprint=digest(6),
        dependency_hash=digest(7),
        parent_checkpoint_hash=request.initial_checkpoint_hash,
        public_preconditions=(digest(8),),
    )


def candidate(*, imported_module: str = PUBLIC_MODULE) -> StagePCandidateSource:
    return StagePCandidateSource(
        fixed_header=(
            f"import {imported_module}\n\n"
            "namespace Generated.StageP\n\n"
            "theorem capability : True :=\n"
        ),
        editable_body="by\n  exact True.intro\n",
        fixed_footer=(
            "\n#check capability\n"
            "assert_standard_axioms capability\n\n"
            "end Generated.StageP\n"
        ),
        allowed_imports=(PUBLIC_MODULE,),
    )


def bound_task(*, semantic_turn_budget: int = 4) -> StagePBoundAuthoringTask:
    request = immutable_request()
    gap = runtime_gap(request)
    return StagePBoundAuthoringTask(
        request=request,
        gap=gap,
        candidate_module="Generated.StageP.Capability",
        candidate_declaration="Generated.StageP.capability",
        declaration_signature=gap.declaration_signature,
        expected_type="True",
        editable_file="Generated/StageP/Capability.lean",
        editable_region="candidate_body",
        allowed_imports=(PUBLIC_MODULE,),
        helper_handles=("public.helper.true_intro",),
        semantic_turn_budget=semantic_turn_budget,
        token_budget=30_000,
    )


def repair_session(*, semantic_turn_budget: int = 4) -> StagePRepairSession:
    return StagePRepairSession(
        task=bound_task(semantic_turn_budget=semantic_turn_budget),
        candidate=candidate(),
        helper_summaries={
            "public.helper.true_intro": "True.intro : True",
        },
    )


def submit_patch(session: StagePRepairSession, body: str) -> str:
    task = session.protocol_task
    return json.dumps(
        {
            "schema_version": "hardness_stage_p_patch_v1",
            "action": "submit_patch",
            "session_id": task.session_id,
            "gap_id": task.gap_id,
            "task_class": task.task_class,
            "base_source_sha256": task.base_source_sha256,
            "editable_file": task.editable_file,
            "editable_region": task.editable_region,
            "replacement_body": body,
            "helper_handles": [],
            "binding_claim": {
                "source_endpoint": task.source_endpoint,
                "target_endpoint": task.target_endpoint,
                "direction": task.direction,
                "objective": task.objective,
                "capability_head": task.capability_head,
                "declaration_signature": task.declaration_signature,
            },
        },
        sort_keys=True,
    )


def helper_request(session: StagePRepairSession) -> str:
    task = session.protocol_task
    return json.dumps(
        {
            "schema_version": "hardness_stage_p_patch_v1",
            "action": "request_helper",
            "session_id": task.session_id,
            "gap_id": task.gap_id,
            "task_class": task.task_class,
            "helper_handle": "public.helper.true_intro",
        },
        sort_keys=True,
    )


def test_candidate_replacement_preserves_fixed_source_and_inserts_no_math() -> None:
    session = repair_session()
    original_header = session.candidate.fixed_header_sha256
    original_footer = session.candidate.fixed_footer_sha256
    original_source = session.candidate.source_sha256
    action = session.accept_model_response(
        submit_patch(session, "by\n  simpa using True.intro\n")
    )
    assert action.action == "submit_patch"
    assert session.candidate.fixed_header_sha256 == original_header
    assert session.candidate.fixed_footer_sha256 == original_footer
    assert session.candidate.source_sha256 != original_source
    assert session.candidate.editable_body == "by\n  simpa using True.intro\n"
    assert session.candidate.compiler_inserted_math_token_count == 0
    assert session.turns[0].base_source_sha256 == original_source
    assert session.turns[0].candidate_source_sha256 == session.candidate.source_sha256


def test_each_repair_turn_binds_the_current_base_source_hash() -> None:
    session = repair_session()
    session.accept_model_response(submit_patch(session, "by\n  trivial\n"))
    current = session.candidate.source_sha256
    stale_response = json.loads(submit_patch(session, "by\n  exact True.intro\n"))
    stale_response["base_source_sha256"] = digest(999)
    with pytest.raises(StagePContractError) as captured:
        session.accept_model_response(json.dumps(stale_response))
    assert captured.value.code == "patch_base_hash_mismatch"
    assert session.candidate.source_sha256 == current


def test_candidate_rejects_unallowlisted_import_before_model_use() -> None:
    unsafe = candidate(imported_module="Benchmark.Private.Answer")
    with pytest.raises(StagePContractError) as captured:
        StagePRepairSession(
            task=bound_task(),
            candidate=unsafe,
            helper_summaries={"public.helper.true_intro": "True.intro : True"},
        )
    assert captured.value.code == "import_not_allowlisted"


def test_repeated_candidate_source_stops_without_another_compile() -> None:
    session = repair_session()
    with pytest.raises(StagePContractError) as captured:
        session.accept_model_response(submit_patch(session, session.candidate.editable_body))
    assert captured.value.code == "authoring_no_progress"
    assert session.accepted_patch_count == 0


def test_bounded_diagnostics_keep_only_the_first_primary_error() -> None:
    raw = (
        "/tmp/Candidate.lean:8:2: error: type mismatch\n"
        "  first error detail\n"
        "/tmp/Candidate.lean:10:1: error: hidden second error\n"
        "  second detail\n"
    )
    summary = summarize_stage_p_diagnostics(
        raw,
        expected_type="E" * 4_000,
        actual_type="False",
        local_context="C" * 4_000,
        candidate_source_sha256=digest(10),
    )
    assert summary.location == "/tmp/Candidate.lean:8:2"
    assert "type mismatch" in summary.primary_error
    assert "first error detail" in summary.primary_error
    assert "hidden second error" not in summary.primary_error
    assert len(summary.primary_error) <= STAGE_P_MAX_PRIMARY_DIAGNOSTIC_CHARS + 20
    assert len(summary.local_context) <= STAGE_P_MAX_LOCAL_CONTEXT_CHARS + 20
    assert summary.raw_diagnostics_sha256.startswith("sha256:")


def test_lsp_style_diagnostics_without_headers_keep_full_message() -> None:
    raw = (
        "Type mismatch\n"
        "  True\n"
        "has type\n"
        "  Prop\n"
        "but is expected to have type\n"
        "  Benchmark.Hardness.Inputs.StageP.ContractProbes.programProbe"
    )
    summary = summarize_stage_p_diagnostics(
        raw,
        expected_type="programProbe",
        candidate_source_sha256=digest(11),
    )
    assert summary.primary_error == (
        "Type mismatch\n"
        "True\n"
        "has type\n"
        "Prop\n"
        "but is expected to have type\n"
        "Benchmark.Hardness.Inputs.StageP.ContractProbes.programProbe"
    )
    assert "has type" in summary.primary_error
    assert "programProbe" in summary.primary_error


def test_repeated_bounded_diagnostics_fail_closed() -> None:
    session = repair_session()
    session.accept_model_response(submit_patch(session, "by\n  trivial\n"))
    raw = "/tmp/Candidate.lean:8:2: error: unsolved goals\n"
    first = session.record_failed_validation(raw, local_context="goal : True")
    assert first.primary_error == "unsolved goals"
    with pytest.raises(StagePContractError) as captured:
        session.record_failed_validation(raw, local_context="goal : True")
    assert captured.value.code == "authoring_diagnostics_repeated"


def test_helper_summary_is_served_only_after_an_allowlisted_request() -> None:
    session = repair_session()
    initial = json.loads(session.build_prompt())
    assert initial["served_helper_summaries"] == {}
    action = session.accept_model_response(helper_request(session))
    assert action.action == "request_helper"
    updated = json.loads(session.build_prompt())
    assert updated["served_helper_summaries"] == {
        "public.helper.true_intro": "True.intro : True"
    }
    with pytest.raises(StagePContractError) as captured:
        session.accept_model_response(helper_request(session))
    assert captured.value.code == "authoring_no_progress"


def test_prompt_contains_only_bounded_diagnostics_and_exact_binding() -> None:
    session = repair_session()
    session.accept_model_response(submit_patch(session, "by\n  trivial\n"))
    session.record_failed_validation(
        "/tmp/Candidate.lean:8:2: error: unsolved goals\n"
        "/tmp/Candidate.lean:9:1: warning: irrelevant\n",
        local_context="goal : True",
    )
    prompt = json.loads(session.build_prompt())
    assert prompt["task"]["source_endpoint"] == "Benchmark.Public.source"
    assert prompt["task"]["target_endpoint"] == "Benchmark.Public.target"
    assert prompt["task"]["parent_checkpoint_hash"] == (
        session.task.gap.parent_checkpoint_hash
    )
    assert prompt["candidate"]["compiler_inserted_math_token_count"] == 0
    assert prompt["bounded_diagnostics"]["primary_error"] == "unsolved goals"
    assert "irrelevant" not in json.dumps(prompt["bounded_diagnostics"])
    assert "expected" not in prompt
    assert "coverage" not in prompt


def test_oracle_text_is_rejected_from_diagnostics_and_helper_context() -> None:
    with pytest.raises(StagePContractError) as diagnostic_error:
        summarize_stage_p_diagnostics(
            "error: use Benchmark.Hardness.Oracles.Gold.answer",
            expected_type="True",
            candidate_source_sha256=digest(10),
        )
    assert diagnostic_error.value.code == "oracle_or_gold_import"
    with pytest.raises(StagePContractError) as helper_error:
        StagePRepairSession(
            task=bound_task(),
            candidate=candidate(),
            helper_summaries={
                "public.helper.true_intro": "Benchmark.Hardness.Oracles.Gold.answer"
            },
        )
    assert helper_error.value.code == "oracle_or_gold_import"


def test_repair_turn_budget_counts_helper_and_patch_model_responses() -> None:
    session = repair_session(semantic_turn_budget=1)
    session.accept_model_response(helper_request(session))
    assert session.remaining_turns == 0
    with pytest.raises(StagePContractError) as captured:
        session.accept_model_response(submit_patch(session, "by\n  trivial\n"))
    assert captured.value.code == "authoring_budget_exhausted"


def test_task_rejects_signature_drift_from_the_core_gap() -> None:
    task = bound_task()
    mutated = replace(task, declaration_signature="Generated.StageP.other : True")
    with pytest.raises(StagePContractError) as captured:
        mutated.validate()
    assert captured.value.code == "candidate_exact_type_mismatch"
