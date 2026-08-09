import hashlib
import json
import shutil
import tempfile
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.models import sha256_id
from agent.hardness.model_client import ModelResponse
from agent.hardness.np_hard_authoring import build_np_hard_authoring_tasks_v2
from agent.hardness.np_hard_gap_runtime import (
    NP_HARD_NODE_PATCH_SCHEMA_V1,
    NPHardGapCheckpointV1,
    NPHardGapRuntimeError,
    NPHardGapRuntimeV1,
    _current_dependency_snapshot,
    _node_request,
    build_np_hard_node_prompt_v1,
    parse_np_hard_node_patch_v1,
)
from agent.hardness.np_hard_generalization import load_np_hard_generalization_suite


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "Benchmark" / "Hardness" / "Suites" / "np_hard_generalization.json"


def tasks():
    return build_np_hard_authoring_tasks_v2(root=ROOT, suite_path=SUITE)


def request(task, ordinal: int = 1):
    return _node_request(
        task=task,
        node_ordinal=ordinal,
        dependency_snapshot=_current_dependency_snapshot(
            root=ROOT, task=task, accepted=()
        ),
        accepted=(),
        total_model_calls=0,
    )


def patch_payload(task, node_request, body: str = "by\n  rfl\n"):
    return {
        "schema_version": NP_HARD_NODE_PATCH_SCHEMA_V1,
        "action": "submit_node_patch",
        "request_id": node_request.request_id,
        "node_id": node_request.node.node_id,
        "declaration": node_request.node.declaration,
        "dependency_fingerprint": node_request.dependency_fingerprint,
        "replacement_body": body,
    }


class EchoRecommendedBodyModel:
    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        assert "recommended_first_body" in prompt
        payload = json.loads(prompt)
        content = json.dumps(payload["response_template"], sort_keys=True)
        return ModelResponse(
            called=True,
            ok=True,
            content=content,
            error=None,
            status_code=200,
            duration_seconds=0.0,
            usage={"fixture_tokens": 0},
            attempts=1,
            finish_reason="stop",
        )


def test_node_requests_expose_exactly_one_topological_gap() -> None:
    counts = [len(task.gap_nodes) for task in tasks()]
    assert counts == [1, 2, 2, 2, 5]
    for task in tasks():
        node_request = request(task)
        assert node_request.node == task.gap_nodes[0]
        assert node_request.node_attempt_budget == 4
        assert node_request.instance_call_budget_remaining == 8
        assert node_request.request_id == node_request.computed_request_id


def test_node_patch_accepts_only_the_active_declaration() -> None:
    task = tasks()[0]
    node_request = request(task)
    parsed = parse_np_hard_node_patch_v1(
        content=json.dumps(patch_payload(task, node_request)),
        request=node_request,
        task=task,
    )
    assert parsed.declaration == task.gap_nodes[0].declaration
    assert parsed.replacement_body.endswith("\n")


def test_node_patch_allows_instance_type_projection() -> None:
    task = tasks()[0]
    node_request = request(task)
    projected = patch_payload(
        task,
        node_request,
        "fun input : Benchmark.Public.source.Instance => input",
    )
    parsed = parse_np_hard_node_patch_v1(
        content=json.dumps(projected), request=node_request, task=task
    )
    assert ".Instance" in parsed.replacement_body


@pytest.mark.parametrize(
    ("mutation", "code"),
    [
        (lambda value: value.update(request_id="sha256:" + "0" * 64), "candidate_dependency_stale"),
        (lambda value: value.update(node_id="other-node"), "candidate_dependency_stale"),
        (lambda value: value.update(declaration="Generated.Other.escape"), "candidate_outside_edit_boundary"),
        (lambda value: value.update(dependency_fingerprint="sha256:" + "1" * 64), "candidate_dependency_stale"),
        (lambda value: value.update(replacement_body="by\n  import Bad.Module"), "import_not_allowlisted"),
        (lambda value: value.update(replacement_body="by\n  exact sorry"), "candidate_nonstandard_axiom"),
        (lambda value: value.update(replacement_body="by\n  exact GoldProof.answer"), "oracle_or_gold_import"),
    ],
)
def test_node_patch_mutations_fail_closed(mutation, code: str) -> None:
    task = tasks()[0]
    node_request = request(task)
    value = patch_payload(task, node_request)
    mutation(value)
    with pytest.raises(NPHardGapRuntimeError) as captured:
        parse_np_hard_node_patch_v1(
            content=json.dumps(value), request=node_request, task=task
        )
    assert captured.value.code == code


def test_node_patch_rejects_extra_envelope_field() -> None:
    task = tasks()[0]
    node_request = request(task)
    value = patch_payload(task, node_request)
    value["extra_declaration"] = "escape"
    with pytest.raises(NPHardGapRuntimeError) as captured:
        parse_np_hard_node_patch_v1(
            content=json.dumps(value), request=node_request, task=task
        )
    assert captured.value.code == "invalid_np_hard_gap_runtime_schema"


def test_node_prompt_contains_no_benchmark_answer_metadata() -> None:
    task = tasks()[0]
    node_request = request(task)
    prompt = build_np_hard_node_prompt_v1(
        root=ROOT,
        task=task,
        request=node_request,
        accepted_bodies={},
        diagnostic=None,
    ).lower()
    for marker in ('"case_id"', '"expected"', ".gold.", ".oracles."):
        assert marker not in prompt
    assert "polyprog.comp (after : polyprog middle target)" in prompt
    assert "polyprog.const (source target : lawfulencodedtype)" in prompt


def test_node_prompt_selects_only_the_public_semantic_shape_recipe() -> None:
    task = tasks()[0]
    payload = json.loads(
        build_np_hard_node_prompt_v1(
            root=ROOT,
            task=task,
            request=request(task),
            accepted_bodies={},
            diagnostic=None,
        )
    )
    assert "false_tag" in payload["proof_recipes"]
    assert "conjunction_identity" not in payload["proof_recipes"]
    serialized = json.dumps(payload).lower()
    assert ".gold." not in serialized and ".oracles." not in serialized


def test_public_shape_recommendations_compile_end_to_end() -> None:
    suite = load_np_hard_generalization_suite(SUITE, root=ROOT)
    cases = [case for case in suite.cases if case.kind == "model_authoring"]
    run_root = Path(
        tempfile.mkdtemp(prefix="pytest-public-shape-", dir=ROOT / "tmp")
    )
    try:
        for case, task in zip(cases, tasks(), strict=True):
            authoring = case.authoring
            assert authoring is not None
            if task.task_class == "semantic_proof":
                final_program = authoring["program_reference"]
            else:
                suffix = (
                    "composedProgram"
                    if task.task_class == "program_composition"
                    else "synthesizedProgram"
                )
                final_program = f"{task.candidate_module}.{suffix}"
            result = NPHardGapRuntimeV1(
                root=ROOT,
                task=task,
                output_root=run_root / case.id,
                model=EchoRecommendedBodyModel(),
                final_program_declaration=final_program,
                timeout_seconds=600,
            ).run()
            assert result.status == "VERIFIED", (
                case.id,
                result.failure_code,
                result.failure_message,
            )
            assert result.model_calls == len(task.gap_nodes)
            assert len(result.accepted_nodes) == len(task.gap_nodes)
            assert all(not row["fallback_used"] for row in result.worker_results)
    finally:
        shutil.rmtree(run_root)


def test_checkpoint_content_hash_detects_mutation() -> None:
    task = tasks()[0]
    arguments = {
        "task_request_id": task.request_id,
        "dependency_snapshot": _current_dependency_snapshot(
            root=ROOT, task=task, accepted=()
        ),
        "accepted_nodes": (),
        "remaining_gap_graph": tuple(node.to_dict() for node in task.gap_nodes),
        "total_model_calls": 0,
        "per_node_model_calls": (),
        "model_call_ledger": (),
    }
    provisional = NPHardGapCheckpointV1(
        checkpoint_hash="sha256:" + "0" * 64, **arguments
    )
    checkpoint = replace(
        provisional, checkpoint_hash=provisional.computed_checkpoint_hash
    )
    checkpoint.validate(task)
    value = checkpoint.to_dict(task)
    value["total_model_calls"] = 1
    with pytest.raises(NPHardGapRuntimeError) as captured:
        NPHardGapCheckpointV1.from_dict(value, task=task)
    assert captured.value.code == "checkpoint_tampered"


def test_formal_g_c_report_satisfies_exit_conditions() -> None:
    path = ROOT / "Benchmark" / "Hardness" / "NP_HARD_GAP_RUNTIME_REPORT.json"
    if not path.is_file():
        pytest.skip("formal G-C runtime report has not been generated")
    report = json.loads(path.read_text(encoding="utf-8"))
    metrics = report["metrics"]
    assert report["passed"] is True
    assert metrics["task_count"] == metrics["verified_task_count"] == 5
    assert metrics["accepted_node_count"] == 12
    assert metrics["multi_gap_verified_count"] >= 1
    assert metrics["program_synthesis_verified_count"] == 1
    assert metrics["nontrivial_semantic_verified_count"] == 2
    assert metrics["fresh_core_rediscovery_count"] >= 12
    assert metrics["checkpoint_resume_verified_count"] == 1
    assert metrics["exact_native_np_hard_final_count"] == 5
    assert metrics["independent_replay_count"] == 5
    assert metrics["persistent_worker_count_per_session"] == 1
    assert metrics["worker_fallback_count"] == 0
    assert metrics["compiler_inserted_math_token_count"] == 0
    assert all(report["tamper_audits"].values())
    # G-C is a completed historical qualification.  Its provenance must stay
    # frozen when the active plan advances to later work packages.
    assert len(report["active_plan_sha256"]) == 64
    int(report["active_plan_sha256"], 16)


def test_full_45_case_report_is_content_addressed_and_complete() -> None:
    summary_path = ROOT / "Benchmark" / "Hardness" / "MAIN_G_C_45_FULL_REPORT.json"
    summary = json.loads(summary_path.read_text(encoding="utf-8"))
    raw_path = ROOT / summary["raw_report"]["file"]
    raw = json.loads(raw_path.read_text(encoding="utf-8"))
    assert summary["passed"] is True
    assert hashlib.sha256(raw_path.read_bytes()).hexdigest() == summary["raw_report"]["sha256"]
    assert raw["total"] == raw["passed"] == 45
    assert raw["failed"] == 0
    assert summary["counts"]["positive_verified_count"] == 29
    assert summary["counts"]["negative_expected_outcome_count"] == 16
    assert summary["real_model"]["http_ok_count"] == 1
    assert summary["real_model"]["status_code"] == 200
    assert all(summary["gates"].values())
