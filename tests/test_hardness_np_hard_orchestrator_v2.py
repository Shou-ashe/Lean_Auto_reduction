from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.model_client import ModelResponse
from agent.hardness.np_hard import NP_HARD_RESULT_SCHEMA_V1
from agent.hardness.np_hard_authoring import build_np_hard_authoring_tasks_v2
from agent.hardness.np_hard_orchestrator import (
    NPHardOrchestratorConfigV2,
    NPHardOrchestratorError,
    NPHardOrchestratorV2,
    NPHardProofRequestV2,
    NPHardProofResultV2,
    build_np_hard_proof_request_v2,
    read_np_hard_result,
)


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "Benchmark/Hardness/Suites/np_hard_generalization.json"


class RecommendedBodyModel:
    def __init__(self) -> None:
        self.calls = 0

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        assert "untrusted Lean 4 author" in system
        self.calls += 1
        payload = json.loads(prompt)
        response = dict(payload["response_template"])
        assert payload["recommended_first_body"]
        response["replacement_body"] = payload["recommended_first_body"]
        return ModelResponse(
            called=True,
            ok=True,
            content=json.dumps(response),
            error=None,
            status_code=200,
            duration_seconds=0.0,
            usage={"fixture_tokens": 0},
            attempts=1,
            finish_reason="stop",
        )


def _tasks():
    return build_np_hard_authoring_tasks_v2(root=ROOT, suite_path=SUITE)


def _final_program(task) -> str:
    if task.task_class == "semantic_proof":
        return task.allowed_primitives[0]
    suffix = "composedProgram" if task.task_class == "program_composition" else "synthesizedProgram"
    return f"{task.candidate_module}.{suffix}"


def _config(task, output: Path, **changes) -> NPHardOrchestratorConfigV2:
    config = NPHardOrchestratorConfigV2(
        root=ROOT,
        input_module=task.target_problem.module,
        problem_declaration=task.target_problem.term,
        output_dir=output,
        authoring_policy="model-required",
        authoring_task=task,
        final_program_declaration=_final_program(task),
        runtime_prebuilt=True,
    )
    return replace(config, **changes)


def test_v2_request_is_strict_content_addressed_and_round_trips() -> None:
    task = _tasks()[0]
    request = build_np_hard_proof_request_v2(_config(task, ROOT / "tmp/unused-v2"))
    assert NPHardProofRequestV2.from_dict(request.to_dict()) == request

    unknown = request.to_dict()
    unknown["benchmark_case_id"] = "hidden-answer"
    with pytest.raises(NPHardOrchestratorError) as raised:
        NPHardProofRequestV2.from_dict(unknown)
    assert raised.value.code == "invalid_np_hard_proof_v2_schema"

    drifted = request.to_dict()
    drifted["toolchain"] = "leanprover/lean4:stale"
    with pytest.raises(NPHardOrchestratorError) as raised:
        NPHardProofRequestV2.from_dict(drifted)
    assert raised.value.code == "candidate_dependency_stale"


def test_v2_rejects_wrong_endpoint_and_preserves_v1_result_reading() -> None:
    task = _tasks()[0]
    request = build_np_hard_proof_request_v2(_config(task, ROOT / "tmp/unused-v2"))
    wrong = replace(request, problem_declaration=task.source_problem.term)
    wrong = replace(wrong, request_id=wrong.computed_request_id)
    with pytest.raises(NPHardOrchestratorError) as raised:
        wrong.validate()
    assert raised.value.code == "candidate_wrong_endpoint"

    legacy = {"schema_version": NP_HARD_RESULT_SCHEMA_V1, "status": "VERIFIED"}
    assert read_np_hard_result(legacy) == legacy
    with pytest.raises(NPHardOrchestratorError):
        read_np_hard_result({"schema_version": "unknown"})


def test_v2_production_orchestrator_covers_all_authoring_classes(tmp_path) -> None:
    rows = []
    for index, task in enumerate(_tasks(), start=1):
        model = RecommendedBodyModel()
        result = NPHardOrchestratorV2(
            _config(task, tmp_path / f"case-{index}"), model_client=model
        ).run()
        payload = result.to_dict()
        parsed = NPHardProofResultV2.from_dict(payload)
        assert parsed == result
        assert result.status == "VERIFIED"
        assert result.model_calls == model.calls == len(task.gap_nodes)
        assert payload["artifact"]["endpoint"] == task.target_problem.term
        assert payload["independent_replay"]["passed"] is True
        assert payload["axiom_audit"]["passed"] is True
        assert payload["deletion_audit"]["passed"] is True
        assert payload["deletion_audit"]["node_count"] == len(task.gap_nodes)
        assert len(payload["candidate_publication"]) == len(task.gap_nodes)
        rows.append((task.task_class, len(task.gap_nodes)))
    assert rows == [
        ("semantic_proof", 1),
        ("semantic_proof", 2),
        ("program_composition", 2),
        ("program_composition", 2),
        ("program_synthesis", 5),
    ]


def test_v2_resume_is_same_job_only_and_revalidates_prefix(tmp_path) -> None:
    task = _tasks()[1]
    output = tmp_path / "resume"
    first_model = RecommendedBodyModel()
    first = NPHardOrchestratorV2(
        _config(task, output, max_new_nodes=1), model_client=first_model
    ).run()
    assert first.status == "BLOCKED"
    assert first.failure_code == "authoring_checkpoint_created"
    checkpoint = first.authoring_runtime["checkpoint_path"]
    checkpoint_hash = first.authoring_runtime["checkpoint_file_sha256"]

    second_model = RecommendedBodyModel()
    second = NPHardOrchestratorV2(
        _config(
            task,
            output,
            resume_checkpoint_path=Path(checkpoint),
            expected_checkpoint_file_sha256=checkpoint_hash,
        ),
        model_client=second_model,
    ).run()
    assert second.status == "VERIFIED"
    assert second.authoring_runtime["resumed"] is True
    assert second.model_calls == len(task.gap_nodes)
    assert second_model.calls == len(task.gap_nodes) - 1

    with pytest.raises(NPHardOrchestratorError) as raised:
        NPHardOrchestratorV2(
            _config(
                task,
                tmp_path / "other-job",
                resume_checkpoint_path=Path(checkpoint),
                expected_checkpoint_file_sha256=checkpoint_hash,
            ),
            model_client=RecommendedBodyModel(),
        ).run()
    assert raised.value.code == "cross_job_candidate"
