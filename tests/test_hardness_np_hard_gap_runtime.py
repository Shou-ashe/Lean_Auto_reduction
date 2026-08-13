from __future__ import annotations

from dataclasses import replace
import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from agent.hardness.model_client import ModelResponse
from agent.hardness.models import CommandResult
from agent.hardness.np_hard_authoring import NPHardAuthoringTaskV2
from agent.hardness.np_hard_authoring_planner import NPHardAuthoringPlannerV2
from agent.hardness.np_hard_gap_runtime import NPHardGapRuntimeV1


ROOT = Path(__file__).resolve().parents[1]
MODULE = "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case04PositiveExactlyOne3"
PROBLEM = f"{MODULE}.problem"


class _FakeWorkerPool:
    fail_semantic_forward = False

    def __init__(self, **_: object) -> None:
        pass

    def start_session(self, **_: object) -> str:
        return "fake-session"

    def validate(self, *, key, **_: object):
        declaration = key.editable_allowlist[0]
        failed = self.fail_semantic_forward and declaration.endswith(
            ".semanticForward"
        )
        diagnostics = (
            ({"message": "semantic theorem is false for the compiled mapping"},)
            if failed
            else ()
        )
        payload = {
            "verified": not failed,
            "diagnostics": list(diagnostics),
            "declaration": declaration,
        }
        return SimpleNamespace(
            verified=not failed,
            diagnostics=diagnostics,
            to_dict=lambda: payload,
        )

    def close_session(self, **_: object) -> None:
        pass

    def close(self) -> None:
        pass


def _ok_run(command, **_: object) -> CommandResult:
    return CommandResult(
        command=tuple(str(item) for item in command),
        exit_code=0,
        stdout="",
        stderr="",
        duration_seconds=0.0,
    )


def _with_attempt_budget(
    task: NPHardAuthoringTaskV2, attempt_budget: int
) -> NPHardAuthoringTaskV2:
    provisional = replace(
        task,
        request_id="sha256:" + "0" * 64,
        attempt_budget=attempt_budget,
    )
    updated = replace(provisional, request_id=provisional.computed_request_id)
    updated.validate()
    return updated


@pytest.fixture(scope="module")
def whole_reduction_plan(tmp_path_factory):
    return NPHardAuthoringPlannerV2(
        root=ROOT,
        input_module=MODULE,
        input_problem_declaration=PROBLEM,
        output_dir=tmp_path_factory.mktemp("gap-runtime-plan"),
        attempt_budget=2,
    ).plan()


class _LengthThenBodyModel:
    def __init__(self, *, always_length: bool = False) -> None:
        self.always_length = always_length
        self.calls = 0
        self.prompts: list[dict[str, object]] = []

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        assert "untrusted Lean 4 author" in system
        self.calls += 1
        payload = json.loads(prompt)
        self.prompts.append(payload)
        if self.always_length or self.calls == 1:
            return ModelResponse(
                called=True,
                ok=False,
                content="",
                error="empty assistant content (finish_reason=length)",
                status_code=200,
                duration_seconds=0.0,
                usage={"completion_tokens": 16_000},
                attempts=1,
                finish_reason="length",
            )
        response = dict(payload["response_template"])
        response["replacement_body"] = "fun _ => []"
        return ModelResponse(
            called=True,
            ok=True,
            content=json.dumps(response),
            error=None,
            status_code=200,
            duration_seconds=0.0,
            usage={"completion_tokens": 20},
            attempts=1,
            finish_reason="stop",
        )


class _ProfiledLengthThenBodyModel:
    def __init__(self, *, length_failures: int) -> None:
        self.length_failures = length_failures
        self.calls = 0
        self.profiles: list[tuple[int, str | None]] = []
        self.config = SimpleNamespace(max_tokens=128_000, reasoning_effort="max")

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        raise AssertionError("profile-aware model must use complete_json_with_profile")

    def complete_json_with_profile(
        self,
        *,
        system: str,
        prompt: str,
        max_tokens: int,
        reasoning_effort: str | None,
    ) -> ModelResponse:
        assert "untrusted Lean 4 author" in system
        self.calls += 1
        self.profiles.append((max_tokens, reasoning_effort))
        if self.calls <= self.length_failures:
            return ModelResponse(
                called=True,
                ok=False,
                content="",
                error="empty assistant content (finish_reason=length)",
                status_code=200,
                duration_seconds=0.0,
                usage={"completion_tokens": max_tokens},
                attempts=1,
                finish_reason="length",
            )
        payload = json.loads(prompt)
        response = dict(payload["response_template"])
        response["replacement_body"] = "fun _ => []"
        return ModelResponse(
            called=True,
            ok=True,
            content=json.dumps(response),
            error=None,
            status_code=200,
            duration_seconds=0.0,
            usage={"completion_tokens": 20},
            attempts=1,
            finish_reason="stop",
        )


class _RollbackModel:
    def __init__(self) -> None:
        self.executable_calls = 0
        self.prompts: list[dict[str, object]] = []

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        assert "untrusted Lean 4 author" in system
        payload = json.loads(prompt)
        self.prompts.append(payload)
        response = dict(payload["response_template"])
        node_id = response["node_id"]
        if node_id == "reduction-executable":
            self.executable_calls += 1
            response["replacement_body"] = (
                "fun _ => []"
                if self.executable_calls == 1
                else "fun input => input"
            )
        else:
            response["replacement_body"] = "by trivial"
        return ModelResponse(
            called=True,
            ok=True,
            content=json.dumps(response),
            error=None,
            status_code=200,
            duration_seconds=0.0,
            usage={"completion_tokens": 20},
            attempts=1,
            finish_reason="stop",
        )


def _runtime(*, task, plan, output_root: Path, model) -> NPHardGapRuntimeV1:
    assert plan.final_program_declaration is not None
    return NPHardGapRuntimeV1(
        root=ROOT,
        task=task,
        output_root=output_root,
        model=model,
        final_program_declaration=plan.final_program_declaration,
    )


def test_final_wrapper_marks_noncomputable_target_request(
    whole_reduction_plan,
) -> None:
    from agent.hardness.np_hard_gap_runtime import _candidate_source

    bodies = {
        node.declaration: "by\n  trivial\n"
        for node in whole_reduction_plan.task.gap_nodes
    }
    source = _candidate_source(
        task=whole_reduction_plan.task,
        bodies=bodies,
        include_final=True,
        final_program_declaration=whole_reduction_plan.final_program_declaration,
    )
    assert (
        "noncomputable def authoredTargetRequest : "
        "ComplexityReduction.Protocol.TypedNPHardRequestV1 :="
    ) in source


def test_http_200_length_exhaustion_retries_with_static_profile_diagnostic(
    monkeypatch, tmp_path: Path, whole_reduction_plan
) -> None:
    import agent.hardness.np_hard_gap_runtime as runtime_module

    monkeypatch.setattr(runtime_module, "LeanWorkerPool", _FakeWorkerPool)
    monkeypatch.setattr(runtime_module, "run_command", _ok_run)
    model = _LengthThenBodyModel()
    result = _runtime(
        task=whole_reduction_plan.task,
        plan=whole_reduction_plan,
        output_root=tmp_path / "length-retry",
        model=model,
    ).run(max_new_nodes=1)

    assert result.status == "CHECKPOINTED"
    assert result.failure_code is None
    assert result.model_calls == model.calls == 2
    assert result.accepted_nodes == ("reduction-executable",)
    assert "audited static capability profile remains" in model.prompts[1][
        "lean_diagnostic"
    ]


def test_empty_length_response_preserves_static_invention_profile(
    monkeypatch, tmp_path: Path, whole_reduction_plan
) -> None:
    import agent.hardness.np_hard_gap_runtime as runtime_module

    monkeypatch.setattr(runtime_module, "LeanWorkerPool", _FakeWorkerPool)
    monkeypatch.setattr(runtime_module, "run_command", _ok_run)
    model = _ProfiledLengthThenBodyModel(length_failures=1)
    result = _runtime(
        task=whole_reduction_plan.task,
        plan=whole_reduction_plan,
        output_root=tmp_path / "static-profile-retry",
        model=model,
    ).run(max_new_nodes=1)

    assert result.status == "CHECKPOINTED"
    assert model.profiles == [(128_000, "max"), (128_000, "max")]
    assert {
        item["node_reasoning_profile"]["profile_id"]
        for item in result.model_call_ledger
    } == {"reduction_invention"}
    assert all(
        item["node_reasoning_profile"]["static_profile_applied"] is True
        for item in result.model_call_ledger
    )


def test_length_exhaustion_never_changes_static_capability_profile(
    monkeypatch, tmp_path: Path, whole_reduction_plan
) -> None:
    import agent.hardness.np_hard_gap_runtime as runtime_module

    monkeypatch.setattr(runtime_module, "LeanWorkerPool", _FakeWorkerPool)
    monkeypatch.setattr(runtime_module, "run_command", _ok_run)
    task = _with_attempt_budget(whole_reduction_plan.task, 4)
    model = _ProfiledLengthThenBodyModel(length_failures=4)
    result = _runtime(
        task=task,
        plan=whole_reduction_plan,
        output_root=tmp_path / "static-profile-exhausted",
        model=model,
    ).run(max_new_nodes=1)

    assert result.status == "FAILED"
    assert result.failure_code == "model_output_exhausted"
    assert model.profiles == [(128_000, "max")] * 4


def test_capability_profiles_are_static_and_generic() -> None:
    from agent.hardness.np_hard_gap_runtime import _node_reasoning_profile

    model = _ProfiledLengthThenBodyModel(length_failures=0)
    expected = {
        "clause_constraint": ("reduction_invention", 128_000, "max"),
        "direct_tm": ("direct_tm", 128_000, "max"),
        "reference_direct_tm": ("direct_tm", 128_000, "max"),
        "semantic_forward": ("global_semantic", 128_000, "max"),
        "reference_semantic_reverse": ("global_semantic", 128_000, "max"),
        "gadget_semantic_forward": ("local_proof", 32_000, "high"),
        "output_wellformed": ("local_proof", 32_000, "high"),
        "poly_program": ("mechanical", 8_000, "low"),
    }
    for capability, profile_tuple in expected.items():
        profile = _node_reasoning_profile(model=model, capability=capability)
        assert (
            profile["profile_id"],
            profile["effective_max_tokens"],
            profile["effective_reasoning_effort"],
        ) == profile_tuple


def test_node_patch_accepts_large_tm_body_within_32k_boundary(
    whole_reduction_plan,
) -> None:
    from agent.hardness.np_hard_gap_runtime import (
        _node_request,
        parse_np_hard_node_patch_v1,
    )

    task = whole_reduction_plan.task
    request = _node_request(
        task=task,
        node_ordinal=1,
        dependency_snapshot=task.dependency_hashes,
        accepted=(),
        total_model_calls=0,
        instance_call_budget=64,
    )
    envelope = {
        "schema_version": "hardness_np_hard_node_patch_v1",
        "action": "submit_node_patch",
        "request_id": request.request_id,
        "node_id": request.node.node_id,
        "declaration": request.node.declaration,
        "dependency_fingerprint": request.dependency_fingerprint,
        "replacement_body": "fun _ => " + "[] " * 6_000,
    }
    patch = parse_np_hard_node_patch_v1(
        content=json.dumps(envelope), request=request, task=task
    )
    assert len(patch.replacement_body) > 12_000
    assert len(patch.replacement_body) < 32_000


def test_http_200_length_exhaustion_has_distinct_failure_code(
    monkeypatch, tmp_path: Path, whole_reduction_plan
) -> None:
    import agent.hardness.np_hard_gap_runtime as runtime_module

    monkeypatch.setattr(runtime_module, "LeanWorkerPool", _FakeWorkerPool)
    monkeypatch.setattr(runtime_module, "run_command", _ok_run)
    model = _LengthThenBodyModel(always_length=True)
    result = _runtime(
        task=whole_reduction_plan.task,
        plan=whole_reduction_plan,
        output_root=tmp_path / "length-exhausted",
        model=model,
    ).run()

    assert result.status == "FAILED"
    assert result.failure_code == "model_output_exhausted"
    assert result.model_calls == model.calls == 2


def test_semantic_failure_preserves_accepted_construction_and_tm_nodes(
    monkeypatch, tmp_path: Path, whole_reduction_plan
) -> None:
    import agent.hardness.np_hard_gap_runtime as runtime_module

    class SemanticFailingPool(_FakeWorkerPool):
        fail_semantic_forward = True

    monkeypatch.setattr(runtime_module, "LeanWorkerPool", SemanticFailingPool)
    monkeypatch.setattr(runtime_module, "run_command", _ok_run)
    task = _with_attempt_budget(whole_reduction_plan.task, 1)
    model = _RollbackModel()
    result = _runtime(
        task=task,
        plan=whole_reduction_plan,
        output_root=tmp_path / "semantic-rollback",
        model=model,
    ).run()

    assert result.status == "FAILED"
    assert result.failure_code == "semantic_proof_failed"
    assert result.model_calls == 6
    assert result.accepted_nodes == (
        "reduction-executable",
        "direct-tm",
        "reduction-primitive",
        "poly-program",
        "program-run-coherence",
    )
    prompt_files = [item["prompt_file"] for item in result.model_call_ledger]
    response_files = [item["response_file"] for item in result.model_call_ledger]
    assert len(set(prompt_files)) == len(prompt_files)
    assert len(set(response_files)) == len(response_files)
    assert result.rollback_events == ()
    executable_prompts = [
        prompt
        for prompt in model.prompts
        if prompt["response_template"]["node_id"] == "reduction-executable"
    ]
    assert len(executable_prompts) == 1
