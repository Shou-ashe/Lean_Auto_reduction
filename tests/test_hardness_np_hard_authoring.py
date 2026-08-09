from __future__ import annotations

import json
from pathlib import Path

import pytest

from agent.hardness.model_client import ModelResponse
from agent.hardness.models import CommandResult
from agent.hardness.np_hard_authoring import (
    NP_HARD_AUTHORING_PATCH_SCHEMA_V1,
    author_exact_np_hard_reduction,
    build_np_hard_authoring_task,
    build_np_hard_candidate,
    parse_np_hard_authoring_body,
)
from agent.hardness.np_hard import NPHardAgentConfigV1, NPHardAgentV1


def task():
    return build_np_hard_authoring_task(
        request_id="lean:request",
        registry_fingerprint="lean:registry",
        input_module="Example.Target",
        input_problem_declaration="Example.Target.problem",
        hub_declaration="Example.ThreeSAT.problem",
        seed_evidence_declaration="Example.ThreeSAT.nativeCompleteness",
        seed_evidence_kind="native_completeness_projection",
        input_source_sha256="0" * 64,
        job_id="sha256:" + "1" * 64,
        max_attempts=2,
    )


def patch_payload(authoring_task, *, direction=None, body="by\n  exact route"):
    return {
        "schema_version": NP_HARD_AUTHORING_PATCH_SCHEMA_V1,
        "action": "submit_patch",
        "request_id": authoring_task.request_id,
        "gap_id": authoring_task.gap_id,
        "direction": direction or authoring_task.direction,
        "source_declaration": authoring_task.hub_declaration,
        "target_declaration": authoring_task.input_problem_declaration,
        "candidate_declaration": authoring_task.candidate_declaration,
        "declaration_signature": authoring_task.exact_type,
        "replacement_body": body,
    }


def test_authoring_task_and_candidate_freeze_forward_exact_type() -> None:
    authoring_task = task()
    candidate = build_np_hard_candidate(authoring_task)
    assert authoring_task.direction == "hardness_seed_to_problem"
    assert authoring_task.gap_id.startswith("sha256:")
    assert authoring_task.exact_type.endswith(
        "Example.ThreeSAT.problem Example.Target.problem"
    )
    assert authoring_task.exact_type in candidate.fixed_header
    assert "complexity_reduction_ir_typed_edge" in candidate.fixed_header
    assert "assert_standard_axioms" in candidate.fixed_footer


def test_authoring_parser_rejects_direction_and_endpoint_mutation() -> None:
    authoring_task = task()
    mutated = patch_payload(
        authoring_task, direction="problem_to_hardness_seed"
    )
    with pytest.raises(ValueError, match="direction"):
        parse_np_hard_authoring_body(
            content=json.dumps(mutated), task=authoring_task
        )
    mutated = patch_payload(authoring_task)
    mutated["target_declaration"] = "Example.Other.problem"
    with pytest.raises(ValueError, match="target_declaration"):
        parse_np_hard_authoring_body(
            content=json.dumps(mutated), task=authoring_task
        )


def test_authoring_parser_rejects_trust_tokens() -> None:
    authoring_task = task()
    with pytest.raises(ValueError, match="forbidden"):
        parse_np_hard_authoring_body(
            content=json.dumps(
                patch_payload(authoring_task, body="by\n  sorry")
            ),
            task=authoring_task,
        )


def test_bounded_authoring_accepts_only_after_lean_compile(monkeypatch, tmp_path) -> None:
    authoring_task = task()

    class FakeModel:
        def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
            assert "no proof authority" in system
            assert json.loads(prompt)["gap_id"] == authoring_task.gap_id
            return ModelResponse(
                called=True,
                ok=True,
                content=json.dumps(patch_payload(authoring_task)),
                error=None,
                status_code=200,
                duration_seconds=0.01,
                usage={"total_tokens": 10},
                attempts=1,
                finish_reason="stop",
            )

    def fake_run(command, *, cwd, timeout_seconds):
        return CommandResult(
            command=tuple(command),
            exit_code=0,
            stdout="",
            stderr="",
            duration_seconds=0.01,
        )

    monkeypatch.setattr(
        "agent.hardness.np_hard_authoring.run_command", fake_run
    )
    authored = author_exact_np_hard_reduction(
        task=authoring_task,
        input_source="namespace Example.Target\ndef problem := unit\nend Example.Target",
        model=FakeModel(),
        lean_root=tmp_path,
        candidate_path=tmp_path / "Candidate.lean",
        timeout_seconds=10,
    )
    assert authored.model_calls == 1
    assert authored.commands[0].ok
    assert authored.body_sha256.startswith("sha256:")
    assert "exact route" in authored.source


@pytest.mark.parametrize(
    ("mutation", "expected_code"),
    (
        ("direction", "candidate_wrong_direction"),
        ("endpoint", "candidate_wrong_endpoint"),
        ("axiom", "candidate_nonstandard_axiom"),
    ),
)
def test_repeated_authoring_mutations_return_stable_failure(
    mutation, expected_code, tmp_path
) -> None:
    authoring_task = task()

    class MutatingModel:
        def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
            payload = patch_payload(authoring_task)
            if mutation == "direction":
                payload["direction"] = "problem_to_hardness_seed"
            elif mutation == "endpoint":
                payload["target_declaration"] = "Example.Other.problem"
            else:
                payload["replacement_body"] = "by\n  axiom injected : False"
            return ModelResponse(
                called=True,
                ok=True,
                content=json.dumps(payload),
                error=None,
                status_code=200,
                duration_seconds=0.01,
                usage={"total_tokens": 10},
                attempts=1,
                finish_reason="stop",
            )

    failure = author_exact_np_hard_reduction(
        task=authoring_task,
        input_source="def publicInput := True",
        model=MutatingModel(),
        lean_root=tmp_path,
        candidate_path=tmp_path / "Candidate.lean",
        timeout_seconds=10,
    )
    assert failure.code == expected_code
    assert not failure.commands


def test_model_authored_forward_reduction_closes_real_lean_request(tmp_path) -> None:
    root = Path(__file__).resolve().parents[1]

    class TaggedThreeSATModel:
        def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
            task_payload = json.loads(prompt)
            response = dict(task_payload["response_template"])
            response["replacement_body"] = """by
  refine
    { program :=
        Benchmark.Hardness.Inputs.NPHardMVP.ModelAuthoredTaggedThreeSAT.forwardProgram
      correct := ?_ }
  intro input
  rfl
"""
            return ModelResponse(
                called=True,
                ok=True,
                content=json.dumps(response),
                error=None,
                status_code=200,
                duration_seconds=0.01,
                usage={"total_tokens": 100},
                attempts=1,
                finish_reason="stop",
            )

    result = NPHardAgentV1(
        NPHardAgentConfigV1(
            root=root,
            input_module=(
                "Benchmark.Hardness.Inputs.NPHardMVP.ModelAuthoredTaggedThreeSAT"
            ),
            problem_declaration=(
                "Benchmark.Hardness.Inputs.NPHardMVP.ModelAuthoredTaggedThreeSAT.source"
            ),
            output_dir=tmp_path / "job",
            authoring_mode="model-required",
            authoring_attempt_budget=2,
        ),
        model_client=TaggedThreeSATModel(),
    ).run()
    assert result.status == "VERIFIED"
    assert result.model_calls == 1
    assert result.probe is not None and result.probe.failure is not None
    assert result.probe.failure.code == "no_forward_path_from_hardness_seed"
    assert result.authored_probe is not None
    assert result.authored_probe.resolution is not None
    assert result.candidate_worker is not None
    assert result.candidate_worker["validation_authority"] == "persistent_lean_worker"
    assert result.candidate_worker["final_authority"] is False
    assert result.candidate_worker["during_authoring"]["worker_start_count"] == 1
    assert result.candidate_worker["during_authoring"]["cold_fallback_count"] == 0
    assert result.candidate_worker["after_close"]["active_session_count"] == 0
    assert not any(result.candidate_worker["after_close"]["workers_alive"])
    assert all(
        item["verified"] and not item["fallback_used"]
        for item in result.candidate_worker["results"]
    )
    assert any(
        atom.endswith(".authoredForwardReduction")
        for atom in result.authored_probe.resolution.atoms
    )
    artifact = (tmp_path / "job" / "Artifact.lean").read_text(encoding="utf-8")
    assert "NativeTMNPHard" in artifact
    assert "by_np_hard_resolver" in artifact


def test_formal_real_model_report_records_fresh_core_and_deletion_audit() -> None:
    root = Path(__file__).resolve().parents[1]
    report = json.loads(
        (root / "Benchmark/Hardness/NP_HARD_MVP_REPORT.json").read_text(
            encoding="utf-8"
        )
    )
    assert report["schema_version"] == "hardness_np_hard_mvp_real_report_v1"
    assert report["passed"] is True
    assert report["verified_job"]["model_calls"] >= 1
    assert report["verified_job"]["initial_failure"]["code"] == (
        "no_forward_path_from_hardness_seed"
    )
    candidate = report["verified_job"]["task"]["candidate_declaration"]
    assert candidate in report["verified_job"]["fresh_resolution"]["atoms"]
    assert report["deletion_body_audit"]["failure_code"] == (
        "no_forward_path_from_hardness_seed"
    )
    assert report["metrics"]["exact_final_np_hardness_rate"] == 1.0
    assert report["metrics"]["compiler_inserted_math_token_count"] == 0
