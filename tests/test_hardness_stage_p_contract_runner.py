from __future__ import annotations

import json
import sys
from pathlib import Path

from agent.hardness.model_client import ModelResponse
from agent.hardness.models import CommandResult
import scripts.run_deepseek_stage_p_contract_benchmark as runner


class FrozenContractClient:
    """Protocol-only test double; never used by the real qualification command."""

    def __init__(self, config):
        self.config = config

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        payload = json.loads(prompt)
        task = payload["task"]
        blocker = task["public_blocker"]
        if blocker is not None:
            content = {
                "schema_version": "hardness_stage_p_patch_v1",
                "action": "stop_authoring",
                "session_id": task["session_id"],
                "gap_id": task["gap_id"],
                "task_class": task["task_class"],
                "failure_code": blocker["failure_code"],
                "confirmed_facts": [blocker["facts"][0]],
                "missing_conditions": ["A lawful candidate under the immutable public task."],
            }
        else:
            expected_type = payload["fixed_declaration"]["expected_type"]
            if expected_type.endswith("programProbe"):
                body = "fun value => value"
            elif expected_type.endswith("directTMProbe"):
                body = "by intro value; exact Nat.le_refl value"
            elif expected_type.endswith("completenessProbe"):
                body = "by trivial"
            else:
                body = "by intro value; rfl"
            content = dict(payload["response_template"])
            content["replacement_body"] = body
        return ModelResponse(
            called=True,
            ok=True,
            content=json.dumps(content),
            error=None,
            status_code=200,
            duration_seconds=0.001,
            usage={"prompt_tokens": 10, "completion_tokens": 5, "total_tokens": 15},
            attempts=1,
            finish_reason="stop",
        )


def test_stage_p_full_contract_orchestration_is_24_of_24(
    tmp_path: Path, monkeypatch
) -> None:
    output_root = tmp_path / "fresh-output"
    canonical_report = tmp_path / "canonical.json"
    monkeypatch.setenv("DEEPSEEK_API_KEY", "stage-p-test-key-not-a-real-secret")
    monkeypatch.setattr(runner, "DeepSeekClient", FrozenContractClient)
    monkeypatch.setattr(
        runner,
        "run_command",
        lambda *args, **kwargs: CommandResult(
            command=tuple(args[0]),
            exit_code=0,
            stdout="",
            stderr="",
            duration_seconds=0.001,
        ),
    )
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "run_deepseek_stage_p_contract_benchmark.py",
            "--output-root",
            str(output_root),
            "--canonical-report",
            str(canonical_report),
            "--jobs",
            "4",
        ],
    )

    assert runner.main() == 0
    report = json.loads(canonical_report.read_text(encoding="utf-8"))
    assert report["status"] == "VERIFIED"
    assert report["summary"]["protocol_expected_count"] == 24
    assert report["summary"]["positive_expected_count"] == 12
    assert report["summary"]["negative_expected_count"] == 12
    assert report["summary"]["model_generated_probe_body_count"] == 11
    assert report["summary"]["model_eligible_cases_with_http_call"] == 23
    assert report["cases"][11]["external_api_calls_this_run"] == 0
    assert report["lean_input_gate"]["hidden_module_exposed_to_model"] is False
    assert report["benchmark"]["hidden_semantic_feasibility_sha256"]
    assert report["benchmark"]["exact_cover_standard_helper_sha256"]
    assert report["registry_absence_preflight"][
        "producer_target_native_membership_support_present"
    ] is True
    assert all(report["gates"].values())


def test_repair_feedback_removes_case_workspace_identifier(tmp_path: Path) -> None:
    positive = runner.load_benchmark_suite(runner.DEFAULT_POSITIVE_SUITE)
    case = positive.cases[0]
    message = str(tmp_path / "cases" / case.id / "candidate" / "turn-01.lean")
    sanitized = runner._feedback_for_prompt(
        case=case,
        output_root=tmp_path,
        message=message + ":1:1: error: failed",
    )
    assert case.id not in sanitized
    assert "<case-workspace>" in sanitized
