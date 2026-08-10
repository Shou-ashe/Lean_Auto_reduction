from __future__ import annotations

import json
from pathlib import Path

import pytest

from agent.hardness.archon_blackbox_benchmark import load_archon_benchmark_cases
from agent.hardness.archon_runner import render_public_case_material
from agent.hardness.model_client import DeepSeekConfig, ModelResponse
from compare.OneShotLLM.client import (
    OneShotLLMClient,
    public_material_sha256,
    render_one_shot_prompt,
)
from scripts.run_hardness_benchmark import build_parser


ROOT = Path(__file__).resolve().parents[1]


class _FakeTransport:
    def __init__(self, response: ModelResponse):
        self.response = response
        self.calls: list[tuple[str, str]] = []

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        self.calls.append((system, prompt))
        return self.response


def _formal_config() -> DeepSeekConfig:
    return DeepSeekConfig(
        api_key="test-key",
        model="deepseek-v4-flash",
        timeout_seconds=300,
        temperature=0.0,
        max_tokens=16_000,
        max_retries=0,
        reasoning_effort="low",
    )


def _material():
    case = load_archon_benchmark_cases(
        root=ROOT,
        selected_case_ids=("cdev-er-01-three-sat-seed",),
    )[0]
    return case, render_public_case_material(
        case_id=case.case_id,
        statement=case.statement,
        requirement=case.requirement,
        imports=case.imports,
        exact_type=case.exact_type,
    )


def test_one_shot_serializes_archons_exact_public_artifacts() -> None:
    case, material = _material()
    prompt = render_one_shot_prompt(material)
    assert material.user_hints in prompt
    assert material.objective_source.rstrip() in prompt
    assert case.statement in prompt
    assert case.requirement in prompt
    assert case.exact_type in prompt
    for forbidden in (
        "recommended_first_body",
        "recommended_proof",
        "oracle",
        "typed_dag",
        "dependency_body",
        "lean_diagnostic",
    ):
        assert forbidden not in prompt.lower()
    assert public_material_sha256(material).startswith("sha256:")


def test_one_shot_makes_exactly_one_request_and_extracts_body() -> None:
    _, material = _material()
    transport = _FakeTransport(
        ModelResponse(
            called=True,
            ok=True,
            content=json.dumps({"proof_body": "by\n  exact 0"}),
            error=None,
            status_code=200,
            duration_seconds=1.25,
            usage={
                "prompt_tokens": 100,
                "completion_tokens": 20,
                "total_tokens": 120,
            },
            attempts=1,
            finish_reason="stop",
        )
    )
    result = OneShotLLMClient(_formal_config(), transport=transport).complete(material)
    assert len(transport.calls) == 1
    assert result.called is True
    assert result.ok is True
    assert result.body == "by\n  exact 0"
    assert result.attempts == 1
    assert result.usage["direct_llm_requests"] == 1
    assert result.usage["estimated_cost_usd"] > 0


def test_one_shot_rejects_extra_response_fields() -> None:
    _, material = _material()
    transport = _FakeTransport(
        ModelResponse(
            called=True,
            ok=True,
            content=json.dumps({"proof_body": "by trivial", "analysis": "hidden"}),
            error=None,
            status_code=200,
            duration_seconds=1.0,
            usage={"prompt_tokens": 1, "completion_tokens": 1, "total_tokens": 2},
            attempts=1,
            finish_reason="stop",
        )
    )
    result = OneShotLLMClient(_formal_config(), transport=transport).complete(material)
    assert result.ok is False
    assert result.body is None
    assert "exactly one proof_body" in result.error


def test_one_shot_disallows_transport_retries() -> None:
    config = DeepSeekConfig(api_key="test-key", max_retries=1)
    with pytest.raises(ValueError, match="max_retries=0"):
        OneShotLLMClient(config)


def test_unified_benchmark_parser_accepts_oneshot_llm() -> None:
    arguments = build_parser().parse_args(
        ["--output-root", "out", "--agent", "oneshot-llm"]
    )
    assert arguments.agent == "oneshot-llm"
