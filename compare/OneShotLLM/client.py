"""One-shot DeepSeek client using exactly the public Archon task material."""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from typing import Any

from agent.hardness.archon_runner import PublicCaseMaterial
from agent.hardness.model_client import (
    DeepSeekClient,
    DeepSeekConfig,
    ModelResponse,
    extract_json_object,
)


SYSTEM_PROMPT = """You are the direct one-shot LLM control for an isolated Lean 4 benchmark task.
Use only the task material in the user message. You have no tools, filesystem,
search, compiler feedback, follow-up turn, or reviewer. Return exactly one JSON
object with one string field named `proof_body`. The value must be the complete
Lean term replacing the fenced body and normally starts with `by`. Do not use
`sorry`, `admit`, `axiom`, or `unsafe`."""


@dataclass(frozen=True)
class OneShotResult:
    ok: bool
    called: bool
    body: str | None
    error: str | None
    duration_seconds: float
    usage: dict[str, Any] | None
    status_code: int | None
    attempts: int
    finish_reason: str | None
    response_sha256: str
    prompt_sha256: str
    public_material_sha256: str
    prompt: str
    raw_response: str


def _sha256_text(value: str) -> str:
    return "sha256:" + hashlib.sha256(value.encode("utf-8")).hexdigest()


def public_material_sha256(material: PublicCaseMaterial) -> str:
    canonical = json.dumps(
        {
            "objective_source": material.objective_source,
            "user_hints": material.user_hints,
        },
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    )
    return _sha256_text(canonical)


def render_one_shot_prompt(material: PublicCaseMaterial) -> str:
    """Serialize Archon's exact two public artifacts into one user message."""

    return "\n".join(
        [
            "PUBLIC_TASK_MATERIAL_BEGIN",
            "",
            "USER_HINTS.md",
            material.user_hints.rstrip(),
            "",
            "FORMAL_GOAL.lean",
            "```lean",
            material.objective_source.rstrip(),
            "```",
            "",
            "PUBLIC_TASK_MATERIAL_END",
            "",
            'Return exactly: {"proof_body":"by\\n  ..."}',
            "",
        ]
    )


def _estimated_cost_usd(model: str, usage: dict[str, Any] | None) -> float | None:
    if not isinstance(usage, dict):
        return None
    prompt_tokens = int(usage.get("prompt_tokens") or 0)
    completion_tokens = int(usage.get("completion_tokens") or 0)
    lowered = model.lower()
    if "flash" in lowered:
        input_rate, output_rate = 0.075, 0.30
    elif "deepseek-reasoner" in lowered or "deepseek-r1" in lowered:
        input_rate, output_rate = 0.55, 2.19
    elif "deepseek-chat" in lowered or "deepseek-v3" in lowered or "deepseek" in lowered:
        input_rate, output_rate = 0.14, 0.28
    else:
        return None
    return round(
        (prompt_tokens * input_rate + completion_tokens * output_rate) / 1_000_000,
        9,
    )


def _usage_with_audit(config: DeepSeekConfig, response: ModelResponse) -> dict[str, Any] | None:
    if not isinstance(response.usage, dict):
        return None
    usage = dict(response.usage)
    usage["direct_llm_requests"] = 1
    cost = _estimated_cost_usd(config.model, usage)
    if cost is not None:
        usage["estimated_cost_usd"] = cost
    return usage


class OneShotLLMClient:
    """Make exactly one chat-completions request for one public benchmark case."""

    def __init__(self, config: DeepSeekConfig, *, transport: Any | None = None):
        if config.max_retries != 0:
            raise ValueError("one-shot LLM requires max_retries=0")
        self.config = config
        self._transport = transport or DeepSeekClient(config)

    def complete(self, material: PublicCaseMaterial) -> OneShotResult:
        prompt = render_one_shot_prompt(material)
        response: ModelResponse = self._transport.complete_json(
            system=SYSTEM_PROMPT,
            prompt=prompt,
        )
        raw = response.content
        body: str | None = None
        error = response.error
        ok = False
        if response.ok:
            payload = extract_json_object(raw)
            if not isinstance(payload, dict) or set(payload) != {"proof_body"}:
                error = "one-shot response must be exactly one proof_body JSON field"
            elif not isinstance(payload.get("proof_body"), str) or not payload["proof_body"].strip():
                error = "one-shot proof_body must be a non-empty string"
            else:
                body = payload["proof_body"].strip()
                ok = True
        return OneShotResult(
            ok=ok,
            called=response.called,
            body=body,
            error=error,
            duration_seconds=response.duration_seconds,
            usage=_usage_with_audit(self.config, response),
            status_code=response.status_code,
            attempts=response.attempts,
            finish_reason=response.finish_reason,
            response_sha256=_sha256_text(raw),
            prompt_sha256=_sha256_text(prompt),
            public_material_sha256=public_material_sha256(material),
            prompt=prompt,
            raw_response=raw,
        )
