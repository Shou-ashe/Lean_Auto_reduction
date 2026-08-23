"""Dedicated JSON transport for model-authored Boolean-CSP gadget plans."""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from typing import Any, Mapping

from agent.hardness.model_client import extract_json_object

from ..boolean_csp_gadget_authoring import (
    BooleanCSPGadgetAuthoringBrief,
    BooleanCSPGadgetPlanV1,
    BooleanCSPGadgetProtocolError,
    GADGET_AUTHORING_GENERATOR_NAME,
    GADGET_AUTHORING_GENERATOR_VERSION,
)
from ..models import ModelCallRecord, stable_sha256
from .protocol import JSONModel


GADGET_AUTHORING_BASE_TOKEN_PROFILE = "gadget-authoring-base-16k-v1"
GADGET_AUTHORING_ESCALATED_TOKEN_PROFILE = "gadget-authoring-escalated-64k-v1"


@dataclass(frozen=True)
class BooleanCSPGadgetModelAttempt:
    purpose: str
    plan: BooleanCSPGadgetPlanV1 | None
    parsed_response: Mapping[str, Any] | None
    response_payload_sha256: str
    model_response_sha256: str
    requested_base_sha256: str | None
    returned_base_sha256: str | None
    changed_reason: str | None
    error_code: str | None
    error: str | None
    finish_reason: str | None
    token_profile: str
    requested_max_tokens: int | None
    reasoning_effort: str | None
    request_payload_sha256: str

    @property
    def length_exhausted(self) -> bool:
        return self.plan is None and self.finish_reason == "length"

    def repair_payload(self) -> Mapping[str, Any]:
        if self.parsed_response is not None:
            return dict(self.parsed_response)
        return {
            "unparsed_model_response_sha256": self.model_response_sha256,
            "content_not_replayed": True,
        }

    def to_receipt_dict(self) -> dict[str, Any]:
        return {
            "purpose": self.purpose,
            "plan_id": self.plan.plan_id if self.plan is not None else None,
            "semantic_payload_sha256": (
                self.plan.semantic_payload_sha256 if self.plan is not None else None
            ),
            "response_payload_sha256": self.response_payload_sha256,
            "model_response_sha256": self.model_response_sha256,
            "requested_base_sha256": self.requested_base_sha256,
            "returned_base_sha256": self.returned_base_sha256,
            "changed_reason": self.changed_reason,
            "error_code": self.error_code,
            "error": self.error,
            "finish_reason": self.finish_reason,
            "token_profile": self.token_profile,
            "requested_max_tokens": self.requested_max_tokens,
            "reasoning_effort": self.reasoning_effort,
            "request_payload_sha256": self.request_payload_sha256,
            "length_exhausted": self.length_exhausted,
        }


def _raw_response_sha256(content: str) -> str:
    return "sha256:" + hashlib.sha256(content.encode("utf-8")).hexdigest()


def _payload_sha256(parsed: Mapping[str, Any] | None, content: str) -> str:
    if parsed is not None:
        return stable_sha256(dict(parsed))
    return stable_sha256(
        {
            "unparsed_model_response_sha256": _raw_response_sha256(content),
            "content_length": len(content),
        }
    )


def _record(
    *,
    response,
    attempt: BooleanCSPGadgetModelAttempt,
) -> ModelCallRecord:
    return ModelCallRecord(
        purpose=attempt.purpose,
        called=response.called,
        ok=response.ok and attempt.plan is not None and attempt.error is None,
        status_code=response.status_code,
        duration_seconds=response.duration_seconds,
        usage=response.usage,
        attempts=response.attempts,
        response_sha256=attempt.model_response_sha256.removeprefix("sha256:"),
        error=attempt.error or response.error,
        proposal_id=(attempt.plan.plan_id if attempt.plan is not None else None),
        finish_reason=attempt.finish_reason,
        token_profile=attempt.token_profile,
        requested_max_tokens=attempt.requested_max_tokens,
        reasoning_effort=attempt.reasoning_effort,
        request_payload_sha256=attempt.request_payload_sha256,
    )


def _complete_json(
    *,
    model: JSONModel,
    system: str,
    prompt: str,
    max_tokens: int | None,
    reasoning_effort: str | None,
):
    profiled = getattr(model, "complete_json_with_profile", None)
    if max_tokens is not None and callable(profiled):
        return profiled(
            system=system,
            prompt=prompt,
            max_tokens=max_tokens,
            reasoning_effort=reasoning_effort,
        )
    return model.complete_json(system=system, prompt=prompt)


def _request_payload_sha256(*, system: str, prompt: str) -> str:
    return stable_sha256({"system": system, "prompt": prompt})


def _attempt_error(
    *,
    response,
    plan: BooleanCSPGadgetPlanV1 | None,
    error_code: str | None,
    error: str | None,
) -> tuple[str | None, str | None]:
    if plan is None and response.finish_reason == "length":
        return (
            "gadget_authoring_output_length_exhausted",
            response.error or "model output exhausted its token profile",
        )
    if response.ok:
        return error_code, error
    return "gadget_authoring_transport_error", response.error


def _parse_plan(
    *,
    payload: Mapping[str, Any] | None,
    brief: BooleanCSPGadgetAuthoringBrief,
) -> tuple[BooleanCSPGadgetPlanV1 | None, str | None, str | None]:
    if payload is None:
        return (
            None,
            "gadget_authoring_response_not_json",
            "model response did not contain one JSON object",
        )
    try:
        return BooleanCSPGadgetPlanV1.from_mapping(payload, brief.context), None, None
    except BooleanCSPGadgetProtocolError as error:
        return None, error.code, error.message


def propose_initial_gadget_plan(
    *,
    model: JSONModel,
    brief: BooleanCSPGadgetAuthoringBrief,
    token_profile: str = "configured-default",
    max_tokens: int | None = None,
    reasoning_effort: str | None = None,
) -> tuple[BooleanCSPGadgetModelAttempt, ModelCallRecord]:
    prompt = {
        "provider_protocol": {
            "name": GADGET_AUTHORING_GENERATOR_NAME,
            "version": GADGET_AUTHORING_GENERATOR_VERSION,
            "mode": "initial",
        },
        "generator_brief": brief.prompt_dict(),
        "required_output": (
            "Return exactly one BooleanCSPGadgetPlanV1 JSON object. Do not return "
            "a candidate list, Lean code, a theorem name, or a search trace."
        ),
    }
    system = (
        "You are the independent Boolean-CSP pp-gadget author. Construct exactly "
        "one concrete gadget plan from the complete public truth tables in the "
        "answer-free brief. You must choose every variable, output, target symbol, "
        "and constraint. Do not enumerate alternatives and do not invoke or name "
        "an existing gadget, template, database, solver, or benchmark answer. "
        "The runtime will only validate and serialize your single JSON plan. "
        "Return one compact JSON object matching the exact schema."
    )
    serialized_prompt = json.dumps(prompt, ensure_ascii=False)
    response = _complete_json(
        model=model,
        system=system,
        prompt=serialized_prompt,
        max_tokens=max_tokens,
        reasoning_effort=reasoning_effort,
    )
    parsed = extract_json_object(response.content) if response.ok else None
    plan, error_code, error = _parse_plan(payload=parsed, brief=brief)
    error_code, error = _attempt_error(
        response=response,
        plan=plan,
        error_code=error_code,
        error=error,
    )
    attempt = BooleanCSPGadgetModelAttempt(
        purpose="gadget-authoring-initial",
        plan=plan,
        parsed_response=parsed,
        response_payload_sha256=_payload_sha256(parsed, response.content),
        model_response_sha256=_raw_response_sha256(response.content),
        requested_base_sha256=None,
        returned_base_sha256=None,
        changed_reason=None,
        error_code=error_code,
        error=error,
        finish_reason=response.finish_reason,
        token_profile=token_profile,
        requested_max_tokens=max_tokens,
        reasoning_effort=reasoning_effort,
        request_payload_sha256=_request_payload_sha256(
            system=system, prompt=serialized_prompt
        ),
    )
    return attempt, _record(response=response, attempt=attempt)


def propose_gadget_plan_repair(
    *,
    model: JSONModel,
    brief: BooleanCSPGadgetAuthoringBrief,
    previous_attempt: BooleanCSPGadgetModelAttempt,
    token_profile: str = "configured-default",
    max_tokens: int | None = None,
    reasoning_effort: str | None = None,
) -> tuple[BooleanCSPGadgetModelAttempt, ModelCallRecord]:
    base_sha256 = previous_attempt.response_payload_sha256
    prompt = {
        "provider_protocol": {
            "name": GADGET_AUTHORING_GENERATOR_NAME,
            "version": GADGET_AUTHORING_GENERATOR_VERSION,
            "mode": "repair",
        },
        "generator_brief": brief.prompt_dict(),
        "previous_response_payload": previous_attempt.repair_payload(),
        "base_sha256": base_sha256,
        "repair_policy": (
            "Return one changed, complete replacement plan. Address only the supplied "
            "schema failure, finite semantic counterexample, or Lean failure. Do not "
            "return alternatives or candidate lists."
        ),
        "required_output": {
            "exact_keys": ["base_sha256", "plan", "changed_reason"],
            "base_sha256": base_sha256,
            "plan": "one complete BooleanCSPGadgetPlanV1 object",
            "changed_reason": "short nonempty explanation of the repair",
        },
    }
    system = (
        "Repair one model-authored Boolean-CSP gadget plan. The answer-free truth "
        "tables and exact schema failure, semantic counterexample, or Lean failure "
        "are authoritative. Return the exact base_sha256, one complete changed "
        "replacement plan, and a short changed_reason. Do not return Lean code, "
        "theorem names, templates, solver output, candidates, or multiple "
        "alternatives. Return one compact JSON object."
    )
    serialized_prompt = json.dumps(prompt, ensure_ascii=False)
    response = _complete_json(
        model=model,
        system=system,
        prompt=serialized_prompt,
        max_tokens=max_tokens,
        reasoning_effort=reasoning_effort,
    )
    parsed = extract_json_object(response.content) if response.ok else None
    plan_payload: Mapping[str, Any] | None = None
    returned_base: str | None = None
    changed_reason: str | None = None
    error_code: str | None = None
    error: str | None = response.error
    if response.ok and isinstance(parsed, Mapping):
        if set(parsed) != {"base_sha256", "plan", "changed_reason"}:
            error_code = "gadget_repair_envelope_invalid"
            error = "repair response must contain exactly base_sha256, plan, changed_reason"
        else:
            returned_base = (
                parsed.get("base_sha256")
                if isinstance(parsed.get("base_sha256"), str)
                else None
            )
            changed_reason = (
                parsed.get("changed_reason")
                if isinstance(parsed.get("changed_reason"), str)
                else None
            )
            raw_plan = parsed.get("plan")
            if returned_base != base_sha256:
                error_code = "gadget_repair_base_hash_mismatch"
                error = "repair response base_sha256 does not match previous payload"
            elif not changed_reason or not changed_reason.strip():
                error_code = "gadget_repair_reason_missing"
                error = "repair response changed_reason must be nonempty"
            elif not isinstance(raw_plan, Mapping):
                error_code = "gadget_repair_plan_missing"
                error = "repair response plan must be an object"
            else:
                plan_payload = raw_plan
    elif response.ok:
        error_code = "gadget_authoring_response_not_json"
        error = "model repair response did not contain one JSON object"
    if plan_payload is not None:
        plan, plan_error_code, plan_error = _parse_plan(
            payload=plan_payload, brief=brief
        )
        if plan_error is not None:
            error_code = plan_error_code
            error = plan_error
    else:
        plan = None
    error_code, error = _attempt_error(
        response=response,
        plan=plan,
        error_code=error_code,
        error=error,
    )
    attempt = BooleanCSPGadgetModelAttempt(
        purpose="gadget-authoring-repair",
        plan=plan,
        parsed_response=parsed,
        response_payload_sha256=_payload_sha256(parsed, response.content),
        model_response_sha256=_raw_response_sha256(response.content),
        requested_base_sha256=base_sha256,
        returned_base_sha256=returned_base,
        changed_reason=(changed_reason.strip() if changed_reason else None),
        error_code=error_code,
        error=error,
        finish_reason=response.finish_reason,
        token_profile=token_profile,
        requested_max_tokens=max_tokens,
        reasoning_effort=reasoning_effort,
        request_payload_sha256=_request_payload_sha256(
            system=system, prompt=serialized_prompt
        ),
    )
    return attempt, _record(response=response, attempt=attempt)


__all__ = [
    "BooleanCSPGadgetModelAttempt",
    "GADGET_AUTHORING_BASE_TOKEN_PROFILE",
    "GADGET_AUTHORING_ESCALATED_TOKEN_PROFILE",
    "propose_gadget_plan_repair",
    "propose_initial_gadget_plan",
]
