"""Bounded model-assisted theorem-route selection.

The model only ranks Lean-indexed declarations.  Its JSON output cannot add a
theorem or close a goal; the selected artifact is elaborated independently.
"""

from __future__ import annotations

import hashlib
import json
from typing import Any, Protocol

from agent.hardness.model_client import extract_json_object

from .models import ModelCallRecord, TheoremCandidate


class StrategyModel(Protocol):
    def complete_json(self, *, system: str, prompt: str): ...


def choose_candidate(
    *,
    model: StrategyModel,
    goal: str,
    candidates: tuple[TheoremCandidate, ...],
    failures: tuple[dict[str, Any], ...],
) -> tuple[TheoremCandidate | None, ModelCallRecord]:
    allowed = {
        f"candidate-{index:03d}": candidate
        for index, candidate in enumerate(candidates)
    }
    failed_declarations = {
        failure.get("declaration")
        for failure in failures
        if isinstance(failure.get("declaration"), str)
    }

    def premise_kind(premise: str) -> str:
        if ".Nonempty" in premise:
            return "finite-nonempty"
        if "IsSchaeferTractable" in premise:
            return "finite-hard-side-classification"
        if "NativeTMNPHard" in premise:
            return "np-hard-subgoal"
        if "NativeTMNPComplete" in premise:
            return "np-complete-subgoal"
        if "CertifiedReduction" in premise or "CertifiedPath" in premise:
            return "certified-reduction-subgoal"
        return "other-lean-proposition"

    prompt = json.dumps(
        {
            "goal_class": "native-np-hardness",
            "candidates": [
                {
                    "candidate_id": candidate_id,
                    "premise_count": candidate.premise_count,
                    "premise_kinds": [premise_kind(item) for item in candidate.premises],
                    "previously_failed": candidate.declaration in failed_declarations,
                }
                for candidate_id, candidate in allowed.items()
            ],
            "required_output": {
                "action": "select_candidate|no_route",
                "candidate_id": "one exact opaque candidate ID or null",
                "reason": "short explanation",
            },
        },
        ensure_ascii=False,
    )
    response = model.complete_json(
        system=(
            "You rank only the opaque candidates supplied by the caller. Never invent an ID. "
            "Respond immediately with one compact JSON object; "
            "do not provide chain-of-thought or proof text."
        ),
        prompt=prompt,
    )
    parsed = extract_json_object(response.content) if response.ok else None
    action = parsed.get("action") if isinstance(parsed, dict) else None
    selected_id = parsed.get("candidate_id") if isinstance(parsed, dict) else None
    selected = allowed.get(selected_id) if isinstance(selected_id, str) else None
    error = response.error
    protocol_ok = bool(
        isinstance(parsed, dict)
        and (
            (action == "select_candidate" and isinstance(selected_id, str) and selected is not None)
            or (action == "no_route" and selected_id is None)
        )
    )
    if response.ok and not isinstance(parsed, dict):
        error = "model response did not contain one JSON object"
    elif response.ok and action not in {"select_candidate", "no_route"}:
        error = "model response used an unsupported strategy action"
    elif response.ok and action == "select_candidate" and selected is None:
        error = "model selected an ID outside the Lean-indexed candidate set"
    elif response.ok and action == "no_route" and selected_id is not None:
        error = "no_route must use a null candidate_id"
    record = ModelCallRecord(
        purpose="strategy-proposal",
        called=response.called,
        ok=response.ok and protocol_ok,
        status_code=response.status_code,
        duration_seconds=response.duration_seconds,
        usage=response.usage,
        attempts=response.attempts,
        response_sha256=hashlib.sha256(response.content.encode("utf-8")).hexdigest(),
        selected_candidate_id=(
            selected_id if selected is not None and isinstance(selected_id, str) else None
        ),
        error=error,
    )
    return selected, record


def confirm_existing_route(
    *, model: StrategyModel, goal: str, resolver_result: dict[str, Any]
) -> ModelCallRecord:
    """Ask the model to inspect, but never authorize, a Lean-resolved route."""

    prompt = json.dumps(
        {
            "goal_class": "native-np-hardness",
            "candidate_id": "existing-route",
            "route_source": "lean-closed-resolver",
            "required_output": {
                "action": "select_candidate",
                "candidate_id": "existing-route",
                "reason": "short explanation",
            },
        },
        ensure_ascii=False,
    )
    response = model.complete_json(
        system=(
            "Select the only supplied opaque candidate. Respond immediately with one compact "
            "JSON object and do not propose declarations, chain-of-thought, or proof text."
        ),
        prompt=prompt,
    )
    parsed = extract_json_object(response.content) if response.ok else None
    protocol_ok = bool(
        isinstance(parsed, dict)
        and parsed.get("action") == "select_candidate"
        and parsed.get("candidate_id") == "existing-route"
    )
    error = response.error
    if response.ok and not protocol_ok:
        error = "model did not select the opaque Lean-resolved route"
    return ModelCallRecord(
        purpose="existing-route-review",
        called=response.called,
        ok=response.ok and protocol_ok,
        status_code=response.status_code,
        duration_seconds=response.duration_seconds,
        usage=response.usage,
        attempts=response.attempts,
        response_sha256=hashlib.sha256(response.content.encode("utf-8")).hexdigest(),
        selected_candidate_id="existing-route" if protocol_ok else None,
        error=error,
    )
