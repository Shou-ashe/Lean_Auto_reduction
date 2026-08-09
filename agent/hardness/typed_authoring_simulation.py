"""Prompt-only packet selector for offline Stage-M full-suite tests."""

from __future__ import annotations

import json
from typing import Any, Mapping

from .model_client import DeepSeekConfig, ModelResponse
from .model_authoring import MODEL_SYSTEM_PROMPT
from .typed_authoring import (
    PACKET_SELECTION_SCHEMA,
    TYPED_AUTHORING_SYSTEM_PROMPT,
    audit_packet_selection_prompt,
)


class SimulatedTypedAuthoringClient:
    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        if system != TYPED_AUTHORING_SYSTEM_PROMPT:
            raise ValueError("simulator received the wrong Stage-M system prompt")
        payload = json.loads(prompt)
        if not isinstance(payload, Mapping):
            raise ValueError("Stage-M prompt must be one JSON object")
        audit_packet_selection_prompt(payload)
        index = payload.get("packet_index")
        packets: list[Any] = []
        if isinstance(index, Mapping) and isinstance(index.get("packets"), list):
            packets = index["packets"]
        packet = next((item for item in packets if isinstance(item, Mapping)), None)
        if packet is None:
            content = json.dumps(
                {
                    "schema_version": PACKET_SELECTION_SCHEMA,
                    "action": "select_packet",
                    "task_id": payload["task_id"],
                    "packet_id": "sha256:" + "0" * 64,
                    "bindings": {"candidate_id": "none", "template_kind": "none"},
                    "explanation": "No packet is available.",
                },
                sort_keys=True,
            )
        else:
            content = json.dumps(
                {
                    "schema_version": PACKET_SELECTION_SCHEMA,
                    "action": "select_packet",
                    "task_id": payload["task_id"],
                    "packet_id": packet["packet_id"],
                    "bindings": {
                        "candidate_id": packet["candidate_id"],
                        "template_kind": packet["template_kind"],
                    },
                    "explanation": "Select the exact Lean-confirmed packet matching the active node.",
                },
                sort_keys=True,
            )
        return ModelResponse(
            called=False,
            ok=True,
            content=content,
            error=None,
            status_code=None,
            duration_seconds=0.0,
            usage=None,
            attempts=0,
            finish_reason="simulated",
        )


class SimulatedSemanticProofClient:
    """Offline proof-body client that reads only the public authoring prompt."""

    def __init__(self) -> None:
        self.config = DeepSeekConfig(
            api_key="",
            base_url="https://offline.invalid",
            model="simulated-stage-m",
        )

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        if system != MODEL_SYSTEM_PROMPT:
            raise ValueError("simulator received the wrong model-authoring system prompt")
        marker = "AUTHORING_REQUEST_JSON\n"
        suffix = "\n\nAll current source"
        if marker not in prompt or suffix not in prompt:
            raise ValueError("model-authoring prompt has an unsupported envelope")
        encoded = prompt.split(marker, 1)[1].split(suffix, 1)[0]
        request = json.loads(encoded)
        if not isinstance(request, Mapping) or request.get("stage") != "semantic_proof":
            raise ValueError("offline Stage-M proof client accepts only semantic_proof")
        content = json.dumps(
            {
                "schema_version": "hardness_model_patch_v1",
                "task_id": request["task_id"],
                "stage": request["stage"],
                "editable_file": request["editable_file"],
                "replacement": (
                    "  by\n"
                    "    intro input\n"
                    "    change input = input ↔ True\n"
                    "    simp\n"
                ),
            },
            sort_keys=True,
        )
        return ModelResponse(
            called=False,
            ok=True,
            content=content,
            error=None,
            status_code=None,
            duration_seconds=0.0,
            usage=None,
            attempts=0,
            finish_reason="simulated",
        )
