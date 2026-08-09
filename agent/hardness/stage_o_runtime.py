"""Stage O competitive candidate runtime and answer-isolated model driver."""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass, replace
from typing import Any, Callable, Mapping, Protocol, Sequence

from .benchmark import BenchmarkCase
from .model_client import DeepSeekConfig, ModelResponse
from .models import sha256_id
from .stage_o_contract import (
    STAGE_O_INSPECT_LIMIT,
    STAGE_O_SYSTEM_PROMPT,
    StageOAction,
    StageOCandidateMetadata,
    StageOCandidateSet,
    StageOContractError,
    build_contract_candidate_set,
    build_stage_o_contract_prompt,
    candidate_rejection_reasons,
    globally_valid_candidate,
    inspect_packet,
    locally_valid_candidate,
    parse_stage_o_action,
    validate_stage_o_terminal_action,
)


RUNTIME_CANDIDATE_PRODUCER = "stage_o_runtime_candidate_factory"


class JSONModelClient(Protocol):
    config: DeepSeekConfig

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse: ...


@dataclass(frozen=True)
class RuntimeCandidateContext:
    registry_fingerprint: str | None = None
    gap_ordinal: int = 0
    gap_source_endpoint_id: str | None = None
    gap_target_endpoint_id: str | None = None
    gap_capability_head: str | None = None
    gap_dependency_hash: str | None = None
    published_capability_hash: str | None = None
    removed_packet_ids: frozenset[str] = frozenset()


@dataclass(frozen=True)
class SelectionTurn:
    turn: int
    prompt_sha256: str
    response_sha256: str
    status_code: int | None
    attempts: int
    called: bool
    ok: bool
    usage: Mapping[str, Any]
    action: Mapping[str, Any] | None
    error: str | None
    prompt_text: str
    response_text: str

    @property
    def http_ok(self) -> bool:
        return self.called and self.status_code is not None and 200 <= self.status_code < 300

    def to_dict(self) -> dict[str, Any]:
        return {
            "turn": self.turn,
            "prompt_sha256": self.prompt_sha256,
            "response_sha256": self.response_sha256,
            "status_code": self.status_code,
            "attempts": self.attempts,
            "called": self.called,
            "http_ok": self.http_ok,
            "ok": self.ok,
            "usage": dict(self.usage),
            "action": dict(self.action) if self.action else None,
            "error": self.error,
        }


@dataclass(frozen=True)
class SelectionOutcome:
    candidate_set: StageOCandidateSet
    action: StageOAction
    turns: tuple[SelectionTurn, ...]
    inspected_packet_ids: tuple[str, ...]
    original_model_packet_id: str | None

    @property
    def selected_packet_id(self) -> str | None:
        return self.action.packet_id if self.action.action == "select_packet" else None

    @property
    def model_choice_preserved(self) -> bool:
        return self.original_model_packet_id == self.selected_packet_id

    @property
    def real_model_call_count(self) -> int:
        return sum(turn.called for turn in self.turns)

    @property
    def http_ok_count(self) -> int:
        return sum(turn.http_ok for turn in self.turns)

    @property
    def usage(self) -> dict[str, int]:
        totals = {
            "prompt_tokens": 0,
            "completion_tokens": 0,
            "total_tokens": 0,
            "prompt_cache_hit_tokens": 0,
            "prompt_cache_miss_tokens": 0,
        }
        for turn in self.turns:
            for key in totals:
                value = turn.usage.get(key, 0)
                if isinstance(value, int) and not isinstance(value, bool):
                    totals[key] += value
        return totals

    def to_dict(self) -> dict[str, Any]:
        return {
            "candidate_set_id": self.candidate_set.candidate_set_id,
            "session_id": self.candidate_set.session_id,
            "candidate_count": len(self.candidate_set.candidates),
            "locally_valid_packet_ids": [
                candidate.packet_id
                for candidate in self.candidate_set.candidates
                if locally_valid_candidate(candidate, self.candidate_set)
            ],
            "globally_valid_packet_ids": [
                candidate.packet_id
                for candidate in self.candidate_set.candidates
                if globally_valid_candidate(candidate, self.candidate_set)
            ],
            "candidate_rejections": {
                candidate.packet_id: list(candidate_rejection_reasons(candidate, self.candidate_set))
                for candidate in self.candidate_set.candidates
            },
            "inspected_packet_ids": list(self.inspected_packet_ids),
            "original_model_packet_id": self.original_model_packet_id,
            "selected_packet_id": self.selected_packet_id,
            "model_choice_preserved": self.model_choice_preserved,
            "terminal_action": self.action.to_dict(),
            "turns": [turn.to_dict() for turn in self.turns],
            "usage": self.usage,
        }


def _endpoint_id(declaration: str) -> str:
    return sha256_id(
        {"schema_version": "hardness_stage_o_runtime_endpoint_v1", "declaration": declaration}
    )


def _goal_capability_kind(case: BenchmarkCase) -> str:
    if case.objective in {"reduce_to", "reduce_to_known_np", "reduce_to_known_hardness"}:
        return "ComplexityReduction.Certificate.CertifiedReduction"
    if case.objective == "prove_in_np":
        return "ComplexityReduction.Certificate.NativeTMInNP"
    if case.objective == "prove_np_complete":
        return "ComplexityReduction.Certificate.NativeTMNPComplete"
    raise StageOContractError("unsupported_objective", f"unsupported objective {case.objective}")


def _candidate_kind(capability_head: str) -> str:
    if capability_head.endswith("NativeTMInNP"):
        return "membership_packet"
    if capability_head.endswith("NativeTMNPComplete"):
        return "route_packet"
    if "DirectTM" in capability_head or "Checker" in capability_head:
        return "tm_certificate_packet"
    return "route_packet"


def _positive_candidate_set(
    case: BenchmarkCase, *, context: RuntimeCandidateContext
) -> StageOCandidateSet:
    if context.gap_ordinal:
        if not all(
            (
                context.gap_source_endpoint_id,
                context.gap_target_endpoint_id,
                context.gap_capability_head,
                context.gap_dependency_hash,
            )
        ):
            raise StageOContractError("gap_sequence_mismatch", "runtime gap context is incomplete")
        goal_input = str(context.gap_source_endpoint_id)
        goal_output = str(context.gap_target_endpoint_id)
        capability_head = str(context.gap_capability_head)
        registry = context.registry_fingerprint or sha256_id({"gap": context.gap_ordinal})
    else:
        goal_input = _endpoint_id(case.effective_input_declaration)
        goal_output = _endpoint_id(case.target or f"objective:{case.objective}:exact-source")
        capability_head = _goal_capability_kind(case)
        registry = context.registry_fingerprint or sha256_id(
            {
                "schema_version": "hardness_stage_o_runtime_registry_v1",
                "module": case.module,
                "input": case.effective_input_declaration,
                "resolved_parameters": case.stage_o["resolved_parameters"],
            }
        )
    direction = "identity" if capability_head.endswith(("NativeTMInNP", "NativeTMNPComplete")) else "source_to_target"
    dependencies = ["dep:core", "dep:input-gate", "dep:standard-axioms"]
    required_dependencies: tuple[str, ...] = ("dep:standard-axioms",)
    if case.stage_o["promotion_role"] == "consumer":
        required_dependencies = ("dep:published-capability", "dep:standard-axioms")
        if context.published_capability_hash:
            dependencies.append("dep:published-capability")
    if context.gap_dependency_hash:
        dependencies.append(f"dep:gap-parent:{context.gap_dependency_hash}")
        required_dependencies = (*required_dependencies, f"dep:gap-parent:{context.gap_dependency_hash}")

    base_source_hash = sha256_id(
        {
            "schema_version": "hardness_stage_o_runtime_candidate_source_v1",
            "goal_input": goal_input,
            "goal_output": goal_output,
            "capability_head": capability_head,
            "gap_ordinal": context.gap_ordinal,
            "registry": registry,
        }
    )
    middle_a = sha256_id({"route": "a", "input": goal_input, "output": goal_output})
    middle_b = sha256_id({"route": "b", "input": goal_input, "output": goal_output})

    def valid_candidate(*, role: str, middle: str, salt: str) -> StageOCandidateMetadata:
        source_hash = sha256_id({"base": base_source_hash, "salt": salt})
        return StageOCandidateMetadata(
            candidate_kind=_candidate_kind(capability_head),
            input_endpoint_id=goal_input,
            output_endpoint_id=goal_output,
            direction=direction,
            capability_kind=capability_head,
            preconditions=("dep:core", "dep:input-gate"),
            dependencies=required_dependencies,
            compiler_role=role,
            visibility="published" if case.stage_o["promotion_role"] == "consumer" else "base_registry",
            allowed_imports=("ComplexityReduction.Agent.Hardness.Runtime",),
            declared_axioms=(),
            route_segments=((goal_input, middle), (middle, goal_output)),
            candidate_source_hash=source_hash,
            bound_dependency_hash=source_hash,
            producer=RUNTIME_CANDIDATE_PRODUCER,
        )

    first = valid_candidate(role="typed_path_composition", middle=middle_a, salt="path")
    second = valid_candidate(role="direct_certificate_composition", middle=middle_b, salt="direct")
    missing = replace(
        first,
        compiler_role="locally_valid_missing_dependency",
        dependencies=("dep:not-published",),
    )
    wrong_direction = replace(
        first,
        compiler_role="wrong_direction_decoy",
        direction="identity" if direction == "source_to_target" else "source_to_target",
    )
    wrong_endpoint = replace(
        first,
        compiler_role="wrong_endpoint_decoy",
        output_endpoint_id=middle_a,
        route_segments=((goal_input, middle_a),),
    )
    candidates = tuple(
        sorted(
            (
                candidate
                for candidate in (first, second, missing, wrong_direction, wrong_endpoint)
                if candidate.packet_id not in context.removed_packet_ids
            ),
            key=lambda candidate: candidate.packet_id,
        )
    )
    return StageOCandidateSet(
        goal_input_endpoint_id=goal_input,
        goal_output_endpoint_id=goal_output,
        required_direction=direction,
        required_capability_kind=capability_head,
        available_dependencies=tuple(dependencies),
        registry_fingerprint=registry,
        candidates=candidates,
        producer=RUNTIME_CANDIDATE_PRODUCER,
    )


def build_runtime_candidate_set(
    case: BenchmarkCase, *, context: RuntimeCandidateContext = RuntimeCandidateContext()
) -> StageOCandidateSet:
    if case.stage_o["contract_probe_profile"] != "valid_competitive":
        candidate_set = build_contract_candidate_set(case)
        if context.removed_packet_ids:
            candidate_set = replace(
                candidate_set,
                candidates=tuple(
                    candidate
                    for candidate in candidate_set.candidates
                    if candidate.packet_id not in context.removed_packet_ids
                ),
            )
        return candidate_set
    candidate_set = _positive_candidate_set(case, context=context)
    if not 3 <= len(candidate_set.candidates) <= 8:
        raise StageOContractError(
            "competitive_choice_not_real", "runtime candidate count is outside the frozen 3..8 range"
        )
    return candidate_set


def drive_candidate_selection(
    *,
    client: JSONModelClient,
    candidate_set: StageOCandidateSet,
    max_turns: int = 4,
    on_turn: Callable[[SelectionTurn], None] | None = None,
) -> SelectionOutcome:
    inspected: list[str] = []
    turns: list[SelectionTurn] = []
    retrieved = {candidate.packet_id for candidate in candidate_set.candidates}
    original_model_packet_id: str | None = None
    previous_rejection: str | None = None
    for turn_number in range(1, max_turns + 1):
        prompt = build_stage_o_contract_prompt(
            candidate_set=candidate_set,
            inspected_packet_ids=inspected,
            previous_rejection=previous_rejection,
            remaining_model_turns=max_turns - turn_number + 1,
        )
        response = client.complete_json(system=STAGE_O_SYSTEM_PROMPT, prompt=prompt)
        prompt_hash = hashlib.sha256(prompt.encode("utf-8")).hexdigest()
        response_hash = hashlib.sha256(response.content.encode("utf-8")).hexdigest()
        action: StageOAction | None = None
        error: str | None = response.error
        contract_error: StageOContractError | None = None
        terminal = False
        if response.ok:
            try:
                action = parse_stage_o_action(response.content, candidate_set=candidate_set)
                if action.action == "inspect_packet":
                    packet_id = action.packet_id or ""
                    if packet_id in inspected:
                        raise StageOContractError(
                            "inspect_budget_exhausted",
                            "packet was already inspected; select a packet or stop authoring",
                        )
                    inspect_packet(
                        candidate_set,
                        packet_id,
                        retrieved_packet_ids=retrieved,
                        already_inspected=inspected,
                    )
                    if packet_id not in inspected:
                        inspected.append(packet_id)
                else:
                    validate_stage_o_terminal_action(action, candidate_set=candidate_set)
                    terminal = True
                    if action.action == "select_packet":
                        original_model_packet_id = action.packet_id
            except StageOContractError as rejected:
                contract_error = rejected
                error = f"{rejected.code}: {rejected.message}"
        turn = SelectionTurn(
            turn=turn_number,
            prompt_sha256=prompt_hash,
            response_sha256=response_hash,
            status_code=response.status_code,
            attempts=response.attempts,
            called=response.called,
            ok=response.ok and action is not None and contract_error is None,
            usage=response.usage or {},
            action=action.to_dict() if action else None,
            error=error,
            prompt_text=prompt,
            response_text=response.content,
        )
        turns.append(turn)
        if on_turn is not None:
            on_turn(turn)
        if not response.ok:
            raise StageOContractError("model_request_failed", response.error or "model request failed")
        if contract_error is not None:
            if turn_number == max_turns:
                raise contract_error
            previous_rejection = error
            continue
        previous_rejection = None
        if action is None:
            rejected = StageOContractError("invalid_model_json", error or "invalid model action")
            if turn_number == max_turns:
                raise rejected
            previous_rejection = f"{rejected.code}: {rejected.message}"
            continue
        if action.action == "inspect_packet":
            continue
        if terminal:
            return SelectionOutcome(
                candidate_set=candidate_set,
                action=action,
                turns=tuple(turns),
                inspected_packet_ids=tuple(inspected),
                original_model_packet_id=original_model_packet_id,
            )
    raise StageOContractError("nonterminal_action", "model did not submit a terminal action")


class SimulatedStageOClient:
    """Fixed public-contract policy used only for O-B offline qualification."""

    def __init__(self, candidate_set: StageOCandidateSet, *, choice_salt: str = "offline"):
        self.candidate_set = candidate_set
        self.choice_salt = choice_salt
        self.config = DeepSeekConfig(
            api_key="simulated",
            base_url="https://offline.invalid",
            model="simulated-stage-o",
            timeout_seconds=1,
            max_tokens=4096,
            max_retries=0,
            temperature=0.0,
        )

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        del system
        payload = json.loads(prompt)
        inspected = {
            str(item["packet_id"]): item for item in payload.get("inspected_packets", [])
        }
        valid = [
            candidate
            for candidate in self.candidate_set.candidates
            if globally_valid_candidate(candidate, self.candidate_set)
        ]
        valid.sort(
            key=lambda candidate: sha256_id(
                {"salt": self.choice_salt, "packet_id": candidate.packet_id}
            )
        )
        if valid:
            selected = valid[0]
            if selected.packet_id not in inspected:
                action = {
                    "schema_version": "hardness_stage_o_action_v1",
                    "action": "inspect_packet",
                    "session_id": self.candidate_set.session_id,
                    "packet_id": selected.packet_id,
                    "explanation": "Inspect the public metadata before committing to this candidate.",
                }
            else:
                action = {
                    "schema_version": "hardness_stage_o_action_v1",
                    "action": "select_packet",
                    "session_id": self.candidate_set.session_id,
                    "packet_id": selected.packet_id,
                    "candidate_kind": selected.candidate_kind,
                    "typed_bindings": {
                        "input_endpoint_id": selected.input_endpoint_id,
                        "output_endpoint_id": selected.output_endpoint_id,
                        "direction": selected.direction,
                        "capability_kind": selected.capability_kind,
                    },
                    "dependencies": list(selected.dependencies),
                    "explanation": "Public preconditions, dependencies, topology, visibility, and hashes all validate.",
                }
        else:
            checked = [candidate.packet_id for candidate in self.candidate_set.candidates[:1]]
            if not inspected:
                action = {
                    "schema_version": "hardness_stage_o_action_v1",
                    "action": "inspect_packet",
                    "session_id": self.candidate_set.session_id,
                    "packet_id": checked[0],
                    "explanation": "Inspect a bounded candidate before reporting the deterministic blocker.",
                }
            else:
                reasons = sorted(
                    {
                        reason
                        for candidate in self.candidate_set.candidates
                        for reason in candidate_rejection_reasons(candidate, self.candidate_set)
                    }
                )
                action = {
                    "schema_version": "hardness_stage_o_action_v1",
                    "action": "stop_authoring",
                    "session_id": self.candidate_set.session_id,
                    "checked_packet_ids": sorted(inspected),
                    "missing_conditions": reasons or ["No globally valid candidate remains."],
                    "explanation": "Every inspected candidate violates at least one public validation rule.",
                }
        content = json.dumps(action, ensure_ascii=True, sort_keys=True)
        prompt_tokens = max(1, len(prompt) // 4)
        completion_tokens = max(1, len(content) // 4)
        return ModelResponse(
            called=False,
            ok=True,
            content=content,
            error=None,
            status_code=None,
            duration_seconds=0.0,
            usage={
                "prompt_tokens": prompt_tokens,
                "completion_tokens": completion_tokens,
                "total_tokens": prompt_tokens + completion_tokens,
                "prompt_cache_hit_tokens": 0,
                "prompt_cache_miss_tokens": prompt_tokens,
            },
            attempts=0,
            finish_reason="simulated",
        )
