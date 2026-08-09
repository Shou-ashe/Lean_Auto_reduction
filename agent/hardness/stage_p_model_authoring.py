"""Fenced Stage P candidate authoring and bounded diagnostic repair.

The model can replace only one Lean term body.  Fixed imports, namespace,
declaration head, audit footer, exact endpoints, and task identity remain
orchestrator-owned.  Every accepted turn is content addressed and repeated
source or diagnostic states fail closed.
"""

from __future__ import annotations

import json
import re
from dataclasses import asdict, dataclass, field
from typing import Any, Mapping

from .lean_runner import (
    assert_generated_source_is_safe,
    validate_declaration_name,
    validate_module_name,
)
from .models import sha256_id
from .stage_p_contract import (
    BANNED_BODY_RE,
    ORACLE_MARKERS,
    SAFE_FILE_RE,
    SAFE_REGION_RE,
    STAGE_P_DIAGNOSTICS_SCHEMA,
    STAGE_P_PATCH_SCHEMA,
    STAGE_P_PROMPT_SCHEMA,
    StagePAuthoringTask,
    StagePContractError,
    StagePPatchAction,
    audit_stage_p_prompt,
    parse_stage_p_action,
    validate_stage_p_patch,
)
from .stage_p_runtime import StagePImmutableRequest, StagePRuntimeGap


STAGE_P_BOUND_TASK_SCHEMA = "hardness_stage_p_bound_task_v1"
STAGE_P_REPAIR_TURN_SCHEMA = "hardness_stage_p_repair_turn_v1"
STAGE_P_MAX_HELPERS = 8
STAGE_P_MAX_HELPER_SUMMARY_CHARS = 2_000
STAGE_P_MAX_PRIMARY_DIAGNOSTIC_CHARS = 2_000
STAGE_P_MAX_TYPE_SUMMARY_CHARS = 1_500
STAGE_P_MAX_LOCAL_CONTEXT_CHARS = 2_000

IMPORT_RE = re.compile(r"(?m)^\s*import\s+([A-Z][A-Za-z0-9_']*(?:\.[A-ZA-Za-z0-9_']+)*)\s*$")
DIAGNOSTIC_HEADER_RE = re.compile(
    r"^(?P<location>.*?:\d+:\d+):\s*(?P<severity>error|warning|info):\s*(?P<message>.*)$",
    re.IGNORECASE,
)


def _assert_no_oracle_text(value: str, *, code: str) -> None:
    lowered = value.lower()
    if any(marker.lower() in lowered for marker in ORACLE_MARKERS):
        raise StagePContractError(code, "quarantined oracle text entered authoring context")


def _bounded(value: str, limit: int) -> str:
    normalized = value.replace("\r\n", "\n").replace("\r", "\n").strip()
    if len(normalized) <= limit:
        return normalized
    return normalized[:limit] + "\n... bounded ..."


@dataclass(frozen=True)
class StagePCandidateSource:
    fixed_header: str
    editable_body: str
    fixed_footer: str
    allowed_imports: tuple[str, ...]

    @property
    def source(self) -> str:
        return self.fixed_header + self.editable_body + self.fixed_footer

    @property
    def source_sha256(self) -> str:
        return sha256_id(self.source)

    @property
    def fixed_header_sha256(self) -> str:
        return sha256_id(self.fixed_header)

    @property
    def fixed_footer_sha256(self) -> str:
        return sha256_id(self.fixed_footer)

    @property
    def editable_body_sha256(self) -> str:
        return sha256_id(self.editable_body)

    @property
    def compiler_inserted_math_token_count(self) -> int:
        return 0

    def validate(self) -> None:
        if not self.fixed_header.endswith(":=\n"):
            raise StagePContractError(
                "candidate_static_policy_failed",
                "fixed declaration header must end immediately before the Lean term body",
            )
        if not self.editable_body.strip():
            raise StagePContractError(
                "candidate_static_policy_failed", "candidate editable body is empty"
            )
        if BANNED_BODY_RE.search(self.editable_body):
            raise StagePContractError(
                "sorry_axiom_or_unsafe_candidate",
                "candidate editable body contains a forbidden Lean command or trust token",
            )
        if len(set(self.allowed_imports)) != len(self.allowed_imports):
            raise StagePContractError("import_not_allowlisted", "allowed import list has duplicates")
        for module in self.allowed_imports:
            try:
                validate_module_name(module)
            except ValueError as error:
                raise StagePContractError("import_not_allowlisted", str(error)) from error
        imported = tuple(IMPORT_RE.findall(self.fixed_header))
        declared_import_lines = sum(
            1 for line in self.fixed_header.splitlines() if line.lstrip().startswith("import ")
        )
        if declared_import_lines != len(imported):
            raise StagePContractError("import_not_allowlisted", "fixed header has a malformed import")
        if not set(imported).issubset(self.allowed_imports):
            raise StagePContractError("import_not_allowlisted", "fixed header imports an unlisted module")
        _assert_no_oracle_text(self.source, code="oracle_or_gold_import")
        try:
            assert_generated_source_is_safe(self.source)
        except ValueError as error:
            message = str(error)
            code = (
                "oracle_or_gold_import"
                if "quarantined" in message
                else "sorry_axiom_or_unsafe_candidate"
            )
            raise StagePContractError(code, message) from error

    def replace_body(self, body: str) -> "StagePCandidateSource":
        candidate = StagePCandidateSource(
            fixed_header=self.fixed_header,
            editable_body=body if body.endswith("\n") else body + "\n",
            fixed_footer=self.fixed_footer,
            allowed_imports=self.allowed_imports,
        )
        candidate.validate()
        if (
            candidate.fixed_header_sha256 != self.fixed_header_sha256
            or candidate.fixed_footer_sha256 != self.fixed_footer_sha256
        ):
            raise StagePContractError(
                "patch_outside_editable_region", "fixed candidate source changed during replacement"
            )
        return candidate


@dataclass(frozen=True)
class StagePBoundAuthoringTask:
    request: StagePImmutableRequest
    gap: StagePRuntimeGap
    candidate_module: str
    candidate_declaration: str
    declaration_signature: str
    expected_type: str
    editable_file: str
    editable_region: str
    allowed_imports: tuple[str, ...]
    helper_handles: tuple[str, ...]
    semantic_turn_budget: int
    token_budget: int
    schema_version: str = STAGE_P_BOUND_TASK_SCHEMA

    def validate(self) -> None:
        if self.schema_version != STAGE_P_BOUND_TASK_SCHEMA:
            raise StagePContractError("invalid_stage_p_patch_schema", "bound task schema drifted")
        self.gap.validate(self.request)
        try:
            validate_module_name(self.candidate_module)
            validate_declaration_name(
                self.candidate_declaration, label="Stage P candidate declaration"
            )
        except ValueError as error:
            raise StagePContractError("candidate_static_policy_failed", str(error)) from error
        for label, value in {
            "declaration_signature": self.declaration_signature,
            "expected_type": self.expected_type,
        }.items():
            if not value.strip():
                raise StagePContractError("candidate_exact_type_mismatch", f"{label} is empty")
        if self.declaration_signature != self.gap.declaration_signature:
            raise StagePContractError(
                "candidate_exact_type_mismatch", "bound declaration signature differs from Core gap"
            )
        if not SAFE_FILE_RE.fullmatch(self.editable_file):
            raise StagePContractError("patch_outside_editable_region", "editable file is unsafe")
        if not SAFE_REGION_RE.fullmatch(self.editable_region):
            raise StagePContractError("patch_outside_editable_region", "editable region is unsafe")
        if len(self.helper_handles) > STAGE_P_MAX_HELPERS or len(set(self.helper_handles)) != len(
            self.helper_handles
        ):
            raise StagePContractError(
                "fabricated_declaration_handle", "helper handle allowlist is oversized or duplicated"
            )
        if any(not handle.strip() for handle in self.helper_handles):
            raise StagePContractError(
                "fabricated_declaration_handle", "helper handle allowlist contains an empty handle"
            )
        if not 1 <= self.semantic_turn_budget <= 4:
            raise StagePContractError(
                "authoring_budget_exhausted", "task semantic turn budget must be between one and four"
            )
        if self.token_budget <= 0:
            raise StagePContractError("authoring_budget_exhausted", "task token budget is empty")

    @property
    def session_id(self) -> str:
        self.validate()
        return sha256_id(
            {
                "schema_version": "hardness_stage_p_bound_session_v1",
                "request_id": self.request.request_id,
                "gap_id": self.gap.gap_id,
                "parent_checkpoint_hash": self.gap.parent_checkpoint_hash,
                "candidate_module": self.candidate_module,
                "candidate_declaration": self.candidate_declaration,
                "editable_file": self.editable_file,
                "editable_region": self.editable_region,
            }
        )

    def protocol_task(self, *, base_source_sha256: str) -> StagePAuthoringTask:
        self.validate()
        return StagePAuthoringTask(
            session_id=self.session_id,
            gap_id=self.gap.gap_id,
            parent_checkpoint_hash=self.gap.parent_checkpoint_hash,
            task_class=self.gap.task_class,
            capability_head=self.gap.capability_head,
            declaration_signature=self.declaration_signature,
            contract_probe="proof",
            source_endpoint=self.request.source_declaration,
            target_endpoint=self.request.target_declaration,
            direction=self.request.direction,
            objective=self.request.objective,
            editable_file=self.editable_file,
            editable_region=self.editable_region,
            base_source_sha256=base_source_sha256,
            allowed_imports=self.allowed_imports,
            helper_handles=self.helper_handles,
            semantic_turn_budget=self.semantic_turn_budget,
            token_budget=self.token_budget,
            public_blocker=None,
        )

    def prompt_view(self, *, base_source_sha256: str) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "session_id": self.session_id,
            "request_id": self.request.request_id,
            "gap_id": self.gap.gap_id,
            "gap_ordinal": self.gap.ordinal,
            "parent_checkpoint_hash": self.gap.parent_checkpoint_hash,
            "task_class": self.gap.task_class,
            "capability_head": self.gap.capability_head,
            "source_endpoint": self.request.source_declaration,
            "target_endpoint": self.request.target_declaration,
            "direction": self.request.direction,
            "objective": self.request.objective,
            "candidate_module": self.candidate_module,
            "candidate_declaration": self.candidate_declaration,
            "declaration_signature": self.declaration_signature,
            "expected_type": self.expected_type,
            "editable_file": self.editable_file,
            "editable_region": self.editable_region,
            "base_source_sha256": base_source_sha256,
            "allowed_imports": list(self.allowed_imports),
            "helper_handles": list(self.helper_handles),
            "semantic_turn_budget": self.semantic_turn_budget,
            "token_budget": self.token_budget,
        }


@dataclass(frozen=True)
class StagePDiagnostics:
    primary_error: str
    location: str | None
    expected_type: str
    actual_type: str
    local_context: str
    raw_diagnostics_sha256: str
    candidate_source_sha256: str
    schema_version: str = STAGE_P_DIAGNOSTICS_SCHEMA

    @property
    def diagnostics_sha256(self) -> str:
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})

    def to_dict(self) -> dict[str, Any]:
        return {**asdict(self), "diagnostics_sha256": self.diagnostics_sha256}


def summarize_stage_p_diagnostics(
    raw: str,
    *,
    expected_type: str,
    actual_type: str = "",
    local_context: str = "",
    candidate_source_sha256: str,
) -> StagePDiagnostics:
    _assert_no_oracle_text(raw, code="oracle_or_gold_import")
    _assert_no_oracle_text(local_context, code="oracle_or_gold_import")
    lines = raw.replace("\r\n", "\n").replace("\r", "\n").splitlines()
    start = None
    location = None
    primary_lines: list[str] = []
    for index, line in enumerate(lines):
        match = DIAGNOSTIC_HEADER_RE.match(line)
        if match and match.group("severity").lower() == "error":
            start = index
            location = match.group("location")
            primary_lines.append(match.group("message"))
            break
    if start is None:
        primary_lines = [line.strip() for line in lines if line.strip()]
        if not primary_lines:
            primary_lines = ["Lean failed"]
    else:
        for line in lines[start + 1 :]:
            if DIAGNOSTIC_HEADER_RE.match(line):
                break
            primary_lines.append(line)
    primary = _bounded("\n".join(primary_lines), STAGE_P_MAX_PRIMARY_DIAGNOSTIC_CHARS)
    return StagePDiagnostics(
        primary_error=primary,
        location=location,
        expected_type=_bounded(expected_type, STAGE_P_MAX_TYPE_SUMMARY_CHARS),
        actual_type=_bounded(actual_type, STAGE_P_MAX_TYPE_SUMMARY_CHARS),
        local_context=_bounded(local_context, STAGE_P_MAX_LOCAL_CONTEXT_CHARS),
        raw_diagnostics_sha256=sha256_id(raw),
        candidate_source_sha256=candidate_source_sha256,
    )


@dataclass(frozen=True)
class StagePRepairTurn:
    turn: int
    action: str
    model_response_sha256: str
    action_sha256: str
    base_source_sha256: str
    candidate_source_sha256: str
    editable_body_sha256: str
    helper_handle: str | None = None
    schema_version: str = STAGE_P_REPAIR_TURN_SCHEMA

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass
class StagePRepairSession:
    task: StagePBoundAuthoringTask
    candidate: StagePCandidateSource
    helper_summaries: Mapping[str, str] = field(default_factory=dict)
    turns: list[StagePRepairTurn] = field(default_factory=list, init=False)
    requested_helpers: set[str] = field(default_factory=set, init=False)
    seen_candidate_hashes: set[str] = field(default_factory=set, init=False)
    seen_diagnostics_hashes: set[str] = field(default_factory=set, init=False)
    last_diagnostics: StagePDiagnostics | None = field(default=None, init=False)
    accepted_patch_count: int = field(default=0, init=False)

    def __post_init__(self) -> None:
        self.task.validate()
        self.candidate.validate()
        if self.candidate.allowed_imports != self.task.allowed_imports:
            raise StagePContractError(
                "import_not_allowlisted", "candidate and task import allowlists differ"
            )
        if set(self.helper_summaries) != set(self.task.helper_handles):
            raise StagePContractError(
                "fabricated_declaration_handle", "helper summaries do not match retrieved handles"
            )
        for handle, summary in self.helper_summaries.items():
            if not handle.strip() or not summary.strip():
                raise StagePContractError(
                    "fabricated_declaration_handle", "helper handle or summary is empty"
                )
            if len(summary) > STAGE_P_MAX_HELPER_SUMMARY_CHARS:
                raise StagePContractError(
                    "fabricated_declaration_handle", "helper summary exceeds the public bound"
                )
            _assert_no_oracle_text(summary, code="oracle_or_gold_import")
        self.seen_candidate_hashes.add(self.candidate.source_sha256)

    @property
    def remaining_turns(self) -> int:
        return self.task.semantic_turn_budget - len(self.turns)

    @property
    def protocol_task(self) -> StagePAuthoringTask:
        return self.task.protocol_task(base_source_sha256=self.candidate.source_sha256)

    def accept_model_response(self, content: str) -> StagePPatchAction:
        if self.remaining_turns <= 0:
            raise StagePContractError("authoring_budget_exhausted", "repair turn budget exhausted")
        protocol_task = self.protocol_task
        action = parse_stage_p_action(content, task=protocol_task)
        response_sha256 = sha256_id(content)
        action_sha256 = sha256_id(action.to_dict())
        base_source_sha256 = self.candidate.source_sha256
        helper_handle: str | None = None
        if action.action == "request_helper":
            helper_handle = action.helper_handles[0]
            if helper_handle in self.requested_helpers:
                raise StagePContractError(
                    "authoring_no_progress", "model repeated an already served helper request"
                )
            self.requested_helpers.add(helper_handle)
        elif action.action == "submit_patch":
            validate_stage_p_patch(action, task=protocol_task)
            updated = self.candidate.replace_body(action.replacement_body or "")
            if updated.source_sha256 in self.seen_candidate_hashes:
                raise StagePContractError(
                    "authoring_no_progress", "model repeated a previous candidate source"
                )
            self.candidate = updated
            self.seen_candidate_hashes.add(updated.source_sha256)
            self.accepted_patch_count += 1
        else:
            raise StagePContractError(
                "authoring_no_progress", "positive repair session stopped without a candidate"
            )
        turn = StagePRepairTurn(
            turn=len(self.turns) + 1,
            action=action.action,
            model_response_sha256=response_sha256,
            action_sha256=action_sha256,
            base_source_sha256=base_source_sha256,
            candidate_source_sha256=self.candidate.source_sha256,
            editable_body_sha256=self.candidate.editable_body_sha256,
            helper_handle=helper_handle,
        )
        self.turns.append(turn)
        return action

    def record_failed_validation(
        self,
        raw_diagnostics: str,
        *,
        actual_type: str = "",
        local_context: str = "",
    ) -> StagePDiagnostics:
        diagnostics = summarize_stage_p_diagnostics(
            raw_diagnostics,
            expected_type=self.task.expected_type,
            actual_type=actual_type,
            local_context=local_context,
            candidate_source_sha256=self.candidate.source_sha256,
        )
        if diagnostics.diagnostics_sha256 in self.seen_diagnostics_hashes:
            raise StagePContractError(
                "authoring_diagnostics_repeated", "the same bounded Lean diagnostic repeated"
            )
        self.seen_diagnostics_hashes.add(diagnostics.diagnostics_sha256)
        self.last_diagnostics = diagnostics
        return diagnostics

    def build_prompt(self) -> str:
        task = self.protocol_task
        served_helpers = {
            handle: self.helper_summaries[handle]
            for handle in sorted(self.requested_helpers)
        }
        response_template = {
            "schema_version": STAGE_P_PATCH_SCHEMA,
            "action": "submit_patch | request_helper | stop_authoring",
            "session_id": task.session_id,
            "gap_id": task.gap_id,
            "task_class": task.task_class,
            "base_source_sha256": task.base_source_sha256,
            "editable_file": task.editable_file,
            "editable_region": task.editable_region,
            "replacement_body": "<Lean term only; required only for submit_patch>",
            "helper_handles": [],
            "binding_claim": {
                "source_endpoint": task.source_endpoint,
                "target_endpoint": task.target_endpoint,
                "direction": task.direction,
                "objective": task.objective,
                "capability_head": task.capability_head,
                "declaration_signature": task.declaration_signature,
            },
        }
        payload = {
            "schema_version": STAGE_P_PROMPT_SCHEMA,
            "contract_scope": "P-B exact fenced Lean body authoring",
            "task": self.task.prompt_view(base_source_sha256=self.candidate.source_sha256),
            "candidate": {
                "fixed_header_sha256": self.candidate.fixed_header_sha256,
                "fixed_footer_sha256": self.candidate.fixed_footer_sha256,
                "current_source_sha256": self.candidate.source_sha256,
                "current_editable_body": self.candidate.editable_body,
                "compiler_inserted_math_token_count": 0,
            },
            "bounded_diagnostics": (
                self.last_diagnostics.to_dict() if self.last_diagnostics is not None else None
            ),
            "available_helper_handles": list(self.task.helper_handles),
            "served_helper_summaries": served_helpers,
            "remaining_semantic_turns": self.remaining_turns,
            "response_template": response_template,
            "constraints": {
                "json_only": True,
                "one_editable_body": True,
                "may_change_request": False,
                "may_add_imports_or_declarations": False,
                "may_use_unlisted_helpers": False,
                "compiler_inserts_math": False,
            },
        }
        audit_stage_p_prompt(payload)
        return json.dumps(payload, ensure_ascii=False, sort_keys=True)

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": "hardness_stage_p_repair_session_v1",
            "session_id": self.task.session_id,
            "gap_id": self.task.gap.gap_id,
            "remaining_turns": self.remaining_turns,
            "accepted_patch_count": self.accepted_patch_count,
            "requested_helpers": sorted(self.requested_helpers),
            "candidate": {
                "source_sha256": self.candidate.source_sha256,
                "fixed_header_sha256": self.candidate.fixed_header_sha256,
                "fixed_footer_sha256": self.candidate.fixed_footer_sha256,
                "editable_body_sha256": self.candidate.editable_body_sha256,
                "compiler_inserted_math_token_count": 0,
            },
            "last_diagnostics": (
                self.last_diagnostics.to_dict() if self.last_diagnostics is not None else None
            ),
            "turns": [turn.to_dict() for turn in self.turns],
        }
