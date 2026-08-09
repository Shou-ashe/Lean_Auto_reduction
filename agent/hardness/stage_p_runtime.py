"""Versioned Stage P orchestration state for one-to-four authored gaps.

This module is deliberately observational.  It binds exact request and gap
identities, accounts for model/transport budgets, and records the publication
and fresh-Core transition chain.  It never manufactures a Lean capability:
candidate validation, publication, final Lean, the standard-axiom audit, and
release replay remain independent authorities.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass, field, replace
from typing import Any

from .models import sha256_id
from .stage_p_contract import (
    CAPABILITY_HEADS,
    SHA256_RE,
    TASK_CLASSES,
    StagePContractError,
)


STAGE_P_REQUEST_SCHEMA = "hardness_stage_p_immutable_request_v1"
STAGE_P_RUNTIME_GAP_SCHEMA = "hardness_stage_p_runtime_gap_v1"
STAGE_P_CHECKPOINT_SCHEMA = "hardness_stage_p_gap_checkpoint_v1"
STAGE_P_RUNTIME_TRACE_SCHEMA = "hardness_stage_p_runtime_trace_v1"

STAGE_P_MAX_GAPS = 4
STAGE_P_MAX_SEMANTIC_TURNS_PER_GAP = 4
STAGE_P_TOKENS_PER_GAP = 30_000
STAGE_P_MAX_TRANSPORT_RETRIES_PER_SEMANTIC_TURN = 2

STAGE_P_OBJECTIVES = frozenset(
    {
        "reduce_to",
        "reduce_to_known_np",
        "reduce_to_known_hardness",
        "prove_in_np",
        "prove_np_complete",
    }
)
STAGE_P_DIRECTIONS = frozenset({"source_to_target"})


def _require_nonempty(value: str, *, label: str) -> None:
    if not isinstance(value, str) or not value.strip():
        raise StagePContractError("invalid_stage_p_patch_schema", f"{label} is empty")


def _require_hash(value: str, *, code: str, label: str) -> None:
    if not isinstance(value, str) or not SHA256_RE.fullmatch(value):
        raise StagePContractError(code, f"{label} is not a content hash")


@dataclass(frozen=True)
class StagePImmutableRequest:
    """Exact request binding that cannot change during an authoring session."""

    source_declaration: str
    target_declaration: str
    source_endpoint_id: str
    target_endpoint_id: str
    objective: str
    direction: str
    request_policy_sha256: str
    resolved_parameters_sha256: str
    base_registry_fingerprint: str
    max_gap_count: int
    schema_version: str = STAGE_P_REQUEST_SCHEMA

    def validate(self) -> None:
        if self.schema_version != STAGE_P_REQUEST_SCHEMA:
            raise StagePContractError(
                "request_or_endpoint_mutation", "unsupported Stage P request schema"
            )
        for label, value in {
            "source_declaration": self.source_declaration,
            "target_declaration": self.target_declaration,
        }.items():
            _require_nonempty(value, label=label)
        for label, value in {
            "source_endpoint_id": self.source_endpoint_id,
            "target_endpoint_id": self.target_endpoint_id,
            "request_policy_sha256": self.request_policy_sha256,
            "resolved_parameters_sha256": self.resolved_parameters_sha256,
            "base_registry_fingerprint": self.base_registry_fingerprint,
        }.items():
            _require_hash(value, code="request_or_endpoint_mutation", label=label)
        if self.objective not in STAGE_P_OBJECTIVES:
            raise StagePContractError(
                "request_or_endpoint_mutation", "request objective is outside Stage P"
            )
        if self.direction not in STAGE_P_DIRECTIONS:
            raise StagePContractError(
                "request_or_endpoint_mutation", "request direction is outside Stage P"
            )
        if isinstance(self.max_gap_count, bool) or not 1 <= self.max_gap_count <= STAGE_P_MAX_GAPS:
            raise StagePContractError(
                "gap_count_exceeded", "Stage P requests must freeze a one-to-four gap bound"
            )

    @property
    def request_id(self) -> str:
        self.validate()
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})

    @property
    def initial_checkpoint_hash(self) -> str:
        return sha256_id(
            {
                "schema_version": "hardness_stage_p_initial_checkpoint_v1",
                "request_id": self.request_id,
                "base_registry_fingerprint": self.base_registry_fingerprint,
                "request_policy_sha256": self.request_policy_sha256,
                "resolved_parameters_sha256": self.resolved_parameters_sha256,
            }
        )

    def assert_same(self, other: "StagePImmutableRequest") -> None:
        self.validate()
        other.validate()
        if self != other:
            raise StagePContractError(
                "request_or_endpoint_mutation",
                "request, endpoint, direction, objective, parameter, or policy binding changed",
            )


@dataclass(frozen=True)
class StagePRuntimeGap:
    """A single typed gap revealed by a fresh Core resolver invocation."""

    request_id: str
    ordinal: int
    task_class: str
    capability_head: str
    declaration_signature: str
    source_endpoint_id: str
    target_endpoint_id: str
    registry_fingerprint: str
    dependency_hash: str
    parent_checkpoint_hash: str
    public_preconditions: tuple[str, ...] = ()
    schema_version: str = STAGE_P_RUNTIME_GAP_SCHEMA

    def validate(self, request: StagePImmutableRequest) -> None:
        request.validate()
        if self.schema_version != STAGE_P_RUNTIME_GAP_SCHEMA or self.request_id != request.request_id:
            raise StagePContractError("request_or_endpoint_mutation", "gap belongs to another request")
        if isinstance(self.ordinal, bool) or not 1 <= self.ordinal <= STAGE_P_MAX_GAPS:
            raise StagePContractError("gap_count_exceeded", "gap ordinal is outside one-to-four")
        if self.ordinal > request.max_gap_count:
            raise StagePContractError("gap_count_exceeded", "gap exceeds the frozen request bound")
        if self.task_class not in TASK_CLASSES:
            raise StagePContractError("fresh_core_resolve_failed", "Core revealed an unknown task class")
        if self.capability_head not in CAPABILITY_HEADS:
            raise StagePContractError(
                "candidate_canonical_head_mismatch", "Core revealed an unsupported capability head"
            )
        _require_nonempty(self.declaration_signature, label="declaration_signature")
        if (
            self.source_endpoint_id != request.source_endpoint_id
            or self.target_endpoint_id != request.target_endpoint_id
        ):
            raise StagePContractError(
                "request_or_endpoint_mutation", "gap endpoint IDs differ from the immutable request"
            )
        for label, value in {
            "registry_fingerprint": self.registry_fingerprint,
            "dependency_hash": self.dependency_hash,
            "parent_checkpoint_hash": self.parent_checkpoint_hash,
            **{
                f"public_preconditions[{index}]": precondition
                for index, precondition in enumerate(self.public_preconditions)
            },
        }.items():
            _require_hash(value, code="candidate_dependency_stale", label=label)
        if len(set(self.public_preconditions)) != len(self.public_preconditions):
            raise StagePContractError(
                "candidate_dependency_stale", "gap public preconditions contain duplicates"
            )

    @property
    def gap_id(self) -> str:
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})


@dataclass(frozen=True)
class StagePGapCheckpoint:
    """Content-addressed evidence for one validated or published gap."""

    request_id: str
    gap_id: str
    ordinal: int
    task_class: str
    registry_fingerprint: str
    dependency_hash: str
    parent_checkpoint_hash: str
    model_response_sha256: str
    patch_sha256: str
    candidate_source_sha256: str
    diagnostics_sha256: str
    bundle_sha256: str
    axiom_audit_sha256: str
    publication_hash: str | None = None
    schema_version: str = STAGE_P_CHECKPOINT_SCHEMA

    def validate(self) -> None:
        if self.schema_version != STAGE_P_CHECKPOINT_SCHEMA:
            raise StagePContractError("candidate_dependency_stale", "checkpoint schema drifted")
        if isinstance(self.ordinal, bool) or not 1 <= self.ordinal <= STAGE_P_MAX_GAPS:
            raise StagePContractError("gap_count_exceeded", "checkpoint ordinal is outside one-to-four")
        if self.task_class not in TASK_CLASSES:
            raise StagePContractError("candidate_dependency_stale", "checkpoint task class drifted")
        for label, value in {
            "request_id": self.request_id,
            "gap_id": self.gap_id,
            "registry_fingerprint": self.registry_fingerprint,
            "dependency_hash": self.dependency_hash,
            "parent_checkpoint_hash": self.parent_checkpoint_hash,
            "model_response_sha256": self.model_response_sha256,
            "patch_sha256": self.patch_sha256,
            "candidate_source_sha256": self.candidate_source_sha256,
            "diagnostics_sha256": self.diagnostics_sha256,
            "bundle_sha256": self.bundle_sha256,
            "axiom_audit_sha256": self.axiom_audit_sha256,
        }.items():
            _require_hash(value, code="candidate_dependency_stale", label=label)
        if self.publication_hash is not None:
            _require_hash(
                self.publication_hash,
                code="capability_publication_failed",
                label="publication_hash",
            )

    @property
    def checkpoint_hash(self) -> str:
        self.validate()
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})

    @property
    def published(self) -> bool:
        return self.publication_hash is not None


@dataclass
class StagePSequentialAuthoringSession:
    """Generic single-active-gap Stage P state machine."""

    request: StagePImmutableRequest
    max_semantic_turns_per_gap: int = STAGE_P_MAX_SEMANTIC_TURNS_PER_GAP
    max_total_tokens: int | None = None
    max_transport_retries: int | None = None
    state: str = field(default="CORE_BASELINE_BLOCKED", init=False)
    pending_gap: StagePRuntimeGap | None = field(default=None, init=False)
    active_gap: StagePRuntimeGap | None = field(default=None, init=False)
    candidate_checkpoint: StagePGapCheckpoint | None = field(default=None, init=False)
    checkpoints: list[StagePGapCheckpoint] = field(default_factory=list, init=False)
    seen_gap_ids: set[str] = field(default_factory=set, init=False)
    seen_task_classes: set[str] = field(default_factory=set, init=False)
    seen_dependency_hashes: set[str] = field(default_factory=set, init=False)
    semantic_turns: dict[int, int] = field(default_factory=dict, init=False)
    semantic_model_call_count: int = field(default=0, init=False)
    total_tokens: int = field(default=0, init=False)
    http_attempt_count: int = field(default=0, init=False)
    transport_retry_count: int = field(default=0, init=False)
    candidate_attempts: dict[int, int] = field(default_factory=dict, init=False)
    fresh_core_resolve_count: int = field(default=0, init=False)
    events: list[dict[str, Any]] = field(default_factory=list, init=False)
    final_axiom_audit_sha256: str | None = field(default=None, init=False)

    def __post_init__(self) -> None:
        self.request.validate()
        if (
            isinstance(self.max_semantic_turns_per_gap, bool)
            or not 1 <= self.max_semantic_turns_per_gap <= STAGE_P_MAX_SEMANTIC_TURNS_PER_GAP
        ):
            raise StagePContractError(
                "authoring_budget_exhausted", "per-gap semantic turn bound must be between one and four"
            )
        if self.max_total_tokens is None:
            self.max_total_tokens = self.request.max_gap_count * STAGE_P_TOKENS_PER_GAP
        if isinstance(self.max_total_tokens, bool) or self.max_total_tokens <= 0:
            raise StagePContractError("authoring_budget_exhausted", "token budget must be positive")
        if self.max_transport_retries is None:
            self.max_transport_retries = (
                self.request.max_gap_count
                * self.max_semantic_turns_per_gap
                * STAGE_P_MAX_TRANSPORT_RETRIES_PER_SEMANTIC_TURN
            )
        if isinstance(self.max_transport_retries, bool) or self.max_transport_retries < 0:
            raise StagePContractError(
                "authoring_budget_exhausted", "transport retry budget must be non-negative"
            )
        self._event("CORE_BASELINE_BLOCKED")

    @property
    def expected_parent_checkpoint_hash(self) -> str:
        if not self.checkpoints:
            return self.request.initial_checkpoint_hash
        checkpoint = self.checkpoints[-1]
        if not checkpoint.published:
            raise StagePContractError(
                "capability_publication_failed", "latest checkpoint was not published"
            )
        return checkpoint.checkpoint_hash

    @property
    def complete(self) -> bool:
        return self.state == "RELEASE_REPLAY"

    def _event(self, state: str, **details: Any) -> None:
        self.events.append(
            {
                "sequence": len(self.events) + 1,
                "state": state,
                **details,
            }
        )

    def _assert_state(self, *allowed: str) -> None:
        if self.state not in allowed:
            raise StagePContractError(
                "gap_sequence_cycle",
                f"operation is invalid in state {self.state}; expected one of {allowed}",
            )

    def _validate_new_gap(self, gap: StagePRuntimeGap, *, expected_ordinal: int) -> None:
        gap.validate(self.request)
        if gap.ordinal != expected_ordinal:
            if gap.ordinal > STAGE_P_MAX_GAPS or gap.ordinal > self.request.max_gap_count:
                raise StagePContractError("gap_count_exceeded", "fresh Core revealed too many gaps")
            raise StagePContractError("gap_sequence_cycle", "fresh Core revealed a gap out of order")
        if gap.parent_checkpoint_hash != self.expected_parent_checkpoint_hash:
            raise StagePContractError(
                "candidate_dependency_stale", "gap parent checkpoint does not match published state"
            )
        if gap.gap_id in self.seen_gap_ids:
            raise StagePContractError("gap_sequence_cycle", "fresh Core repeated a stable gap ID")
        if gap.task_class in self.seen_task_classes:
            raise StagePContractError("gap_sequence_cycle", "fresh Core repeated a task class")
        if gap.dependency_hash in self.seen_dependency_hashes:
            raise StagePContractError("gap_sequence_cycle", "fresh Core repeated dependency state")
        if self.checkpoints and gap.registry_fingerprint == self.checkpoints[-1].registry_fingerprint:
            raise StagePContractError(
                "published_capability_not_visible",
                "fresh Core registry fingerprint did not change after publication",
            )

    def begin_gap(self, gap: StagePRuntimeGap) -> None:
        self._assert_state("CORE_BASELINE_BLOCKED", "CORE_BLOCKED")
        if self.active_gap is not None or self.candidate_checkpoint is not None:
            raise StagePContractError("gap_sequence_cycle", "two authoring gaps became active")
        expected_ordinal = len(self.checkpoints) + 1
        if self.pending_gap is not None and gap != self.pending_gap:
            raise StagePContractError(
                "request_or_endpoint_mutation", "authoring did not start the exact Core-revealed gap"
            )
        self._validate_new_gap(gap, expected_ordinal=expected_ordinal)
        self.pending_gap = None
        self.active_gap = gap
        self.seen_gap_ids.add(gap.gap_id)
        self.seen_task_classes.add(gap.task_class)
        self.seen_dependency_hashes.add(gap.dependency_hash)
        self.semantic_turns.setdefault(gap.ordinal, 0)
        self.candidate_attempts.setdefault(gap.ordinal, 0)
        self.state = "AUTHORING_STARTED"
        self._event(
            self.state,
            gap_id=gap.gap_id,
            gap_ordinal=gap.ordinal,
            task_class=gap.task_class,
            parent_checkpoint_hash=gap.parent_checkpoint_hash,
        )

    def record_transport_attempt(self, *, retry: bool) -> None:
        self._assert_state("AUTHORING_STARTED")
        self.http_attempt_count += 1
        if retry:
            if self.transport_retry_count + 1 > int(self.max_transport_retries):
                raise StagePContractError(
                    "authoring_budget_exhausted", "transport retry budget exhausted"
                )
            self.transport_retry_count += 1
        self._event(
            "MODEL_TRANSPORT_ATTEMPT",
            gap_id=self.active_gap.gap_id if self.active_gap else None,
            retry=retry,
            http_attempt_count=self.http_attempt_count,
            transport_retry_count=self.transport_retry_count,
        )

    def record_model_turn(self, *, token_count: int) -> None:
        self._assert_state("AUTHORING_STARTED")
        gap = self.active_gap
        if gap is None:
            raise StagePContractError("gap_sequence_cycle", "model turn has no active gap")
        if isinstance(token_count, bool) or token_count < 0:
            raise StagePContractError("authoring_budget_exhausted", "model token count is invalid")
        turns = self.semantic_turns[gap.ordinal] + 1
        if turns > self.max_semantic_turns_per_gap:
            raise StagePContractError(
                "authoring_budget_exhausted", "semantic model-turn budget exhausted for active gap"
            )
        if self.total_tokens + token_count > int(self.max_total_tokens):
            raise StagePContractError("authoring_budget_exhausted", "Stage P token budget exhausted")
        self.semantic_turns[gap.ordinal] = turns
        self.semantic_model_call_count += 1
        self.total_tokens += token_count
        self._event(
            "MODEL_SEMANTIC_TURN",
            gap_id=gap.gap_id,
            gap_ordinal=gap.ordinal,
            semantic_turn=turns,
            token_count=token_count,
        )

    def record_candidate_attempt(self) -> None:
        self._assert_state("AUTHORING_STARTED")
        gap = self.active_gap
        if gap is None:
            raise StagePContractError("gap_sequence_cycle", "candidate attempt has no active gap")
        attempts = self.candidate_attempts[gap.ordinal] + 1
        if attempts > self.max_semantic_turns_per_gap:
            raise StagePContractError(
                "authoring_budget_exhausted", "candidate-attempt budget exhausted for active gap"
            )
        self.candidate_attempts[gap.ordinal] = attempts

    def validate_candidate(
        self,
        *,
        model_response_sha256: str,
        patch_sha256: str,
        candidate_source_sha256: str,
        diagnostics_sha256: str,
        bundle_sha256: str,
        axiom_audit_sha256: str,
    ) -> StagePGapCheckpoint:
        self._assert_state("AUTHORING_STARTED")
        gap = self.active_gap
        if gap is None:
            raise StagePContractError("gap_sequence_cycle", "candidate validation has no active gap")
        if self.candidate_attempts[gap.ordinal] == 0:
            raise StagePContractError(
                "candidate_lean_compile_failed", "candidate validation was not preceded by an attempt"
            )
        checkpoint = StagePGapCheckpoint(
            request_id=self.request.request_id,
            gap_id=gap.gap_id,
            ordinal=gap.ordinal,
            task_class=gap.task_class,
            registry_fingerprint=gap.registry_fingerprint,
            dependency_hash=gap.dependency_hash,
            parent_checkpoint_hash=gap.parent_checkpoint_hash,
            model_response_sha256=model_response_sha256,
            patch_sha256=patch_sha256,
            candidate_source_sha256=candidate_source_sha256,
            diagnostics_sha256=diagnostics_sha256,
            bundle_sha256=bundle_sha256,
            axiom_audit_sha256=axiom_audit_sha256,
        )
        checkpoint.validate()
        self.candidate_checkpoint = checkpoint
        self.state = "CANDIDATE_LEAN_VALIDATED"
        self._event(
            self.state,
            gap_id=gap.gap_id,
            gap_ordinal=gap.ordinal,
            candidate_source_sha256=candidate_source_sha256,
            bundle_sha256=bundle_sha256,
        )
        return checkpoint

    def publish_active(self, *, publication_hash: str) -> StagePGapCheckpoint:
        self._assert_state("CANDIDATE_LEAN_VALIDATED")
        gap = self.active_gap
        checkpoint = self.candidate_checkpoint
        if gap is None or checkpoint is None:
            raise StagePContractError(
                "capability_publication_failed", "publication has no validated candidate"
            )
        _require_hash(
            publication_hash,
            code="capability_publication_failed",
            label="publication_hash",
        )
        published = replace(checkpoint, publication_hash=publication_hash)
        published.validate()
        self.checkpoints.append(published)
        self.active_gap = None
        self.candidate_checkpoint = None
        self.state = "CAPABILITY_CASE_LOCAL_PUBLISHED"
        self._event(
            self.state,
            gap_id=gap.gap_id,
            gap_ordinal=gap.ordinal,
            publication_hash=publication_hash,
            checkpoint_hash=published.checkpoint_hash,
        )
        return published

    def record_fresh_core_resolution(
        self,
        *,
        verified: bool,
        next_gap: StagePRuntimeGap | None = None,
    ) -> None:
        self._assert_state("CAPABILITY_CASE_LOCAL_PUBLISHED")
        current = self.checkpoints[-1]
        self.fresh_core_resolve_count += 1
        self._event(
            "FRESH_CORE_RESOLVE",
            completed_gap_id=current.gap_id,
            completed_gap_ordinal=current.ordinal,
            verified=verified,
        )
        if verified:
            if next_gap is not None:
                raise StagePContractError(
                    "fresh_core_resolve_failed", "Core returned VERIFIED and another active gap"
                )
            self.state = "CORE_VERIFIED"
            self._event(self.state, gap_count=len(self.checkpoints))
            return
        if next_gap is None:
            raise StagePContractError(
                "fresh_core_resolve_failed", "blocked Core result omitted the next typed gap"
            )
        expected_ordinal = len(self.checkpoints) + 1
        if expected_ordinal > self.request.max_gap_count or expected_ordinal > STAGE_P_MAX_GAPS:
            raise StagePContractError("gap_count_exceeded", "fresh Core requested a fifth/excess gap")
        self._validate_new_gap(next_gap, expected_ordinal=expected_ordinal)
        self.pending_gap = next_gap
        self.state = "CORE_BLOCKED"
        self._event(
            self.state,
            gap_id=next_gap.gap_id,
            gap_ordinal=next_gap.ordinal,
            task_class=next_gap.task_class,
        )

    def record_final_combined_lean(self, *, verified: bool) -> None:
        self._assert_state("CORE_VERIFIED")
        if not verified:
            raise StagePContractError("final_lean_failed", "final combined Lean failed")
        self.state = "FINAL_COMBINED_LEAN"
        self._event(self.state)

    def record_standard_axiom_audit(self, *, verified: bool, audit_sha256: str) -> None:
        self._assert_state("FINAL_COMBINED_LEAN")
        if not verified:
            raise StagePContractError(
                "sorry_axiom_or_unsafe_candidate", "standard-axiom audit failed"
            )
        _require_hash(
            audit_sha256,
            code="sorry_axiom_or_unsafe_candidate",
            label="final_axiom_audit_sha256",
        )
        self.final_axiom_audit_sha256 = audit_sha256
        self.state = "STANDARD_AXIOM_AUDIT"
        self._event(self.state, audit_sha256=audit_sha256)

    def record_release_replay(self, *, verified: bool) -> None:
        self._assert_state("STANDARD_AXIOM_AUDIT")
        if not verified:
            raise StagePContractError("release_replay_failed", "independent release replay failed")
        self.state = "RELEASE_REPLAY"
        self._event(self.state)

    def to_dict(self) -> dict[str, Any]:
        payload = {
            "schema_version": STAGE_P_RUNTIME_TRACE_SCHEMA,
            "request_id": self.request.request_id,
            "state": self.state,
            "complete": self.complete,
            "active_gap_id": self.active_gap.gap_id if self.active_gap else None,
            "pending_gap_id": self.pending_gap.gap_id if self.pending_gap else None,
            "semantic_model_call_count": self.semantic_model_call_count,
            "semantic_turns": {
                str(ordinal): count for ordinal, count in sorted(self.semantic_turns.items())
            },
            "total_tokens": self.total_tokens,
            "http_attempt_count": self.http_attempt_count,
            "transport_retry_count": self.transport_retry_count,
            "candidate_attempts": {
                str(ordinal): count for ordinal, count in sorted(self.candidate_attempts.items())
            },
            "fresh_core_resolve_count": self.fresh_core_resolve_count,
            "final_axiom_audit_sha256": self.final_axiom_audit_sha256,
            "events": list(self.events),
            "checkpoints": [
                {**asdict(checkpoint), "checkpoint_hash": checkpoint.checkpoint_hash}
                for checkpoint in self.checkpoints
            ],
        }
        return {**payload, "trace_sha256": sha256_id(payload)}
