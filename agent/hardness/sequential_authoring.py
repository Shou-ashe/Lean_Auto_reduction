"""Strict single-active-node sequential authoring for Stage O.

This module owns only orchestration state.  It never manufactures a Lean
capability: every accepted candidate still has to pass the local bundle,
final-combined-Lean, axiom-gate, and release-replay layers.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from typing import Any

from .models import sha256_id
from .stage_o_contract import (
    SHA256_RE,
    SequentialAuthoringTrace,
    StageOContractError,
    stable_gap_id,
)


STAGE_O_REQUEST_SCHEMA = "hardness_stage_o_immutable_request_v1"
STAGE_O_GAP_SCHEMA = "hardness_stage_o_runtime_gap_v1"
STAGE_O_CHECKPOINT_SCHEMA = "hardness_stage_o_gap_checkpoint_v1"


@dataclass(frozen=True)
class ImmutableStageORequest:
    input_declaration: str
    input_kind: str
    objective: str
    target_declaration: str | None
    capability_head: str
    schema_version: str = STAGE_O_REQUEST_SCHEMA

    @property
    def request_id(self) -> str:
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})

    def assert_same(self, other: "ImmutableStageORequest") -> None:
        if self != other:
            raise StageOContractError(
                "gap_sequence_mismatch",
                "request, endpoint, objective, or capability head changed during authoring",
            )


@dataclass(frozen=True)
class RuntimeGap:
    request_id: str
    ordinal: int
    registry_fingerprint: str
    source_endpoint_id: str
    target_endpoint_id: str
    capability_head: str
    dependency_hash: str
    public_preconditions: tuple[str, ...] = ()
    schema_version: str = STAGE_O_GAP_SCHEMA

    @property
    def gap_id(self) -> str:
        return stable_gap_id(
            request_id=self.request_id,
            ordinal=self.ordinal,
            registry_fingerprint=self.registry_fingerprint,
            source_endpoint_id=self.source_endpoint_id,
            target_endpoint_id=self.target_endpoint_id,
            capability_head=self.capability_head,
            dependency_hash=self.dependency_hash,
        )

    def validate(self, request: ImmutableStageORequest) -> None:
        if self.schema_version != STAGE_O_GAP_SCHEMA or self.request_id != request.request_id:
            raise StageOContractError("gap_sequence_mismatch", "gap belongs to another request")
        if self.ordinal not in {1, 2}:
            raise StageOContractError("gap_sequence_mismatch", "only gap ordinals 1 and 2 exist")
        for value in (
            self.registry_fingerprint,
            self.source_endpoint_id,
            self.target_endpoint_id,
            self.dependency_hash,
        ):
            if not SHA256_RE.fullmatch(value):
                raise StageOContractError("gap_sequence_mismatch", "gap omits a stable content ID")
        if not self.capability_head:
            raise StageOContractError("gap_sequence_mismatch", "gap capability head is empty")


@dataclass(frozen=True)
class GapCheckpoint:
    request_id: str
    gap_id: str
    ordinal: int
    registry_fingerprint: str
    dependency_hash: str
    candidate_hash: str
    bundle_hash: str
    publication_hash: str | None
    previous_checkpoint_hash: str | None
    schema_version: str = STAGE_O_CHECKPOINT_SCHEMA

    @property
    def checkpoint_hash(self) -> str:
        self.validate()
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})

    def validate(self) -> None:
        if self.schema_version != STAGE_O_CHECKPOINT_SCHEMA or self.ordinal not in {1, 2}:
            raise StageOContractError("stale_gap_dependency", "invalid gap checkpoint schema")
        required = (
            self.request_id,
            self.gap_id,
            self.registry_fingerprint,
            self.dependency_hash,
            self.candidate_hash,
            self.bundle_hash,
        )
        optional = (self.publication_hash, self.previous_checkpoint_hash)
        if not all(SHA256_RE.fullmatch(value) for value in required):
            raise StageOContractError("stale_gap_dependency", "checkpoint omits a content hash")
        if any(value is not None and not SHA256_RE.fullmatch(value) for value in optional):
            raise StageOContractError("stale_gap_dependency", "checkpoint has a malformed parent hash")


@dataclass
class SequentialAuthoringSession:
    request: ImmutableStageORequest
    max_model_calls: int = 8
    max_total_tokens: int = 60_000
    max_candidate_attempts_per_gap: int = 3
    trace: SequentialAuthoringTrace = field(init=False)
    active_gap: RuntimeGap | None = field(default=None, init=False)
    checkpoints: list[GapCheckpoint] = field(default_factory=list, init=False)
    model_calls: int = field(default=0, init=False)
    total_tokens: int = field(default=0, init=False)
    candidate_attempts: dict[int, int] = field(default_factory=dict, init=False)
    fresh_core_resolve_count: int = field(default=0, init=False)

    def __post_init__(self) -> None:
        self.trace = SequentialAuthoringTrace(request_id=self.request.request_id)

    def record_model_call(self, *, token_count: int) -> None:
        if token_count < 0:
            raise StageOContractError("sequential_gap_budget_exhausted", "negative token count")
        if self.model_calls + 1 > self.max_model_calls:
            raise StageOContractError(
                "sequential_gap_budget_exhausted", "sequential authoring model-call budget exhausted"
            )
        if self.total_tokens + token_count > self.max_total_tokens:
            raise StageOContractError(
                "sequential_gap_budget_exhausted", "sequential authoring token budget exhausted"
            )
        self.model_calls += 1
        self.total_tokens += token_count

    def begin_gap(self, gap: RuntimeGap) -> None:
        gap.validate(self.request)
        if self.active_gap is not None:
            raise StageOContractError("gap_sequence_mismatch", "two authoring nodes became active")
        expected_ordinal = 1 if self.trace.states[-1] == "CORE_BASELINE_BLOCKED" else 2
        if gap.ordinal != expected_ordinal:
            raise StageOContractError("gap_sequence_mismatch", "Core revealed a gap out of order")
        next_state = "AUTHORING_GAP_1" if gap.ordinal == 1 else "AUTHORING_GAP_2"
        self.trace = self.trace.advance(next_state, gap_id=gap.gap_id)
        self.active_gap = gap
        self.candidate_attempts.setdefault(gap.ordinal, 0)

    def attempt_candidate(self) -> None:
        if self.active_gap is None:
            raise StageOContractError("gap_sequence_mismatch", "candidate attempt has no active gap")
        ordinal = self.active_gap.ordinal
        attempts = self.candidate_attempts.get(ordinal, 0) + 1
        if attempts > self.max_candidate_attempts_per_gap:
            raise StageOContractError(
                "sequential_gap_budget_exhausted", "candidate-attempt budget exhausted for active gap"
            )
        self.candidate_attempts[ordinal] = attempts

    def validate_active_bundle(self, *, candidate_hash: str, bundle_hash: str) -> GapCheckpoint:
        gap = self.active_gap
        if gap is None:
            raise StageOContractError("gap_sequence_mismatch", "bundle validation has no active gap")
        if not SHA256_RE.fullmatch(candidate_hash) or not SHA256_RE.fullmatch(bundle_hash):
            raise StageOContractError("stale_gap_dependency", "bundle is not content addressed")
        next_state = "GAP_1_BUNDLE_VALIDATED" if gap.ordinal == 1 else "GAP_2_BUNDLE_VALIDATED"
        self.trace = self.trace.advance(next_state)
        checkpoint = GapCheckpoint(
            request_id=self.request.request_id,
            gap_id=gap.gap_id,
            ordinal=gap.ordinal,
            registry_fingerprint=gap.registry_fingerprint,
            dependency_hash=gap.dependency_hash,
            candidate_hash=candidate_hash,
            bundle_hash=bundle_hash,
            publication_hash=None,
            previous_checkpoint_hash=(self.checkpoints[-1].checkpoint_hash if self.checkpoints else None),
        )
        checkpoint.validate()
        self.checkpoints.append(checkpoint)
        self.active_gap = None
        return checkpoint

    def publish_gap_one(self, *, publication_hash: str) -> GapCheckpoint:
        if self.trace.states[-1] != "GAP_1_BUNDLE_VALIDATED" or len(self.checkpoints) != 1:
            raise StageOContractError("gap_sequence_mismatch", "gap 1 cannot be published now")
        if not SHA256_RE.fullmatch(publication_hash):
            raise StageOContractError("stale_gap_dependency", "gap 1 publication lacks a hash")
        current = self.checkpoints[0]
        published = GapCheckpoint(
            **{
                **asdict(current),
                "publication_hash": publication_hash,
            }
        )
        published.validate()
        self.checkpoints[0] = published
        self.trace = self.trace.advance("GAP_1_CASE_LOCAL_PUBLISHED")
        return published

    def resolve_after_gap_one(self, next_gap: RuntimeGap | None) -> None:
        if self.trace.states[-1] != "GAP_1_CASE_LOCAL_PUBLISHED":
            raise StageOContractError("gap_sequence_mismatch", "fresh Core resolve 1 is out of order")
        self.trace = self.trace.advance("FRESH_CORE_RESOLVE_1")
        self.fresh_core_resolve_count += 1
        if next_gap is None:
            raise StageOContractError("second_gap_not_revealed", "gap 1 did not reveal a second gap")
        next_gap.validate(self.request)
        if next_gap.ordinal != 2 or next_gap.gap_id == self.checkpoints[0].gap_id:
            raise StageOContractError("gap_sequence_mismatch", "fresh Core returned an invalid gap 2")
        self.trace = self.trace.advance("CORE_BLOCKED_GAP_2")

    def resolve_after_gap_two(self, *, verified: bool) -> None:
        if self.trace.states[-1] != "GAP_2_BUNDLE_VALIDATED":
            raise StageOContractError("gap_sequence_mismatch", "fresh Core resolve 2 is out of order")
        if len(self.checkpoints) != 2:
            raise StageOContractError("gap_sequence_mismatch", "gap 2 has no independent checkpoint")
        self.trace = self.trace.advance("FRESH_CORE_RESOLVE_2")
        self.fresh_core_resolve_count += 1
        if not verified:
            raise StageOContractError("packet_precondition_unsatisfied", "Core remains blocked after gap 2")
        self.trace = self.trace.advance("CORE_VERIFIED")

    def record_final_combined_lean(self, *, verified: bool) -> None:
        if not verified:
            raise StageOContractError("final_lean_failed", "final combined Lean failed")
        self.trace = self.trace.advance("FINAL_COMBINED_LEAN")

    def record_release_replay(self, *, verified: bool) -> None:
        if not verified:
            raise StageOContractError("release_replay_failed", "independent release replay failed")
        self.trace = self.trace.advance("RELEASE_REPLAY")

    def validate_gap_two_checkpoint(self, checkpoint: GapCheckpoint) -> None:
        if not self.checkpoints:
            raise StageOContractError("stale_gap_dependency", "gap 1 checkpoint is missing")
        parent = self.checkpoints[0]
        if checkpoint.ordinal != 2 or checkpoint.previous_checkpoint_hash != parent.checkpoint_hash:
            raise StageOContractError("stale_gap_dependency", "gap 2 checkpoint has a stale parent")
        checkpoint.validate()

    def to_dict(self) -> dict[str, Any]:
        return {
            "request_id": self.request.request_id,
            "states": list(self.trace.states),
            "gap_ids": list(self.trace.gap_ids),
            "active_gap_id": self.active_gap.gap_id if self.active_gap else None,
            "model_calls": self.model_calls,
            "total_tokens": self.total_tokens,
            "candidate_attempts": {str(key): value for key, value in self.candidate_attempts.items()},
            "fresh_core_resolve_count": self.fresh_core_resolve_count,
            "checkpoints": [
                {**asdict(checkpoint), "checkpoint_hash": checkpoint.checkpoint_hash}
                for checkpoint in self.checkpoints
            ],
            "complete": self.trace.complete,
        }
