"""Deterministic hardness-hub enumeration, ranking, and switching.

The selector consumes only Lean-observed native-hardness seeds plus a frozen
gap-analysis profile.  It never asks a model to choose a seed, endpoint, or
direction.  Candidate order is normalized before request hashing, and the
ranking key is exactly the G-D tuple from the active plan.
"""

from __future__ import annotations

import re
from dataclasses import asdict, dataclass
from typing import Any, Iterable, Mapping, Protocol

from .models import sha256_id


NP_HARD_HUB_CANDIDATE_SCHEMA_V1 = "hardness_np_hard_hub_candidate_v1"
NP_HARD_HUB_SELECTION_REQUEST_SCHEMA_V1 = "hardness_np_hard_hub_selection_request_v1"
NP_HARD_HUB_SELECTION_RESULT_SCHEMA_V1 = "hardness_np_hard_hub_selection_result_v1"
NP_HARD_HUB_ATTEMPT_REQUEST_SCHEMA_V1 = "hardness_np_hard_hub_attempt_request_v1"
NP_HARD_HUB_SWITCH_TRACE_SCHEMA_V1 = "hardness_np_hard_hub_switch_trace_v1"
NP_HARD_HUB_DIRECTION = "hardness_seed_to_problem"

NP_HARD_GAP_RISK_RANK = {
    "none": 0,
    "semantic-proof": 1,
    "program-composition": 2,
    "program-synthesis": 3,
    "unsupported": 4,
}
NP_HARD_HUB_ELIGIBILITY = {
    "existing_route",
    "authorable_gap",
    "reverse_only",
    "unsupported",
}
NP_HARD_HUB_CANDIDATE_FAILURES = {
    "program_synthesis_failed",
    "semantic_proof_failed",
    "candidate_wrong_direction",
    "candidate_wrong_endpoint",
    "candidate_nonstandard_axiom",
    "candidate_outside_edit_boundary",
    "candidate_dependency_stale",
    "fresh_core_resolve_failed",
    "lean_infrastructure_error",
}
_HASH_RE = re.compile(r"sha256:[0-9a-f]{64}\Z")


class NPHardHubSelectionError(ValueError):
    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _fail(code: str, message: str) -> None:
    raise NPHardHubSelectionError(code, message)


class NPHardSeedLike(Protocol):
    problem_declaration: str
    evidence_declaration: str
    evidence_kind: str
    registry_fingerprint: str

    @property
    def entry_id(self) -> str: ...


@dataclass(frozen=True)
class NPHardHubCandidateV1:
    stable_seed_id: str
    seed_problem: str
    seed_evidence: str
    seed_evidence_kind: str
    target_problem: str
    registry_fingerprint: str
    eligibility: str
    unresolved_gap_count: int
    gap_risk: str
    existing_route_length: int
    representation_adapter_count: int
    estimated_authoring_nodes: int
    task_class: str | None
    direction: str = NP_HARD_HUB_DIRECTION
    schema_version: str = NP_HARD_HUB_CANDIDATE_SCHEMA_V1

    @property
    def candidate_id(self) -> str:
        return sha256_id({"schema_version": self.schema_version, **asdict(self)})

    @property
    def ranking_key(self) -> tuple[int, int, int, int, int, str]:
        self.validate()
        return (
            self.unresolved_gap_count,
            NP_HARD_GAP_RISK_RANK[self.gap_risk],
            self.existing_route_length,
            self.representation_adapter_count,
            self.estimated_authoring_nodes,
            self.stable_seed_id,
        )

    def validate(self) -> None:
        if self.schema_version != NP_HARD_HUB_CANDIDATE_SCHEMA_V1:
            _fail("invalid_hardness_hub_candidate", "unsupported candidate schema")
        if not _HASH_RE.fullmatch(self.stable_seed_id):
            _fail("fabricated_hardness_seed", "candidate seed ID is not content addressed")
        if not self.seed_problem or not self.seed_evidence or not self.target_problem:
            _fail("fabricated_hardness_seed", "candidate omits an exact Lean declaration")
        if self.seed_evidence_kind not in {
            "native_hardness",
            "native_completeness_projection",
        }:
            _fail("fabricated_hardness_seed", "candidate has no native hardness evidence")
        if not self.registry_fingerprint.startswith("lean:"):
            _fail("candidate_dependency_stale", "candidate registry fingerprint is invalid")
        if self.direction != NP_HARD_HUB_DIRECTION:
            _fail("candidate_wrong_direction", "candidate reversed the NP-hard reduction")
        if self.eligibility not in NP_HARD_HUB_ELIGIBILITY:
            _fail("invalid_hardness_hub_candidate", "candidate eligibility is invalid")
        if self.gap_risk not in NP_HARD_GAP_RISK_RANK:
            _fail("invalid_hardness_hub_candidate", "candidate gap risk is invalid")
        values = (
            self.unresolved_gap_count,
            self.existing_route_length,
            self.representation_adapter_count,
            self.estimated_authoring_nodes,
        )
        if any(isinstance(value, bool) or value < 0 for value in values):
            _fail("invalid_hardness_hub_candidate", "candidate metrics must be nonnegative")
        if self.eligibility == "existing_route" and (
            self.unresolved_gap_count != 0
            or self.gap_risk != "none"
            or self.estimated_authoring_nodes != 0
        ):
            _fail("invalid_hardness_hub_candidate", "existing route declares authoring work")
        if self.eligibility == "authorable_gap" and (
            self.unresolved_gap_count == 0
            or self.gap_risk in {"none", "unsupported"}
            or self.estimated_authoring_nodes == 0
            or self.task_class is None
        ):
            _fail("invalid_hardness_hub_candidate", "authorable candidate lacks a valid gap")
        if self.task_class is not None and self.task_class not in {
            "semantic_proof",
            "program_composition",
            "program_synthesis",
        }:
            _fail("invalid_hardness_hub_candidate", "candidate task class is invalid")

    def to_dict(self) -> dict[str, Any]:
        self.validate()
        return {
            **asdict(self),
            "candidate_id": self.candidate_id,
            "ranking_key": list(self.ranking_key),
        }


@dataclass(frozen=True)
class NPHardHubSelectionRequestV1:
    request_id: str
    target_problem: str
    registry_fingerprint: str
    candidates: tuple[NPHardHubCandidateV1, ...]
    max_unresolved_gaps: int = 5
    max_authoring_nodes: int = 5
    max_instance_model_calls: int = 8
    direction: str = NP_HARD_HUB_DIRECTION
    schema_version: str = NP_HARD_HUB_SELECTION_REQUEST_SCHEMA_V1

    def _content(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "target_problem": self.target_problem,
            "registry_fingerprint": self.registry_fingerprint,
            "direction": self.direction,
            "candidates": [candidate.to_dict() for candidate in self.candidates],
            "max_unresolved_gaps": self.max_unresolved_gaps,
            "max_authoring_nodes": self.max_authoring_nodes,
            "max_instance_model_calls": self.max_instance_model_calls,
        }

    @property
    def computed_request_id(self) -> str:
        return sha256_id(self._content())

    def validate(self) -> None:
        if self.schema_version != NP_HARD_HUB_SELECTION_REQUEST_SCHEMA_V1:
            _fail("invalid_hardness_hub_selection", "unsupported selection schema")
        if self.direction != NP_HARD_HUB_DIRECTION:
            _fail("candidate_wrong_direction", "selection request reversed the direction")
        if not self.target_problem or not self.registry_fingerprint.startswith("lean:"):
            _fail("candidate_dependency_stale", "selection request identity is incomplete")
        if not 1 <= self.max_unresolved_gaps <= 16 or not 1 <= self.max_authoring_nodes <= 16:
            _fail("invalid_hardness_hub_selection", "selection authoring budget is invalid")
        if not 1 <= self.max_instance_model_calls <= 8:
            _fail("invalid_hardness_hub_selection", "selection model-call budget is invalid")
        candidate_ids: set[str] = set()
        for candidate in self.candidates:
            candidate.validate()
            if candidate.target_problem != self.target_problem:
                _fail("candidate_wrong_endpoint", "hub candidate targets another problem")
            if candidate.registry_fingerprint != self.registry_fingerprint:
                _fail("candidate_dependency_stale", "hub candidate uses another Core snapshot")
            if candidate.candidate_id in candidate_ids:
                _fail("fabricated_hardness_seed", "selection request repeats a candidate")
            candidate_ids.add(candidate.candidate_id)
        if tuple(candidate.candidate_id for candidate in self.candidates) != tuple(
            sorted(candidate_ids)
        ):
            _fail("invalid_hardness_hub_selection", "selection candidates are not canonicalized")
        if self.request_id != self.computed_request_id:
            _fail("candidate_dependency_stale", "selection request content hash mismatch")

    def to_dict(self) -> dict[str, Any]:
        self.validate()
        return {"request_id": self.request_id, **self._content()}


def build_np_hard_hub_selection_request(
    *,
    target_problem: str,
    registry_fingerprint: str,
    candidates: Iterable[NPHardHubCandidateV1],
    max_unresolved_gaps: int = 5,
    max_authoring_nodes: int = 5,
    max_instance_model_calls: int = 8,
) -> NPHardHubSelectionRequestV1:
    ordered = tuple(sorted(candidates, key=lambda candidate: candidate.candidate_id))
    arguments = {
        "target_problem": target_problem,
        "registry_fingerprint": registry_fingerprint,
        "candidates": ordered,
        "max_unresolved_gaps": max_unresolved_gaps,
        "max_authoring_nodes": max_authoring_nodes,
        "max_instance_model_calls": max_instance_model_calls,
    }
    provisional = NPHardHubSelectionRequestV1(
        request_id="sha256:" + "0" * 64, **arguments
    )
    request = NPHardHubSelectionRequestV1(
        request_id=provisional.computed_request_id, **arguments
    )
    request.validate()
    return request


@dataclass(frozen=True)
class NPHardHubRejectionV1:
    candidate_id: str
    stable_seed_id: str
    seed_problem: str
    code: str
    explanation: str


@dataclass(frozen=True)
class NPHardHubSelectionResultV1:
    request_id: str
    selected_candidate_id: str | None
    ranked_candidate_ids: tuple[str, ...]
    rejected: tuple[NPHardHubRejectionV1, ...]
    failure_code: str | None
    schema_version: str = NP_HARD_HUB_SELECTION_RESULT_SCHEMA_V1

    def validate(self, request: NPHardHubSelectionRequestV1) -> None:
        request.validate()
        if self.schema_version != NP_HARD_HUB_SELECTION_RESULT_SCHEMA_V1:
            _fail("invalid_hardness_hub_selection", "unsupported selection result schema")
        if self.request_id != request.request_id:
            _fail("candidate_dependency_stale", "selection result belongs to another request")
        all_ids = {candidate.candidate_id for candidate in request.candidates}
        rejected_ids = {item.candidate_id for item in self.rejected}
        if set(self.ranked_candidate_ids) & rejected_ids:
            _fail("invalid_hardness_hub_selection", "candidate is ranked and rejected")
        if set(self.ranked_candidate_ids) | rejected_ids != all_ids:
            _fail("invalid_hardness_hub_selection", "selection result lost a candidate")
        if self.selected_candidate_id != (
            self.ranked_candidate_ids[0] if self.ranked_candidate_ids else None
        ):
            _fail("invalid_hardness_hub_selection", "selection did not choose rank zero")
        if self.selected_candidate_id is None:
            if self.failure_code != "no_authorable_hardness_hub":
                _fail("invalid_hardness_hub_selection", "empty ranking lacks typed failure")
        elif self.failure_code is not None:
            _fail("invalid_hardness_hub_selection", "successful selection claims failure")

    def to_dict(self, request: NPHardHubSelectionRequestV1) -> dict[str, Any]:
        self.validate(request)
        by_id = {candidate.candidate_id: candidate for candidate in request.candidates}
        return {
            "schema_version": self.schema_version,
            "request_id": self.request_id,
            "selected_candidate_id": self.selected_candidate_id,
            "selected_candidate": (
                by_id[self.selected_candidate_id].to_dict()
                if self.selected_candidate_id is not None
                else None
            ),
            "ranked_candidates": [by_id[item].to_dict() for item in self.ranked_candidate_ids],
            "rejected_candidates": [asdict(item) for item in self.rejected],
            "failure_code": self.failure_code,
            "model_calls": 0,
        }


def rank_np_hard_hub_candidates(
    request: NPHardHubSelectionRequestV1,
) -> NPHardHubSelectionResultV1:
    request.validate()
    eligible: list[NPHardHubCandidateV1] = []
    rejected: list[NPHardHubRejectionV1] = []
    for candidate in request.candidates:
        code: str | None = None
        explanation = ""
        if candidate.seed_problem == request.target_problem:
            code = "target_cannot_be_authoring_seed"
            explanation = "the requested target cannot seed its own authoring proof"
        elif candidate.eligibility == "reverse_only":
            code = "candidate_wrong_direction"
            explanation = "only target-to-seed reachability exists"
        elif candidate.eligibility == "unsupported" or candidate.gap_risk == "unsupported":
            code = "unsupported_hardness_hub_gap"
            explanation = "the gap analyzer found no allowlisted authoring capability"
        elif candidate.unresolved_gap_count > request.max_unresolved_gaps:
            code = "authoring_gap_budget_exhausted"
            explanation = "candidate exceeds the unresolved-gap budget"
        elif candidate.estimated_authoring_nodes > request.max_authoring_nodes:
            code = "authoring_gap_budget_exhausted"
            explanation = "candidate exceeds the authoring-node budget"
        if code is None:
            eligible.append(candidate)
        else:
            rejected.append(
                NPHardHubRejectionV1(
                    candidate_id=candidate.candidate_id,
                    stable_seed_id=candidate.stable_seed_id,
                    seed_problem=candidate.seed_problem,
                    code=code,
                    explanation=explanation,
                )
            )
    ranked = tuple(sorted(eligible, key=lambda candidate: candidate.ranking_key))
    result = NPHardHubSelectionResultV1(
        request_id=request.request_id,
        selected_candidate_id=ranked[0].candidate_id if ranked else None,
        ranked_candidate_ids=tuple(candidate.candidate_id for candidate in ranked),
        rejected=tuple(sorted(rejected, key=lambda item: item.candidate_id)),
        failure_code=None if ranked else "no_authorable_hardness_hub",
    )
    result.validate(request)
    return result


def project_np_hard_hub_candidates(
    *,
    seeds: Iterable[NPHardSeedLike],
    target_problem: str,
    profiles: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[NPHardHubCandidateV1, ...]:
    """Bind gap profiles to the exact seeds observed by Lean.

    Missing profiles remain in the candidate inventory as unsupported rows;
    they are never silently dropped.  When no analyzer profile is supplied,
    the production V1 fallback exposes one conservative semantic-proof gap per
    observed seed, replacing the old canonicalThreeSAT name heuristic.
    """

    candidates: list[NPHardHubCandidateV1] = []
    for seed in seeds:
        profile = profiles.get(seed.problem_declaration) if profiles is not None else None
        if profile is None and profiles is None:
            profile = {
                "eligibility": "authorable_gap",
                "unresolved_gap_count": 1,
                "gap_risk": "semantic-proof",
                "existing_route_length": 0,
                "representation_adapter_count": 0,
                "estimated_authoring_nodes": 1,
                "task_class": "semantic_proof",
            }
        elif profile is None:
            profile = {
                "eligibility": "unsupported",
                "unresolved_gap_count": 0,
                "gap_risk": "unsupported",
                "existing_route_length": 0,
                "representation_adapter_count": 0,
                "estimated_authoring_nodes": 0,
                "task_class": None,
            }
        candidate = NPHardHubCandidateV1(
            stable_seed_id=seed.entry_id,
            seed_problem=seed.problem_declaration,
            seed_evidence=seed.evidence_declaration,
            seed_evidence_kind=seed.evidence_kind,
            target_problem=target_problem,
            registry_fingerprint=seed.registry_fingerprint,
            eligibility=str(profile["eligibility"]),
            unresolved_gap_count=int(profile["unresolved_gap_count"]),
            gap_risk=str(profile["gap_risk"]),
            existing_route_length=int(profile["existing_route_length"]),
            representation_adapter_count=int(profile["representation_adapter_count"]),
            estimated_authoring_nodes=int(profile["estimated_authoring_nodes"]),
            task_class=profile.get("task_class"),
        )
        candidate.validate()
        candidates.append(candidate)
    return tuple(candidates)


@dataclass(frozen=True)
class NPHardHubAttemptRequestV1:
    request_id: str
    selection_request_id: str
    candidate_id: str
    seed_problem: str
    target_problem: str
    direction: str
    dependency_fingerprint: str
    candidate_model_call_budget: int
    instance_model_call_budget_remaining: int
    schema_version: str = NP_HARD_HUB_ATTEMPT_REQUEST_SCHEMA_V1

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _attempt_request(
    *,
    selection_request: NPHardHubSelectionRequestV1,
    candidate: NPHardHubCandidateV1,
    consumed_model_calls: int,
) -> NPHardHubAttemptRequestV1:
    content = {
        "schema_version": NP_HARD_HUB_ATTEMPT_REQUEST_SCHEMA_V1,
        "selection_request_id": selection_request.request_id,
        "candidate_id": candidate.candidate_id,
        "seed_problem": candidate.seed_problem,
        "target_problem": candidate.target_problem,
        "direction": candidate.direction,
        "dependency_fingerprint": sha256_id(
            {
                "registry_fingerprint": candidate.registry_fingerprint,
                "stable_seed_id": candidate.stable_seed_id,
                "candidate_id": candidate.candidate_id,
            }
        ),
        "candidate_model_call_budget": min(
            4, selection_request.max_instance_model_calls - consumed_model_calls
        ),
        "instance_model_call_budget_remaining": (
            selection_request.max_instance_model_calls - consumed_model_calls
        ),
    }
    return NPHardHubAttemptRequestV1(
        request_id=sha256_id(content),
        selection_request_id=content["selection_request_id"],
        candidate_id=content["candidate_id"],
        seed_problem=content["seed_problem"],
        target_problem=content["target_problem"],
        direction=content["direction"],
        dependency_fingerprint=content["dependency_fingerprint"],
        candidate_model_call_budget=content["candidate_model_call_budget"],
        instance_model_call_budget_remaining=content[
            "instance_model_call_budget_remaining"
        ],
    )


class NPHardHubSwitchSessionV1:
    """Bounded candidate switching without cross-hub node reuse."""

    def __init__(
        self,
        *,
        request: NPHardHubSelectionRequestV1,
        selection: NPHardHubSelectionResultV1,
    ):
        selection.validate(request)
        self.request = request
        self.selection = selection
        by_id = {candidate.candidate_id: candidate for candidate in request.candidates}
        self._ranked = tuple(by_id[item] for item in selection.ranked_candidate_ids)
        self._index = 0
        self.consumed_model_calls = 0
        self.events: list[dict[str, Any]] = []
        self.complete = not self._ranked
        self.failure_code = selection.failure_code

    @property
    def current_candidate(self) -> NPHardHubCandidateV1 | None:
        return None if self.complete or self._index >= len(self._ranked) else self._ranked[self._index]

    @property
    def current_request(self) -> NPHardHubAttemptRequestV1 | None:
        candidate = self.current_candidate
        if candidate is None:
            return None
        return _attempt_request(
            selection_request=self.request,
            candidate=candidate,
            consumed_model_calls=self.consumed_model_calls,
        )

    def reject_current(
        self,
        *,
        failure_code: str,
        failure_class: str,
        model_calls: int,
        accepted_node_hashes: tuple[str, ...] = (),
    ) -> NPHardHubAttemptRequestV1 | None:
        candidate = self.current_candidate
        attempt = self.current_request
        if candidate is None or attempt is None:
            _fail("no_authorable_hardness_hub", "candidate switch session is complete")
        if failure_code not in NP_HARD_HUB_CANDIDATE_FAILURES:
            _fail("invalid_hardness_hub_switch", "candidate failure code is not typed")
        if failure_class not in {"irrecoverable", "budget_exhausted"}:
            _fail("invalid_hardness_hub_switch", "candidate failure class is invalid")
        if not 0 <= model_calls <= attempt.candidate_model_call_budget:
            _fail("authoring_gap_budget_exhausted", "candidate model-call count is invalid")
        if failure_class == "budget_exhausted" and model_calls != attempt.candidate_model_call_budget:
            _fail("invalid_hardness_hub_switch", "candidate switched before budget exhaustion")
        self.consumed_model_calls += model_calls
        if self.consumed_model_calls > self.request.max_instance_model_calls:
            _fail("authoring_gap_budget_exhausted", "instance model-call budget exceeded")
        for digest in accepted_node_hashes:
            if not _HASH_RE.fullmatch(digest):
                _fail("candidate_dependency_stale", "invalidated node lacks a content hash")
        self._index += 1
        next_candidate = self.current_candidate
        next_request = (
            _attempt_request(
                selection_request=self.request,
                candidate=next_candidate,
                consumed_model_calls=self.consumed_model_calls,
            )
            if next_candidate is not None
            and self.consumed_model_calls < self.request.max_instance_model_calls
            else None
        )
        self.events.append(
            {
                "from_candidate_id": candidate.candidate_id,
                "from_request_id": attempt.request_id,
                "failure_code": failure_code,
                "failure_class": failure_class,
                "model_calls": model_calls,
                "invalidated_node_hashes": list(accepted_node_hashes),
                "to_candidate_id": next_candidate.candidate_id if next_request else None,
                "to_request_id": next_request.request_id if next_request else None,
                "endpoint_reuse": False,
            }
        )
        if next_request is None:
            self.complete = True
            self.failure_code = "no_authorable_hardness_hub"
        return next_request

    def accept_current(self) -> None:
        candidate = self.current_candidate
        attempt = self.current_request
        if candidate is None or attempt is None:
            _fail("no_authorable_hardness_hub", "candidate switch session is complete")
        self.events.append(
            {
                "accepted_candidate_id": candidate.candidate_id,
                "accepted_request_id": attempt.request_id,
                "model_calls": self.consumed_model_calls,
            }
        )
        self.complete = True
        self.failure_code = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": NP_HARD_HUB_SWITCH_TRACE_SCHEMA_V1,
            "selection_request_id": self.request.request_id,
            "ranked_candidate_ids": list(self.selection.ranked_candidate_ids),
            "current_candidate_id": (
                self.current_candidate.candidate_id if self.current_candidate else None
            ),
            "current_request": (
                self.current_request.to_dict() if self.current_request else None
            ),
            "consumed_model_calls": self.consumed_model_calls,
            "max_instance_model_calls": self.request.max_instance_model_calls,
            "events": list(self.events),
            "complete": self.complete,
            "failure_code": self.failure_code,
            "model_selected_hub": False,
        }
