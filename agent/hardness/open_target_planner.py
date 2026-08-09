"""Model-driven planning from a Lean-observed input to a model-selected target.

The target catalog is exported from exact native certificate heads in Lean.
Python performs only bounded retrieval, policy checks, and directed graph
validation.  It neither chooses a target for the model nor runs Lean during a
conversation; all accepted paths and target evidence are checked together in
the final artifact.
"""

from __future__ import annotations

import json
from collections import deque
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any

from .benchmark import (
    KNOWN_HARDNESS_EMITTABLE_EVIDENCE_KINDS,
    OPEN_TARGET_EMITTABLE_EVIDENCE_KINDS,
)
from .connection_catalog import (
    DIRECT_RELATION,
    ConnectionCatalog,
    ConnectionCatalogEntry,
    build_initial_connection_hints,
    connection_search_result,
)
from .frontier_guidance import (
    build_frontier_guidance,
    frontier_guidance_errors,
)
from .hardness_target_catalog import (
    ALLOWED_EVIDENCE_KINDS,
    TARGET_POLICY_SET,
    HardnessTargetCatalog,
    HardnessTargetCatalogEntry,
    HardnessTargetCatalogError,
    HardnessTargetEvidence,
    HardnessTargetSearchError,
    build_initial_hardness_target_hints,
    hardness_target_search_result,
    parse_hardness_target_searches,
    search_hardness_targets,
)
from .input_observation import LeanInputObservation
from .input_planner import (
    MAX_INPUT_PROTOCOL_FEEDBACK,
    MAX_RETRIEVED_REDUCTIONS,
    InputPlanningError,
    ObservedInputPlannerResult,
    ObservedInputPlanningSession,
    RELATION_ACTION_KIND,
    _normalize_action,
    _required_string,
    _string_list,
)
from .model_client import DeepSeekClient, ModelResponse, extract_json_object
from .models import TypedCatalog, TypedInventoryEntry
from .open_target import audit_open_target_prompt
from .predicate_input import audit_predicate_input_prompt
from .plan import (
    PLAN_OUTPUT_SCHEMA,
    PLAN_SCHEMA,
    PLAN_STEP_SCHEMA,
    HardnessPlan,
    parse_hardness_plan,
)
from .problem_catalog import (
    ProblemCatalog,
    ProblemCatalogEntry,
    ProblemMatch,
    build_initial_problem_hints,
    predicate_presentation_groups,
    problem_search_result,
)
from .retrieval import (
    RetrievalValidationError,
    build_library_architecture,
    entry_summary,
    parse_theorem_searches,
)
from .retrieved_view import (
    compact_retrieved_payload,
    compact_retrieved_view_metadata,
)


MAX_OPEN_TARGET_QUERY_ROUNDS = 10
MAX_OPEN_TARGET_MODEL_TURNS = 14
MAX_RETRIEVED_HARDNESS_TARGETS = 20
MAX_KNOWN_HARDNESS_RETRIEVED_REDUCTIONS = 48
MAX_KNOWN_HARDNESS_PROTOCOL_FEEDBACK = 6

OPEN_TARGET_SYSTEM_PROMPT = """You are planning a reduction with an already
compiled Lean library. Each API turn is stateless, so read query_history,
retrieved results, and protocol_feedback in the current prompt. Return exactly
one JSON object on every turn. Do not spend the output budget narrating or
re-deriving the whole graph. For known-hardness requests, frontier_guidance
contains only already retrieved endpoint nodes and declaration-free outgoing
counts; prefer its bounded source-only suggested_searches when more edges are
needed. If terminal_guidance.mode is finish_now, a fully retrieved
policy-compliant path exists: select one and return finish immediately without
another search. If terminal_guidance.mode is stop_now, return stop immediately
with its exact failure_code and the documented selector fields; do not perform
another search. You must identify the input problem, query
search_hardness_targets, select both a returned target_entry_id and a returned
target_evidence_id that satisfy the public request policy, retrieve every
directed reduction edge yourself, and write the complete Lean CertifiedPath
term. Respect the public minimum/maximum atom range and simple-path requirement.
Native-hardness-only evidence does not manufacture target NP membership. Never
invent a declaration, reverse a one-way reduction, add new mathematics, or use
sorry, admit, axioms, imports, commands, or definitions.
For a predicate input, first query both its accepts and domain indexes. Use only
a returned row marked accepts_exact_defeq=true, with match_relation set to
accepts_exact_defeq and a null connection_entry_id. The CertifiedPath starts at
that selected PresentedProblem, never at the raw predicate. If Lean-confirmed
matches span multiple codec_group_id values, or if the required accepts/domain
evidence is absent, return the corresponding documented predicate stop code.
Lean is not run during this conversation; all accepted cases and their exact
target evidence are checked together once at the end. If bounded searches show
that no evidence satisfies the policy, or that eligible targets exist but no
allowed forward route exists, return the corresponding auditable stop action."""


@dataclass(frozen=True)
class OpenTargetRequestPolicy:
    required_hardness: str
    allowed_target_evidence: tuple[str, ...]
    maximum_route_atoms: int
    maximum_dependencies: int
    minimum_route_atoms: int = 0
    allow_reflexive_target: bool = True
    require_simple_path: bool = False
    objective: str = "reduce_to_known_np"

    def __post_init__(self) -> None:
        if self.required_hardness not in TARGET_POLICY_SET:
            raise ValueError("required_hardness is not a supported native policy")
        if not self.allowed_target_evidence or len(
            self.allowed_target_evidence
        ) != len(set(self.allowed_target_evidence)):
            raise ValueError("allowed_target_evidence must be a non-empty unique tuple")
        unknown = set(self.allowed_target_evidence) - ALLOWED_EVIDENCE_KINDS
        if unknown:
            raise ValueError(f"unsupported target evidence kinds: {sorted(unknown)}")
        if self.objective not in {
            "reduce_to_known_np",
            "reduce_to_known_hardness",
        }:
            raise ValueError("unsupported open-target objective")
        emittable_evidence = (
            KNOWN_HARDNESS_EMITTABLE_EVIDENCE_KINDS
            if self.objective == "reduce_to_known_hardness"
            else OPEN_TARGET_EMITTABLE_EVIDENCE_KINDS
        )
        unemittable = set(self.allowed_target_evidence) - emittable_evidence
        if unemittable:
            raise ValueError(
                "open-target artifact cannot emit target evidence kinds: "
                f"{sorted(unemittable)}"
            )
        if self.objective == "reduce_to_known_np" and (
            "transported_native_hardness" in self.allowed_target_evidence
        ):
            raise ValueError(
                "known-NP requests cannot use hardness-only target evidence"
            )
        if self.objective == "reduce_to_known_hardness" and (
            self.required_hardness != "native_np_hard"
        ):
            raise ValueError(
                "known-hardness requests require the native_np_hard policy"
            )
        for label, value in (
            ("minimum_route_atoms", self.minimum_route_atoms),
            ("maximum_route_atoms", self.maximum_route_atoms),
            ("maximum_dependencies", self.maximum_dependencies),
        ):
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"{label} must be a non-negative integer")
        if self.minimum_route_atoms > self.maximum_route_atoms:
            raise ValueError(
                "minimum_route_atoms must not exceed maximum_route_atoms"
            )
        if not isinstance(self.allow_reflexive_target, bool):
            raise ValueError("allow_reflexive_target must be boolean")
        if not isinstance(self.require_simple_path, bool):
            raise ValueError("require_simple_path must be boolean")

    def to_dict(self) -> dict[str, Any]:
        return {
            "required_hardness": self.required_hardness,
            "allowed_target_evidence": list(self.allowed_target_evidence),
            "minimum_route_atoms": self.minimum_route_atoms,
            "maximum_route_atoms": self.maximum_route_atoms,
            "maximum_dependencies": self.maximum_dependencies,
            "allow_reflexive_target": self.allow_reflexive_target,
            "require_simple_path": self.require_simple_path,
            "objective": self.objective,
        }


@dataclass(frozen=True)
class _TargetObservationProxy:
    input_declaration: str
    normalized_problem_node_id: str


def _require_open_target_fingerprints(
    observation: LeanInputObservation,
    problem_catalog: ProblemCatalog,
    connection_catalog: ConnectionCatalog,
    reduction_catalog: TypedCatalog,
    target_catalog: HardnessTargetCatalog,
) -> None:
    fingerprints = {
        observation.registry_fingerprint,
        problem_catalog.registry_fingerprint,
        connection_catalog.registry_fingerprint,
        reduction_catalog.registry_fingerprint,
        target_catalog.registry_fingerprint,
    }
    if len(fingerprints) != 1:
        raise InputPlanningError(
            "stale_catalog_fingerprint",
            "输入观察、问题目录、连接目录、归约目录和 hardness 目标目录并非来自同一个 "
            "Lean registry 指纹，因此不能安全地组合目标证据与归约路线。",
        )


def _require_supported_source(observation: LeanInputObservation) -> None:
    if (
        observation.supported
        and observation.input_kind == "presented_problem"
        and observation.normalized_problem_node_id
    ):
        return
    if (
        observation.supported
        and observation.input_kind == "predicate"
        and observation.predicate_node_id
        and observation.predicate_domain_node_id
    ):
        return
    raise InputPlanningError(
        observation.failure_code or "input_declaration_not_supported",
        observation.explanation
        or "Lean 没有把输入声明确认为一个可用于复杂度归约的 PresentedProblem "
        "或封闭一元谓词。",
    )


def _normalize_open_target_action(payload: dict[str, Any]) -> dict[str, Any]:
    normalized = _normalize_action(payload)
    if normalized is not payload or isinstance(normalized.get("action"), str):
        return normalized
    nested = payload.get("search_hardness_targets")
    if isinstance(nested, dict):
        value = dict(nested)
        value.setdefault("action", "search_hardness_targets")
        return value
    return payload


def _required_open_target_problem_selector(
    payload: Mapping[str, Any], *, failure_code: str
) -> str | Mapping[str, Any]:
    value = payload.get("matched_problem")
    if isinstance(value, str) and value.strip():
        return value.strip()
    if isinstance(value, Mapping):
        selector: dict[str, str] = {}
        for field in ("entry_id", "declaration"):
            if field not in value:
                continue
            item = value.get(field)
            if not isinstance(item, str) or not item.strip():
                raise InputPlanningError(
                    failure_code,
                    "matched_problem 对象的 entry_id/declaration 必须是非空字符串。",
                )
            selector[field] = item.strip()
        if selector:
            return selector
    raise InputPlanningError(
        failure_code,
        "matched_problem 必须是已检索问题的非空 entry_id/declaration 字符串，"
        "或包含这些选择字段的对象。",
    )


def _optional_open_target_connection_id(
    payload: Mapping[str, Any], *, failure_code: str
) -> str | None:
    value = payload.get("connection_entry_id")
    if value is None:
        return None
    if not isinstance(value, str):
        raise InputPlanningError(
            failure_code,
            "connection_entry_id 必须是 JSON null、空字符串，或 "
            "search_connections 返回的非空 ID。",
        )
    return value.strip() or None


class OpenTargetPlanningSession(ObservedInputPlanningSession):
    """One bounded query session with a model-selected, evidence-backed target."""

    def __init__(
        self,
        *,
        observation: LeanInputObservation,
        problem_catalog: ProblemCatalog,
        connection_catalog: ConnectionCatalog,
        reduction_catalog: TypedCatalog,
        target_catalog: HardnessTargetCatalog,
        request_policy: OpenTargetRequestPolicy,
        maximum_query_rounds: int = MAX_OPEN_TARGET_QUERY_ROUNDS,
    ) -> None:
        if not 1 <= maximum_query_rounds <= MAX_OPEN_TARGET_QUERY_ROUNDS:
            raise ValueError(
                f"maximum_query_rounds must be in 1..{MAX_OPEN_TARGET_QUERY_ROUNDS}"
            )
        _require_supported_source(observation)
        _require_open_target_fingerprints(
            observation,
            problem_catalog,
            connection_catalog,
            reduction_catalog,
            target_catalog,
        )
        self.observation = observation
        self.target_observation = _TargetObservationProxy("", "")
        self.problem_catalog = problem_catalog
        self.connection_catalog = connection_catalog
        self.reduction_catalog = reduction_catalog
        self.target_catalog = target_catalog
        self.request_policy = request_policy
        self.maximum_retrieved_reductions = (
            MAX_KNOWN_HARDNESS_RETRIEVED_REDUCTIONS
            if request_policy.objective == "reduce_to_known_hardness"
            else MAX_RETRIEVED_REDUCTIONS
        )
        self.maximum_protocol_feedback = (
            MAX_KNOWN_HARDNESS_PROTOCOL_FEEDBACK
            if request_policy.objective == "reduce_to_known_hardness"
            else MAX_INPUT_PROTOCOL_FEEDBACK
        )
        self.maximum_query_rounds = maximum_query_rounds
        self.query_rounds_used = 0
        self.retrieved_problems: dict[str, ProblemCatalogEntry] = {}
        self.retrieved_connections: dict[str, ConnectionCatalogEntry] = {}
        self.retrieved_reductions: dict[str, TypedInventoryEntry] = {}
        self.retrieved_hardness_targets: dict[str, HardnessTargetCatalogEntry] = {}
        self.retrieved_target_evidences: dict[str, HardnessTargetEvidence] = {}
        self.queried_problem_node_ids: set[str] = set()
        self.queried_problem_accepts_node_ids: set[str] = set()
        self.queried_problem_domain_node_ids: set[str] = set()
        self.queried_connection_source_node_ids: set[str] = set()
        self.queried_reduction_source_node_ids: set[str] = set()
        self.source_only_queried_reduction_source_node_ids: set[str] = set()
        self.fully_queried_reduction_source_node_ids: set[str] = set()
        self.reduction_search_signatures: set[
            tuple[
                tuple[str, ...],
                tuple[str, ...],
                tuple[str, ...],
                tuple[str, ...],
                tuple[str, ...],
                int,
            ]
        ] = set()
        self.queried_hardness_target_policies: set[str] = set()
        self.required_policy_visible_evidence_ids: set[str] = set()
        self.target_search_performed = False
        self.trace: list[Mapping[str, Any]] = []
        self.protocol_feedback: list[dict[str, str]] = []

    def _evidence_dependency_count(self, evidence: HardnessTargetEvidence) -> int:
        return len(set(evidence.provenance_declarations))

    def _evidence_satisfies_request(self, evidence: HardnessTargetEvidence) -> bool:
        membership_available = bool(evidence.membership_lean_term)
        return (
            self.request_policy.required_hardness in evidence.satisfied_policies
            and evidence.evidence_kind
            in self.request_policy.allowed_target_evidence
            and (
                self.request_policy.objective == "reduce_to_known_hardness"
                or membership_available
            )
            and self._evidence_dependency_count(evidence)
            <= self.request_policy.maximum_dependencies
        )

    def _eligible_target_evidences(
        self,
    ) -> tuple[tuple[HardnessTargetCatalogEntry, HardnessTargetEvidence], ...]:
        return tuple(
            (entry, evidence)
            for entry in self.target_catalog.entries
            for evidence in entry.evidences
            if self._evidence_satisfies_request(evidence)
        )

    def _adjacency(self) -> dict[str, tuple[TypedInventoryEntry, ...]]:
        adjacency: dict[str, list[TypedInventoryEntry]] = {}
        for entry in self.reduction_catalog.entries:
            adjacency.setdefault(entry.source_node_id, []).append(entry)
        return {
            node: tuple(sorted(edges, key=lambda item: item.declaration))
            for node, edges in adjacency.items()
        }

    def _retrieved_adjacency(self) -> dict[str, tuple[TypedInventoryEntry, ...]]:
        adjacency: dict[str, list[TypedInventoryEntry]] = {}
        for entry in self.retrieved_reductions.values():
            adjacency.setdefault(entry.source_node_id, []).append(entry)
        return {
            node: tuple(sorted(edges, key=lambda item: item.declaration))
            for node, edges in adjacency.items()
        }

    def _shortest_route_length(self, source_node: str, target_node: str) -> int | None:
        if source_node == target_node:
            return 0
        adjacency = self._adjacency()
        queue: deque[tuple[str, int]] = deque([(source_node, 0)])
        seen = {source_node}
        while queue:
            node, depth = queue.popleft()
            for edge in adjacency.get(node, ()):
                if edge.target_node_id == target_node:
                    return depth + 1
                if edge.target_node_id not in seen:
                    seen.add(edge.target_node_id)
                    queue.append((edge.target_node_id, depth + 1))
        return None

    def _shortest_allowed_route_atom_count(
        self,
        *,
        source_node: str,
        target_node: str,
        evidence: HardnessTargetEvidence,
        connection: ConnectionCatalogEntry | None,
        adjacency: Mapping[str, Sequence[TypedInventoryEntry]] | None = None,
    ) -> int | None:
        initial_atoms = 1 if connection is not None else 0
        initial_dependencies = set(evidence.provenance_declarations)
        if connection is not None:
            initial_dependencies.add(connection.certificate_declaration)
            initial_dependencies.add(connection.projection_declaration)
        if (
            initial_atoms > self.request_policy.maximum_route_atoms
            or len(initial_dependencies) > self.request_policy.maximum_dependencies
        ):
            return None
        if (
            source_node == target_node
            and initial_atoms >= self.request_policy.minimum_route_atoms
            and (initial_atoms > 0 or self.request_policy.allow_reflexive_target)
        ):
            return initial_atoms
        route_adjacency = adjacency if adjacency is not None else self._adjacency()
        initial_visited = (
            frozenset({source_node})
            if self.request_policy.require_simple_path
            else frozenset()
        )
        queue: deque[tuple[str, int, frozenset[str], frozenset[str]]] = deque(
            [
                (
                    source_node,
                    initial_atoms,
                    frozenset(initial_dependencies),
                    initial_visited,
                )
            ]
        )
        seen: set[tuple[str, int, frozenset[str], frozenset[str]]] = set(queue)
        while queue:
            node, atoms, dependencies, visited = queue.popleft()
            if atoms >= self.request_policy.maximum_route_atoms:
                continue
            for edge in route_adjacency.get(node, ()):
                if (
                    self.request_policy.require_simple_path
                    and edge.target_node_id in visited
                ):
                    continue
                next_dependencies = dependencies | {edge.declaration}
                if len(next_dependencies) > self.request_policy.maximum_dependencies:
                    continue
                next_atoms = atoms + 1
                if (
                    edge.target_node_id == target_node
                    and next_atoms >= self.request_policy.minimum_route_atoms
                ):
                    return next_atoms
                if (
                    self.request_policy.require_simple_path
                    and edge.target_node_id == target_node
                ):
                    continue
                next_visited = (
                    visited | {edge.target_node_id}
                    if self.request_policy.require_simple_path
                    else visited
                )
                state = (
                    edge.target_node_id,
                    next_atoms,
                    next_dependencies,
                    next_visited,
                )
                if state not in seen:
                    seen.add(state)
                    queue.append(state)
        return None

    def _retrieved_finish_route_atom_counts(self) -> tuple[int, ...]:
        """Expose terminal availability without choosing a route for the model."""

        starts = self._retrieved_route_starts()
        if not starts:
            return ()

        retrieved_adjacency = self._retrieved_adjacency()
        counts: set[int] = set()
        for target in self.retrieved_hardness_targets.values():
            for evidence in target.evidences:
                if (
                    evidence.evidence_id
                    not in self.required_policy_visible_evidence_ids
                    or not self._evidence_satisfies_request(evidence)
                ):
                    continue
                for source_node, connection in starts:
                    count = self._shortest_allowed_route_atom_count(
                        source_node=source_node,
                        target_node=target.target_node_id,
                        evidence=evidence,
                        connection=connection,
                        adjacency=retrieved_adjacency,
                    )
                    if count is not None:
                        counts.add(count)
        return tuple(sorted(counts))

    def _has_allowed_route(
        self,
        *,
        source_node: str,
        target_node: str,
        evidence: HardnessTargetEvidence,
        connection: ConnectionCatalogEntry | None,
    ) -> bool:
        return (
            self._shortest_allowed_route_atom_count(
                source_node=source_node,
                target_node=target_node,
                evidence=evidence,
                connection=connection,
            )
            is not None
        )

    def _complete_source_frontier_retrieved_via_connections(
        self, source_node: str
    ) -> bool:
        """Accept connection search only when it exposed every direct source edge."""

        if source_node not in self.queried_connection_source_node_ids:
            return False
        expected = {
            entry.declaration
            for entry in self.reduction_catalog.entries
            if entry.source_node_id == source_node
        }
        retrieved = {
            entry.certificate_declaration
            for entry in self.retrieved_connections.values()
            if entry.source_node_id == source_node
            and entry.relation == DIRECT_RELATION
        }
        return expected.issubset(retrieved)

    def _input_route_starts(
        self,
    ) -> tuple[tuple[str, ConnectionCatalogEntry | None], ...]:
        """Return possible verified input matches without selecting one for the model."""

        if self.predicate_input:
            groups = predicate_presentation_groups(
                self.observation,
                self.problem_catalog,
            )
            if len(groups) != 1:
                return ()
            starts: dict[str, tuple[str, ConnectionCatalogEntry | None]] = {}
            for entry in groups[0].entries:
                starts.setdefault(entry.problem_node_id, (entry.problem_node_id, None))
            return tuple(starts.values())

        input_node = self.observation.normalized_problem_node_id or ""
        problem_nodes = {entry.problem_node_id for entry in self.problem_catalog.entries}
        if input_node in problem_nodes:
            # The public protocol tells the model to prefer the exact endpoint and
            # defers connection retrieval in this case, so route policy must use the
            # same start state rather than an unseen alternative connection.
            return ((input_node, None),)
        return tuple(
            (connection.target_node_id, connection)
            for connection in sorted(
                self.connection_catalog.entries,
                key=lambda item: (item.certificate_declaration, item.entry_id),
            )
            if connection.source_node_id == input_node
            and connection.target_node_id in problem_nodes
        )

    def _retrieved_route_starts(
        self,
    ) -> tuple[tuple[str, ConnectionCatalogEntry | None], ...]:
        """Return only starts whose problem and optional connection are visible."""

        retrieved_problem_nodes = {
            entry.problem_node_id for entry in self.retrieved_problems.values()
        }
        return tuple(
            (source_node, connection)
            for source_node, connection in self._input_route_starts()
            if source_node in retrieved_problem_nodes
            and (
                connection is None
                or connection.entry_id in self.retrieved_connections
            )
        )

    def _frontier_guidance(self) -> dict[str, Any]:
        start_atom_counts: dict[str, int] = {}
        for source_node, connection in self._retrieved_route_starts():
            atoms = 1 if connection is not None else 0
            previous = start_atom_counts.get(source_node)
            if previous is None or atoms < previous:
                start_atom_counts[source_node] = atoms
        return build_frontier_guidance(
            retrieved_entries=tuple(self.retrieved_reductions.values()),
            catalog_entries=self.reduction_catalog.entries,
            start_atom_counts=start_atom_counts,
            source_only_queried_node_ids=(
                self.source_only_queried_reduction_source_node_ids
            ),
            maximum_route_atoms=self.request_policy.maximum_route_atoms,
        )

    def _terminal_stop_guidance(self) -> dict[str, Any] | None:
        """Expose an already auditable blocker without choosing model selectors."""

        if self.predicate_input:
            predicate_node = self.observation.predicate_node_id or ""
            domain_node = self.observation.predicate_domain_node_id or ""
            if (
                predicate_node in self.queried_problem_accepts_node_ids
                and domain_node in self.queried_problem_domain_node_ids
            ):
                failure_code = self._predicate_presentation_failure_code()
                if failure_code is not None:
                    return {
                        "mode": "stop_now",
                        "failure_code": failure_code,
                        "required_action": "stop",
                        "selector_fields_required": [],
                        "instruction": (
                            "Lean-confirmed predicate lookup facts already determine this "
                            "blocker. Return stop now with this exact failure_code and a "
                            "specific natural-language explanation."
                        ),
                    }

        required_policy_queried = bool(
            self.target_search_performed
            and self.request_policy.required_hardness
            in self.queried_hardness_target_policies
        )
        if required_policy_queried and not self._eligible_target_evidences():
            return {
                "mode": "stop_now",
                "failure_code": "no_eligible_hardness_target",
                "required_action": "stop",
                "selector_fields_required": [],
                "instruction": (
                    "The same-fingerprint target catalog contains no evidence satisfying "
                    "the public policy, evidence-kind, and dependency limits. Return stop "
                    "now; route searches cannot change target eligibility."
                ),
            }

        if not required_policy_queried or not self.required_policy_visible_evidence_ids:
            return None
        all_starts = self._input_route_starts()
        retrieved_starts = self._retrieved_route_starts()
        if not all_starts or not retrieved_starts:
            return None
        eligible = self._eligible_target_evidences()
        if not eligible:
            return None
        if any(
            self._has_allowed_route(
                source_node=source_node,
                target_node=entry.target_node_id,
                evidence=evidence,
                connection=connection,
            )
            for source_node, connection in all_starts
            for entry, evidence in eligible
        ):
            return None
        if not all(
            source_node in self.queried_reduction_source_node_ids
            or self._complete_source_frontier_retrieved_via_connections(source_node)
            for source_node, _ in retrieved_starts
        ):
            return None
        return {
            "mode": "stop_now",
            "failure_code": "eligible_target_has_no_existing_route",
            "required_action": "stop",
            "selector_fields_required": [
                "matched_problem",
                "match_relation",
                "connection_entry_id",
            ],
            "problem_and_connection_remain_model_selected": True,
            "instruction": (
                "Eligible target evidence exists, but the same-fingerprint directed "
                "catalog has no policy-compliant forward route from any verified input "
                "start. Choose a retrieved problem/connection selector and return stop "
                "now with this exact failure_code."
            ),
        }

    def _shortest_route_length_from_input(self, target_node: str) -> int | None:
        lengths = [
            length
            for source_node, _ in self._input_route_starts()
            if (length := self._shortest_route_length(source_node, target_node))
            is not None
        ]
        return min(lengths) if lengths else None

    def _shortest_reverse_route_length_to_input(
        self, target_node: str
    ) -> int | None:
        lengths = [
            length
            for source_node, _ in self._input_route_starts()
            if (length := self._shortest_route_length(target_node, source_node))
            is not None
        ]
        return min(lengths) if lengths else None

    def _policy_route_atom_count(
        self,
        *,
        target_node: str,
        evidence: HardnessTargetEvidence,
    ) -> int | None:
        counts: list[int] = []
        for source_node, connection in self._input_route_starts():
            count = self._shortest_allowed_route_atom_count(
                source_node=source_node,
                target_node=target_node,
                evidence=evidence,
                connection=connection,
            )
            if count is not None:
                counts.append(count)
        return min(counts) if counts else None

    def _decorate_target_evidence(
        self,
        *,
        entry: HardnessTargetCatalogEntry,
        evidence_raw: Mapping[str, Any],
    ) -> dict[str, Any] | None:
        evidence = self.retrieved_target_evidences.get(
            str(evidence_raw.get("evidence_id"))
        )
        if evidence is None:
            return None
        request_eligible = self._evidence_satisfies_request(evidence)
        policy_route_atoms = (
            self._policy_route_atom_count(
                target_node=entry.target_node_id,
                evidence=evidence,
            )
            if request_eligible
            else None
        )
        rendered = dict(evidence_raw)
        rendered.update(
            {
                "allowed_evidence_kind": evidence.evidence_kind
                in self.request_policy.allowed_target_evidence,
                "target_evidence_dependency_count": self._evidence_dependency_count(
                    evidence
                ),
                "request_eligible": request_eligible,
                "policy_route_allowed": policy_route_atoms is not None,
                "shortest_policy_route_atom_count": policy_route_atoms,
            }
        )
        return rendered

    def search_hardness_targets(self, payload: Mapping[str, Any]) -> dict[str, Any]:
        self._consume_query_round("search_hardness_targets")
        try:
            searches = parse_hardness_target_searches(payload)
            entries = search_hardness_targets(self.target_catalog, searches)
        except (HardnessTargetCatalogError, HardnessTargetSearchError) as error:
            raise InputPlanningError(
                "invalid_hardness_target_search",
                f"模型请求的 hardness 目标查询不符合有界检索协议：{error}",
            ) from error
        self.target_search_performed = True
        for search in searches:
            self.queried_hardness_target_policies.update(search.required_policies)
        room = MAX_RETRIEVED_HARDNESS_TARGETS - len(
            self.retrieved_hardness_targets
        )
        for entry in entries:
            if room <= 0:
                break
            if entry.target_entry_id not in self.retrieved_hardness_targets:
                self.retrieved_hardness_targets[entry.target_entry_id] = entry
                room -= 1
            for evidence in entry.evidences:
                self.retrieved_target_evidences[evidence.evidence_id] = evidence
        required_policies = tuple(
            sorted(
                {policy for search in searches for policy in search.required_policies}
            )
        )
        rendered_results: list[dict[str, Any]] = []
        for entry in entries:
            result = hardness_target_search_result(
                entry, required_policies=required_policies
            )
            route_length = self._shortest_route_length_from_input(
                entry.target_node_id
            )
            reverse_length = self._shortest_reverse_route_length_to_input(
                entry.target_node_id
            )
            evidences = []
            for evidence_raw in result["evidences"]:
                rendered_evidence = self._decorate_target_evidence(
                    entry=entry,
                    evidence_raw=evidence_raw,
                )
                if rendered_evidence is not None:
                    evidences.append(rendered_evidence)
            policy_route_atom_counts = [
                int(item["shortest_policy_route_atom_count"])
                for item in evidences
                if item.get("policy_route_allowed") is True
            ]
            result.update(
                {
                    "evidences": evidences,
                    "request_eligible_evidence_count": sum(
                        bool(item.get("request_eligible")) for item in evidences
                    ),
                    "reachable_from_input": route_length is not None,
                    "shortest_route_length_from_input": route_length,
                    "within_route_atom_limit": route_length is not None
                    and route_length <= self.request_policy.maximum_route_atoms,
                    "policy_route_allowed": bool(policy_route_atom_counts),
                    "shortest_policy_route_atom_count": (
                        min(policy_route_atom_counts)
                        if policy_route_atom_counts
                        else None
                    ),
                    "reverse_route_exists": reverse_length is not None,
                    "route_declarations_included": any(
                        item.get("evidence_kind")
                        in {
                            "transported_native_hardness",
                            "transported_native_completeness",
                        }
                        for item in evidences
                    ),
                }
            )
            rendered_results.append(result)
        if self.request_policy.required_hardness in required_policies:
            self.required_policy_visible_evidence_ids.update(
                str(evidence["evidence_id"])
                for result in rendered_results
                for evidence in result["evidences"]
                if evidence.get("request_eligible") is True
            )
        response = {
            "action": "search_hardness_targets",
            "searches": [search.to_dict() for search in searches],
            "results": rendered_results,
        }
        self.trace.append(response)
        return response

    def search_reductions(self, payload: Mapping[str, Any]) -> dict[str, Any]:
        """Track complete source frontiers and reject exact repeated searches."""

        try:
            searches = parse_theorem_searches(payload)
        except RetrievalValidationError as error:
            raise InputPlanningError(
                "invalid_reduction_search",
                f"模型请求的归约定理查询不符合范围限制：{error}",
            ) from error
        signatures = tuple(
            (
                search.terms,
                search.namespace_prefixes,
                search.roles,
                search.source_node_ids,
                search.target_node_ids,
                search.limit,
            )
            for search in searches
        )
        if (
            self.request_policy.objective == "reduce_to_known_hardness"
            and any(signature in self.reduction_search_signatures for signature in signatures)
        ):
            raise InputPlanningError(
                "repeated_reduction_search",
                "模型重复提交了本会话已经完成的同一归约查询。请使用 "
                "frontier_guidance.suggested_searches 扩展尚未完整查询的已检索 endpoint，"
                "或在 terminal_guidance 出现时立即 finish/stop；重复查询不会提供新授权。",
            )

        response = super().search_reductions(payload)
        self.reduction_search_signatures.update(signatures)
        retained = set(self.retrieved_reductions)
        for search in searches:
            source_only = bool(
                search.source_node_ids
                and not search.terms
                and not search.namespace_prefixes
                and not search.roles
                and not search.target_node_ids
            )
            if not source_only:
                continue
            for source_node in search.source_node_ids:
                self.source_only_queried_reduction_source_node_ids.add(source_node)
                expected = {
                    entry.declaration
                    for entry in self.reduction_catalog.entries
                    if entry.capability_kind == "certified_reduction"
                    and entry.source_node_id == source_node
                }
                if expected.issubset(retained):
                    self.fully_queried_reduction_source_node_ids.add(source_node)
        return response

    def execute_query(self, payload: Mapping[str, Any]) -> dict[str, Any]:
        if payload.get("action") == "search_hardness_targets":
            return self.search_hardness_targets(payload)
        return super().execute_query(payload)

    def _selected_target(
        self,
        *,
        target_entry_id: str,
        target_evidence_id: str,
        target_declaration: str,
    ) -> tuple[HardnessTargetCatalogEntry, HardnessTargetEvidence]:
        entry = self.retrieved_hardness_targets.get(target_entry_id)
        if entry is None:
            raise InputPlanningError(
                "hardness_target_not_retrieved",
                "模型选择的 hardness 目标没有由本会话 search_hardness_targets 返回。",
            )
        if entry.target_declaration != target_declaration:
            raise InputPlanningError(
                "hardness_target_selection_mismatch",
                "模型提交的 target_declaration 与所选 target_entry_id 不一致。",
            )
        evidence = self.retrieved_target_evidences.get(target_evidence_id)
        if evidence is None:
            raise InputPlanningError(
                "target_evidence_not_retrieved",
                "模型选择的目标证据没有由本会话 search_hardness_targets 返回。",
            )
        if evidence not in entry.evidences:
            raise InputPlanningError(
                "target_evidence_endpoint_mismatch",
                "模型选择的证据不属于所选 hardness 目标的 Lean endpoint。",
            )
        if not self._evidence_satisfies_request(evidence):
            raise InputPlanningError(
                "target_evidence_policy_mismatch",
                "模型选择的 Lean 目标证据不满足请求的 Native 政策、证据种类或依赖限制。",
            )
        return entry, evidence

    def _validate_open_topology(
        self,
        *,
        match: ProblemMatch,
        connection: ConnectionCatalogEntry | None,
        reductions: Sequence[TypedInventoryEntry],
        target: HardnessTargetCatalogEntry,
        evidence: HardnessTargetEvidence,
    ) -> None:
        current = match.route_source_node_id
        path_nodes = [current]
        if connection is not None:
            input_node = self.observation.normalized_problem_node_id or ""
            if connection.source_node_id != input_node:
                raise InputPlanningError(
                    "connection_wrong_start",
                    "所选输入连接没有从真实输入的 Lean node 开始。",
                )
            if connection.target_node_id != match.route_source_node_id:
                raise InputPlanningError(
                    "connection_wrong_target",
                    "所选输入连接没有到达 ProblemMatch 记录的路线源 node。",
                )
            path_nodes = [input_node, current]
        if current != match.candidate_node_id:
            raise InputPlanningError(
                "connection_wrong_target",
                "ProblemMatch 的路线源与模型所选库问题的 Lean node 不一致。",
            )
        for reduction in reductions:
            if reduction.source_node_id != current:
                raise InputPlanningError(
                    "reduction_path_disconnected",
                    "模型提交的有序归约中存在 Lean endpoint 无法连接的相邻边。",
                )
            current = reduction.target_node_id
            path_nodes.append(current)
        if current != target.target_node_id:
            raise InputPlanningError(
                "reduction_path_does_not_reach_selected_target",
                "模型路线结束后没有到达它从 search_hardness_targets 选择的目标 node。",
            )
        atom_count = len(reductions) + (1 if connection is not None else 0)
        if atom_count > self.request_policy.maximum_route_atoms:
            raise InputPlanningError(
                "selected_path_too_long",
                "模型选择的路线超过请求公开声明的最大归约边数。",
            )
        if atom_count < self.request_policy.minimum_route_atoms:
            missing_atoms = self.request_policy.minimum_route_atoms - atom_count
            raise InputPlanningError(
                "selected_path_too_short",
                f"模型实际提交了 {atom_count} 条归约边，但请求至少需要 "
                f"{self.request_policy.minimum_route_atoms} 条，当前还缺少至少 "
                f"{missing_atoms} 条。route atom 指有向归约 edge：非空输入连接算一条，"
                "reduction_declarations 中每个声明各算一条；它不是路径 endpoint/node "
                "的数量。请继续调用 search_reductions 检索，并加入足够的、Lean endpoint "
                "连续的额外边后再提交 finish；新路线仍须满足最大边数和 simple-path 要求，"
                "不要原样重复当前 finish。",
            )
        if atom_count == 0 and not self.request_policy.allow_reflexive_target:
            raise InputPlanningError(
                "reflexive_target_forbidden",
                "请求明确禁止零边的 reflexive target，但模型选择了输入自身。",
            )
        if self.request_policy.require_simple_path and len(path_nodes) != len(
            set(path_nodes)
        ):
            raise InputPlanningError(
                "selected_path_not_simple",
                "请求要求 simple path，但模型选择的路线重复经过同一个 Lean endpoint。",
            )
        dependencies = set(evidence.provenance_declarations)
        dependencies.update(reduction.declaration for reduction in reductions)
        if connection is not None:
            dependencies.add(connection.certificate_declaration)
            dependencies.add(connection.projection_declaration)
        if len(dependencies) > self.request_policy.maximum_dependencies:
            raise InputPlanningError(
                "selected_dependencies_exceed_limit",
                "模型选择的目标证据与路线合计超过请求允许的唯一 Lean 依赖数。",
            )

    def _build_open_plan(
        self,
        *,
        match: ProblemMatch,
        candidate: ProblemCatalogEntry,
        connection: ConnectionCatalogEntry | None,
        reductions: Sequence[TypedInventoryEntry],
        target: HardnessTargetCatalogEntry,
        evidence: HardnessTargetEvidence,
        lean_term: str,
        explanation: str,
    ) -> HardnessPlan:
        steps: list[dict[str, Any]] = []
        if connection is None:
            if self.predicate_input:
                steps.append(
                    {
                        "schema_version": PLAN_STEP_SCHEMA,
                        "step_id": "s1",
                        "action_kind": "select.existing_problem_presentation",
                        "output_handles": ["matched_problem"],
                        "parameters": {
                            "problem_declaration": candidate.declaration,
                            "problem_match_id": match.match_id,
                            "problem_node_id": match.route_source_node_id,
                            "relation": match.relation,
                        },
                    }
                )
            else:
                steps.append(
                    {
                        "schema_version": PLAN_STEP_SCHEMA,
                        "step_id": "s1",
                        "action_kind": "reuse.exact_endpoint",
                        "output_handles": ["matched_problem"],
                        "parameters": {
                            "input_declaration": self.observation.input_declaration,
                            "problem_declaration": candidate.declaration,
                            "problem_match_id": match.match_id,
                            "problem_node_id": candidate.problem_node_id,
                        },
                    }
                )
        else:
            steps.append(
                {
                    "schema_version": PLAN_STEP_SCHEMA,
                    "step_id": "s1",
                    "action_kind": RELATION_ACTION_KIND[connection.relation],
                    "capability_kind": connection.capability_kind,
                    "declaration": connection.certificate_declaration,
                    "output_handles": ["matched_problem"],
                    "role": connection.component_role,
                    "source_fingerprint": connection.source_fingerprint,
                    "target_fingerprint": connection.target_fingerprint,
                    "parameters": {
                        "connection_entry_id": connection.entry_id,
                        "projection_declaration": connection.projection_declaration,
                        "executable_lean_term": connection.lean_term,
                        "relation": connection.relation,
                        "problem_match_id": match.match_id,
                    },
                }
            )
        steps.append(
            {
                "schema_version": PLAN_STEP_SCHEMA,
                "step_id": "s2",
                "action_kind": "select.existing_hardness_target",
                "depends_on": ["s1"],
                "output_handles": ["selected_target"],
                "parameters": {
                    "selection_policy": "model_open_target",
                    "target_catalog_id": self.target_catalog.catalog_id,
                    "target_entry_id": target.target_entry_id,
                    "target_evidence_id": evidence.evidence_id,
                    "target_declaration": target.target_declaration,
                    "target_node_id": target.target_node_id,
                    "requested_property": self.request_policy.required_hardness,
                    "evidence_kind": evidence.evidence_kind,
                    "evidence_declaration": evidence.evidence_declaration,
                },
            }
        )
        previous = "s2"
        for index, reduction in enumerate(reductions, start=3):
            step_id = f"s{index}"
            steps.append(
                {
                    "schema_version": PLAN_STEP_SCHEMA,
                    "step_id": step_id,
                    "action_kind": "reuse.certified_reduction",
                    "capability_kind": "certified_reduction",
                    "declaration": reduction.declaration,
                    "depends_on": [previous],
                    "role": reduction.component_role,
                    "source_fingerprint": reduction.source_fingerprint,
                    "target_fingerprint": reduction.target_fingerprint,
                    "parameters": {"catalog_entry_id": reduction.entry_id},
                }
            )
            previous = step_id
        emit_id = f"s{len(steps) + 1}"
        source_declaration = match.route_source_declaration
        expected_type = (
            "ComplexityReduction.Certificate.CertifiedPath "
            f"{source_declaration} {target.target_declaration}"
        )
        steps.append(
            {
                "schema_version": PLAN_STEP_SCHEMA,
                "step_id": emit_id,
                "action_kind": "emit.certified_path",
                "depends_on": [previous],
                "expected_type": expected_type,
            }
        )
        target_evidence = {
            **evidence.to_dict(),
            "target_catalog_id": self.target_catalog.catalog_id,
            "target_entry_id": target.target_entry_id,
            "selection_policy": "model_open_target",
            "requested_hardness": self.request_policy.required_hardness,
            "allowed_target_evidence": list(
                self.request_policy.allowed_target_evidence
            ),
            "policy_satisfied": True,
        }
        payload = {
            "schema_version": PLAN_SCHEMA,
            "objective": self.request_policy.objective,
            "source_declaration": source_declaration,
            "target_declaration": target.target_declaration,
            "registry_fingerprint": self.problem_catalog.registry_fingerprint,
            "catalog_id": self.reduction_catalog.catalog_id,
            "problem_catalog_id": self.problem_catalog.catalog_id,
            "connection_catalog_id": self.connection_catalog.catalog_id,
            "matched_problem_declaration": candidate.declaration,
            "problem_match": match.to_dict(),
            "target_evidence": target_evidence,
            "metadata": {
                "input_observation_id": self.observation.observation_id,
                "input_kind": self.observation.input_kind,
                "model_explanation": explanation,
                "query_rounds_used": self.query_rounds_used,
                "open_target_request": self.request_policy.to_dict(),
            },
            "steps": steps,
            "outputs": [
                {
                    "schema_version": PLAN_OUTPUT_SCHEMA,
                    "output_id": "selected_path",
                    "output_kind": "lean.term",
                    "producer_steps": [step["step_id"] for step in steps],
                    "expected_type": expected_type,
                    "lean_code": lean_term,
                    "metadata": {
                        "connection_entry_id": (
                            connection.entry_id if connection is not None else None
                        ),
                        "reduction_declarations": [
                            reduction.declaration for reduction in reductions
                        ],
                        "target_entry_id": target.target_entry_id,
                        "target_evidence_id": evidence.evidence_id,
                    },
                }
            ],
        }
        return parse_hardness_plan(payload)

    def finish(self, payload: Mapping[str, Any]) -> ObservedInputPlannerResult:
        matched_problem = _required_open_target_problem_selector(
            payload, failure_code="invalid_model_finish"
        )
        relation = _required_string(payload, "match_relation")
        target_entry_id = _required_string(payload, "target_entry_id")
        target_evidence_id = _required_string(payload, "target_evidence_id")
        target_declaration = _required_string(payload, "target_declaration")
        lean_term = _required_string(payload, "lean_term")
        explanation = _required_string(payload, "explanation")[:2000]
        reductions = _string_list(payload, "reduction_declarations")
        connection_id = _optional_open_target_connection_id(
            payload, failure_code="invalid_model_finish"
        )
        candidate = self._selected_problem(matched_problem)
        if relation in {"exact_defeq", "accepts_exact_defeq"} and connection_id is not None:
            raise InputPlanningError(
                "unexpected_connection_for_exact_match",
                "exact 问题匹配的 connection_entry_id 必须表示缺省；推荐"
                " JSON null，空或纯空白字符串也会按缺省处理。",
            )
        connection = self._selected_connection(connection_id)
        match = self._problem_match(
            candidate=candidate,
            relation=relation,
            connection=connection,
        )
        target, evidence = self._selected_target(
            target_entry_id=target_entry_id,
            target_evidence_id=target_evidence_id,
            target_declaration=target_declaration,
        )
        selected_reductions = self._selected_reductions(reductions)
        self._validate_open_topology(
            match=match,
            connection=connection,
            reductions=selected_reductions,
            target=target,
            evidence=evidence,
        )
        self.target_observation = _TargetObservationProxy(
            target.target_declaration, target.target_node_id
        )
        checked_term = self._validate_lean_term(
            lean_term=lean_term,
            candidate=candidate,
            connection=connection,
            reductions=selected_reductions,
        )
        plan = self._build_open_plan(
            match=match,
            candidate=candidate,
            connection=connection,
            reductions=selected_reductions,
            target=target,
            evidence=evidence,
            lean_term=checked_term,
            explanation=explanation,
        )
        self.trace.append(
            {
                "action": "finish",
                "status": "accepted",
                "plan_id": plan.plan_id,
                "target_entry_id": target.target_entry_id,
                "target_evidence_id": evidence.evidence_id,
            }
        )
        return ObservedInputPlannerResult(
            plan=plan,
            lean_term=checked_term,
            problem_match=match,
            selected_connection=connection,
            reduction_declarations=tuple(
                reduction.declaration for reduction in selected_reductions
            ),
            explanation=explanation,
            query_trace=tuple(self.trace),
        )

    def stop(self, payload: Mapping[str, Any]) -> ObservedInputPlannerResult:
        failure_code = payload.get("failure_code")
        explanation = payload.get("explanation")
        if not isinstance(failure_code, str) or not failure_code.strip():
            raise InputPlanningError(
                "invalid_model_stop", "模型的 stop 回答必须包含稳定 failure_code。"
            )
        if not isinstance(explanation, str) or not explanation.strip():
            raise InputPlanningError(
                "invalid_model_stop", "模型的 stop 回答必须包含具体自然语言说明。"
            )
        failure_code = failure_code.strip()
        model_explanation = explanation.strip()[:2000]
        if self.predicate_input and failure_code in {
            "predicate_accepts_not_definitionally_equal",
            "ambiguous_predicate_presentation",
            "predicate_has_no_lawful_presentation",
        }:
            return super().stop(payload)
        if failure_code == "no_lean_verified_problem_match":
            return super().stop(payload)
        if failure_code == "no_eligible_hardness_target":
            if not self.target_search_performed:
                raise InputPlanningError(
                    "model_stop_not_auditable",
                    "模型尚未调用 search_hardness_targets，不能断言没有满足政策的目标。",
                )
            if self.request_policy.required_hardness not in (
                self.queried_hardness_target_policies
            ):
                raise InputPlanningError(
                    "model_stop_not_auditable",
                    "模型没有按请求的 Native 政策查询目标目录。",
                )
            if self._eligible_target_evidences():
                raise InputPlanningError(
                    "model_stop_contradicted_by_catalog",
                    "同一 Lean 指纹的目标目录仍包含满足政策、证据种类和依赖限制的目标。",
                )
            accepted = (
                "Lean 导出的 hardness 目标目录中没有任何证据同时满足请求的 Native 政策、"
                "允许的证据种类和依赖上限；这与存在目标但无路线是不同的阻塞。"
                f" 模型说明：{model_explanation}"
            )
            self.trace.append(
                {"action": "stop", "status": "accepted", "failure_code": failure_code}
            )
            return ObservedInputPlannerResult(
                plan=None,
                lean_term=None,
                problem_match=None,
                selected_connection=None,
                reduction_declarations=(),
                explanation=accepted,
                failure_code=failure_code,
                query_trace=tuple(self.trace),
            )
        if failure_code == "eligible_target_has_no_existing_route":
            if not self.target_search_performed:
                raise InputPlanningError(
                    "model_stop_not_auditable",
                    "模型没有先查询 Lean 验证的 hardness 目标。",
                )
            if self.request_policy.required_hardness not in (
                self.queried_hardness_target_policies
            ):
                raise InputPlanningError(
                    "model_stop_not_auditable",
                    "模型没有按本请求的 Native 政策查询 hardness 目标，因此任意其他"
                    "目标查询不能支撑无路线结论。",
                )
            if not self.required_policy_visible_evidence_ids:
                raise InputPlanningError(
                    "model_stop_not_auditable",
                    "按本请求政策执行的目标查询尚未返回任何可见且满足证据种类与依赖"
                    "上限的证据，不能断言是有合格目标但无路线。",
                )
            relation = payload.get("match_relation")
            matched_problem = _required_open_target_problem_selector(
                payload, failure_code="invalid_model_stop"
            )
            if not isinstance(relation, str) or not relation.strip():
                raise InputPlanningError(
                    "invalid_model_stop", "无路线 stop 必须说明输入问题匹配关系。"
                )
            candidate = self._selected_problem(matched_problem)
            connection_id = _optional_open_target_connection_id(
                payload, failure_code="invalid_model_stop"
            )
            connection = self._selected_connection(connection_id)
            match = self._problem_match(
                candidate=candidate,
                relation=relation.strip(),
                connection=connection,
            )
            current = match.route_source_node_id
            if connection is not None:
                input_node = self.observation.normalized_problem_node_id or ""
                if connection.source_node_id != input_node:
                    raise InputPlanningError(
                        "connection_wrong_start",
                        "所选输入连接没有从真实输入 node 开始。",
                    )
                if connection.target_node_id != match.route_source_node_id:
                    raise InputPlanningError(
                        "connection_wrong_target",
                        "所选输入连接没有到达 ProblemMatch 记录的路线源 node。",
                    )
            if current != match.candidate_node_id:
                raise InputPlanningError(
                    "connection_wrong_target",
                    "ProblemMatch 的路线源与所选库问题 node 不一致。",
                )
            if (
                current not in self.queried_reduction_source_node_ids
                and not self._complete_source_frontier_retrieved_via_connections(
                    current
                )
            ):
                raise InputPlanningError(
                    "model_stop_not_auditable",
                    "模型尚未从已确认问题 node 查询 search_reductions，且 "
                    "search_connections 也未返回该 node 的完整直接归约前沿。",
                )
            eligible = self._eligible_target_evidences()
            if not eligible:
                raise InputPlanningError(
                    "wrong_model_stop_category",
                    "当前阻塞是没有满足政策的目标，应使用 no_eligible_hardness_target。",
                )
            if any(
                self._has_allowed_route(
                    source_node=current,
                    target_node=entry.target_node_id,
                    evidence=evidence,
                    connection=connection,
                )
                for entry, evidence in eligible
            ):
                raise InputPlanningError(
                    "model_stop_contradicted_by_catalog",
                    "至少一个政策合格目标仍存在满足方向、长度和依赖限制的已有前向路线。",
                )
            reverse_exists = any(
                self._shortest_route_length(entry.target_node_id, current) is not None
                for entry, _ in eligible
            )
            direction = (
                "目录中存在从合格目标到输入问题的相反方向路径，但单向归约不能反用。"
                if reverse_exists
                else "目录中也没有从合格目标到输入的反向路径。"
            )
            accepted = (
                "Lean 目录中存在满足证书政策的 hardness 目标，但当前注册归约图没有任何"
                "符合方向、路线长度和依赖限制的输入到目标路径。"
                f"{direction}继续需要库中已有方向正确的归约。模型说明：{model_explanation}"
            )
            self.trace.append(
                {"action": "stop", "status": "accepted", "failure_code": failure_code}
            )
            return ObservedInputPlannerResult(
                plan=None,
                lean_term=None,
                problem_match=match,
                selected_connection=connection,
                reduction_declarations=(),
                explanation=accepted,
                failure_code=failure_code,
                query_trace=tuple(self.trace),
            )
        raise InputPlanningError(
            "invalid_model_stop",
            "开放目标协议只允许 no_lean_verified_problem_match、"
            "no_eligible_hardness_target 或 eligible_target_has_no_existing_route。",
        )

    def prompt_payload(self) -> dict[str, Any]:
        input_node = self.observation.normalized_problem_node_id or ""
        lookup_node = self._input_lookup_node_id()
        problem_hints = build_initial_problem_hints(
            self.problem_catalog,
            input_node_id=input_node,
            observation=self.observation,
        )
        if self.predicate_input:
            connection_hints: dict[str, Any] = {
                "contains_declaration_names": False,
                "input_node_id": lookup_node,
                "deferred": True,
                "raw_predicate_connection_forbidden": True,
                "reason": (
                    "A raw predicate is not a PresentedProblem endpoint. Query the "
                    "accepts/domain indexes and use only a Lean-confirmed "
                    "accepts_exact_defeq presentation with a null connection ID."
                ),
                "full_connection_catalog_included": False,
            }
        elif problem_hints["exact_candidate_count"]:
            connection_hints = {
                "contains_declaration_names": False,
                "input_node_id": input_node,
                "deferred": True,
                "reason": (
                    "An exact-node problem candidate exists; retrieve it with "
                    "search_problems and use exact_defeq with a null connection ID."
                ),
                "full_connection_catalog_included": False,
            }
        else:
            connection_hints = build_initial_connection_hints(
                self.connection_catalog, input_node_id=input_node
            )
        path_source = self._prompt_path_source_declaration()
        transported_target_provenance = any(
            evidence.evidence_kind
            in {
                "transported_native_hardness",
                "transported_native_completeness",
            }
            for entry in self.target_catalog.entries
            for evidence in entry.evidences
        )
        if self.predicate_input:
            problem_search_option = {
                "action": "search_problems",
                "searches": [
                    {
                        "accepts_node_ids": [self.observation.predicate_node_id],
                        "domain_node_ids": [
                            self.observation.predicate_domain_node_id
                        ],
                        "limit": 8,
                    },
                    {
                        "domain_node_ids": [
                            self.observation.predicate_domain_node_id
                        ],
                        "limit": 8,
                    },
                ],
            }
            predicate_workflow_rules = [
                (
                    "For a predicate input, first call search_problems with both the "
                    "predicate node as accepts_node_ids and its domain node; include a "
                    "second domain-only search in the same action so an empty exact "
                    "match can be classified without guessing from the carrier."
                ),
                (
                    "Choose only a returned problem row with accepts_exact_defeq=true. "
                    "Use match_relation=accepts_exact_defeq, JSON null for "
                    "connection_entry_id, and start every reduction query and Lean "
                    "CertifiedPath at that row's problem_node_id/declaration. Never use "
                    "the raw predicate as a CertifiedPath source."
                ),
                (
                    "If exact predicate rows span multiple codec_group_id values, stop "
                    "with ambiguous_predicate_presentation. If no exact row exists but "
                    "domain candidates exist, use predicate_accepts_not_definitionally_equal. "
                    "If neither exists, use predicate_has_no_lawful_presentation."
                ),
            ]
            stop_failure_codes = [
                "predicate_accepts_not_definitionally_equal",
                "ambiguous_predicate_presentation",
                "predicate_has_no_lawful_presentation",
                "no_eligible_hardness_target",
                "eligible_target_has_no_existing_route",
            ]
        else:
            problem_search_option = {
                "action": "search_problems",
                "searches": [{"node_ids": [input_node], "limit": 8}],
            }
            predicate_workflow_rules = [
                "Retrieve an exact input problem with search_problems using the input node."
            ]
            stop_failure_codes = [
                "no_lean_verified_problem_match",
                "no_eligible_hardness_target",
                "eligible_target_has_no_existing_route",
            ]
        retrieved: dict[str, Any] = {
            "problems": [
                problem_search_result(
                    entry,
                    input_node_id=input_node,
                    observation=self.observation,
                )
                for entry in self.retrieved_problems.values()
            ],
            "connections": [
                connection_search_result(entry)
                for entry in self.retrieved_connections.values()
            ],
            "hardness_targets": [
                self._render_retrieved_target(entry)
                for entry in self.retrieved_hardness_targets.values()
            ],
            "reductions": [
                entry_summary(entry)
                for entry in self.retrieved_reductions.values()
            ],
        }
        compact_view = (
            self.request_policy.objective == "reduce_to_known_hardness"
        )
        terminal_route_atom_counts = (
            self._retrieved_finish_route_atom_counts() if compact_view else ()
        )
        terminal_stop_guidance = (
            self._terminal_stop_guidance() if compact_view else None
        )
        frontier_guidance = self._frontier_guidance() if compact_view else None
        if compact_view:
            retrieved = compact_retrieved_payload(retrieved)
        payload = {
            "task": "identify_input_and_select_evidence_backed_hardness_target",
            "expected_lean_type_template": (
                "ComplexityReduction.Certificate.CertifiedPath "
                f"{path_source} <selected target declaration>"
            ),
            "request": {
                "objective": self.request_policy.objective,
                "direction": "source_to_target",
                **self.request_policy.to_dict(),
            },
            "input_observation": {
                "input_module": self.observation.input_module,
                "input_declaration": self.observation.input_declaration,
                "input_kind": self.observation.input_kind,
                "elaborated_type": self.observation.elaborated_type,
                "normalized_problem_node_id": input_node,
                "predicate_node_id": self.observation.predicate_node_id,
                "predicate_domain": self.observation.predicate_domain,
                "predicate_domain_node_id": self.observation.predicate_domain_node_id,
                "predicate_summary": self.observation.predicate_summary,
                "referenced_constants": list(self.observation.referenced_constants),
                "semantic_summary": self.observation.semantic_summary,
                "representation_summary": self.observation.representation_summary,
                "accepts_summary": self.observation.accepts_summary,
            },
            "catalog_view": {
                "mode": self.reduction_catalog.mode,
                "catalog_id": self.reduction_catalog.catalog_id,
                "visible_reduction_count": len(self.reduction_catalog.entries),
                "target_catalog_id": self.target_catalog.catalog_id,
                "same_registry_fingerprint": True,
                "all_reductions_remain_queryable": True,
            },
            "problem_hints": problem_hints,
            "connection_hints": connection_hints,
            "hardness_target_hints": build_initial_hardness_target_hints(
                self.target_catalog
            ),
            "library_architecture": build_library_architecture(
                self.reduction_catalog
            ),
            "query_budget": {
                "used": self.query_rounds_used,
                "maximum": self.maximum_query_rounds,
                "remaining": self.maximum_query_rounds - self.query_rounds_used,
            },
            "query_history": self.query_history(),
            "protocol_feedback": list(self.protocol_feedback[-3:]),
            "retrieved": retrieved,
            "lean_path_api": {
                "zero_edges": (
                    "ComplexityReduction.Certificate.CertifiedPath.refl "
                    f"{path_source}"
                ),
                "one_edge": "ComplexityReduction.Certificate.CertifiedPath.step reduction",
                "append_edge": (
                    "ComplexityReduction.Certificate.CertifiedPath.cons priorPath reduction"
                ),
                "term_only": True,
            },
            "workflow_rules": [
                *predicate_workflow_rules,
                (
                    "For matched_problem, use either the exact entry_id/declaration "
                    "string from one retrieved problem row, or that retrieved result "
                    "object. If an object contains both selectors, they must identify "
                    "the same row; other echoed fields are not trusted."
                ),
                *(
                    [
                        (
                            "retrieved uses an authorization-complete compact view. "
                            "Verbose displays and complete evidence Lean terms remain "
                            "in Agent state; declarations, stable IDs, codec facts, "
                            "policy decisions, dependency provenance, and directed "
                            "Lean endpoint nodes shown here are complete for selection."
                        )
                    ]
                    if compact_view
                    else []
                ),
                (
                    "For an exact_defeq or accepts_exact_defeq problem match, use JSON null for "
                    "connection_entry_id. An empty or whitespace-only string is treated "
                    "as absent for compatibility; any non-empty value must be an exact "
                    "retrieved connection entry_id."
                ),
                (
                    "Call search_hardness_targets with required_policies containing the "
                    "request.required_hardness value."
                ),
                (
                    "Choose only an evidence row marked request_eligible=true; copy both "
                    "target_entry_id and evidence_id exactly."
                ),
                (
                    (
                        "Transported target evidence may expose the provenance of its own "
                        "hardness proof. It does not authorize the input-to-target route: "
                        "retrieve every selected source-path edge with search_reductions."
                    )
                    if transported_target_provenance
                    else (
                        "Use reachability and shortest length only to choose a target; route "
                        "declarations are intentionally absent, so retrieve every edge with "
                        "search_reductions."
                    )
                ),
                (
                    "The submitted path must contain between request.minimum_route_atoms "
                    "and request.maximum_route_atoms inclusive; when require_simple_path "
                    "is true, do not repeat a Lean endpoint."
                ),
                (
                    "For multi-edge routes, expand outgoing reductions from every returned "
                    "frontier node until a connected target path is retrieved or absence is "
                    "auditable."
                ),
                *(
                    [
                        (
                            "frontier_guidance lists only already retrieved endpoint "
                            "nodes plus declaration-free outgoing counts. When it has "
                            "suggested_searches and no terminal guidance is present, prefer "
                            "one batched source-only search action over repeating a prior "
                            "target-filtered or identical query."
                        ),
                        (
                            "When terminal_guidance.mode is finish_now, Agent graph checks "
                            "have confirmed that at least one policy-compliant simple path "
                            "within the public atom range is fully present in retrieved. "
                            "Choose the problem, target evidence, and route yourself, then "
                            "return finish immediately without another search."
                        ),
                        (
                            "When terminal_guidance.mode is stop_now, the documented "
                            "same-fingerprint absence check is already auditable. Return "
                            "stop immediately with its exact failure_code and required "
                            "selector fields; do not spend another query round."
                        )
                    ]
                    if compact_view
                    else []
                ),
            ],
            "response_options": {
                "field_contracts": {
                    "matched_problem": (
                        "non-empty exact entry_id/declaration string, or an object "
                        "containing entry_id and/or declaration from one retrieved row; "
                        "both selectors must resolve to that same row"
                    ),
                    "connection_entry_id": (
                        "JSON null is recommended when absent; empty or whitespace-only "
                        "string is normalized to null, while a non-empty value must be "
                        "an exact entry_id from retrieved connections"
                    ),
                },
                "search_problems": {
                    **problem_search_option,
                },
                "search_connections": {
                    "action": "search_connections",
                    "searches": [{"source_node_ids": [lookup_node], "limit": 8}],
                },
                "search_hardness_targets": {
                    "action": "search_hardness_targets",
                    "searches": [
                        {
                            "required_policies": [
                                self.request_policy.required_hardness
                            ],
                            "limit": 8,
                        }
                    ],
                },
                "search_reductions": {
                    "action": "search_reductions",
                    "searches": [
                        {
                            "source_node_ids": ["current path node"],
                            "target_node_ids": ["optional selected target node"],
                            "limit": 8,
                        }
                    ],
                },
                "finish": {
                    "action_literal": "finish",
                    "required_fields": [
                        "action",
                        "matched_problem",
                        "match_relation",
                        "connection_entry_id",
                        "target_entry_id",
                        "target_evidence_id",
                        "target_declaration",
                        "reduction_declarations",
                        "lean_term",
                        "explanation",
                    ],
                },
                "stop": {
                    "action_literal": "stop",
                    "failure_codes": [
                        *stop_failure_codes,
                    ],
                    "no_route_requires": [
                        "matched_problem",
                        "match_relation",
                        "connection_entry_id",
                    ],
                },
            },
            "constraints": {
                "llm_selects_problem_target_evidence_and_route": True,
                "all_selected_facts_must_have_been_retrieved": True,
                "full_catalogs_are_not_included": True,
                "full_target_catalog_included": False,
                "target_routes_are_not_included": not transported_target_provenance,
                "target_evidence_transport_provenance_may_be_included": (
                    transported_target_provenance
                ),
                "input_route_is_not_preselected": True,
                "new_mathematical_reductions_forbidden": True,
                "raw_predicate_is_not_a_path_source": self.predicate_input,
                "lean_runs_only_after_all_model_tasks_finish": True,
            },
        }
        if compact_view:
            payload["retrieved_view"] = compact_retrieved_view_metadata(retrieved)
            payload["frontier_guidance"] = frontier_guidance
        if terminal_route_atom_counts:
            payload["terminal_guidance"] = {
                "mode": "finish_now",
                "available_route_atom_counts": list(terminal_route_atom_counts),
                "route_and_target_remain_model_selected": True,
                "instruction": (
                    "A compliant route is fully retrieved. Return finish now; do not "
                    "issue another search or re-derive the full graph."
                ),
            }
        elif terminal_stop_guidance is not None:
            payload["terminal_guidance"] = terminal_stop_guidance
        return payload

    def _render_retrieved_target(
        self, entry: HardnessTargetCatalogEntry
    ) -> dict[str, Any]:
        result = hardness_target_search_result(entry)
        route_length = self._shortest_route_length_from_input(entry.target_node_id)
        evidences = []
        for raw in result["evidences"]:
            item = self._decorate_target_evidence(
                entry=entry,
                evidence_raw=raw,
            )
            if item is not None:
                evidences.append(item)
        policy_route_atom_counts = [
            int(item["shortest_policy_route_atom_count"])
            for item in evidences
            if item.get("policy_route_allowed") is True
        ]
        result.update(
            {
                "evidences": evidences,
                "request_eligible_evidence_count": sum(
                    bool(item.get("request_eligible")) for item in evidences
                ),
                "reachable_from_input": route_length is not None,
                "shortest_route_length_from_input": route_length,
                "within_route_atom_limit": route_length is not None
                and route_length <= self.request_policy.maximum_route_atoms,
                "policy_route_allowed": bool(policy_route_atom_counts),
                "shortest_policy_route_atom_count": (
                    min(policy_route_atom_counts)
                    if policy_route_atom_counts
                    else None
                ),
                "route_declarations_included": any(
                    item.get("evidence_kind")
                    in {
                        "transported_native_hardness",
                        "transported_native_completeness",
                    }
                    for item in evidences
                ),
            }
        )
        return result

    def build_prompt(self) -> str:
        payload = self.prompt_payload()
        audit_open_target_prompt(payload)
        frontier_errors = frontier_guidance_errors(payload)
        if frontier_errors:
            raise ValueError(
                "frontier guidance failed its no-oracle contract: "
                + "; ".join(frontier_errors)
            )
        if self.predicate_input:
            audit_predicate_input_prompt(payload)
        return json.dumps(
            payload,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )


def generate_lean_path_to_open_target(
    *,
    observation: LeanInputObservation,
    problem_catalog: ProblemCatalog,
    connection_catalog: ConnectionCatalog,
    reduction_catalog: TypedCatalog,
    target_catalog: HardnessTargetCatalog,
    request_policy: OpenTargetRequestPolicy,
    client: DeepSeekClient,
    maximum_query_rounds: int = MAX_OPEN_TARGET_QUERY_ROUNDS,
    maximum_model_turns: int = MAX_OPEN_TARGET_MODEL_TURNS,
) -> ObservedInputPlannerResult:
    """Run the open-target protocol without invoking Lean between model turns."""

    if not 1 <= maximum_model_turns <= MAX_OPEN_TARGET_MODEL_TURNS:
        raise ValueError(
            "maximum_model_turns must be in "
            f"1..{MAX_OPEN_TARGET_MODEL_TURNS}"
        )

    try:
        session = OpenTargetPlanningSession(
            observation=observation,
            problem_catalog=problem_catalog,
            connection_catalog=connection_catalog,
            reduction_catalog=reduction_catalog,
            target_catalog=target_catalog,
            request_policy=request_policy,
            maximum_query_rounds=maximum_query_rounds,
        )
    except (InputPlanningError, ValueError) as error:
        if isinstance(error, InputPlanningError):
            code = error.failure_code
            explanation = error.explanation
        else:
            code = "invalid_open_target_request"
            explanation = str(error)
        return ObservedInputPlannerResult(
            plan=None,
            lean_term=None,
            problem_match=None,
            selected_connection=None,
            reduction_declarations=(),
            explanation=explanation,
            failure_code=code,
        )
    prompts: list[str] = []
    responses: list[ModelResponse] = []
    for _ in range(maximum_model_turns):
        prompt = session.build_prompt()
        response = client.complete_json(
            system=OPEN_TARGET_SYSTEM_PROMPT,
            prompt=prompt,
        )
        prompts.append(prompt)
        responses.append(response)
        if not response.ok:
            return ObservedInputPlannerResult(
                plan=None,
                lean_term=None,
                problem_match=None,
                selected_connection=None,
                reduction_declarations=(),
                explanation=response.error or "模型 API 调用失败，未得到可处理回答。",
                failure_code="model_api_failure",
                model_prompts=tuple(prompts),
                model_responses=tuple(responses),
                query_trace=tuple(session.trace),
            )
        payload = extract_json_object(response.content)
        if payload is None:
            error = InputPlanningError(
                "invalid_model_json", "模型回答不是一个 JSON 对象。"
            )
            session.record_protocol_feedback(error)
            if len(session.protocol_feedback) >= session.maximum_protocol_feedback:
                return ObservedInputPlannerResult(
                    plan=None,
                    lean_term=None,
                    problem_match=None,
                    selected_connection=None,
                    reduction_declarations=(),
                    explanation=error.explanation,
                    failure_code=error.failure_code,
                    model_prompts=tuple(prompts),
                    model_responses=tuple(responses),
                    query_trace=tuple(session.trace),
                )
            continue
        payload = _normalize_open_target_action(payload)
        try:
            if payload.get("action") == "finish":
                result = session.finish(payload)
                return ObservedInputPlannerResult(
                    plan=result.plan,
                    lean_term=result.lean_term,
                    problem_match=result.problem_match,
                    selected_connection=result.selected_connection,
                    reduction_declarations=result.reduction_declarations,
                    explanation=result.explanation,
                    model_prompts=tuple(prompts),
                    model_responses=tuple(responses),
                    query_trace=tuple(session.trace),
                )
            if payload.get("action") == "stop":
                result = session.stop(payload)
                return ObservedInputPlannerResult(
                    plan=None,
                    lean_term=None,
                    problem_match=result.problem_match,
                    selected_connection=result.selected_connection,
                    reduction_declarations=(),
                    explanation=result.explanation,
                    failure_code=result.failure_code,
                    model_prompts=tuple(prompts),
                    model_responses=tuple(responses),
                    query_trace=tuple(session.trace),
                )
            session.execute_query(payload)
        except InputPlanningError as error:
            session.record_protocol_feedback(error)
            if len(session.protocol_feedback) >= session.maximum_protocol_feedback:
                return ObservedInputPlannerResult(
                    plan=None,
                    lean_term=None,
                    problem_match=None,
                    selected_connection=None,
                    reduction_declarations=(),
                    explanation=error.explanation,
                    failure_code=error.failure_code,
                    model_prompts=tuple(prompts),
                    model_responses=tuple(responses),
                    query_trace=tuple(session.trace),
                )
    return ObservedInputPlannerResult(
        plan=None,
        lean_term=None,
        problem_match=None,
        selected_connection=None,
        reduction_declarations=(),
        explanation="模型在开放目标协议的轮数上限内没有完成或给出可审计停止。",
        failure_code="model_turn_limit_exceeded",
        model_prompts=tuple(prompts),
        model_responses=tuple(responses),
        query_trace=tuple(session.trace),
    )
