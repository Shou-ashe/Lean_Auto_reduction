"""Stage-L multi-objective, model-driven Core reuse protocol.

This ABI is intentionally separate from the production fixed/open-target
prompts.  It keeps one bounded query vocabulary while making reduction,
membership, and completeness finish payloads mutually exclusive.  Python
checks provenance, exact endpoints, direction, and dependency budgets; Lean
remains the only proof authority and runs only after every case finishes.
"""

from __future__ import annotations

import json
import re
from collections import deque
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any

from .connection_catalog import (
    ConnectionCatalog,
    ConnectionCatalogEntry,
    build_initial_connection_hints,
    connection_search_result,
)
from .core_capability_catalog import (
    COMPLETENESS_MEMBERSHIP_PROJECTION,
    NATIVE_COMPLETENESS,
    NATIVE_MEMBERSHIP,
    CoreNativeEvidenceCatalog,
    CoreNativeEvidenceEntry,
    CoreReductionCatalog,
    CoreReductionEntry,
    core_reduction_search_result,
    native_evidence_search_result,
    search_core_reductions,
    search_native_evidence,
)
from .core_generalization import (
    CORE_GENERALIZATION_PROMPT_ABI,
    objective_finish_payload,
)
from .hardness_target_catalog import (
    HardnessTargetCatalog,
    HardnessTargetCatalogError,
    HardnessTargetCatalogEntry,
    HardnessTargetEvidence,
    HardnessTargetSearchError,
    build_initial_hardness_target_hints,
    hardness_target_search_result,
    parse_hardness_target_searches,
    search_hardness_targets,
)
from .input_observation import LeanInputObservation
from .input_planner import (
    FULL_DECLARATION_RE,
    STATIC_PATH_DECLARATIONS,
    InputPlanningError,
    ObservedInputPlannerResult,
    ObservedInputPlanningSession,
    _required_string,
)
from .model_client import DeepSeekClient, ModelResponse, extract_json_object
from .open_target import (
    PROMPT_FORBIDDEN_KEYS,
    _forbidden_key_paths,
)
from .open_target_planner import (
    _optional_open_target_connection_id,
    _required_open_target_problem_selector,
)
from .plan import (
    PLAN_OUTPUT_SCHEMA,
    PLAN_SCHEMA,
    PLAN_STEP_SCHEMA,
    HardnessPlan,
    parse_hardness_plan,
)
from .planner import BANNED_MODEL_TERM_RE, MAX_MODEL_LEAN_TERM_CHARS
from .problem_catalog import (
    ProblemCatalog,
    ProblemCatalogEntry,
    ProblemMatch,
    build_initial_problem_hints,
    predicate_exact_candidates,
    predicate_presentation_groups,
    problem_search_result,
)
from .retrieval import (
    RetrievalValidationError,
    build_library_architecture,
    parse_theorem_searches,
)


MAX_CORE_GENERALIZATION_QUERY_ROUNDS = 10
MAX_CORE_GENERALIZATION_MODEL_TURNS = 14
MAX_CORE_GENERALIZATION_PROTOCOL_FEEDBACK = 6
MAX_RETRIEVED_CORE_REDUCTIONS = 48
MAX_RETRIEVED_NATIVE_EVIDENCE = 20
MAX_RETRIEVED_HARDNESS_TARGETS = 20
CORE_GENERALIZATION_PROMPT_FORBIDDEN_KEYS = frozenset(
    key for key in PROMPT_FORBIDDEN_KEYS if key != "fixed_target"
) | frozenset(
    {
        "policy_route_allowed",
        "shortest_policy_route_atom_count",
    }
)

COMPLETENESS_TRANSPORT = (
    "ComplexityReduction.Certificate.CompletenessTransport.alongPath"
)

CORE_GENERALIZATION_SYSTEM_PROMPT = """You are solving one Stage-L Core-reuse
request against an already compiled Lean library. Each API turn is stateless,
so read query_history, retrieved rows, protocol_feedback, and any
terminal_guidance in the current prompt. Return exactly one JSON object.
Use only bounded search results. Never invent or reverse a capability, add new
mathematics, use sorry/admit/axioms/imports/commands/definitions, or submit a
proof category different from request.objective.

First identify the exact input problem with search_problems. Predicate inputs
must use a Lean-confirmed accepts_exact_defeq row and a null connection. For a
non-exact PresentedProblem match, only a returned directed search_connections
row may connect it. Use search_reductions for every path edge and copy its
entry_id; a reduction result row includes the exact executable Lean term and
all declarations that term authorizes. Connection rows and reduction rows are
distinct views: never copy a retrieved.connections entry_id into
reduction_entry_ids. If a retrieved connection is useful as a normal path
edge, first run the exact search_reductions request shown in
retrieval_guidance.connection_rows_requiring_reduction_search and copy the
returned retrieved.reductions entry_id. Every search action uses the key
"searches" with 1..4 objects. Keep each suggested reduction search as its own
object; merging several source_node_ids shares one result limit and can omit
needed outgoing edges. Use search_hardness_targets only for
open reduction objectives. A retrieved target evidence row's request_eligible
flag is only the public policy/dependency projection, not a route-existence
claim: if any row is true, do not stop with no_eligible_hardness_target. For a
transported target, its retrieved provenance declarations may be used as terms
in search_reductions to discover a possible suffix, but you must separately
retrieve and connect a forward path from the exact input. Use
search_native_evidence for exact NativeTMInNP and NativeTMNPComplete rows.
Prefer the bounded, non-authoritative searches in retrieval_guidance when they
remain unqueried; never repeat an identical reduction search.

The finish payload is objective-specific. Reduction requests submit a complete
CertifiedPath term. A non-empty path may start with CertifiedPath.step, or
equivalently append its first edge to CertifiedPath.refl with
CertifiedPath.cons; append later edges with CertifiedPath.cons. prove_in_np
submits only exact native membership evidence.
prove_np_complete submits exact hub completeness, a forward hub-to-target path,
exact target membership, and one CompletenessTransport.alongPath term. A
hardness path cannot replace target membership. For prove_np_complete, query
native_membership at the exact target node and query native_completeness with
no endpoint filter so all complete hubs remain visible. The selected reduction
path must run from a complete hub to the target; a target-to-hub Cook--Levin
edge has the wrong direction. If terminal_guidance says finish_now or stop_now,
follow it immediately. Lean is not run during this conversation; accepted
cases are checked together once at the end."""


@dataclass(frozen=True)
class CoreGeneralizationRequest:
    objective: str
    minimum_route_atoms: int
    maximum_route_atoms: int
    maximum_dependencies: int
    allow_reflexive_target: bool
    require_simple_path: bool
    required_hardness: str | None = None
    allowed_target_evidence: tuple[str, ...] = ()

    def __post_init__(self) -> None:
        if self.objective not in {
            "reduce_to",
            "reduce_to_known_np",
            "reduce_to_known_hardness",
            "prove_in_np",
            "prove_np_complete",
        }:
            raise ValueError("unsupported Stage-L objective")
        for label, value in (
            ("minimum_route_atoms", self.minimum_route_atoms),
            ("maximum_route_atoms", self.maximum_route_atoms),
            ("maximum_dependencies", self.maximum_dependencies),
        ):
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise ValueError(f"{label} must be a non-negative integer")
        if self.minimum_route_atoms > self.maximum_route_atoms:
            raise ValueError("minimum_route_atoms exceeds maximum_route_atoms")
        if self.objective in {"reduce_to_known_np", "reduce_to_known_hardness"}:
            if not self.required_hardness or not self.allowed_target_evidence:
                raise ValueError("open reduction objective requires target evidence policy")
        elif self.required_hardness is not None or self.allowed_target_evidence:
            raise ValueError("fixed/exact evidence objectives forbid target policy fields")

    @property
    def payload_kind(self) -> str:
        if self.objective == "prove_in_np":
            return "membership"
        if self.objective == "prove_np_complete":
            return "completeness"
        return "reduction"

    def to_dict(self) -> dict[str, Any]:
        return {
            "objective": self.objective,
            "payload_kind": self.payload_kind,
            "minimum_route_atoms": self.minimum_route_atoms,
            "maximum_route_atoms": self.maximum_route_atoms,
            "maximum_dependencies": self.maximum_dependencies,
            "allow_reflexive_target": self.allow_reflexive_target,
            "require_simple_path": self.require_simple_path,
            "required_hardness": self.required_hardness,
            "allowed_target_evidence": list(self.allowed_target_evidence),
        }


def audit_core_generalization_prompt(payload: Mapping[str, Any]) -> None:
    leaked = _forbidden_key_paths(
        payload,
        forbidden=CORE_GENERALIZATION_PROMPT_FORBIDDEN_KEYS,
    )
    if leaked:
        raise ValueError(
            "Core-generalization prompt contains benchmark answer fields: "
            + ", ".join(sorted(leaked))
        )
    if payload.get("schema_version") != CORE_GENERALIZATION_PROMPT_ABI:
        raise ValueError("Core-generalization prompt has the wrong ABI version")


def _compact(value: str) -> str:
    return re.sub(r"\s+", " ", value).strip()


def _string_list(payload: Mapping[str, Any], key: str) -> tuple[str, ...]:
    value = payload.get(key)
    if not isinstance(value, list) or any(
        not isinstance(item, str) or not item.strip() for item in value
    ):
        raise InputPlanningError(
            "invalid_model_finish", f"{key} must be a list of non-empty strings."
        )
    return tuple(item.strip() for item in value)


def _model_stop_explanation(
    payload: Mapping[str, Any],
    *,
    failure_code: str,
    terminal_guidance: Mapping[str, Any] | None,
) -> str:
    raw = payload.get("explanation")
    if isinstance(raw, str) and raw.strip():
        return raw.strip()[:2000]
    if (
        isinstance(terminal_guidance, Mapping)
        and terminal_guidance.get("mode") == "stop_now"
        and terminal_guidance.get("failure_code") == failure_code
    ):
        return "The model followed the exact Lean-audited terminal blocker."
    raise InputPlanningError(
        "invalid_model_stop",
        "A non-terminal stop response must include a brief explanation.",
    )


def _connection_reduction_retrieval_gaps(
    *,
    connections: Sequence[ConnectionCatalogEntry],
    reduction_catalog: CoreReductionCatalog,
    retrieved_reduction_ids: Sequence[str],
    preferred_source_nodes: Sequence[str] = (),
    limit: int = 8,
) -> tuple[dict[str, Any], ...]:
    """Expose exact searches for connection rows not yet retrieved as route rows."""

    def signature(entry: ConnectionCatalogEntry | CoreReductionEntry) -> tuple[str, ...]:
        return (
            entry.certificate_declaration,
            entry.lean_term,
            entry.source_node_id,
            entry.target_node_id,
        )

    catalog_by_signature = {
        signature(entry): entry for entry in reduction_catalog.entries
    }
    retrieved_ids = set(retrieved_reduction_ids)
    preferred = set(preferred_source_nodes)
    candidates: list[ConnectionCatalogEntry] = []
    for entry in connections:
        reduction = catalog_by_signature.get(signature(entry))
        if (
            entry.capability_kind == "certified_reduction"
            and reduction is not None
            and reduction.entry_id not in retrieved_ids
        ):
            candidates.append(entry)
    candidates.sort(
        key=lambda entry: (entry.source_node_id not in preferred, entry.entry_id)
    )
    return tuple(
        {
            "connection_entry_id": entry.entry_id,
            "source_node_id": entry.source_node_id,
            "target_node_id": entry.target_node_id,
            "lean_term": entry.lean_term,
            "usable_in_reduction_entry_ids": False,
            "required_search": {
                "action": "search_reductions",
                "searches": [{"terms": [entry.lean_term], "limit": 8}],
            },
        }
        for entry in candidates[:limit]
    )


def _normalize_action(payload: dict[str, Any]) -> dict[str, Any]:
    if isinstance(payload.get("action"), str):
        return payload
    candidates: list[dict[str, Any]] = []
    for action in (
        "inspect_architecture",
        "search_problems",
        "search_connections",
        "search_reductions",
        "search_hardness_targets",
        "search_native_evidence",
        "finish",
        "stop",
    ):
        nested = payload.get(action)
        if isinstance(nested, dict):
            candidate = dict(nested)
            candidate.setdefault("action", action)
            candidates.append(candidate)
    return candidates[0] if len(candidates) == 1 else payload


class CoreGeneralizationPlanningSession(ObservedInputPlanningSession):
    """One bounded Stage-L session for any Core objective."""

    def __init__(
        self,
        *,
        observation: LeanInputObservation,
        target_observation: LeanInputObservation | None,
        problem_catalog: ProblemCatalog,
        connection_catalog: ConnectionCatalog,
        reduction_catalog: CoreReductionCatalog,
        native_evidence_catalog: CoreNativeEvidenceCatalog,
        hardness_target_catalog: HardnessTargetCatalog,
        request: CoreGeneralizationRequest,
        maximum_query_rounds: int = MAX_CORE_GENERALIZATION_QUERY_ROUNDS,
    ) -> None:
        if not 1 <= maximum_query_rounds <= MAX_CORE_GENERALIZATION_QUERY_ROUNDS:
            raise ValueError(
                "maximum_query_rounds must be in 1.."
                f"{MAX_CORE_GENERALIZATION_QUERY_ROUNDS}"
            )
        if not (
            observation.supported
            and (
                observation.input_kind == "presented_problem"
                and observation.normalized_problem_node_id
                or observation.input_kind == "predicate"
                and observation.predicate_node_id
                and observation.predicate_domain_node_id
            )
        ):
            raise InputPlanningError(
                "input_not_decision_problem",
                "Lean did not confirm a closed PresentedProblem or a closed monomorphic "
                "unary predicate with a lawful presentation boundary.",
            )
        if request.objective == "reduce_to" and target_observation is None:
            raise ValueError("fixed reduce_to request requires a target observation")
        if target_observation is not None and not (
            target_observation.supported
            and target_observation.input_kind == "presented_problem"
            and target_observation.normalized_problem_node_id
        ):
            raise InputPlanningError(
                "target_declaration_not_presented_problem",
                "The fixed target was not confirmed by Lean as a PresentedProblem.",
            )
        fingerprints = {
            observation.registry_fingerprint,
            problem_catalog.registry_fingerprint,
            connection_catalog.registry_fingerprint,
            reduction_catalog.registry_fingerprint,
            native_evidence_catalog.registry_fingerprint,
            hardness_target_catalog.registry_fingerprint,
        }
        if target_observation is not None:
            fingerprints.add(target_observation.registry_fingerprint)
        if len(fingerprints) != 1:
            raise InputPlanningError(
                "stale_catalog_fingerprint",
                "Input, target, problem, connection, reduction, and native evidence "
                "snapshots do not share one Lean registry fingerprint.",
            )
        self.observation = observation
        self.target_observation = target_observation
        self.problem_catalog = problem_catalog
        self.connection_catalog = connection_catalog
        self.reduction_catalog = reduction_catalog
        self.native_evidence_catalog = native_evidence_catalog
        self.hardness_target_catalog = hardness_target_catalog
        self.request = request
        self.maximum_query_rounds = maximum_query_rounds
        self.query_rounds_used = 0
        self.retrieved_problems: dict[str, ProblemCatalogEntry] = {}
        self.retrieved_connections: dict[str, ConnectionCatalogEntry] = {}
        self.retrieved_reductions: dict[str, CoreReductionEntry] = {}
        self.retrieved_native_evidence: dict[str, CoreNativeEvidenceEntry] = {}
        self.retrieved_hardness_targets: dict[str, HardnessTargetCatalogEntry] = {}
        self.retrieved_target_evidence: dict[str, HardnessTargetEvidence] = {}
        self.queried_problem_node_ids: set[str] = set()
        self.queried_problem_accepts_node_ids: set[str] = set()
        self.queried_problem_domain_node_ids: set[str] = set()
        self.queried_connection_source_node_ids: set[str] = set()
        self.queried_reduction_source_node_ids: set[str] = set()
        self.fully_queried_reduction_source_node_ids: set[str] = set()
        self.reduction_search_signatures: set[str] = set()
        self.native_evidence_searches: set[tuple[str, str]] = set()
        self.queried_hardness_target_policies: set[str] = set()
        self.queried_hardness_target_namespaces: set[str] = set()
        self.target_search_performed = False
        self.trace: list[Mapping[str, Any]] = []
        self.protocol_feedback: list[dict[str, str]] = []

    def _input_route_starts(self) -> tuple[str, ...]:
        if self.predicate_input:
            return tuple(
                sorted(
                    {
                        entry.problem_node_id
                        for entry in predicate_exact_candidates(
                            self.observation, self.problem_catalog
                        )
                    }
                )
            )
        node = self.observation.normalized_problem_node_id or ""
        return (node,) if node else ()

    def _adjacency(
        self, *, retrieved_only: bool = False
    ) -> dict[str, tuple[CoreReductionEntry, ...]]:
        entries = (
            self.retrieved_reductions.values()
            if retrieved_only
            else self.reduction_catalog.entries
        )
        grouped: dict[str, list[CoreReductionEntry]] = {}
        for entry in entries:
            grouped.setdefault(entry.source_node_id, []).append(entry)
        return {
            node: tuple(sorted(rows, key=lambda row: row.entry_id))
            for node, rows in grouped.items()
        }

    def _shortest_path(
        self,
        *,
        source_node: str,
        target_node: str,
        initial_dependencies: Sequence[str] = (),
        retrieved_only: bool = False,
    ) -> tuple[CoreReductionEntry, ...] | None:
        if source_node == target_node:
            return () if self.request.allow_reflexive_target else None
        adjacency = self._adjacency(retrieved_only=retrieved_only)
        queue: deque[
            tuple[str, tuple[CoreReductionEntry, ...], frozenset[str], frozenset[str]]
        ] = deque(
            [
                (
                    source_node,
                    (),
                    frozenset(initial_dependencies),
                    frozenset({source_node}),
                )
            ]
        )
        seen: set[tuple[str, int, frozenset[str], frozenset[str]]] = set()
        while queue:
            node, path, dependencies, visited = queue.popleft()
            if len(path) >= self.request.maximum_route_atoms:
                continue
            for edge in adjacency.get(node, ()):
                if self.request.require_simple_path and edge.target_node_id in visited:
                    continue
                next_dependencies = dependencies | set(edge.provenance_declarations)
                if len(next_dependencies) > self.request.maximum_dependencies:
                    continue
                next_path = (*path, edge)
                next_visited = (
                    visited | {edge.target_node_id}
                    if self.request.require_simple_path
                    else visited
                )
                if (
                    edge.target_node_id == target_node
                    and self.request.minimum_route_atoms
                    <= len(next_path)
                    <= self.request.maximum_route_atoms
                ):
                    return next_path
                state = (
                    edge.target_node_id,
                    len(next_path),
                    frozenset(next_dependencies),
                    frozenset(next_visited),
                )
                if state not in seen:
                    seen.add(state)
                    queue.append(
                        (
                            edge.target_node_id,
                            next_path,
                            frozenset(next_dependencies),
                            frozenset(next_visited),
                        )
                    )
        return None

    def _evidence_satisfies_target_request(
        self, evidence: HardnessTargetEvidence
    ) -> bool:
        assert self.request.required_hardness is not None
        return (
            self.request.required_hardness in evidence.satisfied_policies
            and evidence.evidence_kind in self.request.allowed_target_evidence
            and (
                self.request.objective == "reduce_to_known_hardness"
                or bool(evidence.membership_lean_term)
            )
            and len(set(evidence.provenance_declarations))
            <= self.request.maximum_dependencies
        )

    def _eligible_targets(
        self,
    ) -> tuple[tuple[HardnessTargetCatalogEntry, HardnessTargetEvidence], ...]:
        return tuple(
            (target, evidence)
            for target in self.hardness_target_catalog.entries
            for evidence in target.evidences
            if self._evidence_satisfies_target_request(evidence)
        )

    def _hardness_target_prompt_result(
        self, entry: HardnessTargetCatalogEntry
    ) -> dict[str, Any]:
        """Render only request-local target facts that are safe to expose.

        Eligibility is a deterministic projection of the public request and a
        retrieved evidence row.  Route existence and shortest-path data are
        deliberately omitted: the model must establish a path through bounded
        ``search_reductions`` calls instead of receiving a graph oracle.
        """

        row = hardness_target_search_result(entry)
        evidence_rows: list[dict[str, Any]] = []
        for raw in row["evidences"]:
            evidence = next(
                evidence
                for evidence in entry.evidences
                if evidence.evidence_id == raw["evidence_id"]
            )
            evidence_rows.append(
                {
                    **raw,
                    "dependency_count": len(
                        set(evidence.provenance_declarations)
                    ),
                    "request_eligible": self._evidence_satisfies_target_request(
                        evidence
                    ),
                }
            )
        row["evidences"] = evidence_rows
        row["request_eligible_evidence_count"] = sum(
            item["request_eligible"] for item in evidence_rows
        )
        return row

    def search_reductions(self, payload: Mapping[str, Any]) -> dict[str, Any]:
        self._consume_query_round("search_reductions")
        try:
            searches = parse_theorem_searches(payload)
        except RetrievalValidationError as error:
            raise InputPlanningError(
                "invalid_reduction_search",
                f"The bounded reduction search is invalid: {error}",
            ) from error
        signatures = [
            json.dumps(search.to_dict(), sort_keys=True, separators=(",", ":"))
            for search in searches
        ]
        if any(signature in self.reduction_search_signatures for signature in signatures):
            raise InputPlanningError(
                "repeated_reduction_search",
                "The identical reduction query was already completed; use returned "
                "frontier nodes or finish/stop instead of repeating it.",
            )
        self.reduction_search_signatures.update(signatures)
        results = search_core_reductions(self.reduction_catalog, searches)
        for search in searches:
            self.queried_reduction_source_node_ids.update(search.source_node_ids)
            source_only = bool(
                search.source_node_ids
                and not search.terms
                and not search.namespace_prefixes
                and not search.roles
                and not search.target_node_ids
            )
            if source_only:
                for source_node in search.source_node_ids:
                    expected = {
                        entry.entry_id
                        for entry in self.reduction_catalog.entries
                        if entry.source_node_id == source_node
                    }
                    returned = {
                        entry.entry_id
                        for entry in results
                        if entry.source_node_id == source_node
                    }
                    if expected.issubset(returned):
                        self.fully_queried_reduction_source_node_ids.add(source_node)
        room = MAX_RETRIEVED_CORE_REDUCTIONS - len(self.retrieved_reductions)
        for entry in results:
            if room <= 0:
                break
            if entry.entry_id not in self.retrieved_reductions:
                self.retrieved_reductions[entry.entry_id] = entry
                room -= 1
        response = {
            "action": "search_reductions",
            "searches": [search.to_dict() for search in searches],
            "results": [core_reduction_search_result(entry) for entry in results],
        }
        self.trace.append(response)
        return response

    def search_native_evidence(self, payload: Mapping[str, Any]) -> dict[str, Any]:
        self._consume_query_round("search_native_evidence")
        raw_searches = payload.get("searches")
        if not isinstance(raw_searches, list) or not 1 <= len(raw_searches) <= 4:
            raise InputPlanningError(
                "invalid_native_evidence_search",
                "search_native_evidence.searches must contain 1..4 objects.",
            )
        selected: dict[str, CoreNativeEvidenceEntry] = {}
        normalized: list[dict[str, Any]] = []
        for index, raw in enumerate(raw_searches):
            if not isinstance(raw, Mapping):
                raise InputPlanningError(
                    "invalid_native_evidence_search",
                    f"searches[{index}] must be an object.",
                )
            kinds = raw.get("evidence_kinds", [])
            nodes = raw.get("endpoint_node_ids", [])
            terms = raw.get("terms", [])
            limit = raw.get("limit", 8)
            if (
                not isinstance(kinds, list)
                or not isinstance(nodes, list)
                or not isinstance(terms, list)
                or any(not isinstance(item, str) or not item.strip() for item in (*kinds, *nodes, *terms))
                or not isinstance(limit, int)
                or isinstance(limit, bool)
            ):
                raise InputPlanningError(
                    "invalid_native_evidence_search",
                    f"searches[{index}] has invalid filters.",
                )
            if not kinds and not nodes and not terms:
                raise InputPlanningError(
                    "invalid_native_evidence_search",
                    f"searches[{index}] must include a kind, endpoint, or term filter.",
                )
            try:
                results = search_native_evidence(
                    self.native_evidence_catalog,
                    evidence_kinds=tuple(kinds),
                    endpoint_node_ids=tuple(nodes),
                    terms=tuple(terms),
                    limit=min(max(limit, 1), 8),
                )
            except ValueError as error:
                raise InputPlanningError(
                    "invalid_native_evidence_search", str(error)
                ) from error
            normalized.append(
                {
                    "evidence_kinds": kinds,
                    "endpoint_node_ids": nodes,
                    "terms": terms,
                    "limit": min(max(limit, 1), 8),
                }
            )
            for kind in kinds:
                if nodes:
                    self.native_evidence_searches.update((kind, node) for node in nodes)
                else:
                    self.native_evidence_searches.add((kind, "*"))
            for entry in results:
                selected.setdefault(entry.entry_id, entry)
        room = MAX_RETRIEVED_NATIVE_EVIDENCE - len(self.retrieved_native_evidence)
        for entry in selected.values():
            if room <= 0:
                break
            if entry.entry_id not in self.retrieved_native_evidence:
                self.retrieved_native_evidence[entry.entry_id] = entry
                room -= 1
        response = {
            "action": "search_native_evidence",
            "searches": normalized,
            "results": [
                native_evidence_search_result(entry) for entry in selected.values()
            ],
        }
        self.trace.append(response)
        return response

    def search_hardness_targets(self, payload: Mapping[str, Any]) -> dict[str, Any]:
        if self.request.objective not in {
            "reduce_to_known_np",
            "reduce_to_known_hardness",
        }:
            raise InputPlanningError(
                "wrong_objective_query",
                "search_hardness_targets is available only to open reduction objectives.",
            )
        self._consume_query_round("search_hardness_targets")
        try:
            searches = parse_hardness_target_searches(payload)
            entries = search_hardness_targets(self.hardness_target_catalog, searches)
        except (ValueError, HardnessTargetCatalogError, HardnessTargetSearchError) as error:
            raise InputPlanningError(
                "invalid_hardness_target_search",
                f"The bounded hardness-target search is invalid: {error}",
            ) from error
        self.target_search_performed = True
        for search in searches:
            self.queried_hardness_target_policies.update(search.required_policies)
            self.queried_hardness_target_namespaces.update(
                search.namespace_prefixes
            )
        room = MAX_RETRIEVED_HARDNESS_TARGETS - len(self.retrieved_hardness_targets)
        rendered: list[dict[str, Any]] = []
        for entry in entries:
            if room > 0 and entry.target_entry_id not in self.retrieved_hardness_targets:
                self.retrieved_hardness_targets[entry.target_entry_id] = entry
                room -= 1
            for evidence in entry.evidences:
                self.retrieved_target_evidence[evidence.evidence_id] = evidence
            rendered.append(self._hardness_target_prompt_result(entry))
        response = {
            "action": "search_hardness_targets",
            "searches": [search.to_dict() for search in searches],
            "results": rendered,
        }
        self.trace.append(response)
        return response

    def execute_query(self, payload: Mapping[str, Any]) -> dict[str, Any]:
        action = payload.get("action")
        if action == "search_reductions":
            return self.search_reductions(payload)
        if action == "search_native_evidence":
            return self.search_native_evidence(payload)
        if action == "search_hardness_targets":
            return self.search_hardness_targets(payload)
        return super().execute_query(payload)

    def _selected_reduction_entries(
        self, entry_ids: Sequence[str]
    ) -> tuple[CoreReductionEntry, ...]:
        if len(entry_ids) != len(set(entry_ids)):
            raise InputPlanningError(
                "repeated_reduction_entry", "The selected path repeats a reduction entry."
            )
        if len(entry_ids) > self.request.maximum_route_atoms:
            raise InputPlanningError(
                "selected_path_too_long", "The selected path exceeds the public atom limit."
            )
        missing = [
            entry_id
            for entry_id in entry_ids
            if entry_id not in self.retrieved_reductions
        ]
        if missing:
            connection_only = [
                entry_id for entry_id in missing if entry_id in self.retrieved_connections
            ]
            explanation = (
                "These selected reduction_entry_ids were not returned by "
                f"search_reductions: {', '.join(missing)}."
            )
            if connection_only:
                explanation += (
                    " They currently appear only in retrieved.connections and cannot be "
                    "used as route rows. Run the matching exact request in "
                    "retrieval_guidance.connection_rows_requiring_reduction_search first."
                )
            raise InputPlanningError("reduction_not_retrieved", explanation)
        selected = [self.retrieved_reductions[entry_id] for entry_id in entry_ids]
        return tuple(selected)

    def _select_problem_match(
        self, payload: Mapping[str, Any]
    ) -> tuple[ProblemCatalogEntry, ProblemMatch, ConnectionCatalogEntry | None]:
        selector = _required_open_target_problem_selector(
            payload, failure_code="invalid_model_finish"
        )
        relation = _required_string(payload, "match_relation")
        connection_id = _optional_open_target_connection_id(
            payload, failure_code="invalid_model_finish"
        )
        candidate = self._selected_problem(selector)
        connection = self._selected_connection(connection_id)
        match = self._problem_match(
            candidate=candidate,
            relation=relation,
            connection=connection,
        )
        return candidate, match, connection

    def _exact_evidence_match_required(
        self,
        *,
        match: ProblemMatch,
        connection: ConnectionCatalogEntry | None,
    ) -> None:
        if connection is not None:
            raise InputPlanningError(
                "objective_requires_exact_problem",
                "Membership and completeness require exact endpoint evidence; a "
                "one-way input connection cannot transport these objectives.",
            )
        input_node = (
            match.route_source_node_id
            if self.predicate_input
            else self.observation.normalized_problem_node_id or ""
        )
        if match.candidate_node_id != input_node:
            raise InputPlanningError(
                "objective_requires_exact_problem",
                "The selected evidence endpoint is not the exact input problem.",
            )

    def _selected_target(
        self, payload: Mapping[str, Any]
    ) -> tuple[HardnessTargetCatalogEntry, HardnessTargetEvidence]:
        target_entry_id = _required_string(payload, "target_entry_id")
        evidence_id = _required_string(payload, "target_evidence_id")
        declaration = _required_string(payload, "target_declaration")
        target = self.retrieved_hardness_targets.get(target_entry_id)
        if target is None or target.target_declaration != declaration:
            raise InputPlanningError(
                "hardness_target_not_retrieved",
                "The selected target is not an exact row returned by search_hardness_targets.",
            )
        evidence = self.retrieved_target_evidence.get(evidence_id)
        if evidence is None or evidence not in target.evidences:
            raise InputPlanningError(
                "target_evidence_not_retrieved",
                "The selected evidence is not attached to the selected target row.",
            )
        if not self._evidence_satisfies_target_request(evidence):
            raise InputPlanningError(
                "target_evidence_policy_mismatch",
                "The selected target evidence does not satisfy the public request policy.",
            )
        return target, evidence

    def _validate_path_topology(
        self,
        *,
        match: ProblemMatch,
        connection: ConnectionCatalogEntry | None,
        reductions: Sequence[CoreReductionEntry],
        target_node: str,
        extra_dependencies: Sequence[str] = (),
        source_node: str | None = None,
    ) -> int:
        current = source_node or match.route_source_node_id
        nodes = [current]
        dependencies = set(extra_dependencies)
        atom_count = 0
        if connection is not None:
            input_node = self.observation.normalized_problem_node_id or ""
            if connection.source_node_id != input_node or connection.target_node_id != current:
                raise InputPlanningError(
                    "connection_endpoint_mismatch",
                    "The selected input connection does not join the real input to ProblemMatch.",
                )
            dependencies.update(
                (connection.certificate_declaration, connection.projection_declaration)
            )
            atom_count += 1
            nodes.insert(0, input_node)
        for reduction in reductions:
            if reduction.source_node_id != current:
                raise InputPlanningError(
                    "reduction_path_disconnected",
                    "Adjacent selected reduction entries do not have identical Lean endpoints.",
                )
            current = reduction.target_node_id
            nodes.append(current)
            dependencies.update(reduction.provenance_declarations)
            atom_count += 1
        if current != target_node:
            raise InputPlanningError(
                "reduction_path_does_not_reach_target",
                "The ordered path does not reach the exact requested/selected target node.",
            )
        if not self.request.minimum_route_atoms <= atom_count <= self.request.maximum_route_atoms:
            raise InputPlanningError(
                "selected_path_outside_atom_range",
                "The selected path is outside the public route-atom range.",
            )
        if self.request.require_simple_path and len(nodes) != len(set(nodes)):
            raise InputPlanningError(
                "selected_path_not_simple", "The selected path repeats a Lean endpoint."
            )
        if len(dependencies) > self.request.maximum_dependencies:
            raise InputPlanningError(
                "selected_dependency_limit_exceeded",
                "The selected evidence and route exceed the public dependency limit.",
            )
        return atom_count

    def _validate_model_term(
        self,
        *,
        term: str,
        expected_fragments: Sequence[str],
        allowed_declarations: Sequence[str],
        require_path: bool,
        edge_count: int = 0,
    ) -> str:
        checked = term.strip()
        if not checked:
            raise InputPlanningError("missing_lean_term", "The finish payload has no Lean term.")
        if len(checked) > MAX_MODEL_LEAN_TERM_CHARS:
            raise InputPlanningError("lean_term_too_large", "The Lean term exceeds the audit limit.")
        if BANNED_MODEL_TERM_RE.search(checked):
            raise InputPlanningError(
                "forbidden_lean_syntax",
                "The Lean term contains a forbidden placeholder, command, import, or declaration.",
            )
        compact = _compact(checked)
        position = 0
        for fragment in expected_fragments:
            needle = _compact(fragment)
            found = compact.find(needle, position)
            if found < 0:
                raise InputPlanningError(
                    "lean_term_missing_selected_fact",
                    "The Lean term does not reference every selected fact in the required order.",
                )
            position = found + len(needle)
        if require_path:
            step = "ComplexityReduction.Certificate.CertifiedPath.step"
            cons = "ComplexityReduction.Certificate.CertifiedPath.cons"
            refl = "ComplexityReduction.Certificate.CertifiedPath.refl"
            if edge_count == 0 and refl not in compact:
                raise InputPlanningError(
                    "lean_term_missing_path_constructor", "A zero-edge path must use CertifiedPath.refl."
                )
            if edge_count > 0:
                starts_with_step = step in compact
                starts_from_refl = refl in compact
                if not starts_with_step and not starts_from_refl:
                    raise InputPlanningError(
                        "lean_term_missing_path_constructor",
                        "A non-empty path must use CertifiedPath.step or append its first edge to CertifiedPath.refl.",
                    )
                minimum_cons = edge_count - 1 if starts_with_step else edge_count
                if compact.count(cons) < minimum_cons:
                    raise InputPlanningError(
                        "lean_term_missing_path_constructor",
                        "The CertifiedPath term does not append every selected edge.",
                    )
        used = set(FULL_DECLARATION_RE.findall(checked))
        unexpected = sorted(used - set(allowed_declarations))
        if unexpected:
            raise InputPlanningError(
                "lean_term_uses_unretrieved_declaration",
                "The Lean term references declarations outside retrieved provenance: "
                + ", ".join(unexpected[:5]),
            )
        return checked

    def _grounding_step(
        self,
        *,
        candidate: ProblemCatalogEntry,
        match: ProblemMatch,
        connection: ConnectionCatalogEntry | None,
    ) -> dict[str, Any]:
        if connection is None:
            return {
                "schema_version": PLAN_STEP_SCHEMA,
                "step_id": "s1",
                "action_kind": (
                    "select.existing_problem_presentation"
                    if self.predicate_input
                    else "reuse.exact_endpoint"
                ),
                "output_handles": ["matched_problem"],
                "parameters": {
                    "problem_declaration": candidate.declaration,
                    "problem_match_id": match.match_id,
                    "problem_node_id": match.route_source_node_id,
                    "relation": match.relation,
                },
            }
        return {
            "schema_version": PLAN_STEP_SCHEMA,
            "step_id": "s1",
            "action_kind": "reuse.input_connection",
            "capability_kind": connection.capability_kind,
            "declaration": connection.certificate_declaration,
            "output_handles": ["matched_problem"],
            "role": connection.component_role,
            "parameters": {
                "connection_entry_id": connection.entry_id,
                "projection_declaration": connection.projection_declaration,
                "executable_lean_term": connection.lean_term,
                "relation": connection.relation,
                "problem_match_id": match.match_id,
            },
        }

    def _build_plan(
        self,
        *,
        candidate: ProblemCatalogEntry,
        match: ProblemMatch,
        connection: ConnectionCatalogEntry | None,
        reductions: Sequence[CoreReductionEntry],
        proof_term: str,
        explanation: str,
        target_declaration: str | None,
        target_evidence: Mapping[str, Any],
        output_kind: str,
        expected_type: str,
    ) -> HardnessPlan:
        steps: list[dict[str, Any]] = [
            self._grounding_step(candidate=candidate, match=match, connection=connection)
        ]
        previous = "s1"
        for index, entry in enumerate(reductions, start=2):
            step_id = f"s{index}"
            steps.append(
                {
                    "schema_version": PLAN_STEP_SCHEMA,
                    "step_id": step_id,
                    "action_kind": "reuse.certified_reduction",
                    "capability_kind": "certified_reduction",
                    "declaration": entry.certificate_declaration,
                    "depends_on": [previous],
                    "role": entry.component_role,
                    "parameters": {
                        "core_reduction_entry_id": entry.entry_id,
                        "executable_lean_term": entry.lean_term,
                        "provenance_declarations": list(entry.provenance_declarations),
                    },
                }
            )
            previous = step_id
        evidence_step = f"s{len(steps) + 1}"
        steps.append(
            {
                "schema_version": PLAN_STEP_SCHEMA,
                "step_id": evidence_step,
                "action_kind": f"emit.{output_kind.replace('.', '_')}",
                "depends_on": [previous],
                "expected_type": expected_type,
            }
        )
        payload = {
            "schema_version": PLAN_SCHEMA,
            "objective": self.request.objective,
            "source_declaration": self._path_source_declaration(match),
            "target_declaration": target_declaration,
            "registry_fingerprint": self.problem_catalog.registry_fingerprint,
            "catalog_id": self.reduction_catalog.catalog_id,
            "problem_catalog_id": self.problem_catalog.catalog_id,
            "connection_catalog_id": self.connection_catalog.catalog_id,
            "matched_problem_declaration": candidate.declaration,
            "problem_match": match.to_dict(),
            "target_evidence": dict(target_evidence),
            "metadata": {
                "prompt_abi": CORE_GENERALIZATION_PROMPT_ABI,
                "input_observation_id": self.observation.observation_id,
                "model_explanation": explanation,
                "query_rounds_used": self.query_rounds_used,
                "request": self.request.to_dict(),
            },
            "steps": steps,
            "outputs": [
                {
                    "schema_version": PLAN_OUTPUT_SCHEMA,
                    "output_id": "objective_evidence",
                    "output_kind": output_kind,
                    "producer_steps": [step["step_id"] for step in steps],
                    "expected_type": expected_type,
                    "lean_code": proof_term,
                    "metadata": {
                        "connection_entry_id": connection.entry_id if connection else None,
                        "reduction_entry_ids": [entry.entry_id for entry in reductions],
                    },
                }
            ],
        }
        return parse_hardness_plan(payload)

    def _finish_reduction(self, payload: Mapping[str, Any]) -> ObservedInputPlannerResult:
        forbidden = {
            "membership_evidence_id",
            "membership_declaration",
            "membership_lean_term",
            "hub_completeness_evidence_id",
            "target_membership_evidence_id",
            "completeness_lean_term",
        }
        if forbidden.intersection(payload):
            raise InputPlanningError(
                "objective_payload_type_mismatch",
                "A reduction finish payload cannot contain membership/completeness fields.",
            )
        candidate, match, connection = self._select_problem_match(payload)
        entry_ids = _string_list(payload, "reduction_entry_ids")
        reductions = self._selected_reduction_entries(entry_ids)
        lean_term = _required_string(payload, "lean_term")
        explanation = _required_string(payload, "explanation")[:2000]
        if self.request.objective == "reduce_to":
            if any(key in payload for key in ("target_entry_id", "target_evidence_id")):
                raise InputPlanningError(
                    "objective_payload_type_mismatch",
                    "A fixed reduce_to payload must not select open-target evidence.",
                )
            assert self.target_observation is not None
            target_declaration = self.target_observation.input_declaration
            target_node = self.target_observation.normalized_problem_node_id or ""
            evidence: Mapping[str, Any] = {
                "evidence_kind": "fixed_target_observation",
                "target_declaration": target_declaration,
                "target_node_id": target_node,
                "observation_id": self.target_observation.observation_id,
            }
            extra_dependencies: Sequence[str] = ()
        else:
            target, selected_evidence = self._selected_target(payload)
            target_declaration = target.target_declaration
            target_node = target.target_node_id
            evidence = {
                **selected_evidence.to_dict(),
                "target_entry_id": target.target_entry_id,
                "policy_satisfied": True,
            }
            extra_dependencies = selected_evidence.provenance_declarations
        atom_count = self._validate_path_topology(
            match=match,
            connection=connection,
            reductions=reductions,
            target_node=target_node,
            extra_dependencies=extra_dependencies,
        )
        fragments = [
            *([connection.lean_term] if connection is not None else []),
            *(entry.lean_term for entry in reductions),
        ]
        allowed = set(STATIC_PATH_DECLARATIONS)
        allowed.update(
            {
                candidate.declaration,
                match.route_source_declaration,
                self._path_source_declaration(match),
                target_declaration,
            }
        )
        if connection is not None:
            allowed.update(
                (connection.certificate_declaration, connection.projection_declaration)
            )
        for entry in reductions:
            allowed.update(entry.provenance_declarations)
        checked = self._validate_model_term(
            term=lean_term,
            expected_fragments=fragments,
            allowed_declarations=tuple(allowed),
            require_path=True,
            edge_count=atom_count,
        )
        expected_type = (
            "ComplexityReduction.Certificate.CertifiedPath "
            f"{self._path_source_declaration(match)} {target_declaration}"
        )
        plan = self._build_plan(
            candidate=candidate,
            match=match,
            connection=connection,
            reductions=reductions,
            proof_term=checked,
            explanation=explanation,
            target_declaration=target_declaration,
            target_evidence=evidence,
            output_kind="certificate.certified_path",
            expected_type=expected_type,
        )
        return ObservedInputPlannerResult(
            plan=plan,
            lean_term=checked,
            problem_match=match,
            selected_connection=connection,
            reduction_declarations=tuple(
                entry.certificate_declaration for entry in reductions
            ),
            explanation=explanation,
            query_trace=tuple(self.trace),
        )

    def _selected_native_evidence(
        self, entry_id: str, *, expected_kind: str
    ) -> CoreNativeEvidenceEntry:
        entry = self.retrieved_native_evidence.get(entry_id)
        if entry is None:
            raise InputPlanningError(
                "native_evidence_not_retrieved",
                "The selected native evidence ID was not returned by this session.",
            )
        if entry.evidence_kind != expected_kind:
            raise InputPlanningError(
                "objective_payload_type_mismatch",
                f"The selected evidence is {entry.evidence_kind}, not {expected_kind}.",
            )
        return entry

    def _finish_membership(self, payload: Mapping[str, Any]) -> ObservedInputPlannerResult:
        forbidden = {
            "target_entry_id",
            "target_evidence_id",
            "reduction_entry_ids",
            "lean_term",
            "completeness_lean_term",
            "hub_completeness_evidence_id",
            "target_membership_evidence_id",
        }
        if forbidden.intersection(payload):
            raise InputPlanningError(
                "objective_payload_type_mismatch",
                "prove_in_np accepts only an exact native-membership payload.",
            )
        candidate, match, connection = self._select_problem_match(payload)
        self._exact_evidence_match_required(match=match, connection=connection)
        evidence_id = _required_string(payload, "membership_evidence_id")
        declaration = _required_string(payload, "membership_declaration")
        term = _required_string(payload, "membership_lean_term")
        explanation = _required_string(payload, "explanation")[:2000]
        evidence = self._selected_native_evidence(
            evidence_id, expected_kind=NATIVE_MEMBERSHIP
        )
        if evidence.endpoint_node_id != match.candidate_node_id:
            raise InputPlanningError(
                "native_evidence_endpoint_mismatch",
                "Native membership is not for the exact input problem endpoint.",
            )
        if evidence.evidence_declaration != declaration:
            raise InputPlanningError(
                "native_evidence_selection_mismatch",
                "membership_declaration does not match the selected evidence row.",
            )
        if _compact(term) != _compact(evidence.lean_term):
            raise InputPlanningError(
                "native_evidence_term_mismatch",
                "membership_lean_term must be the untouched term from the selected row.",
            )
        checked = self._validate_model_term(
            term=term,
            expected_fragments=(evidence.lean_term,),
            allowed_declarations=evidence.provenance_declarations,
            require_path=False,
        )
        expected_type = (
            "ComplexityReduction.Certificate.NativeTMInNP "
            f"{self._path_source_declaration(match)}"
        )
        plan = self._build_plan(
            candidate=candidate,
            match=match,
            connection=None,
            reductions=(),
            proof_term=checked,
            explanation=explanation,
            target_declaration=None,
            target_evidence={
                **evidence.to_dict(),
                "policy_satisfied": True,
            },
            output_kind="evidence.native_tm_in_np",
            expected_type=expected_type,
        )
        return ObservedInputPlannerResult(
            plan=plan,
            lean_term=checked,
            problem_match=match,
            selected_connection=None,
            reduction_declarations=(),
            explanation=explanation,
            query_trace=tuple(self.trace),
        )

    def _render_path_term(
        self, reductions: Sequence[CoreReductionEntry], *, source_declaration: str
    ) -> str:
        if not reductions:
            return (
                "ComplexityReduction.Certificate.CertifiedPath.refl "
                + source_declaration
            )
        rendered = (
            "ComplexityReduction.Certificate.CertifiedPath.step ("
            + reductions[0].lean_term
            + ")"
        )
        for entry in reductions[1:]:
            rendered = (
                "ComplexityReduction.Certificate.CertifiedPath.cons ("
                + rendered
                + ") ("
                + entry.lean_term
                + ")"
            )
        return rendered

    def _finish_completeness(self, payload: Mapping[str, Any]) -> ObservedInputPlannerResult:
        forbidden = {
            "target_entry_id",
            "target_evidence_id",
            "membership_evidence_id",
            "membership_declaration",
            "membership_lean_term",
            "lean_term",
        }
        if forbidden.intersection(payload):
            raise InputPlanningError(
                "objective_payload_type_mismatch",
                "prove_np_complete requires the completeness-specific payload.",
            )
        candidate, match, connection = self._select_problem_match(payload)
        self._exact_evidence_match_required(match=match, connection=connection)
        hub = self._selected_native_evidence(
            _required_string(payload, "hub_completeness_evidence_id"),
            expected_kind=NATIVE_COMPLETENESS,
        )
        membership = self._selected_native_evidence(
            _required_string(payload, "target_membership_evidence_id"),
            expected_kind=NATIVE_MEMBERSHIP,
        )
        reductions = self._selected_reduction_entries(
            _string_list(payload, "reduction_entry_ids")
        )
        term = _required_string(payload, "completeness_lean_term")
        explanation = _required_string(payload, "explanation")[:2000]
        if membership.endpoint_node_id != match.candidate_node_id:
            raise InputPlanningError(
                "native_membership_endpoint_mismatch",
                "Completeness transport requires exact native membership of the target.",
            )
        atom_count = self._validate_path_topology(
            match=match,
            connection=None,
            reductions=reductions,
            target_node=match.candidate_node_id,
            extra_dependencies=(
                *hub.provenance_declarations,
                *membership.provenance_declarations,
                COMPLETENESS_TRANSPORT,
            ),
            source_node=hub.endpoint_node_id,
        )
        fragments = (
            COMPLETENESS_TRANSPORT,
            hub.lean_term,
            *(entry.lean_term for entry in reductions),
            membership.lean_term,
        )
        allowed = {
            COMPLETENESS_TRANSPORT,
            *STATIC_PATH_DECLARATIONS,
            *hub.provenance_declarations,
            *membership.provenance_declarations,
            hub.endpoint_declaration,
            match.route_source_declaration,
            self._path_source_declaration(match),
        }
        for entry in reductions:
            allowed.update(entry.provenance_declarations)
        checked = self._validate_model_term(
            term=term,
            expected_fragments=fragments,
            allowed_declarations=tuple(allowed),
            require_path=False,
        )
        expected_type = (
            "ComplexityReduction.Certificate.NativeTMNPComplete "
            f"{self._path_source_declaration(match)}"
        )
        plan = self._build_plan(
            candidate=candidate,
            match=match,
            connection=None,
            reductions=reductions,
            proof_term=checked,
            explanation=explanation,
            target_declaration=None,
            target_evidence={
                "evidence_kind": "transported_native_completeness",
                "hub_completeness": hub.to_dict(),
                "target_membership": membership.to_dict(),
                "reduction_entry_ids": [entry.entry_id for entry in reductions],
                "route_atom_count": atom_count,
                "policy_satisfied": True,
            },
            output_kind="evidence.native_tm_np_complete",
            expected_type=expected_type,
        )
        return ObservedInputPlannerResult(
            plan=plan,
            lean_term=checked,
            problem_match=match,
            selected_connection=None,
            reduction_declarations=tuple(
                entry.certificate_declaration for entry in reductions
            ),
            explanation=explanation,
            query_trace=tuple(self.trace),
        )

    def finish(self, payload: Mapping[str, Any]) -> ObservedInputPlannerResult:
        if self.request.payload_kind == "reduction":
            result = self._finish_reduction(payload)
        elif self.request.payload_kind == "membership":
            result = self._finish_membership(payload)
        else:
            result = self._finish_completeness(payload)
        assert result.plan is not None
        self.trace.append(
            {
                "action": "finish",
                "status": "accepted",
                "objective": self.request.objective,
                "plan_id": result.plan.plan_id,
            }
        )
        return result

    def _problem_search_complete(self) -> bool:
        if self.predicate_input:
            return bool(
                (self.observation.predicate_node_id or "")
                in self.queried_problem_accepts_node_ids
                and (self.observation.predicate_domain_node_id or "")
                in self.queried_problem_domain_node_ids
            )
        node = self.observation.normalized_problem_node_id or ""
        return node in self.queried_problem_node_ids

    def _has_retrieved_exact_match(self) -> bool:
        if self.predicate_input:
            exact = {
                entry.entry_id
                for entry in predicate_exact_candidates(
                    self.observation, self.problem_catalog
                )
            }
            return any(entry_id in exact for entry_id in self.retrieved_problems)
        node = self.observation.normalized_problem_node_id or ""
        return any(
            entry.problem_node_id == node for entry in self.retrieved_problems.values()
        )

    def stop(self, payload: Mapping[str, Any]) -> ObservedInputPlannerResult:
        failure_code = _required_string(payload, "failure_code")
        model_explanation = _model_stop_explanation(
            payload,
            failure_code=failure_code,
            terminal_guidance=self._terminal_guidance(),
        )
        if self.predicate_input and failure_code == "ambiguous_predicate_presentation":
            if not self._problem_search_complete() or len(
                predicate_presentation_groups(self.observation, self.problem_catalog)
            ) <= 1:
                raise InputPlanningError(
                    "model_stop_not_auditable",
                    "The ambiguous predicate blocker is not established by completed Lean-index searches.",
                )
            explanation = (
                "Lean-confirmed predicate matches span multiple encoder-bound codec groups, "
                "so Core cannot choose a presentation. "
                f"Model explanation: {model_explanation}"
            )
        elif failure_code == "missing_lawful_presentation":
            if not self._problem_search_complete():
                raise InputPlanningError(
                    "model_stop_not_auditable", "The exact problem/predicate search has not completed."
                )
            if self._has_retrieved_exact_match():
                raise InputPlanningError(
                    "model_stop_contradicted_by_catalog", "An exact Lean-confirmed problem match is available."
                )
            if not self.predicate_input:
                node = self.observation.normalized_problem_node_id or ""
                if node not in self.queried_connection_source_node_ids:
                    raise InputPlanningError(
                        "model_stop_not_auditable",
                        "A non-exact PresentedProblem must also query outgoing connections.",
                    )
            explanation = (
                "Lean confirmed the input endpoint, but no exact existing problem or lawful "
                "direction-specific presentation connection relates its representation to the "
                "library. Carrier or semantic similarity alone is insufficient. "
                f"Model explanation: {model_explanation}"
            )
        elif failure_code == "no_eligible_hardness_target":
            if (
                not self.target_search_performed
                or self.request.required_hardness not in self.queried_hardness_target_policies
                or self._eligible_targets()
            ):
                raise InputPlanningError(
                    "model_stop_not_auditable",
                    "The required target-policy search does not establish an empty eligible set.",
                )
            explanation = (
                "The same-fingerprint target catalog has no evidence satisfying the requested "
                "Native policy, evidence kind, and dependency bound. "
                f"Model explanation: {model_explanation}"
            )
        elif failure_code == "eligible_target_has_no_existing_route":
            if not self._eligible_targets() or not self._problem_search_complete():
                raise InputPlanningError(
                    "model_stop_not_auditable", "Eligible targets and the exact input match were not established."
                )
            starts = self._input_route_starts()
            if any(
                self._shortest_path(
                    source_node=source,
                    target_node=target.target_node_id,
                    initial_dependencies=evidence.provenance_declarations,
                )
                is not None
                for source in starts
                for target, evidence in self._eligible_targets()
            ):
                raise InputPlanningError(
                    "model_stop_contradicted_by_catalog", "A policy-compliant forward route exists."
                )
            if not all(source in self.queried_reduction_source_node_ids for source in starts):
                raise InputPlanningError(
                    "model_stop_not_auditable", "The model has not queried reductions from every verified start."
                )
            explanation = (
                "Eligible target evidence exists, but the directed same-fingerprint Core graph "
                "has no route satisfying the public atom/dependency bounds; reverse edges cannot "
                "be reused forward. "
                f"Model explanation: {model_explanation}"
            )
        elif failure_code == "missing_native_membership":
            node = self.observation.normalized_problem_node_id or ""
            if (NATIVE_MEMBERSHIP, node) not in self.native_evidence_searches:
                raise InputPlanningError(
                    "model_stop_not_auditable", "Exact native membership was not queried for the input node."
                )
            if any(
                entry.evidence_kind == NATIVE_MEMBERSHIP
                and entry.endpoint_node_id == node
                for entry in self.native_evidence_catalog.entries
            ):
                raise InputPlanningError(
                    "model_stop_contradicted_by_catalog", "Exact NativeTMInNP evidence exists."
                )
            explanation = (
                "Lean confirmed the exact problem, but the native evidence view contains no "
                "NativeTMInNP capability for that endpoint. Hardness or backend membership cannot "
                "replace exact native membership. "
                f"Model explanation: {model_explanation}"
            )
        elif failure_code == "missing_native_completeness":
            node = self.observation.normalized_problem_node_id or ""
            required_searches = {
                (NATIVE_MEMBERSHIP, node),
                (NATIVE_COMPLETENESS, "*"),
            }
            if not required_searches.issubset(self.native_evidence_searches):
                raise InputPlanningError(
                    "model_stop_not_auditable",
                    "Completeness audit requires exact target membership and complete-hub searches.",
                )
            direct = any(
                entry.evidence_kind == NATIVE_COMPLETENESS
                and entry.endpoint_node_id == node
                for entry in self.native_evidence_catalog.entries
            )
            transported = any(
                self._shortest_path(
                    source_node=hub.endpoint_node_id,
                    target_node=node,
                    initial_dependencies=(
                        *hub.provenance_declarations,
                        *membership.provenance_declarations,
                        COMPLETENESS_TRANSPORT,
                    ),
                )
                is not None
                for hub in self.native_evidence_catalog.entries
                if hub.evidence_kind == NATIVE_COMPLETENESS
                for membership in self.native_evidence_catalog.entries
                if membership.evidence_kind == NATIVE_MEMBERSHIP
                and membership.endpoint_node_id == node
            )
            if direct or transported:
                raise InputPlanningError(
                    "model_stop_contradicted_by_catalog", "Exact native completeness is constructible from Core facts."
                )
            explanation = (
                "The exact endpoint has no NativeTMNPComplete evidence and no valid forward "
                "complete-hub transport with exact target NativeTMInNP. Backend-only or wrong-head "
                "completeness is rejected. "
                f"Model explanation: {model_explanation}"
            )
        else:
            raise InputPlanningError(
                "invalid_model_stop", f"Unsupported Stage-L stop code: {failure_code}"
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
            explanation=explanation,
            failure_code=failure_code,
            query_trace=tuple(self.trace),
        )

    def _terminal_guidance(self) -> dict[str, Any] | None:
        if self.predicate_input and self._problem_search_complete():
            groups = predicate_presentation_groups(self.observation, self.problem_catalog)
            if len(groups) > 1:
                return {
                    "mode": "stop_now",
                    "failure_code": "ambiguous_predicate_presentation",
                    "instruction": "Return stop immediately with this exact code.",
                }
            if not groups:
                return {
                    "mode": "stop_now",
                    "failure_code": "missing_lawful_presentation",
                    "instruction": (
                        "Return stop immediately. Domain/carrier similarity cannot replace "
                        "a Lean-confirmed predicate presentation."
                    ),
                }
        if not self.predicate_input and self._problem_search_complete():
            node = self.observation.normalized_problem_node_id or ""
            exact_exists = any(
                entry.problem_node_id == node for entry in self.problem_catalog.entries
            )
            if not exact_exists and node in self.queried_connection_source_node_ids:
                connected_problem_nodes = {
                    entry.target_node_id
                    for entry in self.connection_catalog.entries
                    if entry.source_node_id == node
                }
                catalog_problem_nodes = {
                    entry.problem_node_id for entry in self.problem_catalog.entries
                }
                if not connected_problem_nodes.intersection(catalog_problem_nodes):
                    return {
                        "mode": "stop_now",
                        "failure_code": "missing_lawful_presentation",
                        "instruction": (
                            "Return stop immediately. Exact problem and directed presentation "
                            "searches establish no lawful Core grounding."
                        ),
                    }
        if self.request.objective == "prove_in_np":
            node = self.observation.normalized_problem_node_id or ""
            if (NATIVE_MEMBERSHIP, node) in self.native_evidence_searches and not any(
                entry.evidence_kind == NATIVE_MEMBERSHIP
                and entry.endpoint_node_id == node
                for entry in self.native_evidence_catalog.entries
            ):
                return {
                    "mode": "stop_now",
                    "failure_code": "missing_native_membership",
                    "instruction": "Return stop immediately with this exact code.",
                }
        if self.request.objective in {"reduce_to_known_np", "reduce_to_known_hardness"}:
            if (
                self.target_search_performed
                and self.request.required_hardness in self.queried_hardness_target_policies
                and not self._eligible_targets()
            ):
                return {
                    "mode": "stop_now",
                    "failure_code": "no_eligible_hardness_target",
                    "instruction": "Return stop immediately; route queries cannot change target eligibility.",
                }
            starts = self._input_route_starts()
            if (
                self.target_search_performed
                and self._eligible_targets()
                and self._problem_search_complete()
                and starts
                and all(node in self.queried_reduction_source_node_ids for node in starts)
                and not any(
                    self._shortest_path(
                        source_node=source,
                        target_node=target.target_node_id,
                        initial_dependencies=evidence.provenance_declarations,
                    )
                    is not None
                    for source in starts
                    for target, evidence in self._eligible_targets()
                )
            ):
                return {
                    "mode": "stop_now",
                    "failure_code": "eligible_target_has_no_existing_route",
                    "instruction": (
                        "Return stop immediately. Eligible evidence exists, but no bounded "
                        "forward Core route exists; reverse edges are not usable."
                    ),
                }
        if self.request.objective == "prove_np_complete":
            node = self.observation.normalized_problem_node_id or ""
            required_searches = {
                (NATIVE_MEMBERSHIP, node),
                (NATIVE_COMPLETENESS, "*"),
            }
            if required_searches.issubset(self.native_evidence_searches):
                direct = any(
                    entry.evidence_kind == NATIVE_COMPLETENESS
                    and entry.endpoint_node_id == node
                    for entry in self.native_evidence_catalog.entries
                )
                transported = any(
                    self._shortest_path(
                        source_node=hub.endpoint_node_id,
                        target_node=node,
                        initial_dependencies=(
                            *hub.provenance_declarations,
                            *membership.provenance_declarations,
                            COMPLETENESS_TRANSPORT,
                        ),
                    )
                    is not None
                    for hub in self.native_evidence_catalog.entries
                    if hub.evidence_kind == NATIVE_COMPLETENESS
                    for membership in self.native_evidence_catalog.entries
                    if membership.evidence_kind == NATIVE_MEMBERSHIP
                    and membership.endpoint_node_id == node
                )
                if not direct and not transported:
                    return {
                        "mode": "stop_now",
                        "failure_code": "missing_native_completeness",
                        "instruction": (
                            "Return stop immediately. Exact membership plus the complete-hub "
                            "searches establish no valid native completeness construction."
                        ),
                    }
        return None

    def prompt_payload(self) -> dict[str, Any]:
        lookup_node = self._input_lookup_node_id()
        input_node = self.observation.normalized_problem_node_id or ""
        problem_hints = build_initial_problem_hints(
            self.problem_catalog,
            input_node_id=lookup_node,
            observation=self.observation,
        )
        if self.predicate_input:
            connection_hints: dict[str, Any] = {
                "contains_declaration_names": False,
                "not_applicable": True,
                "reason": "Raw predicates require accepts_exact_defeq grounding, not an edge.",
            }
            problem_searches = [
                {
                    "accepts_node_ids": [self.observation.predicate_node_id],
                    "domain_node_ids": [self.observation.predicate_domain_node_id],
                    "limit": 8,
                },
                {
                    "domain_node_ids": [self.observation.predicate_domain_node_id],
                    "limit": 8,
                },
            ]
        else:
            connection_hints = build_initial_connection_hints(
                self.connection_catalog, input_node_id=input_node
            )
            problem_searches = [{"node_ids": [input_node], "limit": 8}]
        fixed_target = None
        if self.target_observation is not None:
            fixed_target = {
                "declaration": self.target_observation.input_declaration,
                "node_id": self.target_observation.normalized_problem_node_id,
                "semantic_summary": self.target_observation.semantic_summary,
                "representation_summary": self.target_observation.representation_summary,
            }
        retrieved = {
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
            "reductions": [
                core_reduction_search_result(entry)
                for entry in self.retrieved_reductions.values()
            ],
            "native_evidence": [
                native_evidence_search_result(entry)
                for entry in self.retrieved_native_evidence.values()
            ],
            "hardness_targets": [
                self._hardness_target_prompt_result(entry)
                for entry in self.retrieved_hardness_targets.values()
            ],
        }
        reduction_frontier = tuple(
            dict.fromkeys(
                (
                    *(
                        node
                        for node in self._input_route_starts()
                        if node not in self.queried_reduction_source_node_ids
                    ),
                    *(
                        entry.target_node_id
                        for entry in self.retrieved_reductions.values()
                        if entry.target_node_id
                        not in self.queried_reduction_source_node_ids
                    ),
                )
            )
        )
        connection_reduction_gaps = _connection_reduction_retrieval_gaps(
            connections=tuple(self.retrieved_connections.values()),
            reduction_catalog=self.reduction_catalog,
            retrieved_reduction_ids=tuple(self.retrieved_reductions),
            preferred_source_nodes=(
                *self._input_route_starts(),
                *reduction_frontier,
            ),
        )
        target_summary = (
            build_initial_hardness_target_hints(self.hardness_target_catalog)
            if self.request.objective
            in {"reduce_to_known_np", "reduce_to_known_hardness"}
            else None
        )
        unqueried_target_namespaces = (
            [
                row["namespace"]
                for row in target_summary.get("nearby_namespaces", [])
                if isinstance(row, Mapping)
                and isinstance(row.get("namespace"), str)
                and row["namespace"]
                not in self.queried_hardness_target_namespaces
            ]
            if isinstance(target_summary, Mapping)
            else []
        )
        payload: dict[str, Any] = {
            "schema_version": CORE_GENERALIZATION_PROMPT_ABI,
            "task": "core_reuse_multi_objective_hardness_planning",
            "request": self.request.to_dict(),
            "input_observation": {
                "input_module": self.observation.input_module,
                "input_declaration": self.observation.input_declaration,
                "input_kind": self.observation.input_kind,
                "elaborated_type": self.observation.elaborated_type,
                "normalized_problem_node_id": self.observation.normalized_problem_node_id,
                "predicate_node_id": self.observation.predicate_node_id,
                "predicate_domain": self.observation.predicate_domain,
                "predicate_domain_node_id": self.observation.predicate_domain_node_id,
                "predicate_summary": self.observation.predicate_summary,
                "semantic_summary": self.observation.semantic_summary,
                "representation_summary": self.observation.representation_summary,
                "accepts_summary": self.observation.accepts_summary,
                "referenced_constants": list(self.observation.referenced_constants),
            },
            "fixed_target": fixed_target,
            "catalog_view": {
                "problem_catalog_id": self.problem_catalog.catalog_id,
                "connection_catalog_id": self.connection_catalog.catalog_id,
                "core_reduction_catalog_id": self.reduction_catalog.catalog_id,
                "native_evidence_catalog_id": self.native_evidence_catalog.catalog_id,
                "hardness_target_catalog_id": self.hardness_target_catalog.catalog_id,
                "same_registry_fingerprint": True,
                "full_catalogs_included": False,
                "all_catalog_rows_remain_queryable": True,
            },
            "problem_hints": problem_hints,
            "connection_hints": connection_hints,
            "hardness_target_hints": target_summary,
            "retrieval_guidance": {
                "unqueried_reduction_frontier_nodes": list(
                    reduction_frontier[:4]
                ),
                "suggested_reduction_searches": [
                    {"source_node_ids": [node], "limit": 8}
                    for node in reduction_frontier[:4]
                ],
                "suggested_reduction_searches_must_remain_separate_objects": True,
                "connection_rows_requiring_reduction_search": list(
                    connection_reduction_gaps
                ),
                "unqueried_target_namespaces": unqueried_target_namespaces[:4],
                "suggested_target_searches": [
                    {
                        "required_policies": [self.request.required_hardness],
                        "namespace_prefixes": [namespace],
                        "limit": 8,
                    }
                    for namespace in unqueried_target_namespaces[:4]
                ],
                "guidance_is_non_authoritative": True,
            },
            "library_architecture": build_library_architecture(self.reduction_catalog),
            "query_budget": {
                "used": self.query_rounds_used,
                "maximum": self.maximum_query_rounds,
                "remaining": self.maximum_query_rounds - self.query_rounds_used,
            },
            "query_history": self.query_history(),
            "protocol_feedback": list(self.protocol_feedback[-3:]),
            "retrieved": retrieved,
            "response_options": {
                "inspect_architecture": {
                    "action": "inspect_architecture",
                    "queries": [{"source_node_ids": ["known endpoint"], "limit": 8}],
                },
                "search_problems": {
                    "action": "search_problems",
                    "searches": problem_searches,
                },
                "search_connections": {
                    "action": "search_connections",
                    "request_key": "searches",
                    "maximum_search_objects": 4,
                    "searches": [{"source_node_ids": [lookup_node], "limit": 8}],
                },
                "search_reductions": {
                    "action": "search_reductions",
                    "request_key": "searches",
                    "maximum_search_objects": 4,
                    "keep_suggested_search_objects_separate": True,
                    "searches": [{"source_node_ids": ["current path node"], "limit": 8}],
                },
                "search_hardness_targets": {
                    "available": self.request.objective
                    in {"reduce_to_known_np", "reduce_to_known_hardness"},
                    "action": "search_hardness_targets",
                    "request_key": "searches",
                    "maximum_search_objects": 4,
                    "supported_search_fields": [
                        "required_policies",
                        "terms",
                        "namespace_prefixes",
                        "limit",
                    ],
                    "searches": [
                        {
                            "required_policies": [self.request.required_hardness],
                            "limit": 8,
                        }
                    ],
                },
                "search_native_evidence": {
                    "action": "search_native_evidence",
                    "request_key": "searches",
                    "maximum_search_objects": 4,
                    "searches": (
                        [
                            {
                                "evidence_kinds": [NATIVE_MEMBERSHIP],
                                "endpoint_node_ids": [input_node],
                                "limit": 8,
                            }
                        ]
                        if self.request.objective == "prove_in_np"
                        else (
                            [
                                {
                                    "evidence_kinds": [NATIVE_MEMBERSHIP],
                                    "endpoint_node_ids": [input_node],
                                    "limit": 8,
                                },
                                {
                                    "evidence_kinds": [NATIVE_COMPLETENESS],
                                    "limit": 8,
                                },
                            ]
                            if self.request.objective == "prove_np_complete"
                            else [
                                {
                                    "evidence_kinds": [NATIVE_COMPLETENESS],
                                    "endpoint_node_ids": ["optional exact endpoint"],
                                    "limit": 8,
                                }
                            ]
                        )
                    ),
                },
                "finish": objective_finish_payload(self.request.objective),
                "stop": {
                    "action_literal": "stop",
                    "failure_codes": [
                        "ambiguous_predicate_presentation",
                        "missing_lawful_presentation",
                        "no_eligible_hardness_target",
                        "eligible_target_has_no_existing_route",
                        "missing_native_membership",
                        "missing_native_completeness",
                    ],
                    "response_shape": {
                        "action": "stop",
                        "failure_code": "<one listed stable blocker>",
                        "explanation": "<brief reason from retrieved rows or terminal guidance>",
                    },
                    "terminal_explanation_optional": True,
                },
            },
            "lean_api": {
                "path_refl": "ComplexityReduction.Certificate.CertifiedPath.refl source",
                "path_step": "ComplexityReduction.Certificate.CertifiedPath.step reductionTerm",
                "path_cons": "ComplexityReduction.Certificate.CertifiedPath.cons priorPath reductionTerm",
                "completeness_transport": (
                    "ComplexityReduction.Certificate.CompletenessTransport.alongPath "
                    "hubCompleteness forwardPath exactTargetMembership"
                ),
            },
            "constraints": {
                "llm_selects_problem_target_evidence_and_route": True,
                "all_selected_rows_must_have_been_retrieved": True,
                "all_lean_declarations_must_be_in_retrieved_provenance": True,
                "objective_payloads_are_mutually_exclusive": True,
                "new_mathematics_forbidden": True,
                "authoring_available": False,
                "lean_runs_only_after_all_case_tasks": True,
            },
        }
        terminal = self._terminal_guidance()
        if terminal is not None:
            payload["terminal_guidance"] = terminal
        return payload

    def build_prompt(self) -> str:
        payload = self.prompt_payload()
        audit_core_generalization_prompt(payload)
        return json.dumps(
            payload,
            ensure_ascii=False,
            sort_keys=True,
            separators=(",", ":"),
        )


def generate_core_generalization_evidence(
    *,
    observation: LeanInputObservation,
    target_observation: LeanInputObservation | None,
    problem_catalog: ProblemCatalog,
    connection_catalog: ConnectionCatalog,
    reduction_catalog: CoreReductionCatalog,
    native_evidence_catalog: CoreNativeEvidenceCatalog,
    hardness_target_catalog: HardnessTargetCatalog,
    request: CoreGeneralizationRequest,
    client: DeepSeekClient,
    maximum_query_rounds: int = MAX_CORE_GENERALIZATION_QUERY_ROUNDS,
    maximum_model_turns: int = MAX_CORE_GENERALIZATION_MODEL_TURNS,
) -> ObservedInputPlannerResult:
    """Run Stage L without invoking Lean between model turns."""

    if not 1 <= maximum_model_turns <= MAX_CORE_GENERALIZATION_MODEL_TURNS:
        raise ValueError(
            "maximum_model_turns must be in 1.."
            f"{MAX_CORE_GENERALIZATION_MODEL_TURNS}"
        )
    try:
        session = CoreGeneralizationPlanningSession(
            observation=observation,
            target_observation=target_observation,
            problem_catalog=problem_catalog,
            connection_catalog=connection_catalog,
            reduction_catalog=reduction_catalog,
            native_evidence_catalog=native_evidence_catalog,
            hardness_target_catalog=hardness_target_catalog,
            request=request,
            maximum_query_rounds=maximum_query_rounds,
        )
    except (InputPlanningError, ValueError) as error:
        if isinstance(error, InputPlanningError):
            code, explanation = error.failure_code, error.explanation
        else:
            code, explanation = "invalid_core_generalization_request", str(error)
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
            system=CORE_GENERALIZATION_SYSTEM_PROMPT,
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
                explanation=response.error or "The model API call failed.",
                failure_code="model_api_failure",
                model_prompts=tuple(prompts),
                model_responses=tuple(responses),
                query_trace=tuple(session.trace),
            )
        payload = extract_json_object(response.content)
        if payload is None:
            error = InputPlanningError(
                "invalid_model_json", "The model response is not one JSON object."
            )
            session.record_protocol_feedback(error)
            if len(session.protocol_feedback) >= MAX_CORE_GENERALIZATION_PROTOCOL_FEEDBACK:
                break
            continue
        payload = _normalize_action(payload)
        try:
            action = payload.get("action")
            if action == "finish":
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
            if action == "stop":
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
            if len(session.protocol_feedback) >= MAX_CORE_GENERALIZATION_PROTOCOL_FEEDBACK:
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
        explanation="The model did not finish or give an auditable stop within the Stage-L turn limit.",
        failure_code="model_turn_limit_exceeded",
        model_prompts=tuple(prompts),
        model_responses=tuple(responses),
        query_trace=tuple(session.trace),
    )
