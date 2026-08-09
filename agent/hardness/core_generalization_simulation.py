"""Prompt-only model double for the Stage-L Core-generalization protocol.

The simulator deliberately sees only the JSON prompt exposed to a real model.
It has no benchmark case IDs, family table, expected failures, or direct access
to a catalog.  Its purpose is to regression-test the query ABI, provenance
checks, typed finish payloads, blockers, and final artifact without HTTP calls.
"""

from __future__ import annotations

import json
from collections import deque
from collections.abc import Mapping, Sequence
from typing import Any

from .core_capability_catalog import NATIVE_COMPLETENESS, NATIVE_MEMBERSHIP
from .core_generalization_planner import (
    COMPLETENESS_TRANSPORT,
    CORE_GENERALIZATION_SYSTEM_PROMPT,
    audit_core_generalization_prompt,
)
from .model_client import ModelResponse


class SimulatedCoreGeneralizationClient:
    """Select only Lean-confirmed rows already visible in the current prompt."""

    def __init__(self) -> None:
        self.logical_turns = 0

    @staticmethod
    def _response(payload: Mapping[str, Any]) -> ModelResponse:
        return ModelResponse(
            called=False,
            ok=True,
            content=json.dumps(payload, ensure_ascii=False, sort_keys=True),
            error=None,
            status_code=None,
            duration_seconds=0.0,
            usage=None,
            attempts=0,
            finish_reason="simulated",
        )

    @staticmethod
    def _history_searches(
        history: Sequence[Any], action: str
    ) -> tuple[Mapping[str, Any], ...]:
        searches: list[Mapping[str, Any]] = []
        for row in history:
            if not isinstance(row, Mapping) or row.get("action") != action:
                continue
            raw = row.get("searches")
            if not isinstance(raw, list):
                continue
            searches.extend(item for item in raw if isinstance(item, Mapping))
        return tuple(searches)

    @classmethod
    def _problem_search_complete(
        cls,
        history: Sequence[Any],
        *,
        input_kind: str,
        input_node: str,
        predicate_node: str,
        domain_node: str,
    ) -> bool:
        searches = cls._history_searches(history, "search_problems")
        if input_kind != "predicate":
            return any(
                input_node in search.get("node_ids", [])
                for search in searches
                if isinstance(search.get("node_ids", []), list)
            )
        exact = any(
            predicate_node in search.get("accepts_node_ids", [])
            and domain_node in search.get("domain_node_ids", [])
            for search in searches
            if isinstance(search.get("accepts_node_ids", []), list)
            and isinstance(search.get("domain_node_ids", []), list)
        )
        carrier = any(
            domain_node in search.get("domain_node_ids", [])
            and not search.get("accepts_node_ids", [])
            for search in searches
            if isinstance(search.get("domain_node_ids", []), list)
        )
        return exact and carrier

    @classmethod
    def _source_was_queried(
        cls, history: Sequence[Any], action: str, source_node: str
    ) -> bool:
        key = (
            "source_node_ids"
            if action in {"search_connections", "search_reductions"}
            else "endpoint_node_ids"
        )
        return any(
            source_node in search.get(key, [])
            for search in cls._history_searches(history, action)
            if isinstance(search.get(key, []), list)
        )

    @classmethod
    def _native_search_done(
        cls, history: Sequence[Any], *, kind: str, endpoint: str | None
    ) -> bool:
        for search in cls._history_searches(history, "search_native_evidence"):
            kinds = search.get("evidence_kinds", [])
            nodes = search.get("endpoint_node_ids", [])
            if not isinstance(kinds, list) or kind not in kinds:
                continue
            if endpoint is None:
                if not nodes:
                    return True
            elif isinstance(nodes, list) and endpoint in nodes:
                return True
        return False

    @classmethod
    def _target_search_done(cls, history: Sequence[Any], policy: str) -> bool:
        return any(
            policy in search.get("required_policies", [])
            for search in cls._history_searches(history, "search_hardness_targets")
            if isinstance(search.get("required_policies", []), list)
        )

    @classmethod
    def _queried_reduction_terms(cls, history: Sequence[Any]) -> frozenset[str]:
        return frozenset(
            term
            for search in cls._history_searches(history, "search_reductions")
            for term in search.get("terms", [])
            if isinstance(term, str) and term
        )

    @staticmethod
    def _evidence_path_atom_hint(evidence: Mapping[str, Any]) -> int:
        term = str(evidence.get("evidence_lean_term") or "")
        return term.count("CertifiedPath.step") + term.count(
            "CertifiedPath.cons"
        )

    @staticmethod
    def _codec_key(problem: Mapping[str, Any]) -> tuple[str, ...]:
        codec = problem.get("codec_group_id")
        if isinstance(codec, str) and codec:
            return ("codec", codec)
        identity = problem.get("encoder_bound_identity_node_id")
        if isinstance(identity, str) and identity:
            return ("identity", identity)
        return (
            "unproven",
            str(problem.get("entry_id")),
            str(problem.get("declaration")),
        )

    @staticmethod
    def _path(
        *,
        source_node: str,
        target_node: str,
        reductions: Sequence[Mapping[str, Any]],
        initial_atoms: int,
        initial_dependencies: frozenset[str],
        minimum_atoms: int,
        maximum_atoms: int,
        maximum_dependencies: int,
        allow_reflexive: bool,
        require_simple: bool,
    ) -> tuple[tuple[Mapping[str, Any], ...] | None, tuple[str, ...]]:
        adjacency: dict[str, list[Mapping[str, Any]]] = {}
        for edge in reductions:
            source = edge.get("source_node_id")
            target = edge.get("target_node_id")
            entry_id = edge.get("entry_id")
            lean_term = edge.get("lean_term")
            if all(isinstance(value, str) and value for value in (source, target, entry_id, lean_term)):
                adjacency.setdefault(str(source), []).append(edge)
        for edges in adjacency.values():
            edges.sort(key=lambda edge: str(edge.get("entry_id")))

        if initial_atoms > maximum_atoms or len(initial_dependencies) > maximum_dependencies:
            return None, ()
        if (
            source_node == target_node
            and minimum_atoms <= initial_atoms <= maximum_atoms
            and (initial_atoms > 0 or allow_reflexive)
        ):
            return (), ()

        initial_visited = frozenset({source_node}) if require_simple else frozenset()
        queue: deque[
            tuple[
                str,
                tuple[Mapping[str, Any], ...],
                int,
                frozenset[str],
                frozenset[str],
            ]
        ] = deque(
            [(source_node, (), initial_atoms, initial_dependencies, initial_visited)]
        )
        seen = {(source_node, initial_atoms, initial_dependencies, initial_visited)}
        frontier: list[str] = []
        while queue:
            node, path, atoms, dependencies, visited = queue.popleft()
            if atoms >= maximum_atoms:
                continue
            frontier.append(node)
            for edge in adjacency.get(node, []):
                next_node = str(edge["target_node_id"])
                if require_simple and next_node in visited:
                    continue
                provenance = {
                    str(item)
                    for item in edge.get("provenance_declarations", [])
                    if isinstance(item, str)
                }
                next_dependencies = dependencies | provenance
                if len(next_dependencies) > maximum_dependencies:
                    continue
                next_atoms = atoms + 1
                next_path = (*path, edge)
                if (
                    next_node == target_node
                    and minimum_atoms <= next_atoms <= maximum_atoms
                ):
                    return next_path, tuple(dict.fromkeys(frontier))
                next_visited = visited | {next_node} if require_simple else visited
                state = (next_node, next_atoms, next_dependencies, next_visited)
                if state not in seen:
                    seen.add(state)
                    queue.append(
                        (
                            next_node,
                            next_path,
                            next_atoms,
                            frozenset(next_dependencies),
                            frozenset(next_visited),
                        )
                    )
        return None, tuple(dict.fromkeys(frontier))

    @staticmethod
    def _render_path(
        *,
        source_declaration: str,
        connection: Mapping[str, Any] | None,
        reductions: Sequence[Mapping[str, Any]],
    ) -> str:
        terms: list[str] = []
        if connection is not None:
            terms.append(str(connection["lean_term"]))
        terms.extend(str(edge["lean_term"]) for edge in reductions)
        if not terms:
            return (
                "ComplexityReduction.Certificate.CertifiedPath.refl "
                + source_declaration
            )
        rendered = (
            "ComplexityReduction.Certificate.CertifiedPath.step ("
            + terms[0]
            + ")"
        )
        for term in terms[1:]:
            rendered = (
                "ComplexityReduction.Certificate.CertifiedPath.cons ("
                + rendered
                + ") ("
                + term
                + ")"
            )
        return rendered

    @staticmethod
    def _selected_problem(
        *,
        input_kind: str,
        input_node: str,
        predicate_node: str,
        domain_node: str,
        problems: Sequence[Any],
    ) -> tuple[Mapping[str, Any] | None, str | None]:
        rows = [row for row in problems if isinstance(row, Mapping)]
        if input_kind == "predicate":
            exact = [
                row
                for row in rows
                if row.get("accepts_exact_defeq") is True
                and row.get("domain_node_id") == domain_node
            ]
            groups = {SimulatedCoreGeneralizationClient._codec_key(row) for row in exact}
            if len(groups) > 1:
                return None, "ambiguous_predicate_presentation"
            if not exact:
                return None, "missing_lawful_presentation"
            return (
                min(
                    exact,
                    key=lambda row: (
                        row.get("registered") is not True,
                        str(row.get("declaration")),
                    ),
                ),
                None,
            )
        exact = [
            row
            for row in rows
            if row.get("problem_node_id") == input_node
            and row.get("exact_defeq") is True
        ]
        return (exact[0], None) if exact else (None, None)

    @staticmethod
    def _finish_common(
        *,
        selected_problem: Mapping[str, Any],
        input_kind: str,
        connection: Mapping[str, Any] | None,
    ) -> dict[str, Any]:
        return {
            "action": "finish",
            "matched_problem": str(selected_problem["declaration"]),
            "match_relation": (
                "accepts_exact_defeq"
                if input_kind == "predicate"
                else (
                    str(connection["relation"])
                    if connection is not None
                    else "exact_defeq"
                )
            ),
            "connection_entry_id": (
                str(connection["entry_id"]) if connection is not None else None
            ),
            "explanation": (
                "Reuse only the exact Lean-confirmed endpoint and bounded capability "
                "rows returned by this session."
            ),
        }

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        if system != CORE_GENERALIZATION_SYSTEM_PROMPT:
            raise ValueError("simulator received the wrong Stage-L system prompt")
        payload = json.loads(prompt)
        if not isinstance(payload, dict):
            raise ValueError("Stage-L prompt must be a JSON object")
        audit_core_generalization_prompt(payload)
        self.logical_turns += 1

        request = payload["request"]
        observation = payload["input_observation"]
        retrieved = payload["retrieved"]
        history = payload.get("query_history", [])
        if not isinstance(request, Mapping) or not isinstance(observation, Mapping):
            raise ValueError("Stage-L prompt has malformed request/observation")
        if not isinstance(retrieved, Mapping) or not isinstance(history, list):
            raise ValueError("Stage-L prompt has malformed retrieved/history views")

        input_kind = str(observation.get("input_kind") or "")
        input_node = str(observation.get("normalized_problem_node_id") or "")
        predicate_node = str(observation.get("predicate_node_id") or "")
        domain_node = str(observation.get("predicate_domain_node_id") or "")
        if not self._problem_search_complete(
            history,
            input_kind=input_kind,
            input_node=input_node,
            predicate_node=predicate_node,
            domain_node=domain_node,
        ):
            if input_kind == "predicate":
                return self._response(
                    {
                        "action": "search_problems",
                        "searches": [
                            {
                                "accepts_node_ids": [predicate_node],
                                "domain_node_ids": [domain_node],
                                "limit": 8,
                            },
                            {"domain_node_ids": [domain_node], "limit": 8},
                        ],
                    }
                )
            return self._response(
                {
                    "action": "search_problems",
                    "searches": [{"node_ids": [input_node], "limit": 8}],
                }
            )

        problems = retrieved.get("problems", [])
        if not isinstance(problems, list):
            raise ValueError("retrieved.problems must be a list")
        selected_problem, problem_failure = self._selected_problem(
            input_kind=input_kind,
            input_node=input_node,
            predicate_node=predicate_node,
            domain_node=domain_node,
            problems=problems,
        )
        terminal = payload.get("terminal_guidance")
        if (
            isinstance(terminal, Mapping)
            and terminal.get("mode") == "stop_now"
            and isinstance(terminal.get("failure_code"), str)
        ):
            return self._response(
                {
                    "action": "stop",
                    "failure_code": terminal["failure_code"],
                    "explanation": str(
                        terminal.get("instruction")
                        or "The bounded Core audit established this blocker."
                    ),
                }
            )
        if problem_failure == "ambiguous_predicate_presentation":
            return self._response(
                {
                    "action": "stop",
                    "failure_code": problem_failure,
                    "explanation": (
                        "The Lean-confirmed predicate matches span incompatible "
                        "encoder-bound presentation identities."
                    ),
                }
            )

        selected_connection: Mapping[str, Any] | None = None
        if selected_problem is None and input_kind != "predicate":
            if not self._source_was_queried(
                history, "search_connections", input_node
            ):
                return self._response(
                    {
                        "action": "search_connections",
                        "searches": [
                            {"source_node_ids": [input_node], "limit": 8}
                        ],
                    }
                )
            connections = retrieved.get("connections", [])
            if not isinstance(connections, list):
                raise ValueError("retrieved.connections must be a list")
            outgoing = [
                row
                for row in connections
                if isinstance(row, Mapping)
                and row.get("source_node_id") == input_node
            ]
            for connection in outgoing:
                target_node = str(connection.get("target_node_id") or "")
                candidates = [
                    row
                    for row in problems
                    if isinstance(row, Mapping)
                    and row.get("problem_node_id") == target_node
                ]
                if candidates:
                    selected_connection = connection
                    selected_problem = candidates[0]
                    break
                if target_node and not self._problem_search_complete(
                    history,
                    input_kind="presented_problem",
                    input_node=target_node,
                    predicate_node="",
                    domain_node="",
                ):
                    return self._response(
                        {
                            "action": "search_problems",
                            "searches": [{"node_ids": [target_node], "limit": 8}],
                        }
                    )
        if selected_problem is None:
            return self._response(
                {
                    "action": "stop",
                    "failure_code": "missing_lawful_presentation",
                    "explanation": (
                        "Exact-node and directed presentation searches returned no "
                        "Lean-certified lawful input relation."
                    ),
                }
            )

        current_node = str(selected_problem["problem_node_id"])
        common = self._finish_common(
            selected_problem=selected_problem,
            input_kind=input_kind,
            connection=selected_connection,
        )
        objective = str(request["objective"])

        native_rows = retrieved.get("native_evidence", [])
        if not isinstance(native_rows, list):
            raise ValueError("retrieved.native_evidence must be a list")
        native = [row for row in native_rows if isinstance(row, Mapping)]
        if objective == "prove_in_np":
            if not self._native_search_done(
                history, kind=NATIVE_MEMBERSHIP, endpoint=current_node
            ):
                return self._response(
                    {
                        "action": "search_native_evidence",
                        "searches": [
                            {
                                "evidence_kinds": [NATIVE_MEMBERSHIP],
                                "endpoint_node_ids": [current_node],
                                "limit": 8,
                            }
                        ],
                    }
                )
            memberships = [
                row
                for row in native
                if row.get("evidence_kind") == NATIVE_MEMBERSHIP
                and row.get("endpoint_node_id") == current_node
            ]
            if not memberships:
                return self._response(
                    {
                        "action": "stop",
                        "failure_code": "missing_native_membership",
                        "explanation": (
                            "No exact NativeTMInNP row was returned for the input endpoint."
                        ),
                    }
                )
            evidence = memberships[0]
            return self._response(
                {
                    **common,
                    "membership_evidence_id": evidence["entry_id"],
                    "membership_declaration": evidence["evidence_declaration"],
                    "membership_lean_term": evidence["lean_term"],
                }
            )

        reductions_raw = retrieved.get("reductions", [])
        if not isinstance(reductions_raw, list):
            raise ValueError("retrieved.reductions must be a list")
        reductions = [row for row in reductions_raw if isinstance(row, Mapping)]
        minimum_atoms = int(request["minimum_route_atoms"])
        maximum_atoms = int(request["maximum_route_atoms"])
        maximum_dependencies = int(request["maximum_dependencies"])
        allow_reflexive = bool(request["allow_reflexive_target"])
        require_simple = bool(request["require_simple_path"])

        if objective == "prove_np_complete":
            if not self._native_search_done(
                history, kind=NATIVE_MEMBERSHIP, endpoint=current_node
            ):
                return self._response(
                    {
                        "action": "search_native_evidence",
                        "searches": [
                            {
                                "evidence_kinds": [NATIVE_MEMBERSHIP],
                                "endpoint_node_ids": [current_node],
                                "limit": 8,
                            }
                        ],
                    }
                )
            if not self._native_search_done(
                history, kind=NATIVE_COMPLETENESS, endpoint=None
            ):
                return self._response(
                    {
                        "action": "search_native_evidence",
                        "searches": [
                            {
                                "evidence_kinds": [NATIVE_COMPLETENESS],
                                "limit": 8,
                            }
                        ],
                    }
                )
            memberships = [
                row
                for row in native
                if row.get("evidence_kind") == NATIVE_MEMBERSHIP
                and row.get("endpoint_node_id") == current_node
            ]
            hubs = [
                row
                for row in native
                if row.get("evidence_kind") == NATIVE_COMPLETENESS
            ]
            candidates: list[
                tuple[tuple[Mapping[str, Any], ...], Mapping[str, Any], Mapping[str, Any]]
            ] = []
            visible_frontier: list[str] = []
            for hub in hubs:
                for membership in memberships:
                    initial_dependencies = frozenset(
                        {
                            COMPLETENESS_TRANSPORT,
                            *(
                                str(item)
                                for item in hub.get("provenance_declarations", [])
                                if isinstance(item, str)
                            ),
                            *(
                                str(item)
                                for item in membership.get("provenance_declarations", [])
                                if isinstance(item, str)
                            ),
                        }
                    )
                    path, frontier = self._path(
                        source_node=str(hub["endpoint_node_id"]),
                        target_node=current_node,
                        reductions=reductions,
                        initial_atoms=0,
                        initial_dependencies=initial_dependencies,
                        minimum_atoms=minimum_atoms,
                        maximum_atoms=maximum_atoms,
                        maximum_dependencies=maximum_dependencies,
                        allow_reflexive=allow_reflexive,
                        require_simple=require_simple,
                    )
                    visible_frontier.extend(frontier)
                    if path is not None:
                        candidates.append((path, hub, membership))
            if not candidates:
                hub_nodes = [str(hub["endpoint_node_id"]) for hub in hubs]
                unqueried = [
                    node
                    for node in (*hub_nodes, *visible_frontier)
                    if node
                    and not self._source_was_queried(
                        history, "search_reductions", node
                    )
                ]
                if unqueried:
                    return self._response(
                        {
                            "action": "search_reductions",
                            "searches": [
                                {"source_node_ids": [node], "limit": 8}
                                for node in tuple(dict.fromkeys(unqueried))[:4]
                            ],
                        }
                    )
                return self._response(
                    {
                        "action": "stop",
                        "failure_code": "missing_native_completeness",
                        "explanation": (
                            "No exact native completeness row or valid complete-hub-to-target "
                            "transport with exact target membership is available."
                        ),
                    }
                )
            path, hub, membership = min(
                candidates,
                key=lambda item: (
                    len(item[0]),
                    str(item[1]["entry_id"]),
                    tuple(str(edge["entry_id"]) for edge in item[0]),
                ),
            )
            path_term = self._render_path(
                source_declaration=str(hub["endpoint_declaration"]),
                connection=None,
                reductions=path,
            )
            completeness_term = (
                COMPLETENESS_TRANSPORT
                + " ("
                + str(hub["lean_term"])
                + ") ("
                + path_term
                + ") ("
                + str(membership["lean_term"])
                + ")"
            )
            return self._response(
                {
                    **common,
                    "hub_completeness_evidence_id": hub["entry_id"],
                    "target_membership_evidence_id": membership["entry_id"],
                    "reduction_entry_ids": [edge["entry_id"] for edge in path],
                    "completeness_lean_term": completeness_term,
                }
            )

        selected_target: Mapping[str, Any] | None = None
        selected_target_evidence: Mapping[str, Any] | None = None
        if objective == "reduce_to":
            fixed_target = payload.get("fixed_target")
            if not isinstance(fixed_target, Mapping):
                raise ValueError("fixed reduction prompt has no target observation")
            target_node = str(fixed_target["node_id"])
            target_declaration = str(fixed_target["declaration"])
            initial_target_dependencies: frozenset[str] = frozenset()
        else:
            policy = str(request["required_hardness"])
            if not self._target_search_done(history, policy):
                return self._response(
                    {
                        "action": "search_hardness_targets",
                        "searches": [
                            {"required_policies": [policy], "limit": 8}
                        ],
                    }
                )
            target_rows = retrieved.get("hardness_targets", [])
            if not isinstance(target_rows, list):
                raise ValueError("retrieved.hardness_targets must be a list")
            eligible: list[tuple[Mapping[str, Any], Mapping[str, Any]]] = []
            for target in target_rows:
                if not isinstance(target, Mapping):
                    continue
                evidences = target.get("evidences", [])
                if not isinstance(evidences, list):
                    continue
                for evidence in evidences:
                    if (
                        isinstance(evidence, Mapping)
                        and evidence.get("request_eligible") is True
                    ):
                        eligible.append((target, evidence))
            if not eligible:
                return self._response(
                    {
                        "action": "stop",
                        "failure_code": "no_eligible_hardness_target",
                        "explanation": (
                            "The bounded target query returned no same-fingerprint evidence "
                            "satisfying the public policy and dependency limit."
                        ),
                    }
                )
            target_candidates: list[
                tuple[
                    tuple[Mapping[str, Any], ...],
                    Mapping[str, Any],
                    Mapping[str, Any],
                ]
            ] = []
            visible_frontier: list[str] = []
            for target, evidence in eligible:
                evidence_dependencies = frozenset(
                    str(item)
                    for item in evidence.get("provenance_declarations", [])
                    if isinstance(item, str)
                )
                candidate_path, candidate_frontier = self._path(
                    source_node=current_node,
                    target_node=str(target["target_node_id"]),
                    reductions=reductions,
                    initial_atoms=0,
                    initial_dependencies=evidence_dependencies,
                    minimum_atoms=minimum_atoms,
                    maximum_atoms=maximum_atoms,
                    maximum_dependencies=maximum_dependencies,
                    allow_reflexive=allow_reflexive,
                    require_simple=require_simple,
                )
                visible_frontier.extend(candidate_frontier)
                if candidate_path is not None:
                    target_candidates.append(
                        (candidate_path, target, evidence)
                    )
            if target_candidates:
                path, selected_target, selected_target_evidence = min(
                    target_candidates,
                    key=lambda item: (
                        len(item[0]),
                        str(item[1].get("target_declaration")),
                        str(item[2].get("evidence_id")),
                    ),
                )
                finish = {
                    **common,
                    "reduction_entry_ids": [edge["entry_id"] for edge in path],
                    "lean_term": self._render_path(
                        source_declaration=(
                            str(selected_problem["declaration"])
                            if input_kind == "predicate"
                            else str(observation["input_declaration"])
                        ),
                        connection=selected_connection,
                        reductions=path,
                    ),
                    "target_entry_id": selected_target["target_entry_id"],
                    "target_evidence_id": selected_target_evidence["evidence_id"],
                    "target_declaration": selected_target["target_declaration"],
                }
                return self._response(finish)

            queried_terms = self._queried_reduction_terms(history)
            evidence_searches: list[dict[str, Any]] = []
            for _, evidence in sorted(
                eligible,
                key=lambda pair: (
                    -self._evidence_path_atom_hint(pair[1]),
                    str(pair[0].get("target_declaration")),
                    str(pair[1].get("evidence_id")),
                ),
            ):
                if self._evidence_path_atom_hint(evidence) <= 0:
                    continue
                terms = tuple(
                    dict.fromkeys(
                        str(item)
                        for item in evidence.get("provenance_declarations", [])
                        if isinstance(item, str)
                        and item
                        and item not in queried_terms
                    )
                )
                if terms:
                    evidence_searches.append(
                        {"terms": list(terms[:8]), "limit": 8}
                    )
                if len(evidence_searches) == 4:
                    break
            if evidence_searches:
                return self._response(
                    {
                        "action": "search_reductions",
                        "searches": evidence_searches,
                    }
                )

            unqueried = [
                node
                for node in (current_node, *visible_frontier)
                if node
                and not self._source_was_queried(
                    history, "search_reductions", node
                )
            ]
            if unqueried:
                return self._response(
                    {
                        "action": "search_reductions",
                        "searches": [
                            {"source_node_ids": [node], "limit": 8}
                            for node in tuple(dict.fromkeys(unqueried))[:4]
                        ],
                    }
                )

            queried_prefixes = {
                str(prefix)
                for search in self._history_searches(
                    history, "search_hardness_targets"
                )
                for prefix in search.get("namespace_prefixes", [])
                if isinstance(prefix, str)
            }
            hints = payload.get("hardness_target_hints")
            nearby = (
                hints.get("nearby_namespaces", [])
                if isinstance(hints, Mapping)
                else []
            )
            unqueried_prefixes = [
                str(row["namespace"])
                for row in nearby
                if isinstance(row, Mapping)
                and isinstance(row.get("namespace"), str)
                and row["namespace"] not in queried_prefixes
            ]
            if unqueried_prefixes:
                return self._response(
                    {
                        "action": "search_hardness_targets",
                        "searches": [
                            {
                                "required_policies": [policy],
                                "namespace_prefixes": [prefix],
                                "limit": 8,
                            }
                            for prefix in unqueried_prefixes[:4]
                        ],
                    }
                )
            return self._response(
                {
                    "action": "stop",
                    "failure_code": "eligible_target_has_no_existing_route",
                    "explanation": (
                        "Eligible target evidence exists, but bounded directed searches "
                        "expose no allowed Core path from the exact source."
                    ),
                }
            )

        initial_dependencies = set(initial_target_dependencies)
        initial_atoms = 0
        if selected_connection is not None:
            initial_atoms = 1
            for key in ("certificate_declaration", "projection_declaration"):
                declaration = selected_connection.get(key)
                if isinstance(declaration, str):
                    initial_dependencies.add(declaration)
        path, frontier = self._path(
            source_node=current_node,
            target_node=target_node,
            reductions=reductions,
            initial_atoms=initial_atoms,
            initial_dependencies=frozenset(initial_dependencies),
            minimum_atoms=minimum_atoms,
            maximum_atoms=maximum_atoms,
            maximum_dependencies=maximum_dependencies,
            allow_reflexive=allow_reflexive,
            require_simple=require_simple,
        )
        if path is None:
            unqueried = [
                node
                for node in (current_node, *frontier)
                if node
                and not self._source_was_queried(
                    history, "search_reductions", node
                )
            ]
            if unqueried:
                return self._response(
                    {
                        "action": "search_reductions",
                        "searches": [
                            {"source_node_ids": [node], "limit": 8}
                            for node in tuple(dict.fromkeys(unqueried))[:4]
                        ],
                    }
                )
            return self._response(
                {
                    "action": "stop",
                    "failure_code": "eligible_target_has_no_existing_route",
                    "explanation": (
                        "The bounded directed reduction searches expose no path to the "
                        "fixed or policy-selected target."
                    ),
                }
            )

        finish = {
            **common,
            "reduction_entry_ids": [edge["entry_id"] for edge in path],
            "lean_term": self._render_path(
                source_declaration=(
                    str(selected_problem["declaration"])
                    if input_kind == "predicate"
                    else str(observation["input_declaration"])
                ),
                connection=selected_connection,
                reductions=path,
            ),
        }
        if selected_target is not None and selected_target_evidence is not None:
            finish.update(
                {
                    "target_entry_id": selected_target["target_entry_id"],
                    "target_evidence_id": selected_target_evidence["evidence_id"],
                    "target_declaration": target_declaration,
                }
            )
        return self._response(finish)
