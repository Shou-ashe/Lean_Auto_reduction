"""Prompt-only model double for Stage G/H offline integration tests."""

from __future__ import annotations

import json
from collections import deque
from collections.abc import Mapping
from typing import Any

from .model_client import ModelResponse
from .open_target import audit_open_target_prompt
from .predicate_input import audit_predicate_input_prompt


class SimulatedOpenTargetClient:
    """Choose only from bounded facts visible in each stateless model prompt."""

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
    def _searched(
        history: list[Any], action: str, *, source_node: str | None = None
    ) -> bool:
        for row in history:
            if not isinstance(row, Mapping) or row.get("action") != action:
                continue
            if source_node is None:
                return True
            searches = row.get("searches", [])
            if not isinstance(searches, list):
                continue
            for search in searches:
                if not isinstance(search, Mapping):
                    continue
                key = "node_ids" if action == "search_problems" else "source_node_ids"
                nodes = search.get(key, [])
                if isinstance(nodes, list) and source_node in nodes:
                    return True
        return False

    @staticmethod
    def _searched_predicate_problems(
        history: list[Any], *, predicate_node: str, domain_node: str
    ) -> bool:
        """Require both the exact accepts/domain and carrier-only lookups.

        The second lookup is what lets the model distinguish a known carrier
        with a different predicate from a carrier with no lawful presentation.
        """

        exact_lookup = False
        domain_lookup = False
        for row in history:
            if not isinstance(row, Mapping) or row.get("action") != "search_problems":
                continue
            searches = row.get("searches", [])
            if not isinstance(searches, list):
                continue
            for search in searches:
                if not isinstance(search, Mapping):
                    continue
                accepts_nodes = search.get("accepts_node_ids", [])
                domain_nodes = search.get("domain_node_ids", [])
                if not isinstance(accepts_nodes, list) or not isinstance(
                    domain_nodes, list
                ):
                    continue
                if predicate_node in accepts_nodes and domain_node in domain_nodes:
                    exact_lookup = True
                if domain_node in domain_nodes and not accepts_nodes:
                    domain_lookup = True
        return exact_lookup and domain_lookup

    @staticmethod
    def _predicate_codec_key(problem: Mapping[str, Any]) -> tuple[str, ...]:
        """Group public aliases without merging incompatible presentations."""

        codec_group_id = problem.get("codec_group_id")
        if isinstance(codec_group_id, str) and codec_group_id:
            return ("codec_group_id", codec_group_id)
        encoder_identity = problem.get("encoder_bound_identity_node_id")
        if isinstance(encoder_identity, str) and encoder_identity:
            return ("encoder_bound_identity_node_id", encoder_identity)
        # Missing codec evidence must never make two rows look compatible.
        entry_id = problem.get("entry_id")
        declaration = problem.get("declaration")
        return ("unproven_codec", str(entry_id), str(declaration))

    @staticmethod
    def _searched_reductions(
        history: list[Any],
        *,
        source_node: str,
        target_node: str | None = None,
        outgoing_only: bool = False,
    ) -> bool:
        """Distinguish a target-filtered lookup from complete outgoing lookup."""

        for row in history:
            if not isinstance(row, Mapping) or row.get("action") != "search_reductions":
                continue
            searches = row.get("searches", [])
            if not isinstance(searches, list):
                continue
            for search in searches:
                if not isinstance(search, Mapping):
                    continue
                sources = search.get("source_node_ids", [])
                if not isinstance(sources, list) or source_node not in sources:
                    continue
                targets = search.get("target_node_ids", [])
                if outgoing_only:
                    if not isinstance(targets, list) or not targets:
                        return True
                    continue
                if target_node is None:
                    return True
                if isinstance(targets, list) and target_node in targets:
                    return True
        return False

    @staticmethod
    def _allowed_reduction_path(
        *,
        current_node: str,
        target_node: str,
        reductions: list[Mapping[str, Any]],
        initial_atoms: int,
        initial_dependencies: frozenset[str],
        minimum_route_atoms: int,
        maximum_route_atoms: int,
        maximum_dependencies: int,
        allow_reflexive_target: bool,
        require_simple_path: bool,
    ) -> tuple[list[Mapping[str, Any]] | None, set[str]]:
        adjacency: dict[str, list[Mapping[str, Any]]] = {}
        for edge in reductions:
            adjacency.setdefault(str(edge["source_node_id"]), []).append(edge)
        for edges in adjacency.values():
            edges.sort(key=lambda edge: str(edge["declaration"]))

        if (
            initial_atoms > maximum_route_atoms
            or len(initial_dependencies) > maximum_dependencies
        ):
            return None, set()
        if (
            current_node == target_node
            and initial_atoms >= minimum_route_atoms
            and (initial_atoms > 0 or allow_reflexive_target)
        ):
            return [], set()

        queue: deque[
            tuple[
                str,
                list[Mapping[str, Any]],
                int,
                frozenset[str],
                frozenset[str],
            ]
        ] = deque(
            [
                (
                    current_node,
                    [],
                    initial_atoms,
                    initial_dependencies,
                    frozenset({current_node}) if require_simple_path else frozenset(),
                )
            ]
        )
        seen = {
            (
                current_node,
                initial_atoms,
                initial_dependencies,
                frozenset({current_node}) if require_simple_path else frozenset(),
            )
        }
        searchable_frontier: set[str] = set()
        while queue:
            node, path, atoms, dependencies, visited = queue.popleft()
            if atoms >= maximum_route_atoms:
                continue
            searchable_frontier.add(node)
            for edge in adjacency.get(node, []):
                next_node = str(edge["target_node_id"])
                if require_simple_path and next_node in visited:
                    continue
                next_atoms = atoms + 1
                next_dependencies = dependencies | {str(edge["declaration"])}
                if len(next_dependencies) > maximum_dependencies:
                    continue
                next_path = [*path, edge]
                if next_node == target_node and next_atoms >= minimum_route_atoms:
                    return next_path, searchable_frontier
                if require_simple_path and next_node == target_node:
                    continue
                next_visited = (
                    visited | {next_node} if require_simple_path else visited
                )
                state = (next_node, next_atoms, next_dependencies, next_visited)
                if state not in seen:
                    seen.add(state)
                    queue.append(
                        (
                            next_node,
                            next_path,
                            next_atoms,
                            next_dependencies,
                            next_visited,
                        )
                    )
        return None, searchable_frontier

    @staticmethod
    def _render_path(
        connection: Mapping[str, Any] | None,
        reductions: list[Mapping[str, Any]],
        *,
        source_declaration: str,
    ) -> str:
        atoms: list[tuple[str, bool]] = []
        if connection is not None:
            atoms.append((str(connection["lean_term"]), True))
        atoms.extend((str(edge["declaration"]), False) for edge in reductions)
        if not atoms:
            return (
                "ComplexityReduction.Certificate.CertifiedPath.refl "
                + source_declaration
            )
        first, parenthesized = atoms[0]
        rendered = f"({first})" if parenthesized else first
        term = "ComplexityReduction.Certificate.CertifiedPath.step " + rendered
        for atom, parenthesized in atoms[1:]:
            rendered = f"({atom})" if parenthesized else atom
            term = (
                "ComplexityReduction.Certificate.CertifiedPath.cons ("
                + term
                + ") "
                + rendered
            )
        return term

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        if "JSON" not in system or "search_hardness_targets" not in system:
            raise ValueError("simulated client received the wrong open-target system prompt")
        payload = json.loads(prompt)
        if not isinstance(payload, dict):
            raise ValueError("open-target prompt must be a JSON object")
        audit_open_target_prompt(payload)
        observation = payload["input_observation"]
        predicate_mode = observation.get("input_kind") == "predicate"
        if predicate_mode:
            audit_predicate_input_prompt(payload)
        constraints = payload.get("constraints")
        target_routes_hidden = bool(
            isinstance(constraints, dict)
            and constraints.get("target_routes_are_not_included") is True
        )
        transported_provenance_only = bool(
            isinstance(constraints, dict)
            and constraints.get(
                "target_evidence_transport_provenance_may_be_included"
            )
            is True
            and constraints.get("input_route_is_not_preselected") is True
        )
        if not (target_routes_hidden or transported_provenance_only):
            raise ValueError("open-target prompt failed to preserve route isolation")
        self.logical_turns += 1

        request = payload["request"]
        retrieved = payload["retrieved"]
        history = payload.get("query_history", [])
        if not isinstance(history, list):
            raise ValueError("query_history must be a list")
        input_node = str(observation.get("normalized_problem_node_id") or "")
        predicate_node = str(observation.get("predicate_node_id") or "")
        predicate_domain_node = str(
            observation.get("predicate_domain_node_id") or ""
        )

        if predicate_mode:
            if not predicate_node or not predicate_domain_node:
                raise ValueError("predicate prompt has no predicate/domain node IDs")
            if not self._searched_predicate_problems(
                history,
                predicate_node=predicate_node,
                domain_node=predicate_domain_node,
            ):
                return self._response(
                    {
                        "action": "search_problems",
                        "searches": [
                            {
                                "accepts_node_ids": [predicate_node],
                                "domain_node_ids": [predicate_domain_node],
                                "limit": 8,
                            },
                            {
                                "domain_node_ids": [predicate_domain_node],
                                "limit": 8,
                            },
                        ],
                    }
                )
        elif not self._searched(
            history, "search_problems", source_node=input_node
        ):
            return self._response(
                {
                    "action": "search_problems",
                    "searches": [{"node_ids": [input_node], "limit": 8}],
                }
            )

        problems = retrieved["problems"]
        if not isinstance(problems, list):
            raise ValueError("retrieved.problems must be a list")
        if predicate_mode:
            exact = [
                item
                for item in problems
                if isinstance(item, Mapping)
                and item.get("accepts_exact_defeq") is True
                and item.get("domain_node_id") == predicate_domain_node
            ]
            codec_groups: dict[tuple[str, ...], list[Mapping[str, Any]]] = {}
            for item in exact:
                codec_groups.setdefault(
                    self._predicate_codec_key(item), []
                ).append(item)
            if len(codec_groups) > 1:
                return self._response(
                    {
                        "action": "stop",
                        "failure_code": "ambiguous_predicate_presentation",
                        "explanation": (
                            "Lean-confirmed accepts matches were retrieved for more than "
                            "one encoder-bound presentation identity. A raw predicate "
                            "cannot choose between incompatible codecs."
                        ),
                    }
                )
            if not codec_groups:
                carrier_presentations = [
                    item
                    for item in problems
                    if isinstance(item, Mapping)
                    and item.get("domain_node_id") == predicate_domain_node
                ]
                if carrier_presentations:
                    return self._response(
                        {
                            "action": "stop",
                            "failure_code": (
                                "predicate_accepts_not_definitionally_equal"
                            ),
                            "explanation": (
                                "The domain-only search found lawful presentations for "
                                "the predicate carrier, but no retrieved row was marked "
                                "accepts_exact_defeq by the nonce-bound Lean observation."
                            ),
                        }
                    )
                return self._response(
                    {
                        "action": "stop",
                        "failure_code": "predicate_has_no_lawful_presentation",
                        "explanation": (
                            "The exact accepts/domain and domain-only searches returned "
                            "no Lean-confirmed lawful PresentedProblem for this predicate."
                        ),
                    }
                )
            aliases = next(iter(codec_groups.values()))
            selected_problem = min(
                aliases,
                key=lambda item: (
                    item.get("registered") is not True,
                    str(item.get("declaration")),
                ),
            )
            current_node = str(selected_problem["problem_node_id"])
        else:
            exact = [
                item
                for item in problems
                if isinstance(item, Mapping)
                and item.get("problem_node_id") == input_node
                and item.get("exact_defeq") is True
            ]
            selected_problem = exact[0] if exact else None
            current_node = input_node
        selected_connection: Mapping[str, Any] | None = None
        if not predicate_mode and selected_problem is None and not self._searched(
            history, "search_connections", source_node=input_node
        ):
            return self._response(
                {
                    "action": "search_connections",
                    "searches": [{"source_node_ids": [input_node], "limit": 8}],
                }
            )
        if not predicate_mode and selected_problem is None:
            outgoing = [
                item
                for item in retrieved["connections"]
                if isinstance(item, Mapping)
                and item.get("source_node_id") == input_node
            ]
            if not outgoing:
                return self._response(
                    {
                        "action": "stop",
                        "failure_code": "no_lean_verified_problem_match",
                        "explanation": (
                            "Exact-node and outgoing-connection searches returned no "
                            "Lean-verified problem match."
                        ),
                    }
                )
            for connection in outgoing:
                connection_target = connection.get("target_node_id")
                candidates = [
                    item
                    for item in retrieved["problems"]
                    if isinstance(item, Mapping)
                    and item.get("problem_node_id") == connection_target
                ]
                if candidates:
                    selected_connection = connection
                    selected_problem = candidates[0]
                    current_node = str(connection_target)
                    break
                if isinstance(connection_target, str) and not self._searched(
                    history, "search_problems", source_node=connection_target
                ):
                    return self._response(
                        {
                            "action": "search_problems",
                            "searches": [
                                {"node_ids": [connection_target], "limit": 8}
                            ],
                        }
                    )
            if selected_problem is None:
                raise ValueError("retrieved input connections do not reach a problem")

        required_policy = str(request["required_hardness"])
        if not self._searched(history, "search_hardness_targets"):
            return self._response(
                {
                    "action": "search_hardness_targets",
                    "searches": [
                        {
                            "required_policies": [required_policy],
                            "limit": 8,
                        }
                    ],
                }
            )

        eligible: list[tuple[Mapping[str, Any], Mapping[str, Any]]] = []
        for target in retrieved["hardness_targets"]:
            if not isinstance(target, Mapping):
                continue
            for evidence in target.get("evidences", []):
                if isinstance(evidence, Mapping) and evidence.get(
                    "request_eligible"
                ) is True:
                    eligible.append((target, evidence))
        if not eligible:
            return self._response(
                {
                    "action": "stop",
                    "failure_code": "no_eligible_hardness_target",
                    "explanation": (
                        "The bounded Lean target search returned no evidence satisfying "
                        "the requested policy, evidence-kind, and dependency limits."
                    ),
                }
            )

        reachable = [
            pair
            for pair in eligible
            if pair[1].get("policy_route_allowed") is True
        ]
        reachable.sort(
            key=lambda pair: (
                int(
                    pair[1].get("shortest_policy_route_atom_count")
                    if pair[1].get("shortest_policy_route_atom_count") is not None
                    else 1_000_000
                ),
                str(pair[0].get("target_declaration")),
                str(pair[1].get("evidence_id")),
            )
        )
        match_relation = (
            "accepts_exact_defeq"
            if predicate_mode
            else (
                str(selected_connection["relation"])
                if selected_connection is not None
                else "exact_defeq"
            )
        )
        connection_id = (
            selected_connection.get("entry_id")
            if selected_connection is not None
            else None
        )
        if not reachable:
            if not self._searched_reductions(
                history,
                source_node=current_node,
                outgoing_only=True,
            ):
                return self._response(
                    {
                        "action": "search_reductions",
                        "searches": [
                            {"source_node_ids": [current_node], "limit": 8}
                        ],
                    }
                )
            return self._response(
                {
                    "action": "stop",
                    "failure_code": "eligible_target_has_no_existing_route",
                    "matched_problem": selected_problem["declaration"],
                    "match_relation": match_relation,
                    "connection_entry_id": connection_id,
                    "explanation": (
                        "Lean-validated targets satisfy the policy, but the bounded directed "
                        "reduction search has no allowed source-to-target path."
                    ),
                }
            )

        selected_target, selected_evidence = reachable[0]
        target_node = str(selected_target["target_node_id"])
        maximum_route_atoms = int(request["maximum_route_atoms"])
        minimum_route_atoms = int(request.get("minimum_route_atoms", 0))
        maximum_dependencies = int(request["maximum_dependencies"])
        allow_reflexive_target = bool(request["allow_reflexive_target"])
        require_simple_path = bool(request.get("require_simple_path", False))
        reductions = [
            item
            for item in retrieved["reductions"]
            if isinstance(item, Mapping)
            and isinstance(item.get("declaration"), str)
            and isinstance(item.get("source_node_id"), str)
            and isinstance(item.get("target_node_id"), str)
        ]
        initial_dependencies = {
            str(item)
            for item in selected_evidence.get("provenance_declarations", [])
            if isinstance(item, str)
        }
        initial_atoms = 0
        if selected_connection is not None:
            initial_atoms = 1
            for key in ("certificate_declaration", "projection_declaration"):
                declaration = selected_connection.get(key)
                if isinstance(declaration, str):
                    initial_dependencies.add(declaration)
        shortest, frontier = self._allowed_reduction_path(
            current_node=current_node,
            target_node=target_node,
            reductions=reductions,
            initial_atoms=initial_atoms,
            initial_dependencies=frozenset(initial_dependencies),
            minimum_route_atoms=minimum_route_atoms,
            maximum_route_atoms=maximum_route_atoms,
            maximum_dependencies=maximum_dependencies,
            allow_reflexive_target=allow_reflexive_target,
            require_simple_path=require_simple_path,
        )

        guidance = payload.get("frontier_guidance")
        suggested_searches = (
            guidance.get("suggested_searches")
            if isinstance(guidance, Mapping)
            and isinstance(guidance.get("suggested_searches"), list)
            else []
        )
        if shortest is None and suggested_searches:
            return self._response(
                {
                    "action": "search_reductions",
                    "searches": [
                        dict(search)
                        for search in suggested_searches[:4]
                        if isinstance(search, Mapping)
                    ],
                }
            )

        if shortest is None and not self._searched_reductions(
            history,
            source_node=current_node,
            target_node=target_node,
        ):
            return self._response(
                {
                    "action": "search_reductions",
                    "searches": [
                        {
                            "source_node_ids": [current_node],
                            "target_node_ids": [target_node],
                            "limit": 8,
                        }
                    ],
                }
            )
        if shortest is None:
            unqueried_frontier = [
                node
                for node in frontier
                if not self._searched_reductions(
                    history,
                    source_node=node,
                    outgoing_only=True,
                )
            ]
            if unqueried_frontier:
                return self._response(
                    {
                        "action": "search_reductions",
                        "searches": [
                            {"source_node_ids": [node], "limit": 8}
                            for node in sorted(unqueried_frontier)[:4]
                        ],
                    }
                )
            raise ValueError("target was reported reachable but no route was retrievable")

        reduction_declarations = [str(edge["declaration"]) for edge in shortest]
        return self._response(
            {
                "action": "finish",
                "matched_problem": selected_problem["declaration"],
                "match_relation": match_relation,
                "connection_entry_id": connection_id,
                "target_entry_id": selected_target["target_entry_id"],
                "target_evidence_id": selected_evidence["evidence_id"],
                "target_declaration": selected_target["target_declaration"],
                "reduction_declarations": reduction_declarations,
                "lean_term": self._render_path(
                    selected_connection,
                    shortest,
                    source_declaration=(
                        str(selected_problem["declaration"])
                        if predicate_mode
                        else str(observation["input_declaration"])
                    ),
                ),
                "explanation": (
                    "Select the shortest policy-compliant reachable target returned by the "
                    "bounded target query and compose only retrieved directed reductions."
                ),
            }
        )
