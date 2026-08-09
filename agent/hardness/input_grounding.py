"""Offline input-grounding benchmark support without hidden route selection.

The simulated client is a protocol test double, not part of the production
planner.  It sees only the same bounded prompt payload as a real model, chooses
returned exact-node candidates and direct returned reductions, and never reads
benchmark expected answers or a route fixture table.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping

from .benchmark import BenchmarkCase, BenchmarkSuite
from .model_client import ModelResponse


INPUT_GROUNDING_SUITE_ID = "input-grounding-fixed-target"
EXPECTED_CASE_COUNT = 24
EXPECTED_POSITIVE_COUNT = 18
EXPECTED_NEGATIVE_COUNT = 6
REPRESENTATION_COMPARISON_SUITE_ID = (
    "input-grounding-representation-comparison"
)
REPRESENTATION_COMPARISON_CASE_COUNT = 36
REPRESENTATION_COMPARISON_GROUP_COUNT = 18
REPRESENTATION_COMPARISON_CATALOG_MODES = frozenset(
    {"flat_api", "component_catalog"}
)
REPRESENTATION_COMPARISON_STUDY_FAMILIES = frozenset(
    {"graph", "clause_csp", "incidence"}
)
REPRESENTATION_COMPARISON_FAMILY_BY_MODULE_LEAF = {
    "Graph": "graph",
    "Clause": "clause_csp",
    "Incidence": "incidence",
}
REPRESENTATION_COMPARISON_GROUP_IDS = frozenset(
    {
        "input-graph-direct",
        "input-graph-alias",
        "input-graph-wrapped",
        "input-structured-cnf-direct",
        "input-structured-cnf-alias",
        "input-structured-cnf-wrapped",
        "input-two-cnf-direct",
        "input-two-cnf-alias",
        "input-two-cnf-wrapped",
        "input-three-sat-direct",
        "input-three-sat-alias",
        "input-three-sat-wrapped",
        "input-exact-cover-direct",
        "input-exact-cover-alias",
        "input-exact-cover-wrapped",
        "input-modified-exact-cover-direct",
        "input-modified-exact-cover-alias",
        "input-modified-exact-cover-wrapped",
    }
)
PROMPT_FORBIDDEN_KEYS = {
    "expected",
    "expected_match_node",
    "family_id",
    "study_family",
    "source_form_id",
    "target_form_id",
    "matched_pair_id",
    "comparison_group_id",
    "logical_source",
    "input_form",
    "gold_match",
    "gold_route",
}


def validate_input_grounding_suite(suite: BenchmarkSuite) -> tuple[BenchmarkCase, ...]:
    """Enforce the fixed-target 18-positive/6-negative study boundary."""

    cases = suite.cases
    positives = tuple(case for case in cases if case.is_positive)
    negatives = tuple(case for case in cases if not case.is_positive)
    if suite.id != INPUT_GROUNDING_SUITE_ID:
        raise ValueError(f"expected suite {INPUT_GROUNDING_SUITE_ID}, got {suite.id}")
    if len(cases) != EXPECTED_CASE_COUNT:
        raise ValueError(f"input-grounding suite must contain {EXPECTED_CASE_COUNT} cases")
    if len(positives) != EXPECTED_POSITIVE_COUNT or len(negatives) != EXPECTED_NEGATIVE_COUNT:
        raise ValueError(
            "input-grounding suite must contain exactly 18 positive and 6 negative cases"
        )
    for case in cases:
        if (
            case.objective != "reduce_to"
            or case.target_policy != "fixed"
            or not case.target
            or case.catalog_mode != "full"
            or case.evaluation_lane != "input_grounding"
            or case.effective_input_declaration != case.source
            or case.family_id is not None
            or case.source_form_id is not None
            or case.target_form_id is not None
            or case.matched_pair_id is not None
        ):
            raise ValueError(f"case {case.id} is outside the input-grounding study ABI")
    return cases


def _representation_comparison_signature(case: BenchmarkCase) -> tuple[Any, ...]:
    """Return every paired field except the case ID and selected catalog view."""

    return (
        case.suite_id,
        case.module,
        case.source,
        case.input_declaration,
        case.input_kind,
        case.membership,
        case.target,
        case.objective,
        case.objective_direction,
        case.target_policy,
        case.planner,
        case.execution_layer,
        case.verification_profile,
        case.enabled,
        case.min_agent_phase,
        case.disabled_reason,
        dict(case.authoring_policy),
        case.expected,
        dict(case.coverage),
        dict(case.resources),
        case.tags,
        case.group_id,
        case.evaluation_lane,
        case.matched_pair_id,
        case.comparison_group_id,
        case.family_id,
        case.source_form_id,
        case.target_form_id,
        case.hub_ids,
    )


def validate_representation_comparison_suite(
    suite: BenchmarkSuite,
) -> tuple[BenchmarkCase, ...]:
    """Enforce the Stage F 18-pair flat-vs-components comparison boundary."""

    cases = suite.cases
    if suite.id != REPRESENTATION_COMPARISON_SUITE_ID:
        raise ValueError(
            f"expected suite {REPRESENTATION_COMPARISON_SUITE_ID}, got {suite.id}"
        )
    if len(cases) != REPRESENTATION_COMPARISON_CASE_COUNT:
        raise ValueError(
            "representation-comparison suite must contain exactly 36 positive cases"
        )

    groups: dict[str, list[BenchmarkCase]] = {}
    for case in cases:
        comparison_group_id = case.comparison_group_id
        if not case.is_positive:
            raise ValueError(
                f"case {case.id} is negative; Stage F comparison accepts positives only"
            )
        if (
            case.objective != "reduce_to"
            or case.objective_direction != "source_to_target"
            or case.target_policy != "fixed"
            or not case.target
            or case.input_kind != "presented_problem"
            or case.effective_input_declaration != case.source
            or case.evaluation_lane != "representation_comparison"
            or case.catalog_mode not in REPRESENTATION_COMPARISON_CATALOG_MODES
            or case.execution_layer != "core_reuse"
            or case.verification_profile != "core"
            or case.authoring_policy != {"enabled": False, "mode": "disabled"}
            or comparison_group_id is None
            or case.matched_pair_id != comparison_group_id
            or case.group_id is not None
            or case.family_id is not None
            or case.source_form_id is not None
            or case.target_form_id is not None
            or case.hub_ids
        ):
            raise ValueError(
                f"case {case.id} is outside the representation-comparison study ABI"
            )
        if case.coverage.get("forbid_model_call") is True:
            raise ValueError(
                f"case {case.id} forbids the real model call required by Stage F"
            )
        module_leaf = case.module.rsplit(".", 1)[-1]
        expected_study_family = REPRESENTATION_COMPARISON_FAMILY_BY_MODULE_LEAF.get(
            module_leaf
        )
        if (
            expected_study_family is None
            or case.coverage.get("study_family") != expected_study_family
        ):
            raise ValueError(
                f"case {case.id} must explicitly declare the Stage F study_family "
                f"for module {module_leaf}"
            )
        if not isinstance(case.coverage.get("logical_source"), str) or not isinstance(
            case.coverage.get("input_form"), str
        ):
            raise ValueError(
                f"case {case.id} must declare logical_source and input_form metrics"
            )
        max_model_calls = case.resources.get("max_model_calls")
        if not isinstance(max_model_calls, int) or isinstance(max_model_calls, bool):
            raise ValueError(f"case {case.id} must declare a positive max_model_calls budget")
        if max_model_calls <= 0:
            raise ValueError(f"case {case.id} must declare a positive max_model_calls budget")
        groups.setdefault(comparison_group_id, []).append(case)

    if set(groups) != REPRESENTATION_COMPARISON_GROUP_IDS:
        raise ValueError(
            "representation-comparison groups must be exactly the 18 fixed-target positives"
        )
    if len(groups) != REPRESENTATION_COMPARISON_GROUP_COUNT:
        raise ValueError("representation-comparison suite must contain exactly 18 groups")
    if {
        str(case.coverage["study_family"])
        for case in cases
    } != REPRESENTATION_COMPARISON_STUDY_FAMILIES:
        raise ValueError(
            "representation-comparison suite must contain graph, clause_csp, and "
            "incidence study families"
        )

    for group_id, pair in sorted(groups.items()):
        if len(pair) != 2:
            raise ValueError(f"comparison group {group_id} must contain exactly two cases")
        by_mode = {case.catalog_mode: case for case in pair}
        if set(by_mode) != REPRESENTATION_COMPARISON_CATALOG_MODES:
            raise ValueError(
                f"comparison group {group_id} must contain flat_api and component_catalog"
            )
        if _representation_comparison_signature(
            by_mode["flat_api"]
        ) != _representation_comparison_signature(by_mode["component_catalog"]):
            raise ValueError(
                f"comparison group {group_id} changes metadata other than id/catalog_mode"
            )
    return cases


def observation_snapshot_path(root: Path, *, module: str, declaration: str) -> Path:
    """Return the deterministic per-module observation snapshot path."""

    module_leaf = module.rsplit(".", 1)[-1]
    declaration_leaf = declaration.rsplit(".", 1)[-1]
    return root / module_leaf / f"{declaration_leaf}.json"


def _all_keys(value: Any) -> set[str]:
    if isinstance(value, dict):
        keys = set(value)
        for item in value.values():
            keys.update(_all_keys(item))
        return keys
    if isinstance(value, list):
        keys: set[str] = set()
        for item in value:
            keys.update(_all_keys(item))
        return keys
    return set()


def find_prompt_forbidden_keys(payload: Mapping[str, Any]) -> tuple[str, ...]:
    """Return benchmark-answer fields that must never reach either model client."""

    return tuple(sorted(_all_keys(payload) & PROMPT_FORBIDDEN_KEYS))


class SimulatedInputGroundingClient:
    """A stateless bounded-query model double driven only by visible prompt facts."""

    def __init__(self) -> None:
        self.logical_turns = 0
        self.prompt_key_leaks: list[tuple[str, ...]] = []

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

    def _audit_prompt(self, payload: Mapping[str, Any]) -> None:
        leaked = find_prompt_forbidden_keys(payload)
        if leaked:
            self.prompt_key_leaks.append(leaked)
            raise ValueError(
                "input-grounding prompt contains benchmark answer fields: "
                + ", ".join(leaked)
            )
        constraints = payload.get("constraints")
        if not isinstance(constraints, dict) or constraints.get(
            "full_catalogs_are_not_included"
        ) is not True:
            raise ValueError("input-grounding prompt does not preserve bounded retrieval")

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        if "complete Lean" not in system or "auditable stop" not in system:
            raise ValueError("simulated client received the wrong input-planning system prompt")
        payload = json.loads(prompt)
        if not isinstance(payload, dict):
            raise ValueError("input-grounding prompt must be a JSON object")
        self._audit_prompt(payload)
        self.logical_turns += 1

        input_observation = payload["input_observation"]
        fixed_target = payload["fixed_target"]
        retrieved = payload["retrieved"]
        query_history = payload.get("query_history", [])
        if not isinstance(query_history, list):
            raise ValueError("input-grounding prompt query_history must be a list")
        input_node = input_observation["normalized_problem_node_id"]
        target_node = fixed_target["node_id"]

        def searched(action: str, *, source_node: str | None = None) -> bool:
            for row in query_history:
                if not isinstance(row, dict) or row.get("action") != action:
                    continue
                if source_node is None:
                    return True
                searches = row.get("searches", [])
                if not isinstance(searches, list):
                    continue
                for search in searches:
                    if not isinstance(search, dict):
                        continue
                    node_key = (
                        "node_ids"
                        if action == "search_problems"
                        else "source_node_ids"
                    )
                    nodes = search.get(node_key, [])
                    if isinstance(nodes, list) and source_node in nodes:
                        return True
            return False

        if not searched("search_problems", source_node=input_node):
            return self._response(
                {
                "action": "search_problems",
                "searches": [{"node_ids": [input_node], "limit": 8}],
                }
            )

        exact = [
            item
            for item in retrieved["problems"]
            if item.get("problem_node_id") == input_node
            and item.get("exact_defeq") is True
        ]
        selected_problem: Mapping[str, Any] | None = exact[0] if exact else None
        selected_connection: Mapping[str, Any] | None = None
        current_node = input_node

        if selected_problem is None and not searched(
            "search_connections", source_node=input_node
        ):
            return self._response(
                {
                    "action": "search_connections",
                    "searches": [{"source_node_ids": [input_node], "limit": 8}],
                }
            )

        if selected_problem is None:
            outgoing = [
                item
                for item in retrieved["connections"]
                if item.get("source_node_id") == input_node
            ]
            if not outgoing:
                return self._response(
                    {
                        "action": "stop",
                        "failure_code": "no_lean_verified_problem_match",
                        "explanation": (
                            "The exact-node problem search and the outgoing existing-connection "
                            "search both returned no Lean-verified way to enter the library graph."
                        ),
                    }
                )
            for connection in outgoing:
                connection_target = connection.get("target_node_id")
                candidates = [
                    item
                    for item in retrieved["problems"]
                    if item.get("problem_node_id") == connection_target
                ]
                if candidates:
                    selected_connection = connection
                    selected_problem = candidates[0]
                    current_node = str(connection_target)
                    break
                if isinstance(connection_target, str) and not searched(
                    "search_problems", source_node=connection_target
                ):
                    return self._response(
                        {
                            "action": "search_problems",
                            "searches": [{"node_ids": [connection_target], "limit": 8}],
                        }
                    )
            if selected_problem is None:
                raise ValueError(
                    "returned connections do not end at a retrieved catalog problem"
                )

        match_relation = (
            selected_connection["relation"]
            if selected_connection is not None
            else "exact_defeq"
        )
        connection_id = (
            selected_connection["entry_id"]
            if selected_connection is not None
            else None
        )

        def reduction_search_completed(
            source_node: str, *, unrestricted_outgoing: bool
        ) -> bool:
            for row in query_history:
                if not isinstance(row, dict) or row.get("action") != "search_reductions":
                    continue
                searches = row.get("searches", [])
                if not isinstance(searches, list):
                    continue
                for search in searches:
                    if not isinstance(search, dict):
                        continue
                    sources = search.get("source_node_ids", [])
                    if not isinstance(sources, list) or source_node not in sources:
                        continue
                    targets = search.get("target_node_ids", [])
                    has_target_filter = isinstance(targets, list) and bool(targets)
                    if unrestricted_outgoing != has_target_filter:
                        return True
            return False

        reductions = [
            item
            for item in retrieved["reductions"]
            if isinstance(item, dict)
            and isinstance(item.get("declaration"), str)
            and isinstance(item.get("source_node_id"), str)
            and isinstance(item.get("target_node_id"), str)
        ]
        adjacency: dict[str, list[Mapping[str, Any]]] = {}
        for item in reductions:
            adjacency.setdefault(str(item["source_node_id"]), []).append(item)
        for edges in adjacency.values():
            edges.sort(key=lambda item: str(item["declaration"]))

        shortest_path: list[Mapping[str, Any]] | None = (
            [] if current_node == target_node else None
        )
        reachable_order = [current_node]
        seen = {current_node}
        queue: list[tuple[str, list[Mapping[str, Any]]]] = [(current_node, [])]
        while queue and shortest_path is None:
            node, path = queue.pop(0)
            for edge in adjacency.get(node, []):
                next_node = str(edge["target_node_id"])
                next_path = [*path, edge]
                if next_node == target_node:
                    shortest_path = next_path
                    break
                if next_node not in seen:
                    seen.add(next_node)
                    reachable_order.append(next_node)
                    queue.append((next_node, next_path))

        if shortest_path is None and not reduction_search_completed(
            current_node, unrestricted_outgoing=False
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

        if shortest_path is None:
            frontier = [
                node
                for node in reachable_order
                if node != target_node
                and not reduction_search_completed(
                    node, unrestricted_outgoing=True
                )
            ]
            if frontier:
                return self._response(
                    {
                        "action": "search_reductions",
                        "searches": [
                            {"source_node_ids": [node], "limit": 8}
                            for node in frontier[:4]
                        ],
                    }
                )
            return self._response(
                {
                    "action": "stop",
                    "failure_code": "no_existing_reduction_route",
                    "matched_problem": selected_problem["declaration"],
                    "match_relation": match_relation,
                    "connection_entry_id": connection_id,
                    "explanation": (
                        "The input problem was Lean-verified, every bounded outgoing frontier "
                        "returned by the catalog was expanded, and the retrieved directed graph "
                        "still contains no path to the fixed target."
                    ),
                }
            )

        reduction_declarations = [str(edge["declaration"]) for edge in shortest_path]
        path_atoms: list[tuple[str, bool]] = []
        if selected_connection is not None:
            path_atoms.append((str(selected_connection["lean_term"]), True))
        path_atoms.extend((declaration, False) for declaration in reduction_declarations)
        if not path_atoms:
            lean_term = "ComplexityReduction.Certificate.CertifiedPath.refl"
        else:
            first_atom, first_needs_parentheses = path_atoms[0]
            rendered_first = f"({first_atom})" if first_needs_parentheses else first_atom
            lean_term = (
                "ComplexityReduction.Certificate.CertifiedPath.step " + rendered_first
            )
            for atom, needs_parentheses in path_atoms[1:]:
                rendered_atom = f"({atom})" if needs_parentheses else atom
                lean_term = (
                    "ComplexityReduction.Certificate.CertifiedPath.cons ("
                    + lean_term
                    + ") "
                    + rendered_atom
                )
        return self._response(
            {
                "action": "finish",
                "matched_problem": selected_problem["declaration"],
                "match_relation": match_relation,
                "connection_entry_id": connection_id,
                "reduction_declarations": reduction_declarations,
                "target_declaration": fixed_target["declaration"],
                "lean_term": lean_term,
                "explanation": (
                    "Use the Lean-verified input match and the shortest connected path in "
                    "the reductions returned by the bounded catalog searches."
                ),
            }
        )
