"""Bounded, route-neutral guidance for expanding retrieved reduction frontiers.

The model remains responsible for choosing a problem, target evidence, route,
and Lean term.  This module only summarizes endpoint nodes that are already
reachable through model-retrieved edges and offers source-only search templates.
It never returns theorem declarations, target selectors, evidence selectors, or
complete paths.
"""

from __future__ import annotations

from collections import deque
from collections.abc import Collection, Mapping, Sequence
from typing import Any

from .models import TypedInventoryEntry


FRONTIER_GUIDANCE_SCHEMA = "hardness_frontier_guidance_v1"
FRONTIER_GUIDANCE_MODE = "retrieved_endpoints_public_counts"
MAX_FRONTIER_GUIDANCE_NODES = 8
MAX_FRONTIER_SUGGESTED_SEARCHES = 4


def build_frontier_guidance(
    *,
    retrieved_entries: Sequence[TypedInventoryEntry],
    catalog_entries: Sequence[TypedInventoryEntry],
    start_atom_counts: Mapping[str, int],
    source_only_queried_node_ids: Collection[str],
    maximum_route_atoms: int,
) -> dict[str, Any]:
    """Build a bounded breadth-first retrieval hint without selecting a route.

    Frontier membership is derived only from retrieved problem starts and
    retrieved reduction targets.  The complete same-fingerprint catalog is used
    solely to report declaration-free outgoing counts, just like a focused
    architecture query.
    """

    retrieved_adjacency: dict[str, list[TypedInventoryEntry]] = {}
    for entry in sorted(retrieved_entries, key=lambda item: item.declaration):
        retrieved_adjacency.setdefault(entry.source_node_id, []).append(entry)

    minimum_depth: dict[str, int] = {}
    queue: deque[str] = deque()
    for node_id, raw_depth in sorted(start_atom_counts.items()):
        depth = max(0, int(raw_depth))
        previous = minimum_depth.get(node_id)
        if previous is None or depth < previous:
            minimum_depth[node_id] = depth
            queue.append(node_id)
    while queue:
        node_id = queue.popleft()
        depth = minimum_depth[node_id]
        if depth >= maximum_route_atoms:
            continue
        for entry in retrieved_adjacency.get(node_id, ()):
            next_depth = depth + 1
            if next_depth > maximum_route_atoms:
                continue
            previous = minimum_depth.get(entry.target_node_id)
            if previous is None or next_depth < previous:
                minimum_depth[entry.target_node_id] = next_depth
                queue.append(entry.target_node_id)

    catalog_outgoing: dict[str, list[TypedInventoryEntry]] = {}
    for entry in catalog_entries:
        if entry.capability_kind == "certified_reduction":
            catalog_outgoing.setdefault(entry.source_node_id, []).append(entry)

    queried_sources = set(source_only_queried_node_ids)
    candidates: list[dict[str, Any]] = []
    for node_id, depth in minimum_depth.items():
        if depth >= maximum_route_atoms or node_id in queried_sources:
            continue
        outgoing = catalog_outgoing.get(node_id, ())
        if not outgoing:
            continue
        candidates.append(
            {
                "node_id": node_id,
                "minimum_retrieved_atom_depth": depth,
                "outgoing_reduction_count": len(outgoing),
                "outgoing_endpoint_count": len(
                    {entry.target_node_id for entry in outgoing}
                ),
                "source_only_query_attempted": False,
            }
        )
    candidates.sort(
        key=lambda row: (
            int(row["minimum_retrieved_atom_depth"]),
            str(row["node_id"]),
        )
    )
    visible = candidates[:MAX_FRONTIER_GUIDANCE_NODES]
    suggested = visible[:MAX_FRONTIER_SUGGESTED_SEARCHES]
    return {
        "schema_version": FRONTIER_GUIDANCE_SCHEMA,
        "mode": FRONTIER_GUIDANCE_MODE,
        "contains_declaration_names": False,
        "contains_target_or_route_selection": False,
        "frontier_origin": (
            "retrieved problem starts and targets of model-retrieved reductions"
        ),
        "catalog_use": "outgoing counts only; no declarations or path ranking",
        "ordering": "breadth_first_then_node_id",
        "retrieved_reachable_node_count": len(minimum_depth),
        "source_only_queried_node_count": len(queried_sources),
        "unqueried_expandable_frontier_count": len(candidates),
        "frontier_truncated": len(candidates) > len(visible),
        "frontier_nodes": visible,
        "suggested_searches": [
            {
                "source_node_ids": [str(row["node_id"])],
                "limit": 8,
            }
            for row in suggested
        ],
        "instruction": (
            "If more edges are needed, prefer one source-only search action containing "
            "these bounded searches. This is retrieval guidance, not a target or route "
            "selection; you may choose another already retrieved frontier node."
        ),
    }


_FORBIDDEN_GUIDANCE_KEYS = {
    "declaration",
    "declarations",
    "evidence_id",
    "evidence_declaration",
    "lean_term",
    "path",
    "paths",
    "reduction_declarations",
    "route",
    "routes",
    "target_declaration",
    "target_entry_id",
    "target_evidence_id",
    "target_node_id",
    "target_node_ids",
}


def _forbidden_guidance_paths(value: Any, *, prefix: str = "") -> set[str]:
    paths: set[str] = set()
    if isinstance(value, Mapping):
        for raw_key, item in value.items():
            key = str(raw_key)
            path = f"{prefix}.{key}" if prefix else key
            if key in _FORBIDDEN_GUIDANCE_KEYS:
                paths.add(path)
            paths.update(_forbidden_guidance_paths(item, prefix=path))
    elif isinstance(value, (list, tuple)):
        for index, item in enumerate(value):
            paths.update(
                _forbidden_guidance_paths(item, prefix=f"{prefix}[{index}]")
            )
    elif isinstance(value, str) and value.startswith(
        ("ComplexityReduction.", "Benchmark.Hardness.")
    ):
        paths.add(prefix)
    return paths


def frontier_guidance_errors(payload: Mapping[str, Any]) -> tuple[str, ...]:
    """Audit the prompt-level Stage-J guidance contract."""

    request = payload.get("request")
    known_hardness = bool(
        isinstance(request, Mapping)
        and request.get("objective") == "reduce_to_known_hardness"
    )
    guidance = payload.get("frontier_guidance")
    if not known_hardness:
        return (
            ("known-NP prompt unexpectedly contains frontier_guidance",)
            if guidance is not None
            else ()
        )
    if not isinstance(guidance, Mapping):
        return ("known-hardness prompt is missing frontier_guidance",)

    errors: list[str] = []
    if guidance.get("schema_version") != FRONTIER_GUIDANCE_SCHEMA:
        errors.append("frontier_guidance schema_version is invalid")
    if guidance.get("mode") != FRONTIER_GUIDANCE_MODE:
        errors.append("frontier_guidance mode is invalid")
    if guidance.get("contains_declaration_names") is not False:
        errors.append("frontier_guidance may not contain declaration names")
    if guidance.get("contains_target_or_route_selection") is not False:
        errors.append("frontier_guidance may not select a target or route")
    leaked = sorted(_forbidden_guidance_paths(guidance))
    if leaked:
        errors.append("frontier_guidance contains forbidden fields: " + ", ".join(leaked))

    retrieved = payload.get("retrieved")
    allowed_nodes: set[str] = set()
    if isinstance(retrieved, Mapping):
        for row in retrieved.get("problems", ()):
            if isinstance(row, Mapping) and isinstance(row.get("problem_node_id"), str):
                allowed_nodes.add(str(row["problem_node_id"]))
        for row in retrieved.get("connections", ()):
            if isinstance(row, Mapping) and isinstance(row.get("target_node_id"), str):
                allowed_nodes.add(str(row["target_node_id"]))
        for row in retrieved.get("reductions", ()):
            if isinstance(row, Mapping) and isinstance(row.get("target_node_id"), str):
                allowed_nodes.add(str(row["target_node_id"]))

    frontier = guidance.get("frontier_nodes")
    frontier_nodes: set[str] = set()
    if not isinstance(frontier, list) or len(frontier) > MAX_FRONTIER_GUIDANCE_NODES:
        errors.append("frontier_nodes is not a bounded list")
    else:
        for index, row in enumerate(frontier):
            if not isinstance(row, Mapping):
                errors.append(f"frontier_nodes[{index}] is not an object")
                continue
            node_id = row.get("node_id")
            if not isinstance(node_id, str) or not node_id:
                errors.append(f"frontier_nodes[{index}] has no node_id")
                continue
            frontier_nodes.add(node_id)
            if node_id not in allowed_nodes:
                errors.append(
                    f"frontier_nodes[{index}] is not a retrieved endpoint"
                )

    searches = guidance.get("suggested_searches")
    if not isinstance(searches, list) or len(searches) > MAX_FRONTIER_SUGGESTED_SEARCHES:
        errors.append("suggested_searches is not a bounded list")
    else:
        for index, search in enumerate(searches):
            if not isinstance(search, Mapping):
                errors.append(f"suggested_searches[{index}] is not an object")
                continue
            if set(search) != {"source_node_ids", "limit"}:
                errors.append(
                    f"suggested_searches[{index}] is not source-only"
                )
                continue
            nodes = search.get("source_node_ids")
            if (
                not isinstance(nodes, list)
                or len(nodes) != 1
                or not isinstance(nodes[0], str)
                or nodes[0] not in frontier_nodes
            ):
                errors.append(
                    f"suggested_searches[{index}] does not reference one frontier node"
                )
            if search.get("limit") != 8:
                errors.append(f"suggested_searches[{index}] changed the bounded limit")
    return tuple(errors)


def frontier_prompt_metrics(payload: Mapping[str, Any]) -> dict[str, Any]:
    guidance = payload.get("frontier_guidance")
    terminal = payload.get("terminal_guidance")
    return {
        "frontier_guidance_present": isinstance(guidance, Mapping),
        "frontier_guidance_errors": list(frontier_guidance_errors(payload)),
        "frontier_node_count": (
            len(guidance.get("frontier_nodes", ()))
            if isinstance(guidance, Mapping)
            and isinstance(guidance.get("frontier_nodes"), list)
            else 0
        ),
        "frontier_suggested_search_count": (
            len(guidance.get("suggested_searches", ()))
            if isinstance(guidance, Mapping)
            and isinstance(guidance.get("suggested_searches"), list)
            else 0
        ),
        "terminal_guidance_mode": (
            terminal.get("mode") if isinstance(terminal, Mapping) else None
        ),
        "terminal_guidance_failure_code": (
            terminal.get("failure_code") if isinstance(terminal, Mapping) else None
        ),
    }
