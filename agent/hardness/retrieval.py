"""Offline theorem search over a compiled-library capability catalog.

The model chooses what to search for.  This module only executes bounded,
deterministic queries against declarations already validated by Lean; it does
not infer a proof or grant any capability.
"""

from __future__ import annotations

import re
from collections import defaultdict
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any

from .models import TypedCatalog, TypedInventoryEntry


MAX_SEARCHES_PER_ROUND = 4
MAX_TERMS_PER_SEARCH = 8
MAX_PREFIXES_PER_SEARCH = 6
MAX_ROLES_PER_SEARCH = 4
MAX_NODE_IDS_PER_SEARCH = 6
MAX_RESULTS_PER_SEARCH = 8
MAX_RESULTS_PER_ROUND = 12
MAX_NAVIGATION_HINTS = 16
MAX_ARCHITECTURE_QUERIES_PER_ROUND = 4
MAX_ARCHITECTURE_RESULTS_PER_QUERY = 8
MAX_ARCHITECTURE_RESULTS_PER_ROUND = 12

WORD_RE = re.compile(r"[A-Za-z0-9]+")
CAMEL_BOUNDARY_RE = re.compile(r"(?<=[a-z0-9])(?=[A-Z])")
NAVIGATION_SUFFIX_RE = re.compile(r"(?:StandardTM|Adapter|Gadget|Input)$")


class RetrievalValidationError(ValueError):
    """A malformed or excessively broad model search request."""


@dataclass(frozen=True)
class TheoremSearch:
    terms: tuple[str, ...] = ()
    namespace_prefixes: tuple[str, ...] = ()
    roles: tuple[str, ...] = ()
    source_node_ids: tuple[str, ...] = ()
    target_node_ids: tuple[str, ...] = ()
    limit: int = MAX_RESULTS_PER_SEARCH

    def to_dict(self) -> dict[str, Any]:
        return {
            "terms": list(self.terms),
            "namespace_prefixes": list(self.namespace_prefixes),
            "roles": list(self.roles),
            "source_node_ids": list(self.source_node_ids),
            "target_node_ids": list(self.target_node_ids),
            "limit": self.limit,
        }


@dataclass(frozen=True)
class ArchitectureQuery:
    terms: tuple[str, ...] = ()
    namespace_prefixes: tuple[str, ...] = ()
    roles: tuple[str, ...] = ()
    source_node_ids: tuple[str, ...] = ()
    target_node_ids: tuple[str, ...] = ()
    limit: int = MAX_ARCHITECTURE_RESULTS_PER_QUERY

    def to_dict(self) -> dict[str, Any]:
        return {
            "terms": list(self.terms),
            "namespace_prefixes": list(self.namespace_prefixes),
            "roles": list(self.roles),
            "source_node_ids": list(self.source_node_ids),
            "target_node_ids": list(self.target_node_ids),
            "limit": self.limit,
        }


def declaration_namespace(declaration: str) -> str:
    namespace, separator, _ = declaration.rpartition(".")
    return namespace if separator else declaration


def entry_summary(entry: TypedInventoryEntry) -> dict[str, Any]:
    return {
        "declaration": entry.declaration,
        "namespace": declaration_namespace(entry.declaration),
        "role": entry.component_role,
        "source": entry.source_display,
        "target": entry.target_display,
        "source_fingerprint": entry.source_fingerprint,
        "target_fingerprint": entry.target_fingerprint,
        "source_node_id": entry.source_node_id,
        "target_node_id": entry.target_node_id,
    }


def namespace_transformation_hint(namespace: str) -> dict[str, str] | None:
    """Extract an architectural A-to-B hint without revealing declarations."""

    leaf = namespace.rsplit(".", 1)[-1]
    stem = NAVIGATION_SUFFIX_RE.sub("", leaf)
    source, separator, target = stem.partition("To")
    if not separator or not source or not target:
        return None
    return {"source_label": source, "target_label": target}


def _namespace_transition_rows(catalog: TypedCatalog) -> tuple[dict[str, Any], ...]:
    grouped: dict[
        tuple[str, str, str], list[TypedInventoryEntry]
    ] = defaultdict(list)
    for entry in catalog.entries:
        if entry.capability_kind != "certified_reduction":
            continue
        grouped[
            (
                declaration_namespace(entry.declaration),
                entry.source_node_id,
                entry.target_node_id,
            )
        ].append(entry)
    rows: list[dict[str, Any]] = []
    for (namespace, source_node_id, target_node_id), entries in sorted(
        grouped.items()
    ):
        row: dict[str, Any] = {
            "namespace": namespace,
            "source_node_id": source_node_id,
            "target_node_id": target_node_id,
            "roles": sorted({entry.component_role for entry in entries}),
            "declaration_count": len(entries),
        }
        transformation = namespace_transformation_hint(namespace)
        if transformation is not None:
            row["transformation_hint"] = transformation
        rows.append(row)
    return tuple(rows)


def build_library_architecture(catalog: TypedCatalog) -> dict[str, Any]:
    """Return a compact orientation guide, not the full namespace topology."""

    reduction_entries = tuple(
        entry
        for entry in catalog.entries
        if entry.capability_kind == "certified_reduction"
    )
    role_counts: dict[str, int] = defaultdict(int)
    for entry in reduction_entries:
        role_counts[entry.component_role] += 1
    namespace_count = len(
        {declaration_namespace(entry.declaration) for entry in reduction_entries}
    )
    return {
        "contains_declaration_names": False,
        "full_namespace_topology_included": False,
        "catalog_summary": {
            "reduction_declaration_count": len(reduction_entries),
            "namespace_count": namespace_count,
            "role_counts": dict(sorted(role_counts.items())),
        },
        "roots": [
            {
                "namespace": "ComplexityReduction.Domain",
                "description": (
                    "reusable reductions and adapters between problem representations"
                ),
            },
            {
                "namespace": "ComplexityReduction.Routes",
                "description": (
                    "end-to-end routes, route-specific input adapters, and route edges"
                ),
            },
        ],
        "role_meanings": {
            "ingress": "an initial conversion from an external input form into a hub",
            "sharedGadget": "a reusable directed mathematical reduction between hubs",
            "egress": "a final conversion from a hub to an external target presentation",
            "finalComposition": "an existing end-to-end route",
            "unannotated": "a registered reduction without a component annotation",
        },
        "navigation_advice": [
            (
                "Use the focused navigation hints first. If they are insufficient, "
                "ask the agent to inspect a few namespace transitions."
            ),
            (
                "Use an egress only when its direction reaches the requested target; "
                "a canonical hub target usually does not need an egress away from it."
            ),
            (
                "Benchmark input declarations may be definitionally equal aliases of "
                "library endpoints, so their fully qualified text need not match."
            ),
        ],
        "endpoint_topology": {
            "node_meaning": (
                "equal node IDs mean Lean-whnf-normalized endpoints can connect"
            ),
            "directed_path_rule": (
                "request source node = first theorem source node; every theorem "
                "target node = next theorem source node; last theorem target node "
                "= request target node"
            ),
            "node_filtered_search_supported": True,
            "search_filter_semantics": (
                "source and target node filters constrain one returned theorem; "
                "they are not the endpoints of a whole multi-theorem path"
            ),
        },
    }


def build_navigation_hints(
    catalog: TypedCatalog,
    *,
    frontier_node_ids: Sequence[str],
    target_node_id: str,
) -> dict[str, Any]:
    """Expose small namespace-level next-hop hints without theorem names."""

    frontier = set(frontier_node_ids)
    rows = _namespace_transition_rows(catalog)
    outgoing = [
        row
        for row in rows
        if row["source_node_id"] in frontier
        and row["source_node_id"] != row["target_node_id"]
    ][:MAX_NAVIGATION_HINTS]
    incoming = [
        row
        for row in rows
        if target_node_id
        and row["target_node_id"] == target_node_id
        and row["source_node_id"] != row["target_node_id"]
    ][:MAX_NAVIGATION_HINTS]
    return {
        "frontier_node_ids": sorted(frontier),
        "outgoing_from_frontier": outgoing,
        "incoming_to_request_target": incoming,
        "contains_declaration_names": False,
    }


def _string_list(
    value: Any, *, label: str, maximum: int
) -> tuple[str, ...]:
    if value is None:
        return ()
    if (
        not isinstance(value, list)
        or len(value) > maximum
        or any(not isinstance(item, str) or not item.strip() for item in value)
    ):
        raise RetrievalValidationError(
            f"{label} must be a string list with at most {maximum} items"
        )
    return tuple(item.strip() for item in value)


def parse_theorem_searches(payload: Mapping[str, Any]) -> tuple[TheoremSearch, ...]:
    raw_searches = payload.get("searches")
    if (
        not isinstance(raw_searches, list)
        or not raw_searches
        or len(raw_searches) > MAX_SEARCHES_PER_ROUND
    ):
        raise RetrievalValidationError(
            f"searches must contain 1..{MAX_SEARCHES_PER_ROUND} search objects"
        )
    searches: list[TheoremSearch] = []
    for index, raw in enumerate(raw_searches):
        if not isinstance(raw, dict):
            raise RetrievalValidationError(f"searches[{index}] must be an object")
        terms = _string_list(
            raw.get("terms"),
            label=f"searches[{index}].terms",
            maximum=MAX_TERMS_PER_SEARCH,
        )
        prefixes = _string_list(
            raw.get("namespace_prefixes"),
            label=f"searches[{index}].namespace_prefixes",
            maximum=MAX_PREFIXES_PER_SEARCH,
        )
        roles = _string_list(
            raw.get("roles"),
            label=f"searches[{index}].roles",
            maximum=MAX_ROLES_PER_SEARCH,
        )
        source_node_ids = _string_list(
            raw.get("source_node_ids"),
            label=f"searches[{index}].source_node_ids",
            maximum=MAX_NODE_IDS_PER_SEARCH,
        )
        target_node_ids = _string_list(
            raw.get("target_node_ids"),
            label=f"searches[{index}].target_node_ids",
            maximum=MAX_NODE_IDS_PER_SEARCH,
        )
        if not terms and not prefixes and not roles and not source_node_ids and not target_node_ids:
            raise RetrievalValidationError(
                f"searches[{index}] must include terms, namespaces, roles, or endpoint nodes"
            )
        limit = raw.get("limit", MAX_RESULTS_PER_SEARCH)
        if (
            not isinstance(limit, int)
            or isinstance(limit, bool)
            or limit < 1
        ):
            raise RetrievalValidationError(
                f"searches[{index}].limit must be a positive integer"
            )
        limit = min(limit, MAX_RESULTS_PER_SEARCH)
        searches.append(
            TheoremSearch(
                terms=terms,
                namespace_prefixes=prefixes,
                roles=roles,
                source_node_ids=source_node_ids,
                target_node_ids=target_node_ids,
                limit=limit,
            )
        )
    return tuple(searches)


def parse_architecture_queries(
    payload: Mapping[str, Any],
) -> tuple[ArchitectureQuery, ...]:
    raw_queries = payload.get("queries")
    if (
        not isinstance(raw_queries, list)
        or not raw_queries
        or len(raw_queries) > MAX_ARCHITECTURE_QUERIES_PER_ROUND
    ):
        raise RetrievalValidationError(
            "queries must contain "
            f"1..{MAX_ARCHITECTURE_QUERIES_PER_ROUND} architecture query objects"
        )
    queries: list[ArchitectureQuery] = []
    for index, raw in enumerate(raw_queries):
        if not isinstance(raw, dict):
            raise RetrievalValidationError(f"queries[{index}] must be an object")
        terms = _string_list(
            raw.get("terms"),
            label=f"queries[{index}].terms",
            maximum=MAX_TERMS_PER_SEARCH,
        )
        prefixes = _string_list(
            raw.get("namespace_prefixes"),
            label=f"queries[{index}].namespace_prefixes",
            maximum=MAX_PREFIXES_PER_SEARCH,
        )
        roles = _string_list(
            raw.get("roles"),
            label=f"queries[{index}].roles",
            maximum=MAX_ROLES_PER_SEARCH,
        )
        source_node_ids = _string_list(
            raw.get("source_node_ids"),
            label=f"queries[{index}].source_node_ids",
            maximum=MAX_NODE_IDS_PER_SEARCH,
        )
        target_node_ids = _string_list(
            raw.get("target_node_ids"),
            label=f"queries[{index}].target_node_ids",
            maximum=MAX_NODE_IDS_PER_SEARCH,
        )
        if not terms and not prefixes and not roles and not source_node_ids and not target_node_ids:
            raise RetrievalValidationError(
                f"queries[{index}] must include terms, namespaces, roles, or endpoint nodes"
            )
        limit = raw.get("limit", MAX_ARCHITECTURE_RESULTS_PER_QUERY)
        if (
            not isinstance(limit, int)
            or isinstance(limit, bool)
            or limit < 1
        ):
            raise RetrievalValidationError(
                f"queries[{index}].limit must be a positive integer"
            )
        queries.append(
            ArchitectureQuery(
                terms=terms,
                namespace_prefixes=prefixes,
                roles=roles,
                source_node_ids=source_node_ids,
                target_node_ids=target_node_ids,
                limit=min(limit, MAX_ARCHITECTURE_RESULTS_PER_QUERY),
            )
        )
    return tuple(queries)


def _search_tokens(value: str) -> tuple[str, ...]:
    expanded = CAMEL_BOUNDARY_RE.sub(" ", value)
    return tuple(token.lower() for token in WORD_RE.findall(expanded))


def _namespace_matches(namespace: str, prefix: str) -> bool:
    left = namespace.lower()
    right = prefix.strip().rstrip(".").lower()
    return bool(
        right
        and (
            left == right
            or left.startswith(right + ".")
            or left.endswith("." + right)
            or ("." + right + ".") in ("." + left + ".")
        )
    )


def _architecture_score(
    row: Mapping[str, Any], query: ArchitectureQuery
) -> int | None:
    namespace = str(row["namespace"])
    roles = set(row.get("roles", ()))
    source_node_id = str(row["source_node_id"])
    target_node_id = str(row["target_node_id"])
    if query.namespace_prefixes and not any(
        _namespace_matches(namespace, prefix) for prefix in query.namespace_prefixes
    ):
        return None
    if query.roles and not roles.intersection(query.roles):
        return None
    if query.source_node_ids and source_node_id not in set(query.source_node_ids):
        return None
    if query.target_node_ids and target_node_id not in set(query.target_node_ids):
        return None
    transformation = row.get("transformation_hint")
    labels = ""
    if isinstance(transformation, dict):
        labels = " ".join(str(value) for value in transformation.values())
    haystack = " ".join((namespace, labels, *sorted(roles)))
    lowered = haystack.lower()
    tokens = set(_search_tokens(haystack))
    has_structural_filter = bool(
        query.source_node_ids or query.target_node_ids
    )
    matched_term = not query.terms or has_structural_filter
    score = 0
    for term in query.terms:
        normalized = term.lower().strip()
        term_tokens = set(_search_tokens(term))
        if normalized and normalized in lowered:
            score += 12
            matched_term = True
        overlap = len(term_tokens & tokens)
        if overlap:
            score += overlap * 3
            matched_term = True
    if not matched_term:
        return None
    for prefix in query.namespace_prefixes:
        normalized = prefix.strip().rstrip(".").lower()
        if namespace.lower() == normalized:
            score += 20
        elif _namespace_matches(namespace, prefix):
            score += 10
    if query.roles:
        score += 4
    if query.source_node_ids:
        score += 30
    if query.target_node_ids:
        score += 30
    return score


def inspect_library_architecture(
    catalog: TypedCatalog, queries: Sequence[ArchitectureQuery]
) -> tuple[dict[str, Any], ...]:
    """Execute bounded namespace/topology queries without returning theorem names."""

    rows = _namespace_transition_rows(catalog)
    selected: dict[tuple[str, str, str], dict[str, Any]] = {}
    for query in queries:
        ranked: list[tuple[int, str, str, str, dict[str, Any]]] = []
        for row in rows:
            score = _architecture_score(row, query)
            if score is None:
                continue
            ranked.append(
                (
                    -score,
                    str(row["namespace"]),
                    str(row["source_node_id"]),
                    str(row["target_node_id"]),
                    row,
                )
            )
        ranked.sort(key=lambda item: item[:4])
        for _, namespace, source_node_id, target_node_id, row in ranked[: query.limit]:
            selected.setdefault(
                (namespace, source_node_id, target_node_id), dict(row)
            )
            if len(selected) >= MAX_ARCHITECTURE_RESULTS_PER_ROUND:
                break
        if len(selected) >= MAX_ARCHITECTURE_RESULTS_PER_ROUND:
            break
    return tuple(selected.values())


def _entry_score(entry: TypedInventoryEntry, search: TheoremSearch) -> int | None:
    namespace = declaration_namespace(entry.declaration)
    if search.namespace_prefixes and not any(
        _namespace_matches(namespace, prefix) for prefix in search.namespace_prefixes
    ):
        return None
    if search.roles and entry.component_role not in set(search.roles):
        return None
    if search.source_node_ids and entry.source_node_id not in set(search.source_node_ids):
        return None
    if search.target_node_ids and entry.target_node_id not in set(search.target_node_ids):
        return None
    haystack = " ".join(
        (
            entry.declaration,
            entry.component_role,
            entry.source_display,
            entry.target_display,
        )
    )
    lowered = haystack.lower()
    tokens = set(_search_tokens(haystack))
    score = 0
    has_structural_filter = bool(
        search.namespace_prefixes
        or search.roles
        or search.source_node_ids
        or search.target_node_ids
    )
    matched_term = not search.terms or has_structural_filter
    for term in search.terms:
        normalized = term.lower().strip()
        term_tokens = set(_search_tokens(term))
        if normalized and normalized in lowered:
            score += 12
            matched_term = True
        overlap = len(term_tokens & tokens)
        if overlap:
            score += overlap * 3
            matched_term = True
    if not matched_term:
        return None
    for prefix in search.namespace_prefixes:
        normalized = prefix.strip().rstrip(".").lower()
        if namespace.lower() == normalized:
            score += 20
        elif _namespace_matches(namespace, prefix):
            score += 10
    if search.roles:
        score += 4
    if search.source_node_ids:
        score += 30
    if search.target_node_ids:
        score += 30
    return score


def search_catalog(
    catalog: TypedCatalog, searches: Sequence[TheoremSearch]
) -> tuple[TypedInventoryEntry, ...]:
    """Execute bounded searches and return a stable union of matching entries."""

    selected: dict[str, TypedInventoryEntry] = {}
    entries = tuple(
        entry
        for entry in catalog.entries
        if entry.capability_kind == "certified_reduction"
    )
    for search in searches:
        ranked: list[tuple[int, str, TypedInventoryEntry]] = []
        for entry in entries:
            score = _entry_score(entry, search)
            if score is not None:
                ranked.append((-score, entry.declaration, entry))
        ranked.sort(key=lambda item: (item[0], item[1]))
        for _, _, entry in ranked[: search.limit]:
            selected.setdefault(entry.declaration, entry)
            if len(selected) >= MAX_RESULTS_PER_ROUND:
                break
        if len(selected) >= MAX_RESULTS_PER_ROUND:
            break
    return tuple(selected.values())


def analyze_retrieved_connectivity(
    entries: Sequence[TypedInventoryEntry],
    *,
    source_node_id: str,
    target_node_id: str,
    maximum_path_length: int = 8,
    maximum_paths: int = 12,
) -> dict[str, Any]:
    """Analyze only model-retrieved edges using compiled endpoint node IDs."""

    if not source_node_id or not target_node_id or any(
        not entry.source_node_id or not entry.target_node_id for entry in entries
    ):
        return {
            "available": False,
            "complete_paths": [],
            "frontier_node_ids": [],
        }

    ordered = tuple(sorted(entries, key=lambda entry: entry.declaration))
    outgoing: dict[str, list[TypedInventoryEntry]] = defaultdict(list)
    for entry in ordered:
        outgoing[entry.source_node_id].append(entry)

    compatible_pairs = [
        [left.declaration, right.declaration]
        for left in ordered
        for right in ordered
        if left.declaration != right.declaration
        and left.target_node_id == right.source_node_id
    ]
    complete_paths: list[list[str]] = []
    reachable_nodes = {source_node_id}

    def visit(node_id: str, path: tuple[TypedInventoryEntry, ...]) -> None:
        if len(complete_paths) >= maximum_paths or len(path) >= maximum_path_length:
            return
        for entry in outgoing.get(node_id, []):
            if any(previous.declaration == entry.declaration for previous in path):
                continue
            next_path = path + (entry,)
            reachable_nodes.add(entry.target_node_id)
            if entry.target_node_id == target_node_id:
                complete_paths.append([item.declaration for item in next_path])
                if len(complete_paths) >= maximum_paths:
                    return
                continue
            visit(entry.target_node_id, next_path)

    visit(source_node_id, ())
    frontier = sorted(
        node_id
        for node_id in reachable_nodes
        if node_id != target_node_id and not outgoing.get(node_id)
    )
    return {
        "available": True,
        "request_source_node_id": source_node_id,
        "request_target_node_id": target_node_id,
        "declarations_starting_at_request_source": [
            entry.declaration for entry in outgoing.get(source_node_id, [])
        ],
        "declarations_ending_at_request_target": [
            entry.declaration for entry in ordered if entry.target_node_id == target_node_id
        ],
        "compatible_declaration_pairs": compatible_pairs,
        "complete_paths": complete_paths,
        "frontier_node_ids": frontier,
        "next_search_hint": (
            {"source_node_ids": frontier}
            if frontier and not complete_paths
            else None
        ),
    }
