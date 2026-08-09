"""Bounded search over Lean-validated, direction-specific problem connections.

The catalog contains existing ``CertifiedReduction`` declarations and the two
fixed reduction projections of ``CertifiedEquiv`` and
``CertifiedPresentationChange``.  Python never reverses an edge or invents a
projection; it only parses the direction and endpoints emitted by Lean.
"""

from __future__ import annotations

import json
import re
from collections import defaultdict
from collections.abc import Mapping, Sequence
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from .input_observation import LeanInputObservation
from .catalog import FULL_CATALOG, build_typed_catalog
from .models import TypedCatalog, TypedInventoryEntry, sha256_id
from .problem_catalog import (
    FORBIDDEN_NAME_COMPONENTS,
    ProblemCatalog,
    ProblemCatalogEntry,
    ProblemCatalogError,
    ProblemMatch,
)


CONNECTION_CATALOG_SCHEMA = "hardness_connection_catalog_v1"
CONNECTION_CATALOG_ENTRY_SCHEMA = "hardness_connection_catalog_entry_v1"
MARKER = "HARDNESS_AGENT"
DECLARATION_RE = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
)
WORD_RE = re.compile(r"[A-Za-z0-9]+")
CAMEL_BOUNDARY_RE = re.compile(r"(?<=[a-z0-9])(?=[A-Z])")

MAX_CONNECTION_SEARCHES_PER_ROUND = 4
MAX_CONNECTION_TERMS_PER_SEARCH = 8
MAX_CONNECTION_PREFIXES_PER_SEARCH = 6
MAX_CONNECTION_NODE_IDS_PER_SEARCH = 6
MAX_CONNECTION_FILTERS_PER_SEARCH = 6
MAX_CONNECTION_RESULTS_PER_SEARCH = 8
MAX_CONNECTION_RESULTS_PER_ROUND = 12
MAX_INITIAL_CONNECTION_NAMESPACES = 8

DIRECT_RELATION = "existing_reduction"
EQUIV_FORWARD_RELATION = "certified_equiv_forward"
EQUIV_BACKWARD_RELATION = "certified_equiv_backward"
PRESENTATION_FORWARD_RELATION = "presentation_change_forward"
PRESENTATION_BACKWARD_RELATION = "presentation_change_backward"

FIXED_PROJECTIONS = {
    EQUIV_FORWARD_RELATION: (
        "certified_equiv",
        "forward",
        "ComplexityReduction.Certificate.CertifiedEquiv.forwardReduction",
    ),
    EQUIV_BACKWARD_RELATION: (
        "certified_equiv",
        "backward",
        "ComplexityReduction.Certificate.CertifiedEquiv.backwardReduction",
    ),
    PRESENTATION_FORWARD_RELATION: (
        "certified_presentation_change",
        "forward",
        "ComplexityReduction.Certificate.CertifiedPresentationChange.forwardReduction",
    ),
    PRESENTATION_BACKWARD_RELATION: (
        "certified_presentation_change",
        "backward",
        "ComplexityReduction.Certificate.CertifiedPresentationChange.backwardReduction",
    ),
}
ALLOWED_RELATIONS = {DIRECT_RELATION, *FIXED_PROJECTIONS}
ALLOWED_CAPABILITY_KINDS = {
    "certified_reduction",
    "certified_equiv",
    "certified_presentation_change",
}
ALLOWED_DIRECTIONS = {"forward", "backward"}
ALLOWED_TERM_KINDS = {"certificate", "fixed_projection"}


class ConnectionCatalogError(ValueError):
    """A malformed, stale, forbidden, or contradictory connection catalog."""


class ConnectionSearchError(ValueError):
    """An invalid or excessively broad ``search_connections`` request."""


def declaration_namespace(declaration: str) -> str:
    namespace, separator, _ = declaration.rpartition(".")
    return namespace if separator else declaration


def _validate_public_declaration(declaration: str, *, label: str) -> str:
    if not DECLARATION_RE.fullmatch(declaration):
        raise ConnectionCatalogError(f"{label} is not a fully-qualified Lean name")
    if FORBIDDEN_NAME_COMPONENTS.intersection(declaration.split(".")):
        raise ConnectionCatalogError(
            f"forbidden declaration entered the public connection catalog: {declaration}"
        )
    return declaration


@dataclass(frozen=True)
class ConnectionCatalogEntry:
    certificate_declaration: str
    capability_kind: str
    relation: str
    direction: str
    term_kind: str
    projection_declaration: str
    lean_term: str
    source_fingerprint: str
    target_fingerprint: str
    source_node_id: str
    target_node_id: str
    source_display: str
    target_display: str
    component_role: str
    registry_fingerprint: str
    schema_version: str = CONNECTION_CATALOG_ENTRY_SCHEMA

    @property
    def namespace(self) -> str:
        return declaration_namespace(self.certificate_declaration)

    @property
    def entry_id(self) -> str:
        return sha256_id(self.to_dict(include_entry_id=False))

    def to_dict(self, *, include_entry_id: bool = True) -> dict[str, Any]:
        value = asdict(self)
        value["namespace"] = self.namespace
        if include_entry_id:
            value["entry_id"] = self.entry_id
        return value


@dataclass(frozen=True)
class ConnectionCatalog:
    registry_fingerprint: str
    entries: tuple[ConnectionCatalogEntry, ...]
    toolchain: str = ""
    lake_manifest_sha256: str = ""
    schema_version: str = CONNECTION_CATALOG_SCHEMA

    @property
    def catalog_id(self) -> str:
        return sha256_id(self.to_dict(include_catalog_id=False))

    def to_dict(self, *, include_catalog_id: bool = True) -> dict[str, Any]:
        value = {
            "schema_version": self.schema_version,
            "registry_fingerprint": self.registry_fingerprint,
            "toolchain": self.toolchain,
            "lake_manifest_sha256": self.lake_manifest_sha256,
            "connection_count": len(self.entries),
            "entries": [entry.to_dict() for entry in self.entries],
        }
        if include_catalog_id:
            value["catalog_id"] = self.catalog_id
        return value


@dataclass(frozen=True)
class ConnectionSearch:
    terms: tuple[str, ...] = ()
    namespace_prefixes: tuple[str, ...] = ()
    source_node_ids: tuple[str, ...] = ()
    target_node_ids: tuple[str, ...] = ()
    relations: tuple[str, ...] = ()
    capability_kinds: tuple[str, ...] = ()
    directions: tuple[str, ...] = ()
    limit: int = MAX_CONNECTION_RESULTS_PER_SEARCH

    def to_dict(self) -> dict[str, Any]:
        return {
            "terms": list(self.terms),
            "namespace_prefixes": list(self.namespace_prefixes),
            "source_node_ids": list(self.source_node_ids),
            "target_node_ids": list(self.target_node_ids),
            "relations": list(self.relations),
            "capability_kinds": list(self.capability_kinds),
            "directions": list(self.directions),
            "limit": self.limit,
        }


def _validate_entry(entry: ConnectionCatalogEntry) -> ConnectionCatalogEntry:
    _validate_public_declaration(
        entry.certificate_declaration, label="connection certificate declaration"
    )
    _validate_public_declaration(
        entry.projection_declaration, label="connection projection declaration"
    )
    if entry.capability_kind not in ALLOWED_CAPABILITY_KINDS:
        raise ConnectionCatalogError("unsupported connection capability kind")
    if entry.relation not in ALLOWED_RELATIONS:
        raise ConnectionCatalogError("unsupported connection relation")
    if entry.direction not in ALLOWED_DIRECTIONS:
        raise ConnectionCatalogError("unsupported connection direction")
    if entry.term_kind not in ALLOWED_TERM_KINDS:
        raise ConnectionCatalogError("unsupported connection term kind")
    if not entry.source_fingerprint.startswith("lean:") or not entry.target_fingerprint.startswith(
        "lean:"
    ):
        raise ConnectionCatalogError("connection entry has no Lean endpoint fingerprints")
    if not entry.source_node_id.startswith("lean-whnf:") or not entry.target_node_id.startswith(
        "lean-whnf:"
    ):
        raise ConnectionCatalogError("connection entry has no Lean whnf endpoints")
    if not entry.source_display or not entry.target_display:
        raise ConnectionCatalogError("connection entry has incomplete endpoint displays")
    if not entry.component_role or not entry.registry_fingerprint:
        raise ConnectionCatalogError("connection entry has incomplete provenance")
    if not entry.lean_term:
        raise ConnectionCatalogError("connection entry has no executable Lean term")
    if entry.relation == DIRECT_RELATION:
        if (
            entry.capability_kind != "certified_reduction"
            or entry.direction != "forward"
            or entry.term_kind != "certificate"
            or entry.projection_declaration != entry.certificate_declaration
        ):
            raise ConnectionCatalogError("direct reduction connection metadata is inconsistent")
    else:
        expected_kind, expected_direction, expected_projection = FIXED_PROJECTIONS[
            entry.relation
        ]
        if (
            entry.capability_kind != expected_kind
            or entry.direction != expected_direction
            or entry.term_kind != "fixed_projection"
            or entry.projection_declaration != expected_projection
        ):
            raise ConnectionCatalogError(
                "connection does not use the fixed projection for its certificate kind"
            )
    if entry.certificate_declaration not in entry.lean_term:
        raise ConnectionCatalogError("connection Lean term omits its certificate declaration")
    if (
        entry.term_kind == "fixed_projection"
        and entry.projection_declaration not in entry.lean_term
    ):
        raise ConnectionCatalogError("connection Lean term omits its fixed projection")
    return entry


def _catalog(
    *,
    registry_fingerprint: str,
    entries: Sequence[ConnectionCatalogEntry],
    toolchain: str = "",
    lake_manifest_sha256: str = "",
) -> ConnectionCatalog:
    if not registry_fingerprint:
        raise ConnectionCatalogError("connection catalog has no registry fingerprint")
    by_id: dict[str, ConnectionCatalogEntry] = {}
    for entry in entries:
        _validate_entry(entry)
        if entry.registry_fingerprint != registry_fingerprint:
            raise ConnectionCatalogError(
                "connection entry does not match the registry fingerprint"
            )
        previous = by_id.get(entry.entry_id)
        if previous is not None and previous != entry:
            raise ConnectionCatalogError("conflicting duplicate connection entry")
        by_id[entry.entry_id] = entry
    return ConnectionCatalog(
        registry_fingerprint=registry_fingerprint,
        entries=tuple(
            sorted(
                by_id.values(),
                key=lambda item: (
                    item.certificate_declaration,
                    item.relation,
                    item.source_node_id,
                    item.target_node_id,
                ),
            )
        ),
        toolchain=toolchain,
        lake_manifest_sha256=lake_manifest_sha256,
    )


def parse_connection_catalog(
    *,
    stdout: str,
    stderr: str,
    nonce: str,
    toolchain: str = "",
    lake_manifest_sha256: str = "",
) -> ConnectionCatalog:
    """Parse one nonce-bound connection export without accepting truncated rows."""

    registry_rows: list[list[str]] = []
    connection_rows: list[list[str]] = []
    for line in f"{stdout}\n{stderr}".splitlines():
        position = line.find(MARKER + "\t")
        if position < 0:
            continue
        fields = line[position:].split("\t")
        if (
            len(fields) < 5
            or fields[1] != CONNECTION_CATALOG_SCHEMA
            or fields[2] != nonce
        ):
            continue
        if fields[3] == "registry":
            registry_rows.append(fields)
        elif fields[3] == "connection":
            connection_rows.append(fields)
    if len(registry_rows) != 1:
        raise ConnectionCatalogError(
            "Lean output must contain exactly one registry row for this connection catalog"
        )
    entries: list[ConnectionCatalogEntry] = []
    for fields in connection_rows:
        if len(fields) < 19:
            raise ConnectionCatalogError("Lean emitted a truncated connection catalog row")
        entries.append(
            ConnectionCatalogEntry(
                certificate_declaration=fields[4].strip(),
                capability_kind=fields[5].strip(),
                relation=fields[6].strip(),
                direction=fields[7].strip(),
                term_kind=fields[8].strip(),
                projection_declaration=fields[9].strip(),
                lean_term=fields[10].strip(),
                source_fingerprint=fields[11].strip(),
                target_fingerprint=fields[12].strip(),
                source_node_id=fields[13].strip(),
                target_node_id=fields[14].strip(),
                source_display=fields[15].strip(),
                target_display=fields[16].strip(),
                component_role=fields[17].strip(),
                registry_fingerprint=fields[18].strip(),
            )
        )
    if not entries:
        raise ConnectionCatalogError("Lean connection catalog contained no public connections")
    return _catalog(
        registry_fingerprint=registry_rows[0][4].strip(),
        entries=entries,
        toolchain=toolchain,
        lake_manifest_sha256=lake_manifest_sha256,
    )


def connection_catalog_from_dict(value: Mapping[str, Any]) -> ConnectionCatalog:
    if value.get("schema_version") != CONNECTION_CATALOG_SCHEMA:
        raise ConnectionCatalogError("unsupported connection catalog schema")
    registry_fingerprint = value.get("registry_fingerprint")
    if not isinstance(registry_fingerprint, str) or not registry_fingerprint:
        raise ConnectionCatalogError("connection catalog registry fingerprint is missing")
    raw_entries = value.get("entries")
    if not isinstance(raw_entries, list):
        raise ConnectionCatalogError("connection catalog entries must be a list")
    entries: list[ConnectionCatalogEntry] = []
    required = (
        "certificate_declaration",
        "capability_kind",
        "relation",
        "direction",
        "term_kind",
        "projection_declaration",
        "lean_term",
        "source_fingerprint",
        "target_fingerprint",
        "source_node_id",
        "target_node_id",
        "source_display",
        "target_display",
        "component_role",
        "registry_fingerprint",
    )
    for index, raw in enumerate(raw_entries):
        if not isinstance(raw, dict):
            raise ConnectionCatalogError(f"connection catalog entry {index} must be an object")
        if raw.get("schema_version") != CONNECTION_CATALOG_ENTRY_SCHEMA:
            raise ConnectionCatalogError(
                f"unsupported connection catalog entry schema at {index}"
            )
        values: dict[str, str] = {}
        for key in required:
            item = raw.get(key)
            if not isinstance(item, str) or not item.strip():
                raise ConnectionCatalogError(
                    f"connection catalog entry {index}.{key} is missing"
                )
            values[key] = item.strip()
        entry = ConnectionCatalogEntry(**values)
        recorded_entry_id = raw.get("entry_id")
        if recorded_entry_id is not None and recorded_entry_id != entry.entry_id:
            raise ConnectionCatalogError(
                f"connection catalog entry {index} content ID does not match its payload"
            )
        entries.append(entry)
    toolchain = value.get("toolchain", "")
    manifest_hash = value.get("lake_manifest_sha256", "")
    if not isinstance(toolchain, str) or not isinstance(manifest_hash, str):
        raise ConnectionCatalogError("connection catalog fingerprints must be strings")
    catalog = _catalog(
        registry_fingerprint=registry_fingerprint,
        entries=entries,
        toolchain=toolchain,
        lake_manifest_sha256=manifest_hash,
    )
    recorded_count = value.get("connection_count")
    if recorded_count is not None and recorded_count != len(catalog.entries):
        raise ConnectionCatalogError("connection catalog count does not match its entries")
    recorded_catalog_id = value.get("catalog_id")
    if recorded_catalog_id is not None and recorded_catalog_id != catalog.catalog_id:
        raise ConnectionCatalogError("connection catalog content ID does not match its payload")
    return catalog


def load_connection_catalog_snapshot(
    path: Path,
    *,
    expected_registry_fingerprint: str | None = None,
    expected_toolchain: str | None = None,
    expected_lake_manifest_sha256: str | None = None,
) -> ConnectionCatalog:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as error:
        raise ConnectionCatalogError(
            f"connection catalog snapshot not found: {path}"
        ) from error
    except json.JSONDecodeError as error:
        raise ConnectionCatalogError(f"invalid connection catalog JSON: {error}") from error
    if not isinstance(raw, dict):
        raise ConnectionCatalogError("connection catalog snapshot must be a JSON object")
    catalog = connection_catalog_from_dict(raw)
    expected = {
        "registry fingerprint": (
            expected_registry_fingerprint,
            catalog.registry_fingerprint,
        ),
        "toolchain": (expected_toolchain, catalog.toolchain),
        "lake manifest SHA-256": (
            expected_lake_manifest_sha256,
            catalog.lake_manifest_sha256,
        ),
    }
    for label, (expected_value, actual_value) in expected.items():
        if expected_value is not None and expected_value != actual_value:
            raise ConnectionCatalogError(
                f"stale connection catalog: {label} does not match the current environment"
            )
    return catalog


def _string_list(value: Any, *, label: str, maximum: int) -> tuple[str, ...]:
    if value is None:
        return ()
    if (
        not isinstance(value, list)
        or len(value) > maximum
        or any(not isinstance(item, str) or not item.strip() for item in value)
    ):
        raise ConnectionSearchError(
            f"{label} must be a string list with at most {maximum} items"
        )
    return tuple(item.strip() for item in value)


def parse_connection_searches(
    payload: Mapping[str, Any],
) -> tuple[ConnectionSearch, ...]:
    raw_searches = payload.get("searches")
    if (
        not isinstance(raw_searches, list)
        or not raw_searches
        or len(raw_searches) > MAX_CONNECTION_SEARCHES_PER_ROUND
    ):
        raise ConnectionSearchError(
            f"searches must contain 1..{MAX_CONNECTION_SEARCHES_PER_ROUND} objects"
        )
    searches: list[ConnectionSearch] = []
    for index, raw in enumerate(raw_searches):
        if not isinstance(raw, dict):
            raise ConnectionSearchError(f"searches[{index}] must be an object")
        terms = _string_list(
            raw.get("terms"),
            label=f"searches[{index}].terms",
            maximum=MAX_CONNECTION_TERMS_PER_SEARCH,
        )
        prefixes = _string_list(
            raw.get("namespace_prefixes"),
            label=f"searches[{index}].namespace_prefixes",
            maximum=MAX_CONNECTION_PREFIXES_PER_SEARCH,
        )
        source_nodes = _string_list(
            raw.get("source_node_ids"),
            label=f"searches[{index}].source_node_ids",
            maximum=MAX_CONNECTION_NODE_IDS_PER_SEARCH,
        )
        target_nodes = _string_list(
            raw.get("target_node_ids"),
            label=f"searches[{index}].target_node_ids",
            maximum=MAX_CONNECTION_NODE_IDS_PER_SEARCH,
        )
        relations = _string_list(
            raw.get("relations"),
            label=f"searches[{index}].relations",
            maximum=MAX_CONNECTION_FILTERS_PER_SEARCH,
        )
        capability_kinds = _string_list(
            raw.get("capability_kinds"),
            label=f"searches[{index}].capability_kinds",
            maximum=MAX_CONNECTION_FILTERS_PER_SEARCH,
        )
        directions = _string_list(
            raw.get("directions"),
            label=f"searches[{index}].directions",
            maximum=MAX_CONNECTION_FILTERS_PER_SEARCH,
        )
        if any(relation not in ALLOWED_RELATIONS for relation in relations):
            raise ConnectionSearchError(f"searches[{index}] has an unsupported relation")
        if any(kind not in ALLOWED_CAPABILITY_KINDS for kind in capability_kinds):
            raise ConnectionSearchError(
                f"searches[{index}] has an unsupported capability kind"
            )
        if any(direction not in ALLOWED_DIRECTIONS for direction in directions):
            raise ConnectionSearchError(f"searches[{index}] has an unsupported direction")
        if not any(
            (
                terms,
                prefixes,
                source_nodes,
                target_nodes,
                relations,
                capability_kinds,
                directions,
            )
        ):
            raise ConnectionSearchError(
                f"searches[{index}] must include a name, namespace, endpoint, relation, "
                "capability, or direction filter"
            )
        limit = raw.get("limit", MAX_CONNECTION_RESULTS_PER_SEARCH)
        if not isinstance(limit, int) or isinstance(limit, bool) or limit < 1:
            raise ConnectionSearchError(
                f"searches[{index}].limit must be a positive integer"
            )
        searches.append(
            ConnectionSearch(
                terms=terms,
                namespace_prefixes=prefixes,
                source_node_ids=source_nodes,
                target_node_ids=target_nodes,
                relations=relations,
                capability_kinds=capability_kinds,
                directions=directions,
                limit=min(limit, MAX_CONNECTION_RESULTS_PER_SEARCH),
            )
        )
    return tuple(searches)


def _search_tokens(value: str) -> set[str]:
    return {
        token.lower()
        for token in WORD_RE.findall(CAMEL_BOUNDARY_RE.sub(" ", value))
    }


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


def _entry_score(entry: ConnectionCatalogEntry, search: ConnectionSearch) -> int | None:
    if search.namespace_prefixes and not any(
        _namespace_matches(entry.namespace, prefix) for prefix in search.namespace_prefixes
    ):
        return None
    if search.source_node_ids and entry.source_node_id not in set(search.source_node_ids):
        return None
    if search.target_node_ids and entry.target_node_id not in set(search.target_node_ids):
        return None
    if search.relations and entry.relation not in set(search.relations):
        return None
    if search.capability_kinds and entry.capability_kind not in set(
        search.capability_kinds
    ):
        return None
    if search.directions and entry.direction not in set(search.directions):
        return None
    haystack = " ".join(
        (
            entry.certificate_declaration,
            entry.projection_declaration,
            entry.relation,
            entry.component_role,
            entry.source_display,
            entry.target_display,
        )
    )
    lowered = haystack.lower()
    tokens = _search_tokens(haystack)
    structural = bool(
        search.namespace_prefixes
        or search.source_node_ids
        or search.target_node_ids
        or search.relations
        or search.capability_kinds
        or search.directions
    )
    matched = not search.terms or structural
    score = 0
    for term in search.terms:
        normalized = term.lower().strip()
        if normalized and normalized in lowered:
            score += 12
            matched = True
        overlap = len(_search_tokens(term) & tokens)
        if overlap:
            score += overlap * 3
            matched = True
    if not matched:
        return None
    if search.source_node_ids:
        score += 40
    if search.target_node_ids:
        score += 40
    if search.namespace_prefixes:
        score += 20
    if search.relations or search.capability_kinds or search.directions:
        score += 8
    return score


def search_connections(
    catalog: ConnectionCatalog,
    searches: Sequence[ConnectionSearch],
) -> tuple[ConnectionCatalogEntry, ...]:
    """Execute bounded deterministic searches over Lean-emitted directions."""

    selected: dict[str, ConnectionCatalogEntry] = {}
    for search in searches:
        ranked: list[tuple[int, str, str, ConnectionCatalogEntry]] = []
        for entry in catalog.entries:
            score = _entry_score(entry, search)
            if score is not None:
                ranked.append(
                    (-score, entry.certificate_declaration, entry.relation, entry)
                )
        ranked.sort(key=lambda item: item[:3])
        for _, _, _, entry in ranked[: search.limit]:
            selected.setdefault(entry.entry_id, entry)
            if len(selected) >= MAX_CONNECTION_RESULTS_PER_ROUND:
                break
        if len(selected) >= MAX_CONNECTION_RESULTS_PER_ROUND:
            break
    return tuple(selected.values())


def connection_search_result(entry: ConnectionCatalogEntry) -> dict[str, Any]:
    return {
        "entry_id": entry.entry_id,
        "certificate_declaration": entry.certificate_declaration,
        "namespace": entry.namespace,
        "capability_kind": entry.capability_kind,
        "relation": entry.relation,
        "direction": entry.direction,
        "projection_declaration": entry.projection_declaration,
        "lean_term": entry.lean_term,
        "source_fingerprint": entry.source_fingerprint,
        "target_fingerprint": entry.target_fingerprint,
        "source_node_id": entry.source_node_id,
        "target_node_id": entry.target_node_id,
        "source_display": entry.source_display,
        "target_display": entry.target_display,
        "component_role": entry.component_role,
        "validation_source": "lean_validated_fixed_projection",
    }


def build_initial_connection_hints(
    catalog: ConnectionCatalog,
    *,
    input_node_id: str,
) -> dict[str, Any]:
    """Reveal bounded outgoing counts without revealing certificate names."""

    outgoing = [
        entry
        for entry in catalog.entries
        if input_node_id and entry.source_node_id == input_node_id
    ]
    namespace_counts: dict[str, int] = defaultdict(int)
    relation_counts: dict[str, int] = defaultdict(int)
    for entry in outgoing:
        namespace_counts[entry.namespace] += 1
        relation_counts[entry.relation] += 1
    return {
        "contains_declaration_names": False,
        "input_node_id": input_node_id,
        "outgoing_connection_count": len(outgoing),
        "relation_counts": dict(sorted(relation_counts.items())),
        "nearby_namespaces": [
            {"namespace": namespace, "connection_count": count}
            for namespace, count in sorted(
                namespace_counts.items(), key=lambda item: (-item[1], item[0])
            )[:MAX_INITIAL_CONNECTION_NAMESPACES]
        ],
        "full_connection_catalog_included": False,
    }


def build_reduction_catalog(
    catalog: ConnectionCatalog,
    *,
    mode: str = FULL_CATALOG,
) -> TypedCatalog:
    """Recover the existing reduction search view from the same Lean export."""

    entries = tuple(
        TypedInventoryEntry(
            declaration=entry.certificate_declaration,
            capability_kind="certified_reduction",
            component_role=entry.component_role,
            source_fingerprint=entry.source_fingerprint,
            target_fingerprint=entry.target_fingerprint,
            is_final_facade=entry.component_role == "finalComposition",
            discovery="registered",
            registry_fingerprint=entry.registry_fingerprint,
            source_display=entry.source_display,
            target_display=entry.target_display,
            source_node_id=entry.source_node_id,
            target_node_id=entry.target_node_id,
        )
        for entry in catalog.entries
        if entry.relation == DIRECT_RELATION
    )
    return build_typed_catalog(
        entries,
        registry_fingerprint=catalog.registry_fingerprint,
        mode=mode,
    )


def connected_problem_match(
    *,
    observation: LeanInputObservation,
    problem_catalog: ProblemCatalog,
    candidate: ProblemCatalogEntry,
    retrieved_problem_entries: Sequence[ProblemCatalogEntry],
    connection_catalog: ConnectionCatalog,
    connection: ConnectionCatalogEntry,
    retrieved_connections: Sequence[ConnectionCatalogEntry],
) -> ProblemMatch:
    """Accept a non-defeq match only through one retrieved Lean connection."""

    if not observation.supported or not observation.normalized_problem_node_id:
        raise ConnectionCatalogError("cannot match a rejected or node-less input observation")
    fingerprints = {
        observation.registry_fingerprint,
        problem_catalog.registry_fingerprint,
        connection_catalog.registry_fingerprint,
        candidate.registry_fingerprint,
        connection.registry_fingerprint,
    }
    if len(fingerprints) != 1:
        raise ConnectionCatalogError(
            "input, problem, and connection catalogs do not share one registry fingerprint"
        )
    if candidate.entry_id not in {entry.entry_id for entry in retrieved_problem_entries}:
        raise ProblemCatalogError(
            "selected problem was not returned by this session's search_problems query"
        )
    if connection.entry_id not in {entry.entry_id for entry in retrieved_connections}:
        raise ConnectionCatalogError(
            "selected connection was not returned by this session's search_connections query"
        )
    if candidate.problem_node_id == observation.normalized_problem_node_id:
        raise ConnectionCatalogError(
            "definitionally equal input and problem must use exact_problem_match"
        )
    if connection.source_node_id != observation.normalized_problem_node_id:
        raise ConnectionCatalogError(
            "selected connection does not start at the observed input node"
        )
    if connection.target_node_id != candidate.problem_node_id:
        raise ConnectionCatalogError(
            "selected connection does not reach the selected problem node"
        )
    supporting = (connection.certificate_declaration,)
    if connection.term_kind == "fixed_projection":
        supporting += (connection.projection_declaration,)
    return ProblemMatch(
        input_declaration=observation.input_declaration,
        candidate_declaration=candidate.declaration,
        relation=connection.relation,
        exact_defeq=False,
        supporting_declarations=supporting,
        input_node_id=observation.normalized_problem_node_id,
        candidate_node_id=candidate.problem_node_id,
        confidence_explanation=(
            "Lean validated the selected certificate and emitted the requested fixed "
            "direction as a CertifiedReduction whose endpoints connect the observed "
            "input to the retrieved problem"
        ),
        validation_source="lean_validated_fixed_projection",
        registry_fingerprint=problem_catalog.registry_fingerprint,
        search_result_entry_id=candidate.entry_id,
        connection_entry_id=connection.entry_id,
        connection_lean_term=connection.lean_term,
    )
