"""Bounded search over Lean-exported public ``PresentedProblem`` declarations.

The catalog is observational.  Node equality can nominate an exact candidate,
but only elaboration of the final artifact at the user's real declaration can
accept the match as part of a proof.
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
from .models import sha256_id


PROBLEM_CATALOG_SCHEMA = "hardness_problem_catalog_v2"
PROBLEM_CATALOG_SCHEMA_V1 = "hardness_problem_catalog_v1"
PROBLEM_CATALOG_ENTRY_SCHEMA = "hardness_problem_catalog_entry_v2"
PROBLEM_CATALOG_ENTRY_SCHEMA_V1 = "hardness_problem_catalog_entry_v1"
PROBLEM_MATCH_SCHEMA = "hardness_problem_match_v2"
PROBLEM_MATCH_SCHEMA_V1 = "hardness_problem_match_v1"
SUPPORTED_PROBLEM_CATALOG_SCHEMAS = {
    PROBLEM_CATALOG_SCHEMA_V1,
    PROBLEM_CATALOG_SCHEMA,
}
CATALOG_ENTRY_SCHEMA_BY_CATALOG_SCHEMA = {
    PROBLEM_CATALOG_SCHEMA_V1: PROBLEM_CATALOG_ENTRY_SCHEMA_V1,
    PROBLEM_CATALOG_SCHEMA: PROBLEM_CATALOG_ENTRY_SCHEMA,
}
MARKER = "HARDNESS_AGENT"
DECLARATION_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
WORD_RE = re.compile(r"[A-Za-z0-9]+")
CAMEL_BOUNDARY_RE = re.compile(r"(?<=[a-z0-9])(?=[A-Z])")
SEARCH_STOPWORDS = {
    "problem",
    "presented",
    "structured",
    "source",
    "target",
    "complexity",
    "reduction",
}
FORBIDDEN_NAME_COMPONENTS = {
    "Oracle",
    "Oracles",
    "Gold",
    "GoldProofs",
    "Expected",
    "HiddenTargets",
    "Legacy",
}

MAX_PROBLEM_SEARCHES_PER_ROUND = 4
MAX_PROBLEM_TERMS_PER_SEARCH = 8
MAX_PROBLEM_PREFIXES_PER_SEARCH = 6
MAX_PROBLEM_NODE_IDS_PER_SEARCH = 6
MAX_PROBLEM_RESULTS_PER_SEARCH = 8
MAX_PROBLEM_RESULTS_PER_ROUND = 12
MAX_INITIAL_PROBLEM_NAMESPACES = 8


class ProblemCatalogError(ValueError):
    """A malformed, stale, forbidden, or contradictory problem catalog."""


class ProblemSearchError(ValueError):
    """An invalid or excessively broad ``search_problems`` request."""


def _parse_bool(value: str, *, label: str) -> bool:
    normalized = value.strip().lower()
    if normalized == "true":
        return True
    if normalized == "false":
        return False
    raise ProblemCatalogError(f"{label} must be true or false")


def _split_names(value: str) -> tuple[str, ...]:
    return tuple(item.strip() for item in value.split(",") if item.strip())


def declaration_namespace(declaration: str) -> str:
    namespace, separator, _ = declaration.rpartition(".")
    return namespace if separator else declaration


def _validate_public_declaration(declaration: str) -> str:
    if not DECLARATION_RE.fullmatch(declaration):
        raise ProblemCatalogError("problem declaration is not a fully-qualified Lean name")
    if FORBIDDEN_NAME_COMPONENTS.intersection(declaration.split(".")):
        raise ProblemCatalogError(
            f"forbidden declaration entered the public problem catalog: {declaration}"
        )
    return declaration


@dataclass(frozen=True)
class ProblemCatalogEntry:
    declaration: str
    declaration_kind: str
    display: str
    problem_node_id: str
    semantic_summary: str
    representation_summary: str
    encoder_bound_identity_summary: str
    referenced_constants: tuple[str, ...]
    registered: bool
    registry_fingerprint: str
    accepts_summary: str = ""
    accepts_node_id: str = ""
    domain_summary: str = ""
    domain_node_id: str = ""
    representation_node_id: str = ""
    encoder_bound_identity_node_id: str = ""
    schema_version: str = PROBLEM_CATALOG_ENTRY_SCHEMA

    @property
    def namespace(self) -> str:
        return declaration_namespace(self.declaration)

    @property
    def entry_id(self) -> str:
        return sha256_id(self.to_dict(include_entry_id=False))

    @property
    def codec_group_id(self) -> str:
        """Stable identity for aliases using the same lawful representation."""

        if not self.encoder_bound_identity_node_id:
            return ""
        return sha256_id(
            {
                "schema_version": "hardness_predicate_codec_group_v1",
                "registry_fingerprint": self.registry_fingerprint,
                "domain_node_id": self.domain_node_id,
                "representation_node_id": self.representation_node_id,
                "encoder_bound_identity_node_id": self.encoder_bound_identity_node_id,
            }
        )

    def to_dict(self, *, include_entry_id: bool = True) -> dict[str, Any]:
        value = asdict(self)
        value["namespace"] = self.namespace
        value["referenced_constants"] = list(self.referenced_constants)
        if self.schema_version == PROBLEM_CATALOG_ENTRY_SCHEMA_V1:
            # Keep the historical payload byte-for-byte canonicalizable so a
            # v1 entry_id remains valid after loading it with the v2 code.
            for key in (
                "accepts_summary",
                "accepts_node_id",
                "domain_summary",
                "domain_node_id",
                "representation_node_id",
                "encoder_bound_identity_node_id",
            ):
                value.pop(key, None)
        if include_entry_id:
            value["entry_id"] = self.entry_id
        return value


@dataclass(frozen=True)
class ProblemCatalog:
    registry_fingerprint: str
    entries: tuple[ProblemCatalogEntry, ...]
    toolchain: str = ""
    lake_manifest_sha256: str = ""
    schema_version: str = PROBLEM_CATALOG_SCHEMA

    @property
    def catalog_id(self) -> str:
        return sha256_id(self.to_dict(include_catalog_id=False))

    def to_dict(self, *, include_catalog_id: bool = True) -> dict[str, Any]:
        value = {
            "schema_version": self.schema_version,
            "registry_fingerprint": self.registry_fingerprint,
            "toolchain": self.toolchain,
            "lake_manifest_sha256": self.lake_manifest_sha256,
            "problem_count": len(self.entries),
            "entries": [entry.to_dict() for entry in self.entries],
        }
        if include_catalog_id:
            value["catalog_id"] = self.catalog_id
        return value


@dataclass(frozen=True)
class ProblemSearch:
    terms: tuple[str, ...] = ()
    namespace_prefixes: tuple[str, ...] = ()
    node_ids: tuple[str, ...] = ()
    accepts_node_ids: tuple[str, ...] = ()
    domain_node_ids: tuple[str, ...] = ()
    representation_node_ids: tuple[str, ...] = ()
    semantic_terms: tuple[str, ...] = ()
    representation_terms: tuple[str, ...] = ()
    registered_only: bool = False
    limit: int = MAX_PROBLEM_RESULTS_PER_SEARCH

    def to_dict(self) -> dict[str, Any]:
        value = {
            "terms": list(self.terms),
            "namespace_prefixes": list(self.namespace_prefixes),
            "node_ids": list(self.node_ids),
            "semantic_terms": list(self.semantic_terms),
            "representation_terms": list(self.representation_terms),
            "registered_only": self.registered_only,
            "limit": self.limit,
        }
        # Preserve the v1 query-history shape for existing searches while
        # serializing every v2 structural filter that was actually requested.
        if self.accepts_node_ids:
            value["accepts_node_ids"] = list(self.accepts_node_ids)
        if self.domain_node_ids:
            value["domain_node_ids"] = list(self.domain_node_ids)
        if self.representation_node_ids:
            value["representation_node_ids"] = list(self.representation_node_ids)
        return value


@dataclass(frozen=True)
class ProblemMatch:
    input_declaration: str
    candidate_declaration: str
    relation: str
    exact_defeq: bool
    supporting_declarations: tuple[str, ...]
    input_node_id: str
    candidate_node_id: str
    confidence_explanation: str
    validation_source: str
    registry_fingerprint: str
    search_result_entry_id: str
    connection_entry_id: str | None = None
    connection_lean_term: str | None = None
    accepts_exact_defeq: bool = False
    predicate_node_id: str | None = None
    predicate_domain_node_id: str | None = None
    candidate_accepts_node_id: str | None = None
    candidate_domain_node_id: str | None = None
    candidate_representation_node_id: str | None = None
    candidate_encoder_bound_identity_node_id: str | None = None
    route_source_declaration: str = ""
    route_source_node_id: str = ""
    schema_version: str = PROBLEM_MATCH_SCHEMA

    def __post_init__(self) -> None:
        # Existing PresentedProblem and connection callers do not need to know
        # about the predicate lane: their route always starts at the selected
        # catalog problem.  Filling these defaults also keeps that invariant
        # true for older construction sites.
        if not self.route_source_declaration:
            object.__setattr__(
                self,
                "route_source_declaration",
                self.candidate_declaration,
            )
        if not self.route_source_node_id:
            object.__setattr__(self, "route_source_node_id", self.candidate_node_id)

    @property
    def match_id(self) -> str:
        return sha256_id(self.to_dict(include_match_id=False))

    def to_dict(self, *, include_match_id: bool = True) -> dict[str, Any]:
        value = asdict(self)
        value["supporting_declarations"] = list(self.supporting_declarations)
        if include_match_id:
            value["match_id"] = self.match_id
        return value


@dataclass(frozen=True)
class PredicatePresentationGroup:
    """Definitionally matching presentation aliases sharing one codec."""

    codec_group_id: str
    domain_node_id: str
    representation_node_id: str
    encoder_bound_identity_node_id: str
    entries: tuple[ProblemCatalogEntry, ...]

    @property
    def representative(self) -> ProblemCatalogEntry:
        return min(
            self.entries,
            key=lambda entry: (not entry.registered, entry.declaration),
        )

    @property
    def alias_declarations(self) -> tuple[str, ...]:
        return tuple(entry.declaration for entry in self.entries)


def _validate_entry(entry: ProblemCatalogEntry) -> ProblemCatalogEntry:
    if entry.schema_version not in {
        PROBLEM_CATALOG_ENTRY_SCHEMA_V1,
        PROBLEM_CATALOG_ENTRY_SCHEMA,
    }:
        raise ProblemCatalogError("unsupported problem catalog entry schema")
    _validate_public_declaration(entry.declaration)
    if not entry.declaration_kind:
        raise ProblemCatalogError("problem catalog entry has no declaration kind")
    if not entry.display:
        raise ProblemCatalogError("problem catalog entry has no bounded display")
    if not entry.problem_node_id.startswith("lean-whnf:"):
        raise ProblemCatalogError("problem catalog entry has no Lean whnf node")
    if not entry.semantic_summary or not entry.representation_summary:
        raise ProblemCatalogError("problem catalog entry has incomplete problem summaries")
    if not entry.encoder_bound_identity_summary:
        raise ProblemCatalogError("problem catalog entry has no encoder-bound identity summary")
    if not entry.registry_fingerprint:
        raise ProblemCatalogError("problem catalog entry has no registry fingerprint")
    if entry.schema_version == PROBLEM_CATALOG_ENTRY_SCHEMA:
        if not entry.accepts_summary:
            raise ProblemCatalogError("problem catalog entry has no accepts summary")
        if not entry.domain_summary:
            raise ProblemCatalogError("problem catalog entry has no domain summary")
        for label, node_id in (
            ("accepts", entry.accepts_node_id),
            ("domain", entry.domain_node_id),
            ("representation", entry.representation_node_id),
            ("encoder-bound identity", entry.encoder_bound_identity_node_id),
        ):
            if not node_id.startswith("lean-whnf:"):
                raise ProblemCatalogError(
                    f"problem catalog entry has no Lean whnf {label} node"
                )
    elif any(
        (
            entry.accepts_summary,
            entry.accepts_node_id,
            entry.domain_summary,
            entry.domain_node_id,
            entry.representation_node_id,
            entry.encoder_bound_identity_node_id,
        )
    ):
        raise ProblemCatalogError(
            "v1 problem catalog entry unexpectedly contains v2 predicate index fields"
        )
    return entry


def _catalog(
    *,
    registry_fingerprint: str,
    entries: Sequence[ProblemCatalogEntry],
    toolchain: str = "",
    lake_manifest_sha256: str = "",
    schema_version: str = PROBLEM_CATALOG_SCHEMA,
) -> ProblemCatalog:
    if schema_version not in SUPPORTED_PROBLEM_CATALOG_SCHEMAS:
        raise ProblemCatalogError("unsupported problem catalog schema")
    if not registry_fingerprint:
        raise ProblemCatalogError("problem catalog has no registry fingerprint")
    expected_entry_schema = CATALOG_ENTRY_SCHEMA_BY_CATALOG_SCHEMA[schema_version]
    by_declaration: dict[str, ProblemCatalogEntry] = {}
    for entry in entries:
        _validate_entry(entry)
        if entry.schema_version != expected_entry_schema:
            raise ProblemCatalogError(
                "problem catalog and entry schemas do not belong to the same version"
            )
        if entry.registry_fingerprint != registry_fingerprint:
            raise ProblemCatalogError(
                "problem catalog entry does not match the registry fingerprint"
            )
        previous = by_declaration.get(entry.declaration)
        if previous is not None and previous != entry:
            raise ProblemCatalogError(
                f"conflicting duplicate problem declaration: {entry.declaration}"
            )
        by_declaration[entry.declaration] = entry
    return ProblemCatalog(
        registry_fingerprint=registry_fingerprint,
        entries=tuple(sorted(by_declaration.values(), key=lambda item: item.declaration)),
        toolchain=toolchain,
        lake_manifest_sha256=lake_manifest_sha256,
        schema_version=schema_version,
    )


def parse_problem_catalog(
    *,
    stdout: str,
    stderr: str,
    nonce: str,
    toolchain: str = "",
    lake_manifest_sha256: str = "",
) -> ProblemCatalog:
    """Parse one nonce-bound catalog export without accepting truncated output."""

    registry_rows: list[list[str]] = []
    problem_rows: list[list[str]] = []
    for line in f"{stdout}\n{stderr}".splitlines():
        position = line.find(MARKER + "\t")
        if position < 0:
            continue
        fields = line[position:].split("\t")
        if (
            len(fields) < 4
            or fields[1] not in SUPPORTED_PROBLEM_CATALOG_SCHEMAS
            or fields[2] != nonce
        ):
            continue
        if fields[3] == "registry":
            registry_rows.append(fields)
        elif fields[3] == "problem":
            problem_rows.append(fields)
    if len(registry_rows) != 1:
        raise ProblemCatalogError(
            "Lean output must contain exactly one registry row for this problem catalog"
        )
    if len(registry_rows[0]) < 5:
        raise ProblemCatalogError("Lean emitted a truncated problem catalog registry row")
    schema_version = registry_rows[0][1]
    registry_fingerprint = registry_rows[0][4].strip()
    entries: list[ProblemCatalogEntry] = []
    for fields in problem_rows:
        if fields[1] != schema_version:
            raise ProblemCatalogError(
                "Lean output mixed problem catalog schemas for one nonce"
            )
        minimum_fields = 20 if schema_version == PROBLEM_CATALOG_SCHEMA else 14
        if len(fields) < minimum_fields:
            raise ProblemCatalogError("Lean emitted a truncated problem catalog row")
        entries.append(
            ProblemCatalogEntry(
                declaration=fields[4].strip(),
                declaration_kind=fields[5].strip(),
                display=fields[6].strip(),
                problem_node_id=fields[7].strip(),
                semantic_summary=fields[8].strip(),
                representation_summary=fields[9].strip(),
                encoder_bound_identity_summary=fields[10].strip(),
                referenced_constants=_split_names(fields[11]),
                registered=_parse_bool(fields[12], label="registered"),
                registry_fingerprint=fields[13].strip(),
                accepts_summary=(
                    fields[14].strip()
                    if schema_version == PROBLEM_CATALOG_SCHEMA
                    else ""
                ),
                accepts_node_id=(
                    fields[15].strip()
                    if schema_version == PROBLEM_CATALOG_SCHEMA
                    else ""
                ),
                domain_summary=(
                    fields[16].strip()
                    if schema_version == PROBLEM_CATALOG_SCHEMA
                    else ""
                ),
                domain_node_id=(
                    fields[17].strip()
                    if schema_version == PROBLEM_CATALOG_SCHEMA
                    else ""
                ),
                representation_node_id=(
                    fields[18].strip()
                    if schema_version == PROBLEM_CATALOG_SCHEMA
                    else ""
                ),
                encoder_bound_identity_node_id=(
                    fields[19].strip()
                    if schema_version == PROBLEM_CATALOG_SCHEMA
                    else ""
                ),
                schema_version=CATALOG_ENTRY_SCHEMA_BY_CATALOG_SCHEMA[
                    schema_version
                ],
            )
        )
    if not entries:
        raise ProblemCatalogError("Lean problem catalog contained no public problems")
    return _catalog(
        registry_fingerprint=registry_fingerprint,
        entries=entries,
        toolchain=toolchain,
        lake_manifest_sha256=lake_manifest_sha256,
        schema_version=schema_version,
    )


def problem_catalog_from_dict(value: Mapping[str, Any]) -> ProblemCatalog:
    schema_version = value.get("schema_version")
    if schema_version not in SUPPORTED_PROBLEM_CATALOG_SCHEMAS:
        raise ProblemCatalogError("unsupported problem catalog schema")
    registry_fingerprint = value.get("registry_fingerprint")
    if not isinstance(registry_fingerprint, str) or not registry_fingerprint:
        raise ProblemCatalogError("problem catalog registry fingerprint is missing")
    raw_entries = value.get("entries")
    if not isinstance(raw_entries, list):
        raise ProblemCatalogError("problem catalog entries must be a list")
    entries: list[ProblemCatalogEntry] = []
    for index, raw in enumerate(raw_entries):
        if not isinstance(raw, dict):
            raise ProblemCatalogError(f"problem catalog entry {index} must be an object")
        expected_entry_schema = CATALOG_ENTRY_SCHEMA_BY_CATALOG_SCHEMA[schema_version]
        if raw.get("schema_version") != expected_entry_schema:
            raise ProblemCatalogError(f"unsupported problem catalog entry schema at {index}")

        def required_string(key: str) -> str:
            item = raw.get(key)
            if not isinstance(item, str) or not item.strip():
                raise ProblemCatalogError(f"problem catalog entry {index}.{key} is missing")
            return item.strip()

        def versioned_string(key: str) -> str:
            if schema_version == PROBLEM_CATALOG_SCHEMA:
                return required_string(key)
            item = raw.get(key, "")
            if not isinstance(item, str):
                raise ProblemCatalogError(
                    f"problem catalog entry {index}.{key} must be a string"
                )
            return item.strip()

        referenced = raw.get("referenced_constants", [])
        if not isinstance(referenced, list) or any(
            not isinstance(item, str) or not item.strip() for item in referenced
        ):
            raise ProblemCatalogError(
                f"problem catalog entry {index}.referenced_constants must be a string list"
            )
        registered = raw.get("registered")
        if not isinstance(registered, bool):
            raise ProblemCatalogError(
                f"problem catalog entry {index}.registered must be boolean"
            )
        entry = ProblemCatalogEntry(
            declaration=required_string("declaration"),
            declaration_kind=required_string("declaration_kind"),
            display=required_string("display"),
            problem_node_id=required_string("problem_node_id"),
            semantic_summary=required_string("semantic_summary"),
            representation_summary=required_string("representation_summary"),
            encoder_bound_identity_summary=required_string(
                "encoder_bound_identity_summary"
            ),
            referenced_constants=tuple(item.strip() for item in referenced),
            registered=registered,
            registry_fingerprint=required_string("registry_fingerprint"),
            accepts_summary=versioned_string("accepts_summary"),
            accepts_node_id=versioned_string("accepts_node_id"),
            domain_summary=versioned_string("domain_summary"),
            domain_node_id=versioned_string("domain_node_id"),
            representation_node_id=versioned_string("representation_node_id"),
            encoder_bound_identity_node_id=versioned_string(
                "encoder_bound_identity_node_id"
            ),
            schema_version=expected_entry_schema,
        )
        recorded_entry_id = raw.get("entry_id")
        if recorded_entry_id is not None and recorded_entry_id != entry.entry_id:
            raise ProblemCatalogError(
                f"problem catalog entry {index} content ID does not match its payload"
            )
        entries.append(entry)
    toolchain = value.get("toolchain", "")
    manifest_hash = value.get("lake_manifest_sha256", "")
    if not isinstance(toolchain, str) or not isinstance(manifest_hash, str):
        raise ProblemCatalogError("problem catalog fingerprints must be strings")
    catalog = _catalog(
        registry_fingerprint=registry_fingerprint,
        entries=entries,
        toolchain=toolchain,
        lake_manifest_sha256=manifest_hash,
        schema_version=schema_version,
    )
    recorded_count = value.get("problem_count")
    if recorded_count is not None and recorded_count != len(catalog.entries):
        raise ProblemCatalogError("problem catalog count does not match its entries")
    recorded_catalog_id = value.get("catalog_id")
    if recorded_catalog_id is not None and recorded_catalog_id != catalog.catalog_id:
        raise ProblemCatalogError("problem catalog content ID does not match its payload")
    return catalog


def load_problem_catalog_snapshot(
    path: Path,
    *,
    expected_registry_fingerprint: str | None = None,
    expected_toolchain: str | None = None,
    expected_lake_manifest_sha256: str | None = None,
) -> ProblemCatalog:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as error:
        raise ProblemCatalogError(f"problem catalog snapshot not found: {path}") from error
    except json.JSONDecodeError as error:
        raise ProblemCatalogError(f"invalid problem catalog JSON: {error}") from error
    if not isinstance(raw, dict):
        raise ProblemCatalogError("problem catalog snapshot must be a JSON object")
    catalog = problem_catalog_from_dict(raw)
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
            raise ProblemCatalogError(
                f"stale problem catalog: {label} does not match the current environment"
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
        raise ProblemSearchError(
            f"{label} must be a string list with at most {maximum} items"
        )
    return tuple(item.strip() for item in value)


def parse_problem_searches(payload: Mapping[str, Any]) -> tuple[ProblemSearch, ...]:
    raw_searches = payload.get("searches")
    if (
        not isinstance(raw_searches, list)
        or not raw_searches
        or len(raw_searches) > MAX_PROBLEM_SEARCHES_PER_ROUND
    ):
        raise ProblemSearchError(
            f"searches must contain 1..{MAX_PROBLEM_SEARCHES_PER_ROUND} objects"
        )
    searches: list[ProblemSearch] = []
    for index, raw in enumerate(raw_searches):
        if not isinstance(raw, dict):
            raise ProblemSearchError(f"searches[{index}] must be an object")
        terms = _string_list(
            raw.get("terms"),
            label=f"searches[{index}].terms",
            maximum=MAX_PROBLEM_TERMS_PER_SEARCH,
        )
        prefixes = _string_list(
            raw.get("namespace_prefixes"),
            label=f"searches[{index}].namespace_prefixes",
            maximum=MAX_PROBLEM_PREFIXES_PER_SEARCH,
        )
        node_ids = _string_list(
            raw.get("node_ids"),
            label=f"searches[{index}].node_ids",
            maximum=MAX_PROBLEM_NODE_IDS_PER_SEARCH,
        )
        accepts_node_ids = _string_list(
            raw.get("accepts_node_ids"),
            label=f"searches[{index}].accepts_node_ids",
            maximum=MAX_PROBLEM_NODE_IDS_PER_SEARCH,
        )
        domain_node_ids = _string_list(
            raw.get("domain_node_ids"),
            label=f"searches[{index}].domain_node_ids",
            maximum=MAX_PROBLEM_NODE_IDS_PER_SEARCH,
        )
        representation_node_ids = _string_list(
            raw.get("representation_node_ids"),
            label=f"searches[{index}].representation_node_ids",
            maximum=MAX_PROBLEM_NODE_IDS_PER_SEARCH,
        )
        semantic_terms = _string_list(
            raw.get("semantic_terms"),
            label=f"searches[{index}].semantic_terms",
            maximum=MAX_PROBLEM_TERMS_PER_SEARCH,
        )
        representation_terms = _string_list(
            raw.get("representation_terms"),
            label=f"searches[{index}].representation_terms",
            maximum=MAX_PROBLEM_TERMS_PER_SEARCH,
        )
        registered_only = raw.get("registered_only", False)
        if not isinstance(registered_only, bool):
            raise ProblemSearchError(
                f"searches[{index}].registered_only must be boolean"
            )
        if not any(
            (
                terms,
                prefixes,
                node_ids,
                accepts_node_ids,
                domain_node_ids,
                representation_node_ids,
                semantic_terms,
                representation_terms,
            )
        ):
            raise ProblemSearchError(
                f"searches[{index}] must include a name, namespace, problem/accepts/"
                "domain/representation node, semantic, or representation filter"
            )
        limit = raw.get("limit", MAX_PROBLEM_RESULTS_PER_SEARCH)
        if not isinstance(limit, int) or isinstance(limit, bool) or limit < 1:
            raise ProblemSearchError(
                f"searches[{index}].limit must be a positive integer"
            )
        searches.append(
            ProblemSearch(
                terms=terms,
                namespace_prefixes=prefixes,
                node_ids=node_ids,
                accepts_node_ids=accepts_node_ids,
                domain_node_ids=domain_node_ids,
                representation_node_ids=representation_node_ids,
                semantic_terms=semantic_terms,
                representation_terms=representation_terms,
                registered_only=registered_only,
                limit=min(limit, MAX_PROBLEM_RESULTS_PER_SEARCH),
            )
        )
    return tuple(searches)


def _search_tokens(value: str) -> set[str]:
    expanded = CAMEL_BOUNDARY_RE.sub(" ", value)
    return {
        token.lower()
        for token in WORD_RE.findall(expanded)
        if token.lower() not in SEARCH_STOPWORDS
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


def _text_score(haystack: str, terms: Sequence[str]) -> int | None:
    lowered = haystack.lower()
    tokens = _search_tokens(haystack)
    score = 0
    matched = not terms
    for term in terms:
        normalized = term.lower().strip()
        term_tokens = _search_tokens(term)
        if normalized and normalized in lowered:
            score += 12
            matched = True
        overlap = len(term_tokens & tokens)
        if overlap:
            score += overlap * 3
            matched = True
    return score if matched else None


def _entry_score(entry: ProblemCatalogEntry, search: ProblemSearch) -> int | None:
    if search.registered_only and not entry.registered:
        return None
    if search.namespace_prefixes and not any(
        _namespace_matches(entry.namespace, prefix) for prefix in search.namespace_prefixes
    ):
        return None
    if search.node_ids and entry.problem_node_id not in set(search.node_ids):
        return None
    if (
        search.accepts_node_ids
        and entry.accepts_node_id not in set(search.accepts_node_ids)
    ):
        return None
    if search.domain_node_ids and entry.domain_node_id not in set(search.domain_node_ids):
        return None
    if (
        search.representation_node_ids
        and entry.representation_node_id not in set(search.representation_node_ids)
    ):
        return None
    semantic_score = _text_score(entry.semantic_summary, search.semantic_terms)
    if semantic_score is None:
        return None
    representation_haystack = " ".join(
        (
            entry.representation_summary,
            entry.encoder_bound_identity_summary,
        )
    )
    representation_score = _text_score(
        representation_haystack,
        search.representation_terms,
    )
    if representation_score is None:
        return None
    general_haystack = " ".join(
        (
            entry.declaration,
            entry.display,
            entry.semantic_summary,
            entry.accepts_summary,
            entry.domain_summary,
            entry.representation_summary,
            entry.encoder_bound_identity_summary,
            *entry.referenced_constants,
        )
    )
    general_score = _text_score(general_haystack, search.terms)
    has_structural_filter = bool(
        search.namespace_prefixes
        or search.node_ids
        or search.accepts_node_ids
        or search.domain_node_ids
        or search.representation_node_ids
        or search.semantic_terms
        or search.representation_terms
    )
    if general_score is None and not has_structural_filter:
        return None
    score = (general_score or 0) + semantic_score + representation_score
    if search.node_ids:
        score += 100
    if search.accepts_node_ids:
        score += 100
    if search.domain_node_ids:
        score += 80
    if search.representation_node_ids:
        score += 80
    if search.namespace_prefixes:
        score += 20
    if search.semantic_terms:
        score += 12
    if search.representation_terms:
        score += 12
    if entry.registered:
        score += 1
    return score


def search_problems(
    catalog: ProblemCatalog,
    searches: Sequence[ProblemSearch],
) -> tuple[ProblemCatalogEntry, ...]:
    """Execute bounded deterministic queries without exposing the full catalog."""

    selected: dict[str, ProblemCatalogEntry] = {}
    for search in searches:
        ranked: list[tuple[int, str, ProblemCatalogEntry]] = []
        for entry in catalog.entries:
            score = _entry_score(entry, search)
            if score is not None:
                ranked.append((-score, entry.declaration, entry))
        ranked.sort(key=lambda item: (item[0], item[1]))
        for _, _, entry in ranked[: search.limit]:
            selected.setdefault(entry.declaration, entry)
            if len(selected) >= MAX_PROBLEM_RESULTS_PER_ROUND:
                break
        if len(selected) >= MAX_PROBLEM_RESULTS_PER_ROUND:
            break
    return tuple(selected.values())


def _predicate_match_for_entry(
    observation: LeanInputObservation | None,
    entry: ProblemCatalogEntry,
):
    """Return the Lean match row only when every catalog identity agrees."""

    if (
        observation is None
        or not observation.supported
        or observation.input_kind != "predicate"
        or not observation.predicate_domain_node_id
        or not observation.predicate_node_id
        or observation.registry_fingerprint != entry.registry_fingerprint
    ):
        return None
    for match in observation.predicate_presentation_matches:
        if match.candidate_declaration != entry.declaration:
            continue
        if (
            match.registry_fingerprint == entry.registry_fingerprint
            and match.problem_node_id == entry.problem_node_id
            and match.accepts_node_id == entry.accepts_node_id
            and match.domain_node_id == entry.domain_node_id
            and match.representation_node_id == entry.representation_node_id
            and match.encoder_bound_identity_node_id
            == entry.encoder_bound_identity_node_id
            and all(
                (
                    entry.accepts_node_id,
                    entry.domain_node_id,
                    entry.representation_node_id,
                    entry.encoder_bound_identity_node_id,
                )
            )
        ):
            return match
    return None


def predicate_exact_candidates(
    observation: LeanInputObservation,
    catalog: ProblemCatalog,
) -> tuple[ProblemCatalogEntry, ...]:
    """Return only catalog entries confirmed by nonce-bound Lean match rows."""

    if observation.registry_fingerprint != catalog.registry_fingerprint:
        raise ProblemCatalogError("input observation and problem catalog fingerprints differ")
    if not observation.supported or observation.input_kind != "predicate":
        return ()
    return tuple(
        entry
        for entry in catalog.entries
        if _predicate_match_for_entry(observation, entry) is not None
    )


def predicate_presentation_groups(
    observation: LeanInputObservation,
    catalog: ProblemCatalog,
) -> tuple[PredicatePresentationGroup, ...]:
    """Group exact predicate candidates by codec, deduplicating public aliases."""

    grouped: dict[
        tuple[str, str, str],
        list[ProblemCatalogEntry],
    ] = defaultdict(list)
    for entry in predicate_exact_candidates(observation, catalog):
        key = (
            entry.domain_node_id,
            entry.representation_node_id,
            entry.encoder_bound_identity_node_id,
        )
        grouped[key].append(entry)
    groups = [
        PredicatePresentationGroup(
            codec_group_id=entries[0].codec_group_id,
            domain_node_id=key[0],
            representation_node_id=key[1],
            encoder_bound_identity_node_id=key[2],
            entries=tuple(sorted(entries, key=lambda item: item.declaration)),
        )
        for key, entries in grouped.items()
    ]
    return tuple(
        sorted(
            groups,
            key=lambda group: (
                group.codec_group_id,
                group.representative.declaration,
            ),
        )
    )


def problem_search_result(
    entry: ProblemCatalogEntry,
    *,
    input_node_id: str = "",
    observation: LeanInputObservation | None = None,
) -> dict[str, Any]:
    exact = bool(input_node_id and entry.problem_node_id == input_node_id)
    predicate_match = _predicate_match_for_entry(observation, entry)
    accepts_exact = predicate_match is not None
    return {
        "entry_id": entry.entry_id,
        "declaration": entry.declaration,
        "namespace": entry.namespace,
        "display": entry.display,
        "problem_node_id": entry.problem_node_id,
        "semantic_summary": entry.semantic_summary,
        "accepts_summary": entry.accepts_summary,
        "accepts_node_id": entry.accepts_node_id,
        "domain_summary": entry.domain_summary,
        "domain_node_id": entry.domain_node_id,
        "representation_summary": entry.representation_summary,
        "representation_node_id": entry.representation_node_id,
        "encoder_bound_identity_summary": entry.encoder_bound_identity_summary,
        "encoder_bound_identity_node_id": entry.encoder_bound_identity_node_id,
        "codec_group_id": entry.codec_group_id,
        "registered": entry.registered,
        "exact_defeq": exact,
        "accepts_exact_defeq": accepts_exact,
        "validation_source": (
            "lean_whnf_node_same_registry"
            if exact
            else (
                "lean_nonce_bound_predicate_match_catalog_nodes"
                if accepts_exact
                else "text_retrieval_only"
            )
        ),
    }


def build_initial_problem_hints(
    catalog: ProblemCatalog,
    *,
    input_node_id: str = "",
    observation: LeanInputObservation | None = None,
) -> dict[str, Any]:
    """Reveal exact-node counts and a few namespaces, never declaration names."""

    predicate_mode = bool(
        observation is not None
        and observation.supported
        and observation.input_kind == "predicate"
    )
    if predicate_mode:
        exact = list(predicate_exact_candidates(observation, catalog))
        groups = predicate_presentation_groups(observation, catalog)
        displayed_input_node_id = observation.predicate_node_id or ""
    else:
        exact = [
            entry
            for entry in catalog.entries
            if input_node_id and entry.problem_node_id == input_node_id
        ]
        groups = ()
        displayed_input_node_id = input_node_id
    namespace_counts: dict[str, int] = defaultdict(int)
    for entry in exact:
        namespace_counts[entry.namespace] += 1
    nearby = [
        {"namespace": namespace, "candidate_count": count}
        for namespace, count in sorted(
            namespace_counts.items(),
            key=lambda item: (-item[1], item[0]),
        )[:MAX_INITIAL_PROBLEM_NAMESPACES]
    ]
    return {
        "contains_declaration_names": False,
        "input_node_id": displayed_input_node_id,
        "match_mode": "predicate_accepts" if predicate_mode else "problem_node",
        "exact_candidate_count": len(exact),
        "registered_exact_candidate_count": sum(1 for entry in exact if entry.registered),
        "predicate_presentation_group_count": len(groups),
        "predicate_codec_ambiguous": len(groups) > 1,
        "nearby_namespaces": nearby,
        "full_problem_catalog_included": False,
    }


def exact_problem_match(
    *,
    observation: LeanInputObservation,
    catalog: ProblemCatalog,
    candidate: ProblemCatalogEntry,
    retrieved_entries: Sequence[ProblemCatalogEntry],
) -> ProblemMatch:
    """Accept an exact candidate only if it came from this session's search results."""

    if not observation.supported or not observation.normalized_problem_node_id:
        raise ProblemCatalogError("cannot match a rejected or node-less input observation")
    if observation.registry_fingerprint != catalog.registry_fingerprint:
        raise ProblemCatalogError("input observation and problem catalog fingerprints differ")
    if candidate.registry_fingerprint != catalog.registry_fingerprint:
        raise ProblemCatalogError("candidate does not belong to this problem catalog")
    retrieved_by_id = {entry.entry_id for entry in retrieved_entries}
    if candidate.entry_id not in retrieved_by_id:
        raise ProblemCatalogError(
            "selected problem was not returned by this session's search_problems query"
        )
    if candidate.problem_node_id != observation.normalized_problem_node_id:
        raise ProblemCatalogError(
            "selected problem is not Lean-whnf-equal to the observed input node"
        )
    return ProblemMatch(
        input_declaration=observation.input_declaration,
        candidate_declaration=candidate.declaration,
        relation="exact_defeq",
        exact_defeq=True,
        supporting_declarations=(),
        input_node_id=observation.normalized_problem_node_id,
        candidate_node_id=candidate.problem_node_id,
        confidence_explanation=(
            "Lean exported the input and candidate with the same whnf endpoint node "
            "under the same registry fingerprint; the final artifact must still elaborate "
            "at the original input declaration"
        ),
        validation_source="lean_whnf_node_same_registry",
        registry_fingerprint=catalog.registry_fingerprint,
        search_result_entry_id=candidate.entry_id,
        route_source_declaration=candidate.declaration,
        route_source_node_id=candidate.problem_node_id,
    )


def exact_predicate_problem_match(
    *,
    observation: LeanInputObservation,
    catalog: ProblemCatalog,
    candidate: ProblemCatalogEntry,
    retrieved_entries: Sequence[ProblemCatalogEntry],
) -> ProblemMatch:
    """Select the unique Lean-confirmed predicate codec presentation.

    Multiple public names for the same encoder are aliases and therefore one
    presentation group.  Distinct encoder identities are intentionally left
    ambiguous rather than allowing declaration order or model preference to
    choose a representation for the user.
    """

    if (
        not observation.supported
        or observation.input_kind != "predicate"
        or not observation.predicate_node_id
        or not observation.predicate_domain_node_id
    ):
        raise ProblemCatalogError(
            "cannot match a rejected or node-less predicate input observation"
        )
    if observation.registry_fingerprint != catalog.registry_fingerprint:
        raise ProblemCatalogError("input observation and problem catalog fingerprints differ")
    if candidate.registry_fingerprint != catalog.registry_fingerprint:
        raise ProblemCatalogError("candidate does not belong to this problem catalog")
    if candidate.entry_id not in {entry.entry_id for entry in retrieved_entries}:
        raise ProblemCatalogError(
            "selected problem was not returned by this session's search_problems query"
        )
    if _predicate_match_for_entry(observation, candidate) is None:
        raise ProblemCatalogError(
            "selected problem has no Lean-confirmed accepts match with agreeing catalog nodes"
        )

    groups = predicate_presentation_groups(observation, catalog)
    if not groups:
        raise ProblemCatalogError(
            "predicate has no Lean-confirmed lawful presentation in this catalog"
        )
    if len(groups) != 1:
        raise ProblemCatalogError(
            "predicate presentation is ambiguous across multiple encoder identities"
        )
    group = groups[0]
    if candidate.entry_id not in {entry.entry_id for entry in group.entries}:
        raise ProblemCatalogError(
            "selected problem is not an alias of the unique predicate codec group"
        )

    return ProblemMatch(
        input_declaration=observation.input_declaration,
        candidate_declaration=candidate.declaration,
        relation="accepts_exact_defeq",
        exact_defeq=False,
        accepts_exact_defeq=True,
        supporting_declarations=(),
        input_node_id=observation.predicate_node_id,
        candidate_node_id=candidate.problem_node_id,
        predicate_node_id=observation.predicate_node_id,
        predicate_domain_node_id=observation.predicate_domain_node_id,
        candidate_accepts_node_id=candidate.accepts_node_id,
        candidate_domain_node_id=candidate.domain_node_id,
        candidate_representation_node_id=candidate.representation_node_id,
        candidate_encoder_bound_identity_node_id=(
            candidate.encoder_bound_identity_node_id
        ),
        route_source_declaration=candidate.declaration,
        route_source_node_id=candidate.problem_node_id,
        confidence_explanation=(
            "Lean emitted a nonce-bound predicate_match after checking the observed "
            "predicate/domain against this catalog presentation; Python verified every "
            "exported problem, accepts, domain, representation, and encoder identity "
            "node against the same-registry catalog. The final artifact must still "
            "elaborate at the original predicate declaration."
        ),
        validation_source="lean_nonce_bound_predicate_match_catalog_nodes",
        registry_fingerprint=catalog.registry_fingerprint,
        search_result_entry_id=candidate.entry_id,
    )
