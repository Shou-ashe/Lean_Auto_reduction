"""Fingerprint-bound search over Lean-validated hardness targets.

The catalog is observational.  A target or evidence row is usable only because
Lean exported its exact endpoint and native capability under the same registry
fingerprint.  Python groups, bounds, and audits those rows; it never upgrades a
backend certificate or infers hardness from a declaration name.
"""

from __future__ import annotations

import json
import re
from collections import defaultdict
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from .models import sha256_id


HARDNESS_TARGET_CATALOG_SCHEMA = "hardness_target_catalog_v1"
HARDNESS_TARGET_ENTRY_SCHEMA = "hardness_target_catalog_entry_v1"
HARDNESS_TARGET_EVIDENCE_SCHEMA = "hardness_target_evidence_v1"
MARKER = "HARDNESS_AGENT"

NATIVE_NP_POLICY = "native_np"
NATIVE_NP_HARD_POLICY = "native_np_hard"
NATIVE_NP_COMPLETE_POLICY = "native_np_complete"
NATIVE_COMPLETENESS_MEMBERSHIP_PROJECTION = (
    "ComplexityReduction.Certificate.NativeTMNPComplete.nativeMembership"
)
TARGET_POLICIES = (
    NATIVE_NP_POLICY,
    NATIVE_NP_HARD_POLICY,
    NATIVE_NP_COMPLETE_POLICY,
)
TARGET_POLICY_SET = frozenset(TARGET_POLICIES)
POLICY_ORDER = {policy: index for index, policy in enumerate(TARGET_POLICIES)}

ALLOWED_EVIDENCE_KINDS = frozenset(
    {
        "native_membership",
        "registered_native_membership",
        "native_completeness",
        "registered_native_completeness",
        "native_completeness_projection",
        "transported_native_hardness",
        "transported_native_completeness",
    }
)
MEMBERSHIP_ONLY_EVIDENCE_KINDS = frozenset(
    {"native_membership", "registered_native_membership"}
)
EXACT_COMPLETENESS_EVIDENCE_KINDS = frozenset(
    {"native_completeness", "registered_native_completeness"}
)
DERIVED_EVIDENCE_KINDS = frozenset(
    {"transported_native_hardness", "transported_native_completeness"}
)

DECLARATION_RE = re.compile(
    r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*"
)
FULL_DECLARATION_RE = re.compile(
    r"(?<![A-Za-z0-9_'])"
    r"(?:[A-Z][A-Za-z0-9_']*\.)+[A-Za-z_][A-Za-z0-9_']*"
    r"(?![A-Za-z0-9_'])"
)
VALIDATION_SOURCE_RE = re.compile(r"[a-z][a-z0-9_.-]*")
WORD_RE = re.compile(r"[A-Za-z0-9]+")
CAMEL_BOUNDARY_RE = re.compile(r"(?<=[a-z0-9])(?=[A-Z])")
FORBIDDEN_TERM_RE = re.compile(
    r"\b(?:sorry|admit|sorryAx|axiom|import|namespace|section|theorem|lemma|def|example)\b"
)

FORBIDDEN_NAME_COMPONENTS = frozenset(
    {
        "Oracle",
        "Oracles",
        "Gold",
        "GoldProofs",
        "Expected",
        "HiddenTargets",
        "Legacy",
    }
)
SEARCH_STOPWORDS = frozenset(
    {
        "problem",
        "presented",
        "target",
        "native",
        "complexity",
        "reduction",
        "certificate",
    }
)

MAX_LEAN_TERM_CHARS = 4096
MAX_TARGET_SEARCHES_PER_ROUND = 4
MAX_TARGET_TERMS_PER_SEARCH = 8
MAX_TARGET_PREFIXES_PER_SEARCH = 6
MAX_TARGET_POLICIES_PER_SEARCH = len(TARGET_POLICIES)
MAX_TARGET_RESULTS_PER_SEARCH = 8
MAX_TARGET_RESULTS_PER_ROUND = 12
MAX_INITIAL_TARGET_NAMESPACES = 8
MAX_SEARCH_TEXT_CHARS = 128


class HardnessTargetCatalogError(ValueError):
    """A malformed, stale, forbidden, or contradictory target catalog."""


class HardnessTargetSearchError(ValueError):
    """An invalid or excessively broad ``search_hardness_targets`` request."""


def declaration_namespace(declaration: str) -> str:
    namespace, separator, _ = declaration.rpartition(".")
    return namespace if separator else declaration


def _validate_public_name(
    value: str,
    *,
    label: str,
    require_qualified: bool = True,
) -> str:
    if not value or not DECLARATION_RE.fullmatch(value):
        raise HardnessTargetCatalogError(f"{label} is not a valid Lean name")
    if require_qualified and "." not in value:
        raise HardnessTargetCatalogError(f"{label} is not fully qualified")
    forbidden = FORBIDDEN_NAME_COMPONENTS.intersection(value.split("."))
    if forbidden:
        raise HardnessTargetCatalogError(
            f"forbidden public target catalog name in {label}: {value}"
        )
    return value


def _validate_fingerprint(value: str, *, label: str) -> str:
    if not value.startswith("lean:") or len(value) <= len("lean:"):
        raise HardnessTargetCatalogError(f"{label} is not a Lean registry fingerprint")
    return value


def _validate_node_id(value: str, *, label: str) -> str:
    if not value.startswith("lean-whnf:") or len(value) <= len("lean-whnf:"):
        raise HardnessTargetCatalogError(f"{label} is not a Lean whnf endpoint node")
    return value


def _validate_lean_term(value: str, *, label: str, allow_empty: bool = False) -> str:
    if not value:
        if allow_empty:
            return value
        raise HardnessTargetCatalogError(f"{label} is empty")
    if len(value) > MAX_LEAN_TERM_CHARS:
        raise HardnessTargetCatalogError(f"{label} exceeds the bounded Lean-term size")
    if any(character in value for character in ("\n", "\r", "\t")):
        raise HardnessTargetCatalogError(f"{label} contains a row-breaking character")
    if FORBIDDEN_TERM_RE.search(value):
        raise HardnessTargetCatalogError(f"{label} contains forbidden Lean syntax")
    for declaration in FULL_DECLARATION_RE.findall(value):
        _validate_public_name(declaration, label=f"{label} declaration")
    return value


def _canonical_policies(
    values: Sequence[str],
    *,
    label: str,
) -> tuple[str, ...]:
    if not values:
        raise HardnessTargetCatalogError(f"{label} must contain at least one policy")
    if len(values) != len(set(values)):
        raise HardnessTargetCatalogError(f"{label} contains a duplicate policy")
    unknown = set(values) - TARGET_POLICY_SET
    if unknown:
        raise HardnessTargetCatalogError(
            f"{label} contains unsupported policies: {sorted(unknown)}"
        )
    return tuple(sorted(values, key=POLICY_ORDER.__getitem__))


def _split_csv(value: str, *, label: str, required: bool = True) -> tuple[str, ...]:
    values = tuple(item.strip() for item in value.split(",") if item.strip())
    if required and not values:
        raise HardnessTargetCatalogError(f"{label} must not be empty")
    if len(values) != len(set(values)):
        raise HardnessTargetCatalogError(f"{label} contains duplicate values")
    return values


@dataclass(frozen=True)
class HardnessTargetEvidence:
    target_declaration: str
    target_node_id: str
    evidence_kind: str
    evidence_declaration: str
    evidence_lean_term: str
    membership_lean_term: str
    satisfied_policies: tuple[str, ...]
    validation_source: str
    provenance_declarations: tuple[str, ...]
    registry_fingerprint: str
    schema_version: str = HARDNESS_TARGET_EVIDENCE_SCHEMA

    @property
    def evidence_id(self) -> str:
        return sha256_id(self.to_dict(include_evidence_id=False))

    def to_dict(self, *, include_evidence_id: bool = True) -> dict[str, Any]:
        value: dict[str, Any] = {
            "schema_version": self.schema_version,
            "target_declaration": self.target_declaration,
            "target_node_id": self.target_node_id,
            "evidence_kind": self.evidence_kind,
            "evidence_declaration": self.evidence_declaration,
            "evidence_lean_term": self.evidence_lean_term,
            "membership_lean_term": self.membership_lean_term,
            "satisfied_policies": list(self.satisfied_policies),
            "validation_source": self.validation_source,
            "provenance_declarations": list(self.provenance_declarations),
            "registry_fingerprint": self.registry_fingerprint,
        }
        if include_evidence_id:
            value["evidence_id"] = self.evidence_id
        return value


@dataclass(frozen=True)
class HardnessTargetCatalogEntry:
    target_declaration: str
    target_display: str
    target_node_id: str
    target_namespace: str
    registry_fingerprint: str
    evidences: tuple[HardnessTargetEvidence, ...]
    schema_version: str = HARDNESS_TARGET_ENTRY_SCHEMA

    @property
    def satisfied_policies(self) -> tuple[str, ...]:
        policies = {
            policy
            for evidence in self.evidences
            for policy in evidence.satisfied_policies
        }
        return tuple(sorted(policies, key=POLICY_ORDER.__getitem__))

    @property
    def target_entry_id(self) -> str:
        return sha256_id(self.to_dict(include_target_entry_id=False))

    def to_dict(self, *, include_target_entry_id: bool = True) -> dict[str, Any]:
        value: dict[str, Any] = {
            "schema_version": self.schema_version,
            "target_declaration": self.target_declaration,
            "target_display": self.target_display,
            "target_node_id": self.target_node_id,
            "target_namespace": self.target_namespace,
            "registry_fingerprint": self.registry_fingerprint,
            "satisfied_policies": list(self.satisfied_policies),
            "evidence_count": len(self.evidences),
            "evidences": [evidence.to_dict() for evidence in self.evidences],
        }
        if include_target_entry_id:
            value["target_entry_id"] = self.target_entry_id
        return value


@dataclass(frozen=True)
class HardnessTargetCatalog:
    registry_fingerprint: str
    entries: tuple[HardnessTargetCatalogEntry, ...]
    toolchain: str = ""
    lake_manifest_sha256: str = ""
    schema_version: str = HARDNESS_TARGET_CATALOG_SCHEMA

    @property
    def evidence_count(self) -> int:
        return sum(len(entry.evidences) for entry in self.entries)

    @property
    def catalog_id(self) -> str:
        return sha256_id(self.to_dict(include_catalog_id=False))

    def to_dict(self, *, include_catalog_id: bool = True) -> dict[str, Any]:
        value: dict[str, Any] = {
            "schema_version": self.schema_version,
            "registry_fingerprint": self.registry_fingerprint,
            "toolchain": self.toolchain,
            "lake_manifest_sha256": self.lake_manifest_sha256,
            "target_count": len(self.entries),
            "evidence_count": self.evidence_count,
            "entries": [entry.to_dict() for entry in self.entries],
        }
        if include_catalog_id:
            value["catalog_id"] = self.catalog_id
        return value


@dataclass(frozen=True)
class HardnessTargetSearch:
    required_policies: tuple[str, ...] = ()
    terms: tuple[str, ...] = ()
    namespace_prefixes: tuple[str, ...] = ()
    limit: int = MAX_TARGET_RESULTS_PER_SEARCH

    def to_dict(self) -> dict[str, Any]:
        return {
            "required_policies": list(self.required_policies),
            "terms": list(self.terms),
            "namespace_prefixes": list(self.namespace_prefixes),
            "limit": self.limit,
        }


def _validate_evidence(evidence: HardnessTargetEvidence) -> None:
    _validate_public_name(
        evidence.target_declaration, label="target evidence endpoint declaration"
    )
    _validate_node_id(evidence.target_node_id, label="target evidence endpoint node")
    _validate_public_name(
        evidence.evidence_declaration, label="target evidence declaration"
    )
    _validate_fingerprint(
        evidence.registry_fingerprint, label="target evidence registry fingerprint"
    )
    if evidence.evidence_kind not in ALLOWED_EVIDENCE_KINDS:
        raise HardnessTargetCatalogError(
            f"unsupported or backend target evidence kind: {evidence.evidence_kind}"
        )
    canonical_policies = _canonical_policies(
        evidence.satisfied_policies,
        label="target evidence satisfied_policies",
    )
    if evidence.satisfied_policies != canonical_policies:
        raise HardnessTargetCatalogError(
            "target evidence satisfied_policies are not in canonical order"
        )
    if evidence.evidence_kind in MEMBERSHIP_ONLY_EVIDENCE_KINDS and set(
        evidence.satisfied_policies
    ) != {NATIVE_NP_POLICY}:
        raise HardnessTargetCatalogError(
            "native membership evidence may satisfy only the native_np policy"
        )
    if evidence.evidence_kind in EXACT_COMPLETENESS_EVIDENCE_KINDS and set(
        evidence.satisfied_policies
    ) != TARGET_POLICY_SET:
        raise HardnessTargetCatalogError(
            "native completeness evidence must satisfy all three native policies"
        )
    if evidence.evidence_kind in EXACT_COMPLETENESS_EVIDENCE_KINDS:
        projection_prefix = NATIVE_COMPLETENESS_MEMBERSHIP_PROJECTION + " "
        if not evidence.membership_lean_term.startswith(projection_prefix):
            raise HardnessTargetCatalogError(
                "native completeness membership projection is missing or malformed"
            )
        if (
            NATIVE_COMPLETENESS_MEMBERSHIP_PROJECTION
            not in evidence.provenance_declarations
        ):
            raise HardnessTargetCatalogError(
                "native completeness membership projection is absent from provenance"
            )
    if evidence.evidence_kind == "native_completeness_projection" and set(
        evidence.satisfied_policies
    ) != {NATIVE_NP_POLICY}:
        raise HardnessTargetCatalogError(
            "native completeness projection evidence may satisfy only native_np"
        )
    if evidence.evidence_kind == "transported_native_hardness" and set(
        evidence.satisfied_policies
    ) != {NATIVE_NP_HARD_POLICY}:
        raise HardnessTargetCatalogError(
            "transported native hardness evidence may satisfy only native_np_hard"
        )
    if evidence.evidence_kind == "transported_native_completeness" and set(
        evidence.satisfied_policies
    ) != TARGET_POLICY_SET:
        raise HardnessTargetCatalogError(
            "transported native completeness evidence must satisfy all native policies"
        )
    if not VALIDATION_SOURCE_RE.fullmatch(evidence.validation_source):
        raise HardnessTargetCatalogError("target evidence validation_source is malformed")
    lowered_source = evidence.validation_source.lower()
    if not lowered_source.startswith("lean_") or any(
        forbidden in lowered_source for forbidden in ("backend", "legacy", "oracle")
    ):
        raise HardnessTargetCatalogError(
            "target evidence validation_source is not a native Lean validation source"
        )
    if not evidence.provenance_declarations:
        raise HardnessTargetCatalogError("target evidence has no Lean provenance")
    if len(evidence.provenance_declarations) != len(
        set(evidence.provenance_declarations)
    ):
        raise HardnessTargetCatalogError(
            "target evidence repeats a provenance declaration"
        )
    for declaration in evidence.provenance_declarations:
        _validate_public_name(declaration, label="target evidence provenance")
    if evidence.evidence_declaration not in evidence.provenance_declarations:
        raise HardnessTargetCatalogError(
            "target evidence declaration is absent from its provenance"
        )
    _validate_lean_term(evidence.evidence_lean_term, label="target evidence Lean term")
    if not any(
        declaration in evidence.evidence_lean_term
        for declaration in evidence.provenance_declarations
    ):
        raise HardnessTargetCatalogError(
            "target evidence Lean term does not reference its provenance"
        )
    membership_required = bool(
        {NATIVE_NP_POLICY, NATIVE_NP_COMPLETE_POLICY}.intersection(
            evidence.satisfied_policies
        )
    )
    _validate_lean_term(
        evidence.membership_lean_term,
        label="target membership Lean term",
        allow_empty=not membership_required,
    )
    if evidence.membership_lean_term and not any(
        declaration in evidence.membership_lean_term
        for declaration in evidence.provenance_declarations
    ):
        raise HardnessTargetCatalogError(
            "target membership Lean term does not reference its provenance"
        )


def _validate_entry(entry: HardnessTargetCatalogEntry) -> None:
    _validate_public_name(entry.target_declaration, label="hardness target declaration")
    if not entry.target_display:
        raise HardnessTargetCatalogError("hardness target has no bounded display")
    if any(character in entry.target_display for character in ("\n", "\r", "\t")):
        raise HardnessTargetCatalogError("hardness target display breaks the row protocol")
    _validate_node_id(entry.target_node_id, label="hardness target node")
    _validate_public_name(
        entry.target_namespace,
        label="hardness target namespace",
        require_qualified=False,
    )
    if entry.target_namespace != declaration_namespace(entry.target_declaration):
        raise HardnessTargetCatalogError(
            "hardness target namespace does not match its declaration"
        )
    _validate_fingerprint(
        entry.registry_fingerprint, label="hardness target registry fingerprint"
    )
    if not entry.evidences:
        raise HardnessTargetCatalogError("hardness target has no native evidence")
    evidence_ids: set[str] = set()
    evidence_declarations: set[str] = set()
    for evidence in entry.evidences:
        _validate_evidence(evidence)
        if evidence.target_declaration != entry.target_declaration:
            raise HardnessTargetCatalogError(
                "target evidence declaration endpoint does not match its target"
            )
        if evidence.target_node_id != entry.target_node_id:
            raise HardnessTargetCatalogError(
                "target evidence node does not match its target"
            )
        if evidence.registry_fingerprint != entry.registry_fingerprint:
            raise HardnessTargetCatalogError(
                "target evidence fingerprint does not match its target"
            )
        if evidence.evidence_id in evidence_ids:
            raise HardnessTargetCatalogError("duplicate target evidence payload")
        if (
            evidence.evidence_declaration in evidence_declarations
            and evidence.evidence_kind not in DERIVED_EVIDENCE_KINDS
        ):
            raise HardnessTargetCatalogError(
                "duplicate target evidence declaration within one target"
            )
        evidence_ids.add(evidence.evidence_id)
        evidence_declarations.add(evidence.evidence_declaration)


def _catalog(
    *,
    registry_fingerprint: str,
    entries: Sequence[HardnessTargetCatalogEntry],
    toolchain: str = "",
    lake_manifest_sha256: str = "",
) -> HardnessTargetCatalog:
    _validate_fingerprint(registry_fingerprint, label="target catalog registry fingerprint")
    if not entries:
        raise HardnessTargetCatalogError("Lean target catalog contained no public targets")
    declarations: set[str] = set()
    nodes: set[str] = set()
    evidence_declarations: set[str] = set()
    normalized: list[HardnessTargetCatalogEntry] = []
    for entry in entries:
        _validate_entry(entry)
        if entry.registry_fingerprint != registry_fingerprint:
            raise HardnessTargetCatalogError(
                "hardness target does not match the catalog registry fingerprint"
            )
        if entry.target_declaration in declarations:
            raise HardnessTargetCatalogError(
                f"duplicate hardness target declaration: {entry.target_declaration}"
            )
        if entry.target_node_id in nodes:
            raise HardnessTargetCatalogError(
                f"duplicate canonical hardness target node: {entry.target_node_id}"
            )
        for evidence in entry.evidences:
            if (
                evidence.evidence_declaration in evidence_declarations
                and evidence.evidence_kind not in DERIVED_EVIDENCE_KINDS
            ):
                raise HardnessTargetCatalogError(
                    "one evidence declaration was assigned to multiple hardness targets"
                )
            if evidence.evidence_kind not in DERIVED_EVIDENCE_KINDS:
                evidence_declarations.add(evidence.evidence_declaration)
        declarations.add(entry.target_declaration)
        nodes.add(entry.target_node_id)
        normalized.append(entry)
    return HardnessTargetCatalog(
        registry_fingerprint=registry_fingerprint,
        entries=tuple(sorted(normalized, key=lambda item: item.target_declaration)),
        toolchain=toolchain,
        lake_manifest_sha256=lake_manifest_sha256,
    )


def parse_hardness_target_catalog(
    *,
    stdout: str,
    stderr: str,
    nonce: str,
    toolchain: str = "",
    lake_manifest_sha256: str = "",
) -> HardnessTargetCatalog:
    """Parse exactly one nonce-bound ``hardness_target_catalog_v1`` export."""

    registry_rows: list[list[str]] = []
    target_rows: list[list[str]] = []
    evidence_rows: list[list[str]] = []
    for line in f"{stdout}\n{stderr}".splitlines():
        position = line.find(MARKER + "\t")
        if position < 0:
            continue
        fields = line[position:].split("\t")
        if len(fields) < 4 or fields[1] != HARDNESS_TARGET_CATALOG_SCHEMA:
            continue
        if fields[2] != nonce:
            continue
        kind = fields[3]
        if kind == "registry":
            if len(fields) != 5:
                raise HardnessTargetCatalogError(
                    "Lean emitted a malformed target catalog registry row"
                )
            registry_rows.append(fields)
        elif kind == "target":
            if len(fields) != 9:
                raise HardnessTargetCatalogError(
                    "Lean emitted a truncated or extended target catalog row"
                )
            target_rows.append(fields)
        elif kind == "evidence":
            if len(fields) != 14:
                raise HardnessTargetCatalogError(
                    "Lean emitted a truncated or extended target evidence row"
                )
            evidence_rows.append(fields)
        else:
            raise HardnessTargetCatalogError(
                f"Lean emitted an unsupported target catalog row kind: {kind}"
            )
    if len(registry_rows) != 1:
        raise HardnessTargetCatalogError(
            "Lean output must contain exactly one registry row for this target catalog"
        )
    registry_fingerprint = registry_rows[0][4].strip()
    _validate_fingerprint(
        registry_fingerprint, label="target catalog registry fingerprint"
    )
    if not target_rows:
        raise HardnessTargetCatalogError("Lean target catalog contained no target rows")

    targets: dict[str, tuple[str, str, str, str]] = {}
    nodes: set[str] = set()
    for fields in target_rows:
        declaration = fields[4].strip()
        if declaration in targets:
            raise HardnessTargetCatalogError(
                f"duplicate target row for declaration: {declaration}"
            )
        node = fields[6].strip()
        if node in nodes:
            raise HardnessTargetCatalogError(f"duplicate target row for node: {node}")
        targets[declaration] = (
            fields[5].strip(),
            node,
            fields[7].strip(),
            fields[8].strip(),
        )
        nodes.add(node)

    grouped_evidence: dict[str, list[HardnessTargetEvidence]] = defaultdict(list)
    evidence_declarations: set[str] = set()
    for fields in evidence_rows:
        target_declaration = fields[4].strip()
        if target_declaration not in targets:
            raise HardnessTargetCatalogError(
                "target evidence references a target row that was not exported"
            )
        evidence_declaration = fields[7].strip()
        if evidence_declaration in evidence_declarations:
            raise HardnessTargetCatalogError(
                f"duplicate target evidence declaration: {evidence_declaration}"
            )
        evidence_declarations.add(evidence_declaration)
        policies = _canonical_policies(
            _split_csv(fields[10], label="target evidence policies"),
            label="target evidence policies",
        )
        provenance = _split_csv(
            fields[12], label="target evidence provenance declarations"
        )
        grouped_evidence[target_declaration].append(
            HardnessTargetEvidence(
                target_declaration=target_declaration,
                target_node_id=fields[5].strip(),
                evidence_kind=fields[6].strip(),
                evidence_declaration=evidence_declaration,
                evidence_lean_term=fields[8].strip(),
                membership_lean_term=fields[9].strip(),
                satisfied_policies=policies,
                validation_source=fields[11].strip(),
                provenance_declarations=provenance,
                registry_fingerprint=fields[13].strip(),
            )
        )

    entries = []
    for declaration, (display, node, namespace, fingerprint) in targets.items():
        evidences = tuple(
            sorted(
                grouped_evidence.get(declaration, []),
                key=lambda item: (item.evidence_kind, item.evidence_declaration),
            )
        )
        entries.append(
            HardnessTargetCatalogEntry(
                target_declaration=declaration,
                target_display=display,
                target_node_id=node,
                target_namespace=namespace,
                registry_fingerprint=fingerprint,
                evidences=evidences,
            )
        )
    return _catalog(
        registry_fingerprint=registry_fingerprint,
        entries=entries,
        toolchain=toolchain,
        lake_manifest_sha256=lake_manifest_sha256,
    )


def _required_string(raw: Mapping[str, Any], key: str, *, label: str) -> str:
    value = raw.get(key)
    if not isinstance(value, str) or not value.strip():
        raise HardnessTargetCatalogError(f"{label}.{key} is missing")
    return value.strip()


def _string_tuple_from_json(
    value: Any,
    *,
    label: str,
    allow_empty: bool = False,
) -> tuple[str, ...]:
    if not isinstance(value, list) or (
        not allow_empty and not value
    ) or any(not isinstance(item, str) or not item.strip() for item in value):
        qualifier = "possibly empty " if allow_empty else "non-empty "
        raise HardnessTargetCatalogError(f"{label} must be a {qualifier}string list")
    normalized = tuple(item.strip() for item in value)
    if len(normalized) != len(set(normalized)):
        raise HardnessTargetCatalogError(f"{label} contains duplicates")
    return normalized


def hardness_target_catalog_from_dict(value: Mapping[str, Any]) -> HardnessTargetCatalog:
    if value.get("schema_version") != HARDNESS_TARGET_CATALOG_SCHEMA:
        raise HardnessTargetCatalogError("unsupported hardness target catalog schema")
    allowed_catalog_fields = {
        "schema_version",
        "catalog_id",
        "registry_fingerprint",
        "toolchain",
        "lake_manifest_sha256",
        "target_count",
        "evidence_count",
        "entries",
    }
    if unknown := set(value) - allowed_catalog_fields:
        raise HardnessTargetCatalogError(
            f"hardness target catalog contains unknown fields: {sorted(unknown)}"
        )
    registry_fingerprint = _required_string(
        value, "registry_fingerprint", label="target catalog"
    )
    raw_entries = value.get("entries")
    if not isinstance(raw_entries, list):
        raise HardnessTargetCatalogError("target catalog entries must be a list")
    entries: list[HardnessTargetCatalogEntry] = []
    for entry_index, raw_entry in enumerate(raw_entries):
        if not isinstance(raw_entry, dict):
            raise HardnessTargetCatalogError(
                f"target catalog entry {entry_index} must be an object"
            )
        if raw_entry.get("schema_version") != HARDNESS_TARGET_ENTRY_SCHEMA:
            raise HardnessTargetCatalogError(
                f"unsupported target catalog entry schema at {entry_index}"
            )
        allowed_entry_fields = {
            "schema_version",
            "target_entry_id",
            "target_declaration",
            "target_display",
            "target_node_id",
            "target_namespace",
            "registry_fingerprint",
            "satisfied_policies",
            "evidence_count",
            "evidences",
        }
        if unknown := set(raw_entry) - allowed_entry_fields:
            raise HardnessTargetCatalogError(
                f"target catalog entry {entry_index} contains unknown fields: {sorted(unknown)}"
            )
        raw_evidences = raw_entry.get("evidences")
        if not isinstance(raw_evidences, list):
            raise HardnessTargetCatalogError(
                f"target catalog entry {entry_index}.evidences must be a list"
            )
        evidences: list[HardnessTargetEvidence] = []
        for evidence_index, raw_evidence in enumerate(raw_evidences):
            label = f"target catalog entry {entry_index}.evidences[{evidence_index}]"
            if not isinstance(raw_evidence, dict):
                raise HardnessTargetCatalogError(f"{label} must be an object")
            if raw_evidence.get("schema_version") != HARDNESS_TARGET_EVIDENCE_SCHEMA:
                raise HardnessTargetCatalogError(
                    f"unsupported target evidence schema at {label}"
                )
            allowed_evidence_fields = {
                "schema_version",
                "evidence_id",
                "target_declaration",
                "target_node_id",
                "evidence_kind",
                "evidence_declaration",
                "evidence_lean_term",
                "membership_lean_term",
                "satisfied_policies",
                "validation_source",
                "provenance_declarations",
                "registry_fingerprint",
            }
            if unknown := set(raw_evidence) - allowed_evidence_fields:
                raise HardnessTargetCatalogError(
                    f"{label} contains unknown fields: {sorted(unknown)}"
                )
            membership_term = raw_evidence.get("membership_lean_term")
            if not isinstance(membership_term, str):
                raise HardnessTargetCatalogError(
                    f"{label}.membership_lean_term must be a string"
                )
            policies = _canonical_policies(
                _string_tuple_from_json(
                    raw_evidence.get("satisfied_policies"),
                    label=f"{label}.satisfied_policies",
                ),
                label=f"{label}.satisfied_policies",
            )
            evidence = HardnessTargetEvidence(
                target_declaration=_required_string(
                    raw_evidence, "target_declaration", label=label
                ),
                target_node_id=_required_string(
                    raw_evidence, "target_node_id", label=label
                ),
                evidence_kind=_required_string(
                    raw_evidence, "evidence_kind", label=label
                ),
                evidence_declaration=_required_string(
                    raw_evidence, "evidence_declaration", label=label
                ),
                evidence_lean_term=_required_string(
                    raw_evidence, "evidence_lean_term", label=label
                ),
                membership_lean_term=membership_term.strip(),
                satisfied_policies=policies,
                validation_source=_required_string(
                    raw_evidence, "validation_source", label=label
                ),
                provenance_declarations=_string_tuple_from_json(
                    raw_evidence.get("provenance_declarations"),
                    label=f"{label}.provenance_declarations",
                ),
                registry_fingerprint=_required_string(
                    raw_evidence, "registry_fingerprint", label=label
                ),
            )
            recorded_evidence_id = raw_evidence.get("evidence_id")
            if (
                recorded_evidence_id is not None
                and recorded_evidence_id != evidence.evidence_id
            ):
                raise HardnessTargetCatalogError(
                    f"{label} content ID does not match its payload"
                )
            evidences.append(evidence)
        entry_label = f"target catalog entry {entry_index}"
        entry = HardnessTargetCatalogEntry(
            target_declaration=_required_string(
                raw_entry, "target_declaration", label=entry_label
            ),
            target_display=_required_string(
                raw_entry, "target_display", label=entry_label
            ),
            target_node_id=_required_string(
                raw_entry, "target_node_id", label=entry_label
            ),
            target_namespace=_required_string(
                raw_entry, "target_namespace", label=entry_label
            ),
            registry_fingerprint=_required_string(
                raw_entry, "registry_fingerprint", label=entry_label
            ),
            evidences=tuple(
                sorted(
                    evidences,
                    key=lambda item: (item.evidence_kind, item.evidence_declaration),
                )
            ),
        )
        recorded_policies = _canonical_policies(
            _string_tuple_from_json(
                raw_entry.get("satisfied_policies"),
                label=f"{entry_label}.satisfied_policies",
            ),
            label=f"{entry_label}.satisfied_policies",
        )
        if recorded_policies != entry.satisfied_policies:
            raise HardnessTargetCatalogError(
                f"{entry_label} satisfied policies do not match its evidence"
            )
        if raw_entry.get("evidence_count") != len(entry.evidences):
            raise HardnessTargetCatalogError(
                f"{entry_label} evidence count does not match its entries"
            )
        recorded_entry_id = raw_entry.get("target_entry_id")
        if recorded_entry_id is not None and recorded_entry_id != entry.target_entry_id:
            raise HardnessTargetCatalogError(
                f"{entry_label} content ID does not match its payload"
            )
        entries.append(entry)
    toolchain = value.get("toolchain", "")
    manifest_hash = value.get("lake_manifest_sha256", "")
    if not isinstance(toolchain, str) or not isinstance(manifest_hash, str):
        raise HardnessTargetCatalogError("target catalog fingerprints must be strings")
    catalog = _catalog(
        registry_fingerprint=registry_fingerprint,
        entries=entries,
        toolchain=toolchain,
        lake_manifest_sha256=manifest_hash,
    )
    if value.get("target_count") != len(catalog.entries):
        raise HardnessTargetCatalogError("target catalog count does not match its entries")
    if value.get("evidence_count") != catalog.evidence_count:
        raise HardnessTargetCatalogError(
            "target catalog evidence count does not match its entries"
        )
    recorded_catalog_id = value.get("catalog_id")
    if recorded_catalog_id is not None and recorded_catalog_id != catalog.catalog_id:
        raise HardnessTargetCatalogError(
            "target catalog content ID does not match its payload"
        )
    return catalog


def load_hardness_target_catalog_snapshot(
    path: Path,
    *,
    expected_registry_fingerprint: str | None = None,
    expected_toolchain: str | None = None,
    expected_lake_manifest_sha256: str | None = None,
) -> HardnessTargetCatalog:
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as error:
        raise HardnessTargetCatalogError(
            f"hardness target catalog snapshot not found: {path}"
        ) from error
    except json.JSONDecodeError as error:
        raise HardnessTargetCatalogError(
            f"invalid hardness target catalog JSON: {error}"
        ) from error
    if not isinstance(raw, dict):
        raise HardnessTargetCatalogError(
            "hardness target catalog snapshot must be a JSON object"
        )
    catalog = hardness_target_catalog_from_dict(raw)
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
            raise HardnessTargetCatalogError(
                f"stale hardness target catalog: {label} does not match the current environment"
            )
    return catalog


def _query_string_list(
    value: Any,
    *,
    label: str,
    maximum: int,
) -> tuple[str, ...]:
    if value is None:
        return ()
    if (
        not isinstance(value, list)
        or len(value) > maximum
        or any(not isinstance(item, str) or not item.strip() for item in value)
    ):
        raise HardnessTargetSearchError(
            f"{label} must be a string list with at most {maximum} items"
        )
    normalized = tuple(item.strip() for item in value)
    if len(normalized) != len(set(normalized)):
        raise HardnessTargetSearchError(f"{label} must not contain duplicates")
    for item in normalized:
        if len(item) > MAX_SEARCH_TEXT_CHARS or any(
            character in item for character in ("\n", "\r", "\t")
        ):
            raise HardnessTargetSearchError(f"{label} contains an unsafe search value")
    return normalized


def parse_hardness_target_searches(
    payload: Mapping[str, Any],
) -> tuple[HardnessTargetSearch, ...]:
    raw_searches = payload.get("searches")
    if (
        not isinstance(raw_searches, list)
        or not raw_searches
        or len(raw_searches) > MAX_TARGET_SEARCHES_PER_ROUND
    ):
        raise HardnessTargetSearchError(
            f"searches must contain 1..{MAX_TARGET_SEARCHES_PER_ROUND} objects"
        )
    searches: list[HardnessTargetSearch] = []
    for index, raw in enumerate(raw_searches):
        if not isinstance(raw, dict):
            raise HardnessTargetSearchError(f"searches[{index}] must be an object")
        allowed_fields = {
            "required_policies",
            "terms",
            "namespace_prefixes",
            "limit",
        }
        if unknown := set(raw) - allowed_fields:
            raise HardnessTargetSearchError(
                f"searches[{index}] contains unsupported fields: {sorted(unknown)}"
            )
        policies = _query_string_list(
            raw.get("required_policies"),
            label=f"searches[{index}].required_policies",
            maximum=MAX_TARGET_POLICIES_PER_SEARCH,
        )
        unknown_policies = set(policies) - TARGET_POLICY_SET
        if unknown_policies:
            raise HardnessTargetSearchError(
                f"searches[{index}] contains unsupported policies: "
                f"{sorted(unknown_policies)}"
            )
        policies = tuple(sorted(policies, key=POLICY_ORDER.__getitem__))
        terms = _query_string_list(
            raw.get("terms"),
            label=f"searches[{index}].terms",
            maximum=MAX_TARGET_TERMS_PER_SEARCH,
        )
        prefixes = _query_string_list(
            raw.get("namespace_prefixes"),
            label=f"searches[{index}].namespace_prefixes",
            maximum=MAX_TARGET_PREFIXES_PER_SEARCH,
        )
        for prefix in prefixes:
            if not DECLARATION_RE.fullmatch(prefix):
                raise HardnessTargetSearchError(
                    f"searches[{index}] contains an invalid namespace prefix"
                )
            if FORBIDDEN_NAME_COMPONENTS.intersection(prefix.split(".")):
                raise HardnessTargetSearchError(
                    f"searches[{index}] requests a forbidden namespace"
                )
        lowered_terms = {
            token.lower()
            for term in terms
            for token in WORD_RE.findall(term)
        }
        if lowered_terms.intersection(
            component.lower() for component in FORBIDDEN_NAME_COMPONENTS
        ):
            raise HardnessTargetSearchError(
                f"searches[{index}] requests forbidden oracle or legacy data"
            )
        if not any((policies, terms, prefixes)):
            raise HardnessTargetSearchError(
                f"searches[{index}] must include a policy, term, or namespace filter"
            )
        limit = raw.get("limit", MAX_TARGET_RESULTS_PER_SEARCH)
        if isinstance(limit, bool) or not isinstance(limit, int) or limit < 1:
            raise HardnessTargetSearchError(
                f"searches[{index}].limit must be a positive integer"
            )
        searches.append(
            HardnessTargetSearch(
                required_policies=policies,
                terms=terms,
                namespace_prefixes=prefixes,
                limit=min(limit, MAX_TARGET_RESULTS_PER_SEARCH),
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


def _entry_score(
    entry: HardnessTargetCatalogEntry,
    search: HardnessTargetSearch,
) -> int | None:
    if not set(search.required_policies).issubset(entry.satisfied_policies):
        return None
    if search.namespace_prefixes and not any(
        _namespace_matches(entry.target_namespace, prefix)
        for prefix in search.namespace_prefixes
    ):
        return None
    score = len(search.required_policies) * 100
    if search.namespace_prefixes:
        score += 20
    if not search.terms:
        return score
    haystack = " ".join(
        (
            entry.target_declaration,
            entry.target_display,
            entry.target_namespace,
            " ".join(entry.satisfied_policies),
            " ".join(evidence.evidence_kind for evidence in entry.evidences),
            " ".join(
                evidence.evidence_declaration for evidence in entry.evidences
            ),
        )
    )
    lowered = haystack.lower()
    tokens = _search_tokens(haystack)
    matched = False
    for term in search.terms:
        normalized = term.lower()
        if normalized in lowered:
            score += 12
            matched = True
        overlap = len(_search_tokens(term) & tokens)
        if overlap:
            score += overlap * 3
            matched = True
    return score if matched else None


def search_hardness_targets(
    catalog: HardnessTargetCatalog,
    searches: Sequence[HardnessTargetSearch],
) -> tuple[HardnessTargetCatalogEntry, ...]:
    """Execute bounded deterministic searches without exposing the full catalog."""

    if not searches or len(searches) > MAX_TARGET_SEARCHES_PER_ROUND:
        raise HardnessTargetSearchError(
            f"a target search round must contain 1..{MAX_TARGET_SEARCHES_PER_ROUND} searches"
        )
    selected: dict[str, tuple[int, HardnessTargetCatalogEntry]] = {}
    for search in searches:
        scored = sorted(
            (
                (score, entry)
                for entry in catalog.entries
                if (score := _entry_score(entry, search)) is not None
            ),
            key=lambda item: (-item[0], item[1].target_declaration),
        )[: search.limit]
        for score, entry in scored:
            previous = selected.get(entry.target_entry_id)
            if previous is None or score > previous[0]:
                selected[entry.target_entry_id] = (score, entry)
    return tuple(
        entry
        for _, entry in sorted(
            selected.values(),
            key=lambda item: (-item[0], item[1].target_declaration),
        )[:MAX_TARGET_RESULTS_PER_ROUND]
    )


def hardness_target_search_result(
    entry: HardnessTargetCatalogEntry,
    *,
    required_policies: Sequence[str] = (),
) -> dict[str, Any]:
    required = set(required_policies)
    evidences = [
        evidence
        for evidence in entry.evidences
        if not required or required.issubset(evidence.satisfied_policies)
    ]
    return {
        "target_entry_id": entry.target_entry_id,
        "target_declaration": entry.target_declaration,
        "target_display": entry.target_display,
        "target_node_id": entry.target_node_id,
        "target_namespace": entry.target_namespace,
        "satisfied_policies": list(entry.satisfied_policies),
        "evidences": [evidence.to_dict() for evidence in evidences],
        "registry_fingerprint": entry.registry_fingerprint,
        "validation_source": "lean_validated_hardness_target_catalog",
    }


def build_hardness_target_summary(catalog: HardnessTargetCatalog) -> dict[str, Any]:
    """Return bounded prompt hints without target or evidence declaration names."""

    policy_counts = {
        policy: sum(policy in entry.satisfied_policies for entry in catalog.entries)
        for policy in TARGET_POLICIES
    }
    evidence_kind_counts: dict[str, int] = defaultdict(int)
    namespace_counts: dict[str, int] = defaultdict(int)
    for entry in catalog.entries:
        namespace_counts[entry.target_namespace] += 1
        for evidence in entry.evidences:
            evidence_kind_counts[evidence.evidence_kind] += 1
    nearby_namespaces = [
        {"namespace": namespace, "target_count": count}
        for namespace, count in sorted(
            namespace_counts.items(), key=lambda item: (-item[1], item[0])
        )[:MAX_INITIAL_TARGET_NAMESPACES]
    ]
    return {
        "contains_declaration_names": False,
        "catalog_id": catalog.catalog_id,
        "registry_fingerprint": catalog.registry_fingerprint,
        "target_count": len(catalog.entries),
        "evidence_count": catalog.evidence_count,
        "policy_target_counts": policy_counts,
        "evidence_kind_counts": dict(sorted(evidence_kind_counts.items())),
        "nearby_namespaces": nearby_namespaces,
        "full_target_catalog_included": False,
    }


def build_initial_hardness_target_hints(
    catalog: HardnessTargetCatalog,
) -> dict[str, Any]:
    """Compatibility name for the prompt-safe target summary."""

    return build_hardness_target_summary(catalog)
