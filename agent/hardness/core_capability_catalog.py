"""Stage-L exact evidence views and executable Core reduction catalog.

The catalog is observational and fingerprint-bound.  Existing connection rows
retain their exact executable projection terms, while native membership rows
derive the already proved generic Cook--Levin instance.  Every derived term is
compiled and axiom-audited by the snapshot builder before a model may query it.
"""

from __future__ import annotations

import json
import re
from collections import defaultdict
from collections.abc import Mapping, Sequence
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any

from .connection_catalog import ConnectionCatalog, ConnectionCatalogEntry
from .hardness_target_catalog import (
    EXACT_COMPLETENESS_EVIDENCE_KINDS,
    FULL_DECLARATION_RE,
    HardnessTargetCatalog,
)
from .lean_runner import validate_module_name
from .models import sha256_id
from .problem_catalog import ProblemCatalog, ProblemCatalogEntry
from .retrieval import TheoremSearch, declaration_namespace


CORE_EVIDENCE_CATALOG_SCHEMA = "hardness_core_native_evidence_catalog_v1"
CORE_EVIDENCE_ENTRY_SCHEMA = "hardness_core_native_evidence_entry_v1"
CORE_REDUCTION_CATALOG_SCHEMA = "hardness_core_reduction_catalog_v1"
CORE_REDUCTION_ENTRY_SCHEMA = "hardness_core_reduction_entry_v1"

NATIVE_MEMBERSHIP = "native_membership"
NATIVE_COMPLETENESS = "native_completeness"
EVIDENCE_KINDS = {NATIVE_MEMBERSHIP, NATIVE_COMPLETENESS}

COOK_LEVIN_REDUCTION = "ComplexityReduction.Certificate.NativeCookLevin.reduce"
COOK_LEVIN_TARGET = (
    "ComplexityReduction.Certificate.NativeCookLevin.canonicalThreeSAT"
)
NATIVE_MEMBERSHIP_HEAD = "ComplexityReduction.Certificate.NativeTMInNP"
NATIVE_COMPLETENESS_HEAD = "ComplexityReduction.Certificate.NativeTMNPComplete"
COMPLETENESS_MEMBERSHIP_PROJECTION = (
    "ComplexityReduction.Certificate.NativeTMNPComplete.nativeMembership"
)

WORD_RE = re.compile(r"[A-Za-z0-9]+")


class CoreCapabilityCatalogError(ValueError):
    """A malformed, stale, or endpoint-inconsistent Stage-L catalog."""


@dataclass(frozen=True)
class CoreNativeEvidenceEntry:
    evidence_kind: str
    endpoint_declaration: str
    endpoint_node_id: str
    evidence_declaration: str
    lean_term: str
    capability_head: str
    provenance_declarations: tuple[str, ...]
    source_evidence_id: str
    validation_source: str
    registry_fingerprint: str
    schema_version: str = CORE_EVIDENCE_ENTRY_SCHEMA

    @property
    def entry_id(self) -> str:
        return sha256_id(self.to_dict(include_entry_id=False))

    def to_dict(self, *, include_entry_id: bool = True) -> dict[str, Any]:
        value = asdict(self)
        value["dependency_count"] = len(set(self.provenance_declarations))
        value["direction"] = "exact_endpoint"
        if include_entry_id:
            value["entry_id"] = self.entry_id
        return value


@dataclass(frozen=True)
class CoreNativeEvidenceCatalog:
    registry_fingerprint: str
    entries: tuple[CoreNativeEvidenceEntry, ...]
    toolchain: str = ""
    lake_manifest_sha256: str = ""
    schema_version: str = CORE_EVIDENCE_CATALOG_SCHEMA

    @property
    def catalog_id(self) -> str:
        return sha256_id(self.to_dict(include_catalog_id=False))

    def to_dict(self, *, include_catalog_id: bool = True) -> dict[str, Any]:
        counts: dict[str, int] = defaultdict(int)
        for entry in self.entries:
            counts[entry.evidence_kind] += 1
        value: dict[str, Any] = {
            "schema_version": self.schema_version,
            "registry_fingerprint": self.registry_fingerprint,
            "toolchain": self.toolchain,
            "lake_manifest_sha256": self.lake_manifest_sha256,
            "entry_count": len(self.entries),
            "evidence_kind_counts": dict(sorted(counts.items())),
            "entries": [entry.to_dict() for entry in self.entries],
        }
        if include_catalog_id:
            value["catalog_id"] = self.catalog_id
        return value


@dataclass(frozen=True)
class CoreReductionEntry:
    certificate_declaration: str
    lean_term: str
    capability_kind: str
    component_role: str
    source_declaration: str
    target_declaration: str
    source_fingerprint: str
    target_fingerprint: str
    source_node_id: str
    target_node_id: str
    source_display: str
    target_display: str
    provenance_declarations: tuple[str, ...]
    discovery: str
    registry_fingerprint: str
    source_evidence_id: str | None = None
    schema_version: str = CORE_REDUCTION_ENTRY_SCHEMA

    @property
    def declaration(self) -> str:
        """Compatibility name used only for namespace/architecture summaries."""

        return self.certificate_declaration

    @property
    def namespace(self) -> str:
        return declaration_namespace(self.certificate_declaration)

    @property
    def entry_id(self) -> str:
        return sha256_id(self.to_dict(include_entry_id=False))

    @property
    def is_cook_levin_root(self) -> bool:
        return self.discovery == "native_membership_cook_levin_instance"

    def to_dict(self, *, include_entry_id: bool = True) -> dict[str, Any]:
        value = asdict(self)
        value.update(
            {
                "namespace": self.namespace,
                "direction": "forward",
                "dependency_count": len(set(self.provenance_declarations)),
                "is_cook_levin_root": self.is_cook_levin_root,
            }
        )
        if include_entry_id:
            value["entry_id"] = self.entry_id
        return value


@dataclass(frozen=True)
class CoreReductionCatalog:
    registry_fingerprint: str
    entries: tuple[CoreReductionEntry, ...]
    toolchain: str = ""
    lake_manifest_sha256: str = ""
    schema_version: str = CORE_REDUCTION_CATALOG_SCHEMA

    @property
    def mode(self) -> str:
        return "full"

    @property
    def catalog_id(self) -> str:
        return sha256_id(self.to_dict(include_catalog_id=False))

    def to_dict(self, *, include_catalog_id: bool = True) -> dict[str, Any]:
        value: dict[str, Any] = {
            "schema_version": self.schema_version,
            "registry_fingerprint": self.registry_fingerprint,
            "toolchain": self.toolchain,
            "lake_manifest_sha256": self.lake_manifest_sha256,
            "entry_count": len(self.entries),
            "cook_levin_root_count": sum(entry.is_cook_levin_root for entry in self.entries),
            "entries": [entry.to_dict() for entry in self.entries],
        }
        if include_catalog_id:
            value["catalog_id"] = self.catalog_id
        return value


def _ordered_declarations(term: str) -> tuple[str, ...]:
    return tuple(dict.fromkeys(FULL_DECLARATION_RE.findall(term)))


def _representatives(problem_catalog: ProblemCatalog) -> dict[str, ProblemCatalogEntry]:
    grouped: dict[str, list[ProblemCatalogEntry]] = defaultdict(list)
    for entry in problem_catalog.entries:
        grouped[entry.problem_node_id].append(entry)
    return {
        node: min(
            entries,
            key=lambda entry: (not entry.registered, len(entry.declaration), entry.declaration),
        )
        for node, entries in grouped.items()
    }


def build_core_native_evidence_catalog(
    native_target_catalog: HardnessTargetCatalog,
) -> CoreNativeEvidenceCatalog:
    """Project exact native membership and completeness into separate typed rows."""

    selected: dict[tuple[str, str, str], CoreNativeEvidenceEntry] = {}
    for target in native_target_catalog.entries:
        for evidence in target.evidences:
            if evidence.evidence_kind == NATIVE_MEMBERSHIP:
                membership_term = evidence.evidence_lean_term
                membership_declaration = evidence.evidence_declaration
                membership_source = evidence.validation_source
            elif evidence.evidence_kind in EXACT_COMPLETENESS_EVIDENCE_KINDS:
                membership_term = evidence.membership_lean_term
                membership_declaration = COMPLETENESS_MEMBERSHIP_PROJECTION
                membership_source = "native_completeness_membership_projection"
            else:
                membership_term = ""
                membership_declaration = ""
                membership_source = ""
            if membership_term:
                provenance = _ordered_declarations(membership_term)
                membership = CoreNativeEvidenceEntry(
                    evidence_kind=NATIVE_MEMBERSHIP,
                    endpoint_declaration=target.target_declaration,
                    endpoint_node_id=target.target_node_id,
                    evidence_declaration=membership_declaration,
                    lean_term=membership_term,
                    capability_head=NATIVE_MEMBERSHIP_HEAD,
                    provenance_declarations=provenance,
                    source_evidence_id=evidence.evidence_id,
                    validation_source=membership_source,
                    registry_fingerprint=target.registry_fingerprint,
                )
                key = (membership.evidence_kind, membership.endpoint_node_id, membership.lean_term)
                selected.setdefault(key, membership)
            if evidence.evidence_kind in EXACT_COMPLETENESS_EVIDENCE_KINDS:
                complete = CoreNativeEvidenceEntry(
                    evidence_kind=NATIVE_COMPLETENESS,
                    endpoint_declaration=target.target_declaration,
                    endpoint_node_id=target.target_node_id,
                    evidence_declaration=evidence.evidence_declaration,
                    lean_term=evidence.evidence_lean_term,
                    capability_head=NATIVE_COMPLETENESS_HEAD,
                    provenance_declarations=evidence.provenance_declarations,
                    source_evidence_id=evidence.evidence_id,
                    validation_source=evidence.validation_source,
                    registry_fingerprint=target.registry_fingerprint,
                )
                key = (complete.evidence_kind, complete.endpoint_node_id, complete.lean_term)
                selected.setdefault(key, complete)
    catalog = CoreNativeEvidenceCatalog(
        registry_fingerprint=native_target_catalog.registry_fingerprint,
        entries=tuple(
            sorted(
                selected.values(),
                key=lambda entry: (
                    entry.evidence_kind,
                    entry.endpoint_declaration,
                    entry.evidence_declaration,
                    entry.entry_id,
                ),
            )
        ),
        toolchain=native_target_catalog.toolchain,
        lake_manifest_sha256=native_target_catalog.lake_manifest_sha256,
    )
    _validate_evidence_catalog(catalog)
    return catalog


def _connection_reduction(
    entry: ConnectionCatalogEntry,
    representatives: Mapping[str, ProblemCatalogEntry],
) -> CoreReductionEntry:
    source = representatives.get(entry.source_node_id)
    target = representatives.get(entry.target_node_id)
    if source is None or target is None:
        raise CoreCapabilityCatalogError(
            "connection endpoint is absent from the same-fingerprint problem catalog"
        )
    provenance = tuple(
        dict.fromkeys(
            (
                entry.certificate_declaration,
                entry.projection_declaration,
                *_ordered_declarations(entry.lean_term),
            )
        )
    )
    return CoreReductionEntry(
        certificate_declaration=entry.certificate_declaration,
        lean_term=entry.lean_term,
        capability_kind="certified_reduction",
        component_role=entry.component_role,
        source_declaration=source.declaration,
        target_declaration=target.declaration,
        source_fingerprint=entry.source_fingerprint,
        target_fingerprint=entry.target_fingerprint,
        source_node_id=entry.source_node_id,
        target_node_id=entry.target_node_id,
        source_display=entry.source_display,
        target_display=entry.target_display,
        provenance_declarations=provenance,
        discovery="lean_connection_catalog",
        registry_fingerprint=entry.registry_fingerprint,
    )


def build_core_reduction_catalog(
    *,
    problem_catalog: ProblemCatalog,
    connection_catalog: ConnectionCatalog,
    evidence_catalog: CoreNativeEvidenceCatalog,
) -> CoreReductionCatalog:
    """Combine exact existing edges with generic checked Cook--Levin instances."""

    fingerprints = {
        problem_catalog.registry_fingerprint,
        connection_catalog.registry_fingerprint,
        evidence_catalog.registry_fingerprint,
    }
    if len(fingerprints) != 1:
        raise CoreCapabilityCatalogError("Core catalogs have different registry fingerprints")
    representatives = _representatives(problem_catalog)
    canonical_candidates = [
        entry
        for entry in problem_catalog.entries
        if entry.declaration == COOK_LEVIN_TARGET
    ]
    if canonical_candidates:
        canonical = canonical_candidates[0]
    else:
        complete_nodes = {
            entry.endpoint_node_id
            for entry in evidence_catalog.entries
            if entry.evidence_kind == NATIVE_COMPLETENESS
        }
        if len(complete_nodes) != 1:
            raise CoreCapabilityCatalogError("cannot identify the canonical complete hub")
        canonical = representatives[next(iter(complete_nodes))]

    rows: list[CoreReductionEntry] = [
        _connection_reduction(entry, representatives)
        for entry in connection_catalog.entries
    ]
    memberships_by_node: dict[str, CoreNativeEvidenceEntry] = {}
    for evidence in evidence_catalog.entries:
        if evidence.evidence_kind != NATIVE_MEMBERSHIP:
            continue
        current = memberships_by_node.get(evidence.endpoint_node_id)
        if current is None or (
            evidence.validation_source != "native_completeness_membership_projection",
            len(evidence.lean_term),
            evidence.evidence_declaration,
        ) < (
            current.validation_source != "native_completeness_membership_projection",
            len(current.lean_term),
            current.evidence_declaration,
        ):
            memberships_by_node[evidence.endpoint_node_id] = evidence
    for node_id, membership in sorted(memberships_by_node.items()):
        if node_id == canonical.problem_node_id:
            continue
        source = representatives.get(node_id)
        if source is None:
            raise CoreCapabilityCatalogError("membership endpoint has no problem representative")
        term = f"{COOK_LEVIN_REDUCTION} ({membership.lean_term})"
        provenance = tuple(
            dict.fromkeys(
                (
                    COOK_LEVIN_REDUCTION,
                    *membership.provenance_declarations,
                )
            )
        )
        rows.append(
            CoreReductionEntry(
                certificate_declaration=COOK_LEVIN_REDUCTION,
                lean_term=term,
                capability_kind="certified_reduction",
                component_role="cookLevinRoot",
                source_declaration=membership.endpoint_declaration,
                target_declaration=COOK_LEVIN_TARGET,
                source_fingerprint=f"lean-node:{node_id}",
                target_fingerprint=f"lean-node:{canonical.problem_node_id}",
                source_node_id=node_id,
                target_node_id=canonical.problem_node_id,
                source_display=source.display,
                target_display=canonical.display,
                provenance_declarations=provenance,
                discovery="native_membership_cook_levin_instance",
                registry_fingerprint=evidence_catalog.registry_fingerprint,
                source_evidence_id=membership.entry_id,
            )
        )
    catalog = CoreReductionCatalog(
        registry_fingerprint=problem_catalog.registry_fingerprint,
        entries=tuple(
            sorted(
                rows,
                key=lambda entry: (
                    entry.source_node_id,
                    entry.target_node_id,
                    entry.certificate_declaration,
                    entry.lean_term,
                ),
            )
        ),
        toolchain=problem_catalog.toolchain,
        lake_manifest_sha256=problem_catalog.lake_manifest_sha256,
    )
    _validate_reduction_catalog(catalog)
    return catalog


def _validate_evidence_entry(entry: CoreNativeEvidenceEntry) -> None:
    if entry.evidence_kind not in EVIDENCE_KINDS:
        raise CoreCapabilityCatalogError("unsupported native evidence kind")
    expected_head = (
        NATIVE_MEMBERSHIP_HEAD
        if entry.evidence_kind == NATIVE_MEMBERSHIP
        else NATIVE_COMPLETENESS_HEAD
    )
    if entry.capability_head != expected_head:
        raise CoreCapabilityCatalogError("native evidence capability head mismatch")
    if not entry.endpoint_node_id.startswith("lean-whnf:"):
        raise CoreCapabilityCatalogError("native evidence has no exact endpoint node")
    if not entry.lean_term or not entry.evidence_declaration:
        raise CoreCapabilityCatalogError("native evidence has no executable term")
    if not entry.provenance_declarations:
        raise CoreCapabilityCatalogError("native evidence has no provenance")


def _validate_evidence_catalog(catalog: CoreNativeEvidenceCatalog) -> None:
    if not catalog.registry_fingerprint:
        raise CoreCapabilityCatalogError("native evidence catalog has no fingerprint")
    ids: set[str] = set()
    for entry in catalog.entries:
        _validate_evidence_entry(entry)
        if entry.registry_fingerprint != catalog.registry_fingerprint:
            raise CoreCapabilityCatalogError("native evidence row has a stale fingerprint")
        if entry.entry_id in ids:
            raise CoreCapabilityCatalogError("duplicate native evidence entry ID")
        ids.add(entry.entry_id)


def _validate_reduction_entry(entry: CoreReductionEntry) -> None:
    if entry.capability_kind != "certified_reduction":
        raise CoreCapabilityCatalogError("Core reduction row has the wrong capability kind")
    if not entry.source_node_id.startswith("lean-whnf:") or not entry.target_node_id.startswith(
        "lean-whnf:"
    ):
        raise CoreCapabilityCatalogError("Core reduction row has no exact endpoint nodes")
    if not entry.lean_term or not entry.provenance_declarations:
        raise CoreCapabilityCatalogError("Core reduction row has no executable provenance")
    if entry.is_cook_levin_root and (
        entry.certificate_declaration != COOK_LEVIN_REDUCTION
        or entry.target_declaration != COOK_LEVIN_TARGET
        or entry.source_evidence_id is None
    ):
        raise CoreCapabilityCatalogError("Cook--Levin instance metadata is inconsistent")


def _validate_reduction_catalog(catalog: CoreReductionCatalog) -> None:
    ids: set[str] = set()
    for entry in catalog.entries:
        _validate_reduction_entry(entry)
        if entry.registry_fingerprint != catalog.registry_fingerprint:
            raise CoreCapabilityCatalogError("Core reduction row has a stale fingerprint")
        if entry.entry_id in ids:
            raise CoreCapabilityCatalogError("duplicate Core reduction entry ID")
        ids.add(entry.entry_id)


def _parse_evidence_entry(value: Mapping[str, Any]) -> CoreNativeEvidenceEntry:
    return CoreNativeEvidenceEntry(
        evidence_kind=str(value.get("evidence_kind") or ""),
        endpoint_declaration=str(value.get("endpoint_declaration") or ""),
        endpoint_node_id=str(value.get("endpoint_node_id") or ""),
        evidence_declaration=str(value.get("evidence_declaration") or ""),
        lean_term=str(value.get("lean_term") or ""),
        capability_head=str(value.get("capability_head") or ""),
        provenance_declarations=tuple(value.get("provenance_declarations") or ()),
        source_evidence_id=str(value.get("source_evidence_id") or ""),
        validation_source=str(value.get("validation_source") or ""),
        registry_fingerprint=str(value.get("registry_fingerprint") or ""),
        schema_version=str(value.get("schema_version") or ""),
    )


def core_native_evidence_catalog_from_dict(
    value: Mapping[str, Any],
) -> CoreNativeEvidenceCatalog:
    if value.get("schema_version") != CORE_EVIDENCE_CATALOG_SCHEMA:
        raise CoreCapabilityCatalogError("unsupported Core native evidence schema")
    raw_entries = value.get("entries")
    if not isinstance(raw_entries, list):
        raise CoreCapabilityCatalogError("Core native evidence entries must be a list")
    catalog = CoreNativeEvidenceCatalog(
        registry_fingerprint=str(value.get("registry_fingerprint") or ""),
        entries=tuple(_parse_evidence_entry(entry) for entry in raw_entries),
        toolchain=str(value.get("toolchain") or ""),
        lake_manifest_sha256=str(value.get("lake_manifest_sha256") or ""),
    )
    _validate_evidence_catalog(catalog)
    supplied = value.get("catalog_id")
    if supplied is not None and supplied != catalog.catalog_id:
        raise CoreCapabilityCatalogError("Core native evidence catalog ID mismatch")
    return catalog


def _parse_reduction_entry(value: Mapping[str, Any]) -> CoreReductionEntry:
    source_evidence_id = value.get("source_evidence_id")
    return CoreReductionEntry(
        certificate_declaration=str(value.get("certificate_declaration") or ""),
        lean_term=str(value.get("lean_term") or ""),
        capability_kind=str(value.get("capability_kind") or ""),
        component_role=str(value.get("component_role") or ""),
        source_declaration=str(value.get("source_declaration") or ""),
        target_declaration=str(value.get("target_declaration") or ""),
        source_fingerprint=str(value.get("source_fingerprint") or ""),
        target_fingerprint=str(value.get("target_fingerprint") or ""),
        source_node_id=str(value.get("source_node_id") or ""),
        target_node_id=str(value.get("target_node_id") or ""),
        source_display=str(value.get("source_display") or ""),
        target_display=str(value.get("target_display") or ""),
        provenance_declarations=tuple(value.get("provenance_declarations") or ()),
        discovery=str(value.get("discovery") or ""),
        registry_fingerprint=str(value.get("registry_fingerprint") or ""),
        source_evidence_id=(str(source_evidence_id) if source_evidence_id is not None else None),
        schema_version=str(value.get("schema_version") or ""),
    )


def core_reduction_catalog_from_dict(value: Mapping[str, Any]) -> CoreReductionCatalog:
    if value.get("schema_version") != CORE_REDUCTION_CATALOG_SCHEMA:
        raise CoreCapabilityCatalogError("unsupported Core reduction catalog schema")
    raw_entries = value.get("entries")
    if not isinstance(raw_entries, list):
        raise CoreCapabilityCatalogError("Core reduction entries must be a list")
    catalog = CoreReductionCatalog(
        registry_fingerprint=str(value.get("registry_fingerprint") or ""),
        entries=tuple(_parse_reduction_entry(entry) for entry in raw_entries),
        toolchain=str(value.get("toolchain") or ""),
        lake_manifest_sha256=str(value.get("lake_manifest_sha256") or ""),
    )
    _validate_reduction_catalog(catalog)
    supplied = value.get("catalog_id")
    if supplied is not None and supplied != catalog.catalog_id:
        raise CoreCapabilityCatalogError("Core reduction catalog ID mismatch")
    return catalog


def _load_json(path: Path) -> Mapping[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise CoreCapabilityCatalogError(f"cannot read Core catalog {path}: {error}") from error
    if not isinstance(value, dict):
        raise CoreCapabilityCatalogError("Core catalog root must be an object")
    return value


def _check_snapshot_metadata(
    *,
    registry_fingerprint: str,
    toolchain: str,
    lake_manifest_sha256: str,
    expected_registry_fingerprint: str | None,
    expected_toolchain: str | None,
    expected_lake_manifest_sha256: str | None,
) -> None:
    if expected_registry_fingerprint is not None and registry_fingerprint != expected_registry_fingerprint:
        raise CoreCapabilityCatalogError("Core catalog registry fingerprint mismatch")
    if expected_toolchain is not None and toolchain != expected_toolchain:
        raise CoreCapabilityCatalogError("Core catalog toolchain mismatch")
    if expected_lake_manifest_sha256 is not None and lake_manifest_sha256 != expected_lake_manifest_sha256:
        raise CoreCapabilityCatalogError("Core catalog lake-manifest fingerprint mismatch")


def load_core_native_evidence_catalog(
    path: Path,
    *,
    expected_registry_fingerprint: str | None = None,
    expected_toolchain: str | None = None,
    expected_lake_manifest_sha256: str | None = None,
) -> CoreNativeEvidenceCatalog:
    catalog = core_native_evidence_catalog_from_dict(_load_json(path))
    _check_snapshot_metadata(
        registry_fingerprint=catalog.registry_fingerprint,
        toolchain=catalog.toolchain,
        lake_manifest_sha256=catalog.lake_manifest_sha256,
        expected_registry_fingerprint=expected_registry_fingerprint,
        expected_toolchain=expected_toolchain,
        expected_lake_manifest_sha256=expected_lake_manifest_sha256,
    )
    return catalog


def load_core_reduction_catalog(
    path: Path,
    *,
    expected_registry_fingerprint: str | None = None,
    expected_toolchain: str | None = None,
    expected_lake_manifest_sha256: str | None = None,
) -> CoreReductionCatalog:
    catalog = core_reduction_catalog_from_dict(_load_json(path))
    _check_snapshot_metadata(
        registry_fingerprint=catalog.registry_fingerprint,
        toolchain=catalog.toolchain,
        lake_manifest_sha256=catalog.lake_manifest_sha256,
        expected_registry_fingerprint=expected_registry_fingerprint,
        expected_toolchain=expected_toolchain,
        expected_lake_manifest_sha256=expected_lake_manifest_sha256,
    )
    return catalog


def native_evidence_search_result(entry: CoreNativeEvidenceEntry) -> dict[str, Any]:
    return entry.to_dict()


def core_reduction_search_result(entry: CoreReductionEntry) -> dict[str, Any]:
    return entry.to_dict()


def search_native_evidence(
    catalog: CoreNativeEvidenceCatalog,
    *,
    evidence_kinds: Sequence[str] = (),
    endpoint_node_ids: Sequence[str] = (),
    terms: Sequence[str] = (),
    limit: int = 8,
) -> tuple[CoreNativeEvidenceEntry, ...]:
    if not 1 <= limit <= 8:
        raise CoreCapabilityCatalogError("native evidence search limit must be in 1..8")
    unknown = set(evidence_kinds) - EVIDENCE_KINDS
    if unknown:
        raise CoreCapabilityCatalogError(f"unsupported native evidence kinds: {sorted(unknown)}")
    nodes = set(endpoint_node_ids)
    lowered_terms = [term.strip().lower() for term in terms if term.strip()]
    ranked: list[tuple[int, str, CoreNativeEvidenceEntry]] = []
    for entry in catalog.entries:
        if evidence_kinds and entry.evidence_kind not in set(evidence_kinds):
            continue
        if nodes and entry.endpoint_node_id not in nodes:
            continue
        haystack = " ".join(
            (
                entry.endpoint_declaration,
                entry.evidence_declaration,
                entry.validation_source,
            )
        ).lower()
        if lowered_terms and not all(term in haystack for term in lowered_terms):
            continue
        score = (40 if nodes else 0) + (20 if evidence_kinds else 0) + len(lowered_terms)
        ranked.append((-score, entry.entry_id, entry))
    ranked.sort(key=lambda item: (item[0], item[1]))
    return tuple(item[2] for item in ranked[:limit])


def _term_tokens(value: str) -> set[str]:
    return {token.lower() for token in WORD_RE.findall(value)}


def _reduction_score(entry: CoreReductionEntry, search: TheoremSearch) -> int | None:
    if search.namespace_prefixes and not any(
        entry.namespace == prefix.rstrip(".")
        or entry.namespace.startswith(prefix.rstrip(".") + ".")
        for prefix in search.namespace_prefixes
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
            entry.certificate_declaration,
            entry.component_role,
            entry.source_declaration,
            entry.target_declaration,
        )
    )
    tokens = _term_tokens(haystack)
    matched = not search.terms or bool(
        search.namespace_prefixes
        or search.roles
        or search.source_node_ids
        or search.target_node_ids
    )
    score = 0
    lowered = haystack.lower()
    for term in search.terms:
        normalized = term.lower()
        if normalized in lowered:
            score += 12
            matched = True
        overlap = len(_term_tokens(term) & tokens)
        if overlap:
            score += overlap * 3
            matched = True
    if not matched:
        return None
    score += 30 * bool(search.source_node_ids)
    score += 30 * bool(search.target_node_ids)
    score += 4 * bool(search.roles)
    return score


def search_core_reductions(
    catalog: CoreReductionCatalog,
    searches: Sequence[TheoremSearch],
    *,
    maximum_results: int = 16,
) -> tuple[CoreReductionEntry, ...]:
    selected: dict[str, CoreReductionEntry] = {}
    for search in searches:
        ranked: list[tuple[int, str, CoreReductionEntry]] = []
        for entry in catalog.entries:
            score = _reduction_score(entry, search)
            if score is not None:
                ranked.append((-score, entry.entry_id, entry))
        ranked.sort(key=lambda item: (item[0], item[1]))
        for _, entry_id, entry in ranked[: search.limit]:
            selected.setdefault(entry_id, entry)
            if len(selected) >= maximum_results:
                break
        if len(selected) >= maximum_results:
            break
    return tuple(selected.values())


def build_core_capability_validation_source(
    *,
    evidence_catalog: CoreNativeEvidenceCatalog,
    reduction_catalog: CoreReductionCatalog,
    root_namespace: str = "Benchmark.Hardness.CoreGeneralizationCapabilityValidation",
    additional_modules: Sequence[str] = (),
) -> str:
    """Compile every exact evidence row and every derived Cook--Levin root once."""

    blocks: list[str] = []
    audited: list[str] = []
    for index, entry in enumerate(evidence_catalog.entries, start=1):
        declaration = f"evidence{index}"
        blocks.append(
            f"noncomputable def {declaration} : {entry.capability_head} "
            f"{entry.endpoint_declaration} :=\n  {entry.lean_term}\n\n"
        )
        audited.append(f"{root_namespace}.{declaration}")
    cook_roots = [entry for entry in reduction_catalog.entries if entry.is_cook_levin_root]
    for index, entry in enumerate(cook_roots, start=1):
        declaration = f"cookLevinRoot{index}"
        blocks.append(
            "noncomputable def "
            f"{declaration} : ComplexityReduction.Certificate.CertifiedReduction "
            f"{entry.source_declaration} {entry.target_declaration} :=\n"
            f"  {entry.lean_term}\n\n"
        )
        audited.append(f"{root_namespace}.{declaration}")
    if not audited:
        raise CoreCapabilityCatalogError("Core capability validation has no declarations")
    audit = ",\n  ".join(audited)
    additional_imports = "".join(
        f"import {validate_module_name(module)}\n"
        for module in dict.fromkeys(additional_modules)
    )
    return f"""import ComplexityReduction.Agent.Hardness.Runtime
{additional_imports}

namespace {root_namespace}

noncomputable section

{''.join(blocks)}end

end {root_namespace}

assert_standard_axioms
  {audit}
"""
