"""Derive bounded native-hardness targets from Lean-validated paths.

The derivation is observational until its generated batch is elaborated by
Lean.  Every atom comes from the fingerprint-matched connection catalog, the
hub proof comes from exact native completeness, and the only constructor is
``NativeTMNPHard.ofCompleteAlongPath``.  No problem name or benchmark family
participates in path selection.
"""

from __future__ import annotations

from collections import defaultdict, deque
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from typing import Any

from .connection_catalog import ConnectionCatalog, ConnectionCatalogEntry
from .hardness_target_catalog import (
    EXACT_COMPLETENESS_EVIDENCE_KINDS,
    FULL_DECLARATION_RE,
    NATIVE_NP_HARD_POLICY,
    HardnessTargetCatalog,
    HardnessTargetCatalogEntry,
    HardnessTargetEvidence,
    declaration_namespace,
    hardness_target_catalog_from_dict,
)
from .lean_runner import validate_module_name
from .problem_catalog import ProblemCatalog, ProblemCatalogEntry


TRANSPORTED_HARDNESS_CONSTRUCTOR = (
    "ComplexityReduction.Certificate.NativeTMNPHard.ofCompleteAlongPath"
)
CERTIFIED_PATH_STEP = "ComplexityReduction.Certificate.CertifiedPath.step"
CERTIFIED_PATH_CONS = "ComplexityReduction.Certificate.CertifiedPath.cons"
TRANSPORT_VALIDATION_SOURCE = "lean_registry_path_composition"

ROLE_ORDER = {
    "ingress": 0,
    "sharedGadget": 1,
    "egress": 2,
    "unannotated": 3,
    "finalComposition": 4,
}


@dataclass(frozen=True)
class TransportedHardnessPath:
    evidence_id: str
    hub_declaration: str
    hub_node_id: str
    target_declaration: str
    target_node_id: str
    reduction_declarations: tuple[str, ...]
    connection_entry_ids: tuple[str, ...]

    @property
    def atom_count(self) -> int:
        return len(self.reduction_declarations)

    def to_dict(self) -> dict[str, Any]:
        return {
            "evidence_id": self.evidence_id,
            "hub_declaration": self.hub_declaration,
            "hub_node_id": self.hub_node_id,
            "target_declaration": self.target_declaration,
            "target_node_id": self.target_node_id,
            "atom_count": self.atom_count,
            "reduction_declarations": list(self.reduction_declarations),
            "connection_entry_ids": list(self.connection_entry_ids),
        }


@dataclass(frozen=True)
class TransportedHardnessCatalogBuild:
    catalog: HardnessTargetCatalog
    paths: tuple[TransportedHardnessPath, ...]

    def to_summary(self) -> dict[str, Any]:
        atom_counts = [path.atom_count for path in self.paths]
        return {
            "transported_evidence_count": len(self.paths),
            "transported_target_count": len(
                {path.target_node_id for path in self.paths}
            ),
            "minimum_transport_atoms": min(atom_counts) if atom_counts else None,
            "maximum_transport_atoms": max(atom_counts) if atom_counts else None,
            "paths": [path.to_dict() for path in self.paths],
        }


def _representatives_by_node(
    problem_catalog: ProblemCatalog,
) -> dict[str, ProblemCatalogEntry]:
    grouped: dict[str, list[ProblemCatalogEntry]] = defaultdict(list)
    for entry in problem_catalog.entries:
        grouped[entry.problem_node_id].append(entry)
    return {
        node_id: min(
            entries,
            key=lambda entry: (
                not entry.registered,
                len(entry.declaration),
                entry.declaration,
            ),
        )
        for node_id, entries in grouped.items()
    }


def _edge_key(entry: ConnectionCatalogEntry) -> tuple[Any, ...]:
    return (
        ROLE_ORDER.get(entry.component_role, ROLE_ORDER["unannotated"]),
        entry.target_node_id,
        entry.certificate_declaration,
        entry.relation,
        entry.entry_id,
    )


def _canonical_shortest_paths(
    connection_catalog: ConnectionCatalog,
    *,
    source_node_id: str,
    maximum_atoms: int,
) -> Mapping[str, tuple[ConnectionCatalogEntry, ...]]:
    adjacency: dict[str, list[ConnectionCatalogEntry]] = defaultdict(list)
    for entry in connection_catalog.entries:
        if entry.source_node_id == entry.target_node_id:
            continue
        adjacency[entry.source_node_id].append(entry)
    for entries in adjacency.values():
        entries.sort(key=_edge_key)

    selected: dict[str, tuple[ConnectionCatalogEntry, ...]] = {}
    queue: deque[
        tuple[str, tuple[ConnectionCatalogEntry, ...], frozenset[str]]
    ] = deque([(source_node_id, (), frozenset({source_node_id}))])
    while queue:
        node_id, path, visited = queue.popleft()
        if len(path) >= maximum_atoms:
            continue
        for edge in adjacency.get(node_id, ()):
            target_node_id = edge.target_node_id
            if target_node_id in visited:
                continue
            next_path = (*path, edge)
            if target_node_id not in selected:
                selected[target_node_id] = next_path
                queue.append(
                    (target_node_id, next_path, visited | {target_node_id})
                )
    return selected


def _render_certified_path(path: Sequence[ConnectionCatalogEntry]) -> str:
    if not path:
        raise ValueError("transported hardness requires a non-empty forward path")
    rendered = f"{CERTIFIED_PATH_STEP} ({path[0].lean_term})"
    for edge in path[1:]:
        rendered = f"{CERTIFIED_PATH_CONS} ({rendered}) ({edge.lean_term})"
    return rendered


def _ordered_declarations(term: str) -> tuple[str, ...]:
    return tuple(dict.fromkeys(FULL_DECLARATION_RE.findall(term)))


def _transported_evidence(
    *,
    hub_evidence: HardnessTargetEvidence,
    target_declaration: str,
    target_node_id: str,
    path: Sequence[ConnectionCatalogEntry],
) -> HardnessTargetEvidence:
    path_term = _render_certified_path(path)
    evidence_term = (
        f"{TRANSPORTED_HARDNESS_CONSTRUCTOR} "
        f"({hub_evidence.evidence_lean_term}) ({path_term})"
    )
    return HardnessTargetEvidence(
        target_declaration=target_declaration,
        target_node_id=target_node_id,
        evidence_kind="transported_native_hardness",
        evidence_declaration=TRANSPORTED_HARDNESS_CONSTRUCTOR,
        evidence_lean_term=evidence_term,
        membership_lean_term="",
        satisfied_policies=(NATIVE_NP_HARD_POLICY,),
        validation_source=TRANSPORT_VALIDATION_SOURCE,
        provenance_declarations=_ordered_declarations(evidence_term),
        registry_fingerprint=hub_evidence.registry_fingerprint,
    )


def build_transported_hardness_catalog(
    *,
    problem_catalog: ProblemCatalog,
    connection_catalog: ConnectionCatalog,
    native_target_catalog: HardnessTargetCatalog,
    maximum_transport_atoms: int = 6,
) -> TransportedHardnessCatalogBuild:
    """Augment exact native targets with bounded, canonical path transports."""

    if not 1 <= maximum_transport_atoms <= 8:
        raise ValueError("maximum_transport_atoms must be in 1..8")
    fingerprints = {
        problem_catalog.registry_fingerprint,
        connection_catalog.registry_fingerprint,
        native_target_catalog.registry_fingerprint,
    }
    if len(fingerprints) != 1:
        raise ValueError("transported hardness catalogs have different fingerprints")
    if (
        problem_catalog.toolchain != connection_catalog.toolchain
        or problem_catalog.toolchain != native_target_catalog.toolchain
        or problem_catalog.lake_manifest_sha256
        != connection_catalog.lake_manifest_sha256
        or problem_catalog.lake_manifest_sha256
        != native_target_catalog.lake_manifest_sha256
    ):
        raise ValueError("transported hardness catalogs have stale build metadata")

    representatives = _representatives_by_node(problem_catalog)
    entries_by_node: dict[str, HardnessTargetCatalogEntry] = {
        entry.target_node_id: entry for entry in native_target_catalog.entries
    }
    path_records: list[TransportedHardnessPath] = []

    hubs = [
        (entry, evidence)
        for entry in native_target_catalog.entries
        for evidence in entry.evidences
        if evidence.evidence_kind in EXACT_COMPLETENESS_EVIDENCE_KINDS
    ]
    for hub_entry, hub_evidence in sorted(
        hubs,
        key=lambda item: (
            item[0].target_declaration,
            item[1].evidence_declaration,
        ),
    ):
        paths = _canonical_shortest_paths(
            connection_catalog,
            source_node_id=hub_entry.target_node_id,
            maximum_atoms=maximum_transport_atoms,
        )
        for target_node_id, path in sorted(
            paths.items(),
            key=lambda item: (len(item[1]), item[0]),
        ):
            representative = representatives.get(target_node_id)
            existing = entries_by_node.get(target_node_id)
            if existing is None and representative is None:
                continue
            target_declaration = (
                existing.target_declaration
                if existing is not None
                else representative.declaration
            )
            evidence = _transported_evidence(
                hub_evidence=hub_evidence,
                target_declaration=target_declaration,
                target_node_id=target_node_id,
                path=path,
            )
            if existing is None:
                assert representative is not None
                updated = HardnessTargetCatalogEntry(
                    target_declaration=target_declaration,
                    target_display=representative.display,
                    target_node_id=target_node_id,
                    target_namespace=declaration_namespace(target_declaration),
                    registry_fingerprint=problem_catalog.registry_fingerprint,
                    evidences=(evidence,),
                )
            else:
                if evidence.evidence_id in {
                    item.evidence_id for item in existing.evidences
                }:
                    continue
                updated = HardnessTargetCatalogEntry(
                    target_declaration=existing.target_declaration,
                    target_display=existing.target_display,
                    target_node_id=existing.target_node_id,
                    target_namespace=existing.target_namespace,
                    registry_fingerprint=existing.registry_fingerprint,
                    evidences=(*existing.evidences, evidence),
                )
            entries_by_node[target_node_id] = updated
            path_records.append(
                TransportedHardnessPath(
                    evidence_id=evidence.evidence_id,
                    hub_declaration=hub_entry.target_declaration,
                    hub_node_id=hub_entry.target_node_id,
                    target_declaration=target_declaration,
                    target_node_id=target_node_id,
                    reduction_declarations=tuple(
                        edge.certificate_declaration for edge in path
                    ),
                    connection_entry_ids=tuple(edge.entry_id for edge in path),
                )
            )

    raw_catalog = HardnessTargetCatalog(
        registry_fingerprint=native_target_catalog.registry_fingerprint,
        entries=tuple(entries_by_node.values()),
        toolchain=native_target_catalog.toolchain,
        lake_manifest_sha256=native_target_catalog.lake_manifest_sha256,
    )
    catalog = hardness_target_catalog_from_dict(
        raw_catalog.to_dict(include_catalog_id=False)
    )
    return TransportedHardnessCatalogBuild(
        catalog=catalog,
        paths=tuple(
            sorted(
                path_records,
                key=lambda item: (
                    item.atom_count,
                    item.target_declaration,
                    item.evidence_id,
                ),
            )
        ),
    )


def build_transported_hardness_validation_source(
    build: TransportedHardnessCatalogBuild,
    *,
    root_namespace: str = "Benchmark.Hardness.TransportedHardnessCatalogValidation",
    additional_modules: Sequence[str] = (),
) -> str:
    """Build one Lean batch that validates every derived target and axiom set."""

    evidences = {
        evidence.evidence_id: (entry, evidence)
        for entry in build.catalog.entries
        for evidence in entry.evidences
        if evidence.evidence_kind == "transported_native_hardness"
    }
    if not build.paths:
        raise ValueError("transported hardness validation requires derived evidence")
    blocks: list[str] = []
    audited: list[str] = []
    for index, path in enumerate(build.paths, start=1):
        entry, evidence = evidences[path.evidence_id]
        declaration = f"evidence{index}"
        blocks.append(
            f"""noncomputable def {declaration} :
    ComplexityReduction.Certificate.NativeTMNPHard {entry.target_declaration} :=
  {evidence.evidence_lean_term}
"""
        )
        audited.append(f"{root_namespace}.{declaration}")
    audit = ",\n  ".join(audited)
    additional_imports = "".join(
        f"import {validate_module_name(module)}\n"
        for module in dict.fromkeys(additional_modules)
    )
    return f"""import ComplexityReduction.Agent.Hardness.Runtime
{additional_imports}

namespace {root_namespace}

noncomputable section

{''.join(blocks)}
end

end {root_namespace}

assert_standard_axioms
  {audit}
"""
