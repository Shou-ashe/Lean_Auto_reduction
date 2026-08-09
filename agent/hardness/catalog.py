"""Deterministic observational catalog views over Lean-validated inventory entries."""

from __future__ import annotations

from collections.abc import Iterable

from .models import TypedCatalog, TypedInventoryEntry


FULL_CATALOG = "full"
FLAT_API_CATALOG = "flat_api"
IR_COMPONENTS_CATALOG = "ir_components"
COMPONENT_CATALOG = "component_catalog"
CATALOG_MODES = {
    FULL_CATALOG,
    FLAT_API_CATALOG,
    IR_COMPONENTS_CATALOG,
    COMPONENT_CATALOG,
}


def _visible(entry: TypedInventoryEntry, *, mode: str) -> bool:
    if mode == FULL_CATALOG:
        return True
    if mode == FLAT_API_CATALOG:
        return entry.capability_kind == "certified_reduction" and (
            entry.is_final_facade or entry.component_role == "unannotated"
        )
    if mode == IR_COMPONENTS_CATALOG:
        # The current closed resolver and Artifact emitter can select only
        # CertifiedReduction declarations.  Equivalence and presentation-change
        # observations remain visible in the full inventory, but must not inflate
        # the Agent-facing IR interface count until projection support exists.
        return entry.capability_kind == "certified_reduction" and not entry.is_final_facade
    if mode == COMPONENT_CATALOG:
        # Stage F compares the flat API against a component-enabled superset.
        # Keeping every flat certified reduction queryable is essential: the
        # component treatment may add choices, but must never win by hiding a
        # final facade that the flat treatment could use.
        return entry.capability_kind == "certified_reduction"
    raise ValueError(f"unsupported typed catalog mode: {mode}")


def build_typed_catalog(
    entries: Iterable[TypedInventoryEntry],
    *,
    registry_fingerprint: str,
    mode: str,
) -> TypedCatalog:
    """Build a stable filtered view without upgrading observational metadata.

    Every retained entry must have been emitted by the same fingerprint-bound
    Lean probe.  Duplicate rows are collapsed by their content-addressed entry
    ID so repeated imports cannot inflate interface metrics.
    """

    if mode not in CATALOG_MODES:
        raise ValueError(f"unsupported typed catalog mode: {mode}")
    if not registry_fingerprint:
        raise ValueError("typed catalog requires a non-empty registry fingerprint")

    by_id: dict[str, TypedInventoryEntry] = {}
    for entry in entries:
        if entry.registry_fingerprint != registry_fingerprint:
            raise ValueError(
                "typed inventory entry does not match the selected registry fingerprint"
            )
        if entry.is_final_facade != (entry.component_role == "finalComposition"):
            raise ValueError(
                "typed inventory entry has inconsistent final-facade role metadata"
            )
        if entry.is_final_facade and entry.capability_kind != "certified_reduction":
            raise ValueError("only a certified reduction can be a final facade")
        if _visible(entry, mode=mode):
            by_id.setdefault(entry.entry_id, entry)

    selected = tuple(
        sorted(
            by_id.values(),
            key=lambda entry: (
                entry.declaration,
                entry.capability_kind,
                entry.component_role,
                entry.source_fingerprint,
                entry.target_fingerprint,
                entry.entry_id,
            ),
        )
    )
    return TypedCatalog(
        mode=mode,
        registry_fingerprint=registry_fingerprint,
        entries=selected,
    )


def build_all_catalogs(
    entries: Iterable[TypedInventoryEntry], *, registry_fingerprint: str
) -> dict[str, TypedCatalog]:
    materialized = tuple(entries)
    return {
        mode: build_typed_catalog(
            materialized,
            registry_fingerprint=registry_fingerprint,
            mode=mode,
        )
        for mode in (
            FULL_CATALOG,
            FLAT_API_CATALOG,
            IR_COMPONENTS_CATALOG,
            COMPONENT_CATALOG,
        )
    }
