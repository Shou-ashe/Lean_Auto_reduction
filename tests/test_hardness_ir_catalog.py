import pytest

from agent.hardness.catalog import build_all_catalogs, build_typed_catalog
from agent.hardness.models import TypedInventoryEntry


def entry(
    declaration: str,
    *,
    role: str,
    kind: str = "certified_reduction",
    final: bool = False,
    fingerprint: str = "registry-1",
) -> TypedInventoryEntry:
    return TypedInventoryEntry(
        declaration=declaration,
        capability_kind=kind,
        component_role=role,
        source_fingerprint=f"source:{declaration}",
        target_fingerprint=f"target:{declaration}",
        is_final_facade=final,
        discovery="registered",
        registry_fingerprint=fingerprint,
    )


def test_catalog_views_are_stable_fail_closed_filters() -> None:
    entries = (
        entry("Edge.direct", role="unannotated"),
        entry("Edge.ingress", role="ingress"),
        entry("Edge.shared", role="sharedGadget"),
        entry("Edge.final", role="finalComposition", final=True),
        entry(
            "Edge.presentation",
            role="egress",
            kind="certified_presentation_change",
        ),
    )
    catalogs = build_all_catalogs(entries, registry_fingerprint="registry-1")

    assert {entry.declaration for entry in catalogs["full"].entries} == {
        "Edge.direct",
        "Edge.ingress",
        "Edge.shared",
        "Edge.final",
        "Edge.presentation",
    }
    assert {entry.declaration for entry in catalogs["flat_api"].entries} == {
        "Edge.direct",
        "Edge.final",
    }
    assert {entry.declaration for entry in catalogs["ir_components"].entries} == {
        "Edge.direct",
        "Edge.ingress",
        "Edge.shared",
    }
    assert {entry.declaration for entry in catalogs["component_catalog"].entries} == {
        "Edge.direct",
        "Edge.ingress",
        "Edge.shared",
        "Edge.final",
    }
    assert catalogs["flat_api"].semantic_atomic_interface_count == 1
    assert catalogs["ir_components"].semantic_atomic_interface_count == 3
    assert catalogs["component_catalog"].semantic_atomic_interface_count == 3


def test_ir_catalog_excludes_typed_entries_the_current_emitter_cannot_select() -> None:
    entries = (
        entry("Edge.reduction", role="sharedGadget"),
        entry("Edge.equiv", role="unannotated", kind="certified_equiv"),
        entry(
            "Edge.presentation",
            role="egress",
            kind="certified_presentation_change",
        ),
    )

    catalog = build_typed_catalog(
        entries, registry_fingerprint="registry-1", mode="ir_components"
    )

    assert [item.declaration for item in catalog.entries] == ["Edge.reduction"]


def test_catalog_deduplicates_rows_and_has_order_independent_id() -> None:
    first = entry("Edge.one", role="ingress")
    second = entry("Edge.two", role="sharedGadget")
    forward = build_typed_catalog(
        (first, second, first), registry_fingerprint="registry-1", mode="full"
    )
    reverse = build_typed_catalog(
        (second, first), registry_fingerprint="registry-1", mode="full"
    )
    assert len(forward.entries) == 2
    assert forward.catalog_id == reverse.catalog_id


def test_catalog_rejects_inventory_from_another_registry_snapshot() -> None:
    with pytest.raises(ValueError, match="registry fingerprint"):
        build_typed_catalog(
            (entry("Edge.foreign", role="ingress", fingerprint="registry-2"),),
            registry_fingerprint="registry-1",
            mode="ir_components",
        )


def test_catalog_rejects_inconsistent_final_facade_metadata() -> None:
    inconsistent = entry("Edge.fakeFinal", role="finalComposition", final=False)
    with pytest.raises(ValueError, match="inconsistent final-facade"):
        build_typed_catalog(
            (inconsistent,), registry_fingerprint="registry-1", mode="full"
        )
