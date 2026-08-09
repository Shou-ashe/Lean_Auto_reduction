import pytest

from agent.hardness.models import TypedCatalog, TypedInventoryEntry
from agent.hardness.retrieval import (
    MAX_RESULTS_PER_SEARCH,
    RetrievalValidationError,
    analyze_retrieved_connectivity,
    build_library_architecture,
    build_navigation_hints,
    inspect_library_architecture,
    parse_architecture_queries,
    parse_theorem_searches,
    search_catalog,
)


def entry(declaration: str, *, role: str, source: str, target: str):
    return TypedInventoryEntry(
        declaration=declaration,
        capability_kind="certified_reduction",
        component_role=role,
        source_fingerprint=f"lean:{source}",
        target_fingerprint=f"lean:{target}",
        is_final_facade=role == "finalComposition",
        discovery="registered",
        registry_fingerprint="registry-1",
        source_display=source,
        target_display=target,
        source_node_id=f"node:{source}",
        target_node_id=f"node:{target}",
    )


def catalog() -> TypedCatalog:
    return TypedCatalog(
        mode="ir_components",
        registry_fingerprint="registry-1",
        entries=(
            entry(
                "ComplexityReduction.Domain.CNFToThreeSAT.sharedGadget",
                role="sharedGadget",
                source="CNF",
                target="ThreeSAT",
            ),
            entry(
                "ComplexityReduction.Domain.ThreeSATToCSP.sharedGadget",
                role="sharedGadget",
                source="ThreeSAT",
                target="CSP",
            ),
            entry(
                "ComplexityReduction.Domain.GraphToGraphIR.sourceAdapter",
                role="ingress",
                source="Graph",
                target="GraphIR",
            ),
        ),
    )


def test_default_architecture_is_a_compact_overview_without_namespace_dump() -> None:
    architecture = build_library_architecture(catalog())

    assert architecture["contains_declaration_names"] is False
    assert architecture["full_namespace_topology_included"] is False
    assert "namespaces" not in architecture
    assert architecture["catalog_summary"] == {
        "namespace_count": 3,
        "reduction_declaration_count": 3,
        "role_counts": {"ingress": 1, "sharedGadget": 2},
    }


def test_model_search_selects_only_requested_namespaces() -> None:
    searches = parse_theorem_searches(
        {
            "searches": [
                {
                    "namespace_prefixes": [
                        "ComplexityReduction.Domain.CNFToThreeSAT",
                        "ComplexityReduction.Domain.ThreeSATToCSP",
                    ],
                    "terms": ["CNF", "CSP"],
                }
            ]
        }
    )

    results = search_catalog(catalog(), searches)

    assert [entry.declaration for entry in results] == [
        "ComplexityReduction.Domain.CNFToThreeSAT.sharedGadget",
        "ComplexityReduction.Domain.ThreeSATToCSP.sharedGadget",
    ]


def test_search_is_bounded_and_rejects_an_empty_request() -> None:
    with pytest.raises(RetrievalValidationError, match="must include"):
        parse_theorem_searches({"searches": [{}]})

    searches = parse_theorem_searches(
        {"searches": [{"terms": ["CSP"], "limit": 100}]}
    )
    assert searches[0].limit == MAX_RESULTS_PER_SEARCH


def test_model_can_follow_compiled_endpoint_nodes_without_a_catalog_dump() -> None:
    selected_catalog = catalog()
    first_search = parse_theorem_searches(
        {"searches": [{"source_node_ids": ["node:CNF"]}]}
    )
    first_results = search_catalog(selected_catalog, first_search)

    assert [item.declaration for item in first_results] == [
        "ComplexityReduction.Domain.CNFToThreeSAT.sharedGadget"
    ]

    second_search = parse_theorem_searches(
        {
            "searches": [
                {"source_node_ids": [first_results[0].target_node_id]}
            ]
        }
    )
    second_results = search_catalog(selected_catalog, second_search)
    connectivity = analyze_retrieved_connectivity(
        (*first_results, *second_results),
        source_node_id="node:CNF",
        target_node_id="node:CSP",
    )

    assert connectivity["complete_paths"] == [
        [
            "ComplexityReduction.Domain.CNFToThreeSAT.sharedGadget",
            "ComplexityReduction.Domain.ThreeSATToCSP.sharedGadget",
        ]
    ]
    assert connectivity["next_search_hint"] is None


def test_navigation_hints_expose_directions_but_not_theorem_names() -> None:
    hints = build_navigation_hints(
        catalog(),
        frontier_node_ids=("node:CNF",),
        target_node_id="node:CSP",
    )

    assert hints["contains_declaration_names"] is False
    assert hints["outgoing_from_frontier"] == [
        {
            "namespace": "ComplexityReduction.Domain.CNFToThreeSAT",
            "source_node_id": "node:CNF",
            "target_node_id": "node:ThreeSAT",
            "roles": ["sharedGadget"],
            "declaration_count": 1,
            "transformation_hint": {
                "source_label": "CNF",
                "target_label": "ThreeSAT",
            },
        }
    ]
    assert hints["incoming_to_request_target"] == [
        {
            "namespace": "ComplexityReduction.Domain.ThreeSATToCSP",
            "source_node_id": "node:ThreeSAT",
            "target_node_id": "node:CSP",
            "roles": ["sharedGadget"],
            "declaration_count": 1,
            "transformation_hint": {
                "source_label": "ThreeSAT",
                "target_label": "CSP",
            },
        }
    ]
    assert "ComplexityReduction.Domain.CNFToThreeSAT.sharedGadget" not in str(hints)


def test_model_can_inspect_selected_namespace_transitions_on_demand() -> None:
    queries = parse_architecture_queries(
        {
            "queries": [
                {
                    "terms": ["CNF", "CSP"],
                    "namespace_prefixes": ["ComplexityReduction.Domain"],
                    "limit": 8,
                }
            ]
        }
    )

    results = inspect_library_architecture(catalog(), queries)

    assert [row["namespace"] for row in results] == [
        "ComplexityReduction.Domain.CNFToThreeSAT",
        "ComplexityReduction.Domain.ThreeSATToCSP",
    ]
    assert all("declaration" not in row for row in results)
    assert "ComplexityReduction.Domain.CNFToThreeSAT.sharedGadget" not in str(results)


def test_text_terms_do_not_hide_exact_structural_matches() -> None:
    searches = parse_theorem_searches(
        {
            "searches": [
                {
                    "source_node_ids": ["node:CNF"],
                    "terms": ["word-that-does-not-occur"],
                }
            ]
        }
    )

    results = search_catalog(catalog(), searches)

    assert [item.declaration for item in results] == [
        "ComplexityReduction.Domain.CNFToThreeSAT.sharedGadget"
    ]
