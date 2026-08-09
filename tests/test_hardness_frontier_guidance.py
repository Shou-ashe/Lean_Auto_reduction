from copy import deepcopy

from agent.hardness.frontier_guidance import (
    FRONTIER_GUIDANCE_MODE,
    FRONTIER_GUIDANCE_SCHEMA,
    MAX_FRONTIER_GUIDANCE_NODES,
    build_frontier_guidance,
    frontier_guidance_errors,
    frontier_prompt_metrics,
)
from agent.hardness.models import TypedInventoryEntry


def edge(declaration: str, source: str, target: str) -> TypedInventoryEntry:
    return TypedInventoryEntry(
        declaration=declaration,
        capability_kind="certified_reduction",
        component_role="sharedGadget",
        source_fingerprint=f"lean:{source}",
        target_fingerprint=f"lean:{target}",
        is_final_facade=False,
        discovery="registered",
        registry_fingerprint="lean:frontier",
        source_display=source,
        target_display=target,
        source_node_id=source,
        target_node_id=target,
    )


def known_hardness_payload(guidance: dict) -> dict:
    return {
        "request": {"objective": "reduce_to_known_hardness"},
        "retrieved": {
            "problems": [{"problem_node_id": "node:a"}],
            "connections": [],
            "hardness_targets": [],
            "reductions": [
                {
                    "declaration": "ComplexityReduction.Routes.AB.edge",
                    "role": "sharedGadget",
                    "source_node_id": "node:a",
                    "target_node_id": "node:b",
                }
            ],
        },
        "frontier_guidance": guidance,
    }


def test_frontier_guidance_uses_retrieved_endpoints_without_route_selection() -> None:
    first = edge("ComplexityReduction.Routes.AB.edge", "node:a", "node:b")
    second = edge("ComplexityReduction.Routes.BC.edge", "node:b", "node:c")

    guidance = build_frontier_guidance(
        retrieved_entries=(first,),
        catalog_entries=(first, second),
        start_atom_counts={"node:a": 0},
        source_only_queried_node_ids={"node:a"},
        maximum_route_atoms=5,
    )

    assert guidance["schema_version"] == FRONTIER_GUIDANCE_SCHEMA
    assert guidance["mode"] == FRONTIER_GUIDANCE_MODE
    assert guidance["frontier_nodes"] == [
        {
            "node_id": "node:b",
            "minimum_retrieved_atom_depth": 1,
            "outgoing_reduction_count": 1,
            "outgoing_endpoint_count": 1,
            "source_only_query_attempted": False,
        }
    ]
    assert guidance["suggested_searches"] == [
        {"source_node_ids": ["node:b"], "limit": 8}
    ]
    assert "ComplexityReduction.Routes.BC.edge" not in str(guidance)
    assert frontier_guidance_errors(known_hardness_payload(guidance)) == ()


def test_frontier_guidance_is_bounded_and_breadth_first() -> None:
    retrieved = tuple(
        edge(f"ComplexityReduction.Routes.A{index}.edge", "node:a", f"node:{index}")
        for index in range(12)
    )
    catalog = (*retrieved, *(
        edge(f"ComplexityReduction.Routes.Next{index}.edge", f"node:{index}", f"end:{index}")
        for index in range(12)
    ))

    guidance = build_frontier_guidance(
        retrieved_entries=retrieved,
        catalog_entries=catalog,
        start_atom_counts={"node:a": 0},
        source_only_queried_node_ids={"node:a"},
        maximum_route_atoms=5,
    )

    assert len(guidance["frontier_nodes"]) == MAX_FRONTIER_GUIDANCE_NODES
    assert len(guidance["suggested_searches"]) == 4
    assert guidance["frontier_truncated"] is True
    assert [row["node_id"] for row in guidance["frontier_nodes"]] == [
        "node:0",
        "node:1",
        "node:10",
        "node:11",
        "node:2",
        "node:3",
        "node:4",
        "node:5",
    ]


def test_frontier_prompt_audit_rejects_target_or_declaration_leaks() -> None:
    first = edge("ComplexityReduction.Routes.AB.edge", "node:a", "node:b")
    second = edge("ComplexityReduction.Routes.BC.edge", "node:b", "node:c")
    guidance = build_frontier_guidance(
        retrieved_entries=(first,),
        catalog_entries=(first, second),
        start_atom_counts={"node:a": 0},
        source_only_queried_node_ids={"node:a"},
        maximum_route_atoms=5,
    )
    payload = known_hardness_payload(guidance)
    leaked = deepcopy(payload)
    leaked["frontier_guidance"]["target_entry_id"] = "sha256:oracle"
    leaked["frontier_guidance"]["frontier_nodes"][0]["declaration"] = (
        "ComplexityReduction.Routes.BC.edge"
    )

    errors = frontier_guidance_errors(leaked)

    assert any("forbidden fields" in error for error in errors)


def test_known_np_prompt_must_not_receive_stage_j_guidance() -> None:
    payload = {
        "request": {"objective": "reduce_to_known_np"},
        "retrieved": {},
    }
    assert frontier_guidance_errors(payload) == ()
    payload["frontier_guidance"] = {}
    assert frontier_guidance_errors(payload) == (
        "known-NP prompt unexpectedly contains frontier_guidance",
    )


def test_frontier_prompt_metrics_include_terminal_mode() -> None:
    guidance = build_frontier_guidance(
        retrieved_entries=(),
        catalog_entries=(),
        start_atom_counts={},
        source_only_queried_node_ids=(),
        maximum_route_atoms=5,
    )
    payload = known_hardness_payload(guidance)
    payload["terminal_guidance"] = {
        "mode": "stop_now",
        "failure_code": "no_eligible_hardness_target",
    }

    metrics = frontier_prompt_metrics(payload)

    assert metrics["frontier_guidance_present"] is True
    assert metrics["frontier_guidance_errors"] == []
    assert metrics["terminal_guidance_mode"] == "stop_now"
    assert metrics["terminal_guidance_failure_code"] == (
        "no_eligible_hardness_target"
    )
