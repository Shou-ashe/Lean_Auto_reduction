import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SNAPSHOT = ROOT / "Reports" / "IR_CATALOG_SNAPSHOT.json"


def test_snapshot_contains_compiled_endpoint_topology_for_reference_ir_paths() -> None:
    snapshot = json.loads(SNAPSHOT.read_text(encoding="utf-8"))

    assert snapshot["schema_version"] == "hardness_ir_catalog_snapshot_v2"
    assert snapshot["endpoint_topology"] == {
        "producer": "lean_whnf_endpoint_hash",
        "registry_fingerprint": snapshot["registry_fingerprint"],
        "schema_version": "hardness_endpoint_topology_v1",
    }
    assert snapshot["inventory_entry_count"] == len(snapshot["inventory_entries"])
    assert all(
        entry["source_node_id"] and entry["target_node_id"]
        for entry in snapshot["inventory_entries"]
    )

    entries = {
        entry["declaration"]: entry for entry in snapshot["inventory_entries"]
    }
    cases = {case["id"]: case for case in snapshot["cases"]}
    reference_paths = {
        "graph-to-role-graph-ir": [
            "ComplexityReduction.Domain.GraphToGraphIRAdapter.sourceAdapter",
            "ComplexityReduction.Domain.GraphIRRoleAssignmentGadget.sharedGadget",
        ],
        "structured-cnf-to-csp-ir": [
            "ComplexityReduction.Domain.CNFToThreeSATStandardTM.sharedGadget",
            "ComplexityReduction.Domain.ThreeSATToThreeSATLikeStandardTM.sharedGadget",
        ],
        "two-cnf-to-csp-ir": [
            "ComplexityReduction.Routes.ClauseToCSP.IngressAdapters.twoCNFIngress",
            "ComplexityReduction.Domain.ThreeSATToThreeSATLikeStandardTM.sharedGadget",
        ],
        "three-sat-to-csp-ir": [
            "ComplexityReduction.Domain.ThreeSATToThreeSATLikeStandardTM.sharedGadget",
        ],
        "exact-cover-to-eon-ir": [
            "ComplexityReduction.Domain.SetSystemToIncidenceAdapter.sourceAdapter",
            "ComplexityReduction.Domain.IncidenceToExactlyOneNeighborGadget.sharedGadget",
        ],
        "modified-exact-cover-to-eon-ir": [
            "ComplexityReduction.Domain.ModifiedExactCoverInput.modifiedSourceAdapter",
            "ComplexityReduction.Domain.IncidenceToExactlyOneNeighborGadget.sharedGadget",
        ],
    }

    for case_id, declarations in reference_paths.items():
        path = [entries[declaration] for declaration in declarations]
        assert path[0]["source_node_id"] == cases[case_id]["source_node_id"]
        assert path[-1]["target_node_id"] == cases[case_id]["target_node_id"]
        assert all(
            left["target_node_id"] == right["source_node_id"]
            for left, right in zip(path, path[1:])
        )
