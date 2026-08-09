import hashlib
import json
from pathlib import Path

from agent.hardness.benchmark import load_benchmark_manifest


ROOT = Path(__file__).resolve().parents[1]
HARDNESS = ROOT / "Benchmark" / "Hardness"


def test_migration_ledger_covers_all_legacy_cases_and_files() -> None:
    ledger = json.loads((HARDNESS / "MIGRATION_LEDGER.json").read_text())
    opencode = ledger["opencode_cases"]
    v2 = ledger["v2_hardness_cases"]
    assert len(opencode) == 107
    assert len(v2) == 3
    identifiers = [case["legacy_case_id"] for case in opencode + v2]
    assert len(identifiers) == len(set(identifiers)) == 110
    assert ledger["source_inventory"] == {
        "opencode_cases": 107,
        "opencode_hidden_targets": 68,
        "opencode_gold_proofs": 39,
        "v2_hardness_cases": 3,
        "total_legacy_cases": 110,
    }
    assert ledger["disposition_counts"] == {
        "migrated": 8,
        "split": 1,
        "deferred": 101,
        "deprecated": 0,
    }
    assert all(case["disposition"] in {"migrated", "split", "deferred", "deprecated"}
               for case in opencode + v2)


def test_legacy_quals_entries_map_to_their_exact_active_cases() -> None:
    ledger = json.loads((HARDNESS / "MIGRATION_LEDGER.json").read_text())
    rows = {case["legacy_case_id"]: case for case in ledger["opencode_cases"]}
    expected = {
        "fall2014_most_neighbors": "fall2014-most-neighbors",
        "fall2016_node_deletion_bipartite": "fall2016-node-deletion-bipartite",
        "spring2015_exactly_one_neighbor": "spring2015-exactly-one-neighbor",
        "uiuc_spring2020_two_disjoint_bounded_paths": (
            "uiuc2020-two-disjoint-bounded-paths"
        ),
        "uiuc_spring2022_seeing_set": "uiuc2022-seeing-set",
    }

    for legacy_id, active_id in expected.items():
        assert rows[legacy_id]["disposition"] == "migrated"
        assert rows[legacy_id]["current_case_ids"] == [active_id]


def test_legacy_archive_counts_match_ledger() -> None:
    legacy = HARDNESS / "Legacy" / "Opencode"
    assert len(list((legacy / "Samples").rglob("*.yaml"))) == 107
    assert len(list((legacy / "HiddenTargets").rglob("*.lean"))) == 68
    assert len(list((legacy / "GoldProofs").rglob("*.lean"))) == 39
    tracked_oracles = []
    for case in json.loads((HARDNESS / "MIGRATION_LEDGER.json").read_text())["opencode_cases"]:
        sample = HARDNESS / "Legacy" / case["legacy_sample_file"]
        assert sample.is_file()
        assert hashlib.sha256(sample.read_bytes()).hexdigest() == case["legacy_sample_sha256"]
        for oracle in case["legacy_oracles"]:
            oracle_file = HARDNESS / "Legacy" / oracle["path"]
            assert oracle_file.is_file()
            assert hashlib.sha256(oracle_file.read_bytes()).hexdigest() == oracle["sha256"]
            tracked_oracles.append(oracle["path"])
    assert len(tracked_oracles) == len(set(tracked_oracles)) == 107


def test_expected_inventory_matches_active_cases() -> None:
    manifest = load_benchmark_manifest(HARDNESS / "MANIFEST.json")
    expected_files = list((HARDNESS / "Expected").glob("*.json"))
    expected_ids = {
        json.loads(path.read_text())["case_id"]
        for path in expected_files
    }
    assert expected_ids == {case.id for case in manifest.cases}
    assert all(json.loads(path.read_text())["authoritative"] is False for path in expected_files)


def test_ir_baseline_is_observational_and_references_active_pairs() -> None:
    manifest = load_benchmark_manifest(HARDNESS / "MANIFEST.json")
    baseline = json.loads((HARDNESS / "IR_FEASIBILITY_BASELINE.json").read_text())
    assert baseline["authoritative"] is False
    assert baseline["inventory_scope"] == "registered_type_validated_certificate_edges"
    assert sum(baseline["typed_inventory"]["role_counts"].values()) == (
        baseline["typed_inventory"]["entry_count"]
    )
    active_pair_ids = {
        case.matched_pair_id for case in manifest.cases if case.matched_pair_id is not None
    }
    assert {
        pair["matched_pair_id"] for pair in baseline["matched_pairs"]
    } <= active_pair_ids


def test_ir_coverage_matrix_uses_only_active_matched_pairs() -> None:
    manifest = load_benchmark_manifest(HARDNESS / "MANIFEST.json")
    coverage = json.loads((HARDNESS / "IR_FEASIBILITY_COVERAGE.json").read_text())
    active_pair_ids = {
        case.matched_pair_id for case in manifest.cases if case.matched_pair_id is not None
    }

    assert coverage["authoritative"] is False
    assert coverage["scope"] == "existing_library_declarations_only"
    assert coverage["library_changes"] is False
    assert coverage["benchmark_local_reduction_facades"] == 0
    assert coverage["coverage"]["logical_matched_pair_count"] == 6
    assert coverage["coverage"]["execution_case_count"] == 12
    assert {
        pair["matched_pair_id"] for pair in coverage["matched_pairs"]
    } == active_pair_ids


def test_every_migrated_ledger_target_resolves_to_an_active_case() -> None:
    manifest = load_benchmark_manifest(HARDNESS / "MANIFEST.json")
    active_ids = {case.id for case in manifest.cases}
    ledger = json.loads((HARDNESS / "MIGRATION_LEDGER.json").read_text())
    for case in ledger["opencode_cases"] + ledger["v2_hardness_cases"]:
        assert set(case["current_case_ids"]) <= active_ids
        if case["disposition"] in {"migrated", "split"}:
            assert case["current_case_ids"]
