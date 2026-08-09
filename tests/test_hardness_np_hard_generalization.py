from __future__ import annotations

import copy
import json
from pathlib import Path

import pytest

from agent.hardness.np_hard_generalization import (
    load_np_hard_generalization_suite,
    load_np_hard_inventory,
)


ROOT = Path(__file__).resolve().parents[1]
HARDNESS = ROOT / "Benchmark" / "Hardness"
SUITE_PATH = HARDNESS / "Suites" / "np_hard_generalization.json"
INVENTORY_PATH = HARDNESS / "np_hard_inventory.json"


def _suite_payload() -> dict:
    return json.loads(SUITE_PATH.read_text(encoding="utf-8"))


def _write_suite(tmp_path: Path, payload: dict) -> Path:
    path = tmp_path / "suite.json"
    path.write_text(json.dumps(payload), encoding="utf-8")
    return path


def test_inventory_and_release_matrix_are_frozen() -> None:
    inventory = load_np_hard_inventory(INVENTORY_PATH, root=ROOT)
    suite = load_np_hard_generalization_suite(SUITE_PATH, root=ROOT)

    assert len(inventory.entries) == 11
    assert len(suite.cases) == 12
    assert {case.family for case in suite.cases} == {
        "sat-csp",
        "graph",
        "set-system",
        "numeric",
    }
    assert {
        kind: sum(case.kind == kind for case in suite.cases)
        for kind in ("existing_route", "model_authoring", "safety_negative")
    } == {"existing_route": 5, "model_authoring": 5, "safety_negative": 2}


def test_existing_route_matrix_has_zero_model_eligible_coverage() -> None:
    suite = load_np_hard_generalization_suite(SUITE_PATH, root=ROOT)
    existing = [case for case in suite.cases if case.kind == "existing_route"]

    assert sum(case.route["minimum_atoms"] >= 2 for case in existing) >= 2
    assert any(not case.membership_available for case in existing)
    assert all(case.initial_expected_status == "VERIFIED" for case in existing)


def test_authoring_matrix_freezes_all_three_task_classes() -> None:
    suite = load_np_hard_generalization_suite(SUITE_PATH, root=ROOT)
    authored = [case for case in suite.cases if case.kind == "model_authoring"]

    assert [case.authoring["task_class"] for case in authored].count(
        "semantic_proof"
    ) == 2
    assert [case.authoring["task_class"] for case in authored].count(
        "program_composition"
    ) == 2
    assert [case.authoring["task_class"] for case in authored].count(
        "program_synthesis"
    ) == 1
    assert sum(
        case.authoring["requires_nontrivial_semantics"] for case in authored
    ) >= 2
    assert any(case.authoring["requires_multi_gap"] for case in authored)
    assert all(
        case.initial_expected_failure_code == "no_forward_path_from_hardness_seed"
        for case in authored
    )


def test_gold_is_separate_and_never_imported_by_public_sources() -> None:
    suite = load_np_hard_generalization_suite(SUITE_PATH, root=ROOT)
    authored = [case for case in suite.cases if case.kind == "model_authoring"]

    assert len({case.authoring["gold_file"] for case in authored}) == 5
    for case in suite.cases:
        for source_name in case.public_source_files:
            source = ROOT / source_name
            text = source.read_text(encoding="utf-8")
            assert "Benchmark.Hardness.Gold" not in text
            assert "Benchmark.Hardness.Oracles" not in text


def test_suite_rejects_case_count_drift(tmp_path: Path) -> None:
    payload = _suite_payload()
    payload["cases"] = payload["cases"][:-1]
    with pytest.raises(ValueError, match="exactly 12"):
        load_np_hard_generalization_suite(_write_suite(tmp_path, payload))


def test_suite_rejects_authoring_class_drift(tmp_path: Path) -> None:
    payload = _suite_payload()
    mutated = copy.deepcopy(payload)
    for case in mutated["cases"]:
        if case["id"] == "nphg-author-graph-program-synthesis":
            case["authoring"]["task_class"] = "semantic_proof"
    with pytest.raises(ValueError, match="task matrix"):
        load_np_hard_generalization_suite(_write_suite(tmp_path, mutated))


def test_suite_rejects_non_topological_gap_dag(tmp_path: Path) -> None:
    payload = _suite_payload()
    for case in payload["cases"]:
        if case["id"] == "nphg-author-graph-program-synthesis":
            case["authoring"]["gap_nodes"][0]["depends_on"] = ["semantic-iff"]
    with pytest.raises(ValueError, match="not topologically ordered"):
        load_np_hard_generalization_suite(_write_suite(tmp_path, payload))


def test_suite_rejects_wrong_direction_contract(tmp_path: Path) -> None:
    payload = _suite_payload()
    payload["direction"] = "problem_to_hardness_seed"
    with pytest.raises(ValueError, match="wrong direction"):
        load_np_hard_generalization_suite(_write_suite(tmp_path, payload))


def test_inventory_rejects_forward_route_on_reverse_only_entry(tmp_path: Path) -> None:
    payload = json.loads(INVENTORY_PATH.read_text(encoding="utf-8"))
    for entry in payload["entries"]:
        if entry["known_reverse_only"]:
            entry["existing_forward_route"] = "single-edge"
    path = tmp_path / "inventory.json"
    path.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(ValueError, match="reverse-only"):
        load_np_hard_inventory(path)

