from __future__ import annotations

import json
from pathlib import Path

from agent.hardness.np_hard_existing_route_qualification import (
    HELDOUT_CASE_FIELDS,
    load_public_existing_route_heldout_suite,
)
from agent.hardness.np_hard_target_matrix import load_np_hard_target_matrix


ROOT = Path(__file__).resolve().parents[1]
MATRIX = ROOT / "Gate/NP_HARD_TARGET_MATRIX.json"
SUITE = ROOT / "Gate/Suites/np_hard_h_h_existing_route_inputs.json"


def test_h_h_matrix_has_22_canonical_existing_route_identities() -> None:
    matrix = load_np_hard_target_matrix(MATRIX)
    rows = [
        row
        for row in matrix["identities"]
        if row["has_forward_certified_reduction_route"] is True
    ]
    assert len(rows) == matrix["known_forward_route_identity_count"] == 22
    assert len({row["identity_id"] for row in rows}) == 22
    assert sum(row["member_count"] for row in rows) > len(rows)
    assert {row["shortest_forward_route_length"] for row in rows} == set(range(6))


def test_h_h_heldout_is_answer_free_public_and_covers_route_families() -> None:
    cases = load_public_existing_route_heldout_suite(SUITE)
    raw = json.loads(SUITE.read_text(encoding="utf-8"))
    assert len(cases) >= 12
    assert all(set(case) == HELDOUT_CASE_FIELDS for case in raw["cases"])
    assert all(case["module"].startswith("ComplexityReduction.") for case in cases)
    assert len({case["family"] for case in cases}) >= 5
    forbidden = {"expected", "status", "route", "gold", "task_class", "gap_nodes"}
    assert all(not forbidden.intersection(case) for case in raw["cases"])


def test_h_h_heldout_matches_distinct_canonical_matrix_identities() -> None:
    matrix = load_np_hard_target_matrix(MATRIX)
    by_problem = {row["canonical_declaration"]: row for row in matrix["identities"]}
    cases = load_public_existing_route_heldout_suite(SUITE)
    identity_ids = []
    lengths = set()
    for case in cases:
        row = by_problem[case["problem"]]
        assert row["canonical_module"] == case["module"]
        assert row["has_forward_route"] is True
        identity_ids.append(row["identity_id"])
        lengths.add(row["shortest_forward_route_length"])
    assert len(identity_ids) == len(set(identity_ids))
    assert lengths == set(range(6))

