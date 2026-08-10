from __future__ import annotations

import copy
import hashlib
import json
from pathlib import Path

import pytest

from agent.hardness.np_hard_archive_audit import (
    EXPECTED_PDF_ONLY_CANDIDATE_COUNT,
    EXPECTED_PDF_ONLY_SOURCE_COUNT,
    EXPECTED_SELECTION_COUNT,
    EXPECTED_SELECTION_SPLIT_COUNTS,
    EXPECTED_SELECTION_STATUS_COUNTS,
    ProblemArchiveAuditError,
    load_archive_selection_bundle,
    validate_problem_archive_audit,
)


ROOT = Path(__file__).resolve().parents[1]
SELECTION = (
    ROOT / "Evaluation/np_hard_problem_archive_selection_v1.json"
)
AUDIT = ROOT / "Reports/PROBLEM_ARCHIVE_AUDIT.json"


def test_frozen_archive_selection_has_24_edges_and_pdf_only_reserve() -> None:
    bundle = load_archive_selection_bundle(SELECTION)
    assert len(bundle.annotations) == EXPECTED_SELECTION_COUNT
    assert len(bundle.pdf_only_sources) == EXPECTED_PDF_ONLY_SOURCE_COUNT
    assert len(bundle.pdf_only_candidates) == EXPECTED_PDF_ONLY_CANDIDATE_COUNT
    assert {
        split: sum(annotation.split == split for annotation in bundle.annotations.values())
        for split in EXPECTED_SELECTION_SPLIT_COUNTS
    } == EXPECTED_SELECTION_SPLIT_COUNTS
    assert {
        status: sum(annotation.status == status for annotation in bundle.annotations.values())
        for status in EXPECTED_SELECTION_STATUS_COUNTS
    } == EXPECTED_SELECTION_STATUS_COUNTS
    assert all(source["capability_weight"] == 0 for source in bundle.pdf_only_sources)
    assert all(
        candidate["capability_weight"] == 0
        for candidate in bundle.pdf_only_candidates
    )


def test_generated_archive_audit_binds_selection_and_records_readme_drift() -> None:
    report = json.loads(AUDIT.read_text(encoding="utf-8"))
    validate_problem_archive_audit(report)
    expected_selection_sha = "sha256:" + hashlib.sha256(SELECTION.read_bytes()).hexdigest()
    assert report["selection_source"]["sha256"] == expected_selection_sha
    assert report["structured_source"]["meta_validation"]["computed"] == {
        "raw_total": 102,
        "total": 63,
        "unique_directions": 60,
        "unique_problems": 57,
    }
    assert report["documentation_drift"]["authoritative_total"] == 63
    assert report["documentation_drift"]["observed_numeric_claims"]["64"] > 0
    assert report["documentation_drift"]["affects_authoritative_metrics"] is False
    assert report["metrics"]["duplicate_direction_count"] == 3
    assert report["metrics"]["selected_case_count"] == 24
    assert report["metrics"]["pdf_only_capability_weight"] == 0


def test_audit_id_rejects_annotation_mutation() -> None:
    report = json.loads(AUDIT.read_text(encoding="utf-8"))
    mutated = copy.deepcopy(report)
    selected = next(row for row in mutated["problems"] if row["selected_case_id"])
    selected["selection_reason"] += " drift"
    with pytest.raises(ProblemArchiveAuditError) as error:
        validate_problem_archive_audit(mutated)
    assert error.value.code == "archive_audit_id_mismatch"


def test_selection_rejects_pdf_candidate_denominator_weight(tmp_path: Path) -> None:
    payload = json.loads(SELECTION.read_text(encoding="utf-8"))
    payload["pdf_only_candidates"][0]["capability_weight"] = 1
    path = tmp_path / "selection.json"
    path.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(ProblemArchiveAuditError) as error:
        load_archive_selection_bundle(path)
    assert error.value.code == "archive_selection_schema_invalid"
