from __future__ import annotations

import copy
from pathlib import Path

import pytest

from scripts.build_np_hard_h_i_full_report import (
    CAPABILITY_SPLITS,
    STAGE_LABELS,
    HIReportError,
    StaticEvidencePaths,
    _assert_no_secret,
    _canonical_content_hash,
    _parse_labeled_paths,
    _validate_http_calls,
    validate_static_assets,
)


ROOT = Path(__file__).resolve().parents[1]
HARDNESS = ROOT / "Benchmark/Hardness"


def _static_paths() -> StaticEvidencePaths:
    return StaticEvidencePaths(
        plan=ROOT / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md",
        registry=ROOT / "Gate/NP_HARD_UNIFIED_BENCHMARK_REGISTRY.json",
        taxonomy=ROOT / "Gate/BENCHMARK_TAXONOMY.json",
        capability_manifest=ROOT / "Archive/CAPABILITY_MANIFEST.json",
        capability_oracle=(
            ROOT / "Evaluation/np_hard_capability_oracle_v1.json"
        ),
        target_matrix=ROOT / "Gate/NP_HARD_TARGET_MATRIX.json",
        public_r1_suite=(
            ROOT / "Gate/Suites/np_hard_public_r1_coverage_v1.json"
        ),
        exact_edge_manifest=HARDNESS / "EXACT_REDUCTION_EDGE_MANIFEST.json",
        exact_edge_oracle=(
            ROOT / "Evaluation/exact_reduction_edge_oracle_v1.json"
        ),
        problem_archive=ROOT / "problems.7z",
        archive_selection=(
            ROOT / "Evaluation/np_hard_problem_archive_selection_v1.json"
        ),
        archive_audit=ROOT / "Reports/PROBLEM_ARCHIVE_AUDIT.json",
    )


def test_frozen_h_i_assets_have_exact_identity_and_edge_partitions() -> None:
    evidence = validate_static_assets(_static_paths())

    assert evidence["registry_taxonomy"]["registry"]["logical_cases"] == 59
    assert evidence["registry_taxonomy"]["registry"]["capability_weight"] == 0
    assert evidence["identity_partition"] == {
        "target_matrix": evidence["identity_partition"]["target_matrix"],
        "c0": 32,
        "f0": 2,
        "r1_public": 10,
        "total": 44,
        "canonical_identity_disjoint": True,
        "matrix_exhaustive": True,
    }
    assert evidence["exact_edge_archive"]["unique_directions"] == 24
    assert evidence["exact_edge_archive"]["split_counts"] == {
        "dev": 6,
        "validation": 6,
        "heldout": 12,
    }
    assert evidence["exact_edge_archive"]["duplicate_direction_count"] == 3
    assert evidence["exact_edge_archive"]["pdf_only_capability_weight"] == 0


def test_five_stage_evidence_is_mandatory_and_partial_input_fails_closed() -> None:
    assert STAGE_LABELS == (
        "h-i.1-registry",
        "h-i.2-capability",
        "h-i.3-scoring",
        "h-i.4-exact-edge",
        "h-i.5-freeze",
    )
    with pytest.raises(HIReportError) as caught:
        _parse_labeled_paths(
            ["h-i.1-registry=tmp/one.json"],
            expected=STAGE_LABELS,
            option="--stage-benchmark",
        )
    assert caught.value.code == "h_i_partial_evidence"


def test_capability_raw_and_score_inputs_require_all_four_splits() -> None:
    with pytest.raises(HIReportError) as caught:
        _parse_labeled_paths(
            ["dev=tmp/dev.json", "validation=tmp/validation.json"],
            expected=CAPABILITY_SPLITS,
            option="--capability-run",
        )
    assert caught.value.code == "h_i_partial_evidence"


def test_duplicate_labeled_evidence_is_rejected() -> None:
    with pytest.raises(HIReportError) as caught:
        _parse_labeled_paths(
            ["dev=tmp/a.json", "dev=tmp/b.json"],
            expected=("dev",),
            option="--capability-score",
        )
    assert caught.value.code == "h_i_cli_evidence_invalid"


def _live_call(index: int) -> dict[str, object]:
    return {
        "called": True,
        "ok": True,
        "status_code": 200,
        "provider_attempts": 1,
        "duration_seconds": 1.25,
        "request_id": "sha256:" + f"{index:064x}",
        "usage": {"prompt_tokens": 10, "completion_tokens": 5, "total_tokens": 15},
    }


def test_real_http_evidence_requires_200_tokens_and_unique_request_ids() -> None:
    calls = [_live_call(1), _live_call(2)]
    assert len(_validate_http_calls(calls, expected_count=2, label="fixture")) == 2

    reused = [_live_call(1), _live_call(1)]
    with pytest.raises(HIReportError) as caught:
        _validate_http_calls(reused, expected_count=2, label="fixture")
    assert caught.value.code == "h_i_deepseek_http_evidence_reused"

    failed = copy.deepcopy(calls)
    failed[0]["status_code"] = 503
    with pytest.raises(HIReportError) as caught:
        _validate_http_calls(failed, expected_count=2, label="fixture")
    assert caught.value.code == "h_i_deepseek_http_evidence_invalid"


def test_secret_scanner_allows_boolean_guards_but_rejects_credentials() -> None:
    _assert_no_secret(
        {
            "api_key_configured": True,
            "api_key_or_authorization_absent": True,
            "secret_absent": True,
        },
        label="safe",
    )
    with pytest.raises(HIReportError) as caught:
        _assert_no_secret(
            {"authorization": "Bearer definitely-not-reportable"},
            label="unsafe",
        )
    assert caught.value.code == "h_i_secret_leak"


def test_content_hash_binding_rejects_report_mutation() -> None:
    report = {"schema_version": "fixture", "run_valid": True, "cases": []}
    report["run_id"] = _canonical_content_hash(report, field="run_id")
    assert report["run_id"] == _canonical_content_hash(report, field="run_id")

    report["run_valid"] = False
    assert report["run_id"] != _canonical_content_hash(report, field="run_id")
