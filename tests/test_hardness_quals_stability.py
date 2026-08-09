import hashlib
import json
from pathlib import Path

from scripts.build_quals_stability_aggregate import DEFAULT_REPORTS, SCHEMA


ROOT = Path(__file__).resolve().parents[1]
AGGREGATE = (
    ROOT
    / "Benchmark"
    / "Hardness"
    / "QUALS_COMPLETENESS_N_C_STABILITY_AGGREGATE.json"
)


def test_n_c_stability_aggregate_freezes_three_independent_real_runs() -> None:
    report = json.loads(AGGREGATE.read_text())

    assert report["schema_version"] == SCHEMA
    assert report["status"] == "VERIFIED"
    assert report["requirements"] == {
        "independent_full_runs": 3,
        "fresh_output_directory_per_run": True,
        "resume_used": False,
        "replayed_model_answers": False,
        "primary_verified_per_run": 5,
        "adversarial_correct_per_run": 7,
        "protocol_expected_per_run": 12,
        "real_http_calls_per_run": 5,
        "gates_passed_per_run": 18,
        "final_lean_processes_per_run": 1,
        "release_replays_per_run": 1,
    }
    assert report["aggregate"]["run_count"] == 3
    assert report["aggregate"]["primary_verified"] == 15
    assert report["aggregate"]["adversarial_correct"] == 21
    assert report["aggregate"]["real_http_calls"] == 15
    assert report["aggregate"]["http_ok"] == 15
    assert report["aggregate"]["replayed_response_count"] == 0
    assert report["aggregate"]["failure_reason_distribution"] == {
        "missing_native_membership": 15,
        "no_registry_path": 6,
    }
    assert report["independence_evidence"] == {
        "unique_run_label_count": 3,
        "unique_output_root_count": 3,
        "unique_report_sha256_count": 3,
        "unique_response_file_count": 15,
        "called_response_count": 15,
        "replayed_response_count": 0,
    }
    assert report["artifact_hash_analysis"]["unique_final_artifact_sha256_count"] == 1
    assert report["artifact_hash_analysis"]["final_artifact_identical_across_runs"] is True
    assert report["validation_errors"] == []


def test_n_c_stability_aggregate_hashes_the_three_canonical_reports() -> None:
    report = json.loads(AGGREGATE.read_text())
    expected = [hashlib.sha256(path.read_bytes()).hexdigest() for path in DEFAULT_REPORTS]

    assert report["artifact_hash_analysis"]["report_sha256"] == expected
    assert [run["report_sha256"] for run in report["runs"]] == expected
    assert all(run["status"] == "VERIFIED" for run in report["runs"])
    assert all(run["primary_verified"] == 5 for run in report["runs"])
    assert all(run["adversarial_correct"] == 7 for run in report["runs"])
    assert all(run["real_http_calls"] == 5 for run in report["runs"])
    assert all(run["replayed_response_count"] == 0 for run in report["runs"])
    assert report["excluded_attempts"][0]["status"] == "RUNNING"
    assert report["excluded_attempts"][0]["counted"] is False
