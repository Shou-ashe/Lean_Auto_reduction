from __future__ import annotations

import hashlib
import json
import threading
from pathlib import Path

import pytest

from agent.hardness.models import sha256_id
from agent.hardness.np_hard_release_benchmark import (
    _run_release_case_tasks,
    _token_usage,
    _validate_release_case_jobs,
)


ROOT = Path(__file__).resolve().parents[1]
HARDNESS = ROOT / "Benchmark" / "Hardness"


def _load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_release_token_usage_aggregates_only_integer_provider_fields() -> None:
    assert _token_usage(
        [
            {"usage": {"prompt_tokens": 10, "total_tokens": 13, "details": {}}},
            {"usage": {"prompt_tokens": 4, "total_tokens": 7}},
            {"usage": None},
        ]
    ) == {"prompt_tokens": 14, "total_tokens": 20}


def test_release_case_executor_observes_four_way_parallelism() -> None:
    barrier = threading.Barrier(4)

    def task(index: int) -> dict:
        barrier.wait(timeout=5)
        return {"index": index}

    results, parallel = _run_release_case_tasks(
        [(f"case-{index}", lambda index=index: task(index)) for index in range(4)],
        jobs=4,
    )

    assert [results[f"case-{index}"]["index"] for index in range(4)] == list(range(4))
    assert parallel["configured_jobs"] == 4
    assert parallel["submitted_case_tasks"] == 4
    assert parallel["maximum_concurrent_case_tasks"] == 4
    assert parallel["final_active_case_tasks"] == 0
    assert parallel["observed_parallelism"] is True


@pytest.mark.parametrize("jobs", [False, 0, 5])
def test_release_case_executor_rejects_invalid_parallelism(jobs) -> None:
    with pytest.raises(ValueError, match="release case jobs must be in 1..4"):
        _validate_release_case_jobs(jobs)


def test_g_e_full_report_is_content_addressed_and_complete() -> None:
    summary = _load(ROOT / "Reports/MAIN_G_E_45_FULL_REPORT.json")
    raw_path = ROOT / summary["raw_report"]["file"]
    entrypoint_path = ROOT / summary["g_e_entrypoint_report"]["file"]
    raw = _load(raw_path)

    assert summary["passed"] is True
    assert _sha256(raw_path) == summary["raw_report"]["sha256"]
    assert _sha256(entrypoint_path) == summary["g_e_entrypoint_report"]["sha256"]
    assert raw["total"] == raw["passed"] == 45
    assert raw["failed"] == 0
    assert summary["g_e_entrypoint"]["normalization_verified_count"] == 3
    assert summary["g_e_entrypoint"]["existing_route_model_calls"] == 0
    assert summary["real_model"]["model_call_count"] == 1
    assert summary["real_model"]["http_ok_count"] == 1
    assert all(summary["gates"].values())


def test_g_f_offline_release_gate_is_complete() -> None:
    report = _load(ROOT / "Reports/NP_HARD_RELEASE_OFFLINE_REPORT.json")
    metrics = report["metrics"]

    assert report["passed"] is True
    assert metrics["case_count"] == 12
    assert metrics["existing_route_verified"] == 5
    assert metrics["authoring_public_blockers_confirmed"] == 5
    assert metrics["safety_negative_count"] == 2
    assert metrics["gold_compile_self_check_count"] == 5
    assert metrics["gold_replay_verified_count"] == 5
    assert metrics["fresh_core_rediscovery_count"] >= 12
    assert metrics["independent_replay_count"] == 5
    assert metrics["worker_fallback_count"] == 0
    assert all(report["mutation_audits"].values())
    assert all(report["isolation_audits"].values())


def test_g_f_three_round_real_release_gate_and_call_ledgers() -> None:
    aggregate = _load(ROOT / "Reports/NP_HARD_RELEASE_STABILITY_AGGREGATE.json")
    metrics = aggregate["metrics"]

    assert aggregate["passed"] is True
    assert metrics["round_count"] == 3
    assert metrics["instance_execution_count"] == 36
    assert metrics["matched_instance_count"] == 36
    assert metrics["positive_execution_count"] == 30
    assert metrics["model_authoring_verified_count"] == 15
    assert metrics["existing_route_model_calls"] == 0
    assert metrics["safety_negative_matched_count"] == 6
    assert metrics["deletion_audit_count"] == 15
    assert metrics["worker_fallback_count"] == 0
    assert 15 <= metrics["real_api_calls"] <= 120
    assert len(aggregate["case_matrix"]) == 12
    assert all(
        len(rows) == 3 and all(row["matched"] for row in rows)
        for rows in aggregate["case_matrix"].values()
    )

    for round_ref in aggregate["rounds"]:
        round_path = ROOT / round_ref["file"]
        assert _sha256(round_path) == round_ref["sha256"]
        run = _load(round_path)
        assert run["passed"] is True
        assert run["metrics"]["case_count"] == 12
        assert run["metrics"]["matched_case_count"] == 12
        assert run["metrics"]["model_authoring_verified_count"] == 5
        assert run["metrics"]["existing_route_model_calls"] == 0
        assert run["metrics"]["safety_negative_matched_count"] == 2
        assert run["metrics"]["deletion_audit_count"] == 5
        assert run["metrics"]["finalization_count"] == 10
        assert run["metrics"]["independent_replay_count"] == 10
        assert run["metrics"]["worker_fallback_count"] == 0
        assert run["security"]["secret_absent"] is True
        assert run["security"]["oracle_or_gold_prompt_acceptance_count"] == 0
        assert run["security"]["nonstandard_axiom_acceptance_count"] == 0

        authoring = [case for case in run["cases"] if case["kind"] == "model_authoring"]
        assert len(authoring) == 5
        for case in authoring:
            ledger = case["model_call_ledger"]
            assert ledger
            assert len(ledger) == case["runtime"]["model_calls"]
            assert case["deletion_audit"]["passed"] is True
            for call in ledger:
                prompt_path = Path(call["prompt_file"])
                response_path = Path(call["response_file"])
                assert call["called"] is True and call["ok"] is True
                assert call["request_id"].startswith("sha256:")
                assert call["prompt_sha256"] == sha256_id(
                    prompt_path.read_text(encoding="utf-8")
                )
                response = _load(response_path)
                assert call["response_sha256"] == sha256_id(response["content"])


def test_g_f_full_report_is_content_addressed_and_complete() -> None:
    summary = _load(ROOT / "Reports/MAIN_G_F_45_FULL_REPORT.json")
    raw_path = ROOT / summary["raw_report"]["file"]
    offline_path = ROOT / summary["g_f_offline_report"]["file"]
    stability_path = ROOT / summary["g_f_stability_report"]["file"]
    raw = _load(raw_path)

    assert summary["passed"] is True
    assert _sha256(raw_path) == summary["raw_report"]["sha256"]
    assert _sha256(offline_path) == summary["g_f_offline_report"]["sha256"]
    assert _sha256(stability_path) == summary["g_f_stability_report"]["sha256"]
    assert raw["total"] == raw["passed"] == 45
    assert raw["failed"] == 0
    assert summary["counts"]["positive_verified_count"] == 29
    assert summary["counts"]["negative_expected_outcome_count"] == 16
    assert summary["g_f_release"]["matched_instance_count"] == 36
    assert summary["g_f_release"]["real_api_calls"] == 36
    assert summary["real_model"]["http_ok_count"] == 1
    assert all(summary["gates"].values())
