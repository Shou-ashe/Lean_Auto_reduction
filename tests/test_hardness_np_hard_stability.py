from __future__ import annotations

import json
from pathlib import Path

from agent.hardness.lean_runner import sha256_file
from agent.hardness.np_hard_stability import (
    NP_HARD_STABILITY_RUN_SCHEMA_V1,
    build_np_hard_stability_aggregate,
)


def _run(root: Path, *, index: int) -> dict:
    gates = {
        "persistent_candidate_worker": True,
        "worker_closed_before_final_authority": True,
        "standard_axiom_audit": True,
        "independent_final_and_release": True,
        "deletion_restores_blocker": True,
        "candidate_policy_safe": True,
        "no_secret_leak": True,
    }
    return {
        "schema_version": NP_HARD_STABILITY_RUN_SCHEMA_V1,
        "run_id": f"run-{index}",
        "started_at": f"2026-08-07T00:00:0{index}+00:00",
        "generated_at": f"2026-08-07T00:01:0{index}+00:00",
        "active_plan_sha256": sha256_file(root / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md"),
        "output_root": f"tmp/stability-{index}",
        "fresh_output_required": True,
        "resume": False,
        "response_replay": False,
        "direction": "hardness_seed_to_problem",
        "passed": True,
        "model": {"model": "deepseek-chat", "api_key_configured": True},
        "real_model_authoring": {
            "status": "VERIFIED",
            "initial_failure_code": "no_forward_path_from_hardness_seed",
            "provenance_kind": "model_generated",
            "candidate_body_sha256": f"sha256:body-{index}",
            "model_response_sha256": f"sha256:response-{index}",
            "task": {
                "hub_declaration": (
                    "ComplexityReduction.Problems.Karp21.Satisfiability."
                    "threeSATStructuredProblem"
                ),
                "input_problem_declaration": (
                    "Benchmark.Hardness.Inputs.NPHardMVP."
                    "ModelAuthoredTaggedThreeSAT.source"
                ),
            },
        },
        "deletion_body_audit": {
            "failure_code": "no_forward_path_from_hardness_seed"
        },
        "gates": gates,
        "metrics": {
            "real_api_calls": 1,
            "canonical_case_count": 6,
            "total_case_count": 8,
        },
    }


def test_three_fresh_real_runs_build_stable_aggregate(tmp_path) -> None:
    root = Path(__file__).resolve().parents[1]
    paths = []
    for index in range(1, 4):
        path = tmp_path / f"run-{index}.json"
        path.write_text(json.dumps(_run(root, index=index)), encoding="utf-8")
        paths.append(path)
    output = tmp_path / "aggregate.json"
    aggregate = build_np_hard_stability_aggregate(
        root=root, run_reports=paths, output_path=output
    )
    assert aggregate["passed"] is True
    assert aggregate["real_api_calls_total"] == 3
    assert aggregate["metrics"]["total_case_executions"] == 24
    assert aggregate["gates"]["persistent_worker_stable"] is True
    assert output.is_file()


def test_stability_aggregate_rejects_reused_output_directory(tmp_path) -> None:
    root = Path(__file__).resolve().parents[1]
    paths = []
    for index in range(1, 4):
        payload = _run(root, index=index)
        payload["output_root"] = "tmp/reused"
        path = tmp_path / f"run-{index}.json"
        path.write_text(json.dumps(payload), encoding="utf-8")
        paths.append(path)
    aggregate = build_np_hard_stability_aggregate(
        root=root,
        run_reports=paths,
        output_path=tmp_path / "aggregate.json",
    )
    assert aggregate["passed"] is False
    assert aggregate["gates"]["exactly_three_fresh_runs"] is False
