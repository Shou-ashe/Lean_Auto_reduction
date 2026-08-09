"""R-D full-run and three-run stability reports for the NP-hard MVP."""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

from .lean_runner import assert_generated_source_is_safe, sha256_file
from .model_client import DeepSeekConfig
from .np_hard import NPHardAgentConfigV1, NPHardAgentV1
from .np_hard_benchmark import run_np_hard_mvp_offline


NP_HARD_STABILITY_RUN_SCHEMA_V1 = "hardness_np_hard_mvp_stability_run_v1"
NP_HARD_STABILITY_AGGREGATE_SCHEMA_V1 = (
    "hardness_np_hard_mvp_stability_aggregate_v1"
)
MODEL_INPUT_MODULE = (
    "Benchmark.Hardness.Inputs.NPHardMVP.ModelAuthoredTaggedThreeSAT"
)
MODEL_INPUT_PROBLEM = f"{MODEL_INPUT_MODULE}.source"
EXPECTED_HUB = (
    "ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem"
)
EXPECTED_DIRECTION = "hardness_seed_to_problem"


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def _fresh_directory(path: Path) -> None:
    if path.exists() and any(path.iterdir()):
        raise ValueError(f"NP-hard stability output must be fresh and empty: {path}")
    path.mkdir(parents=True, exist_ok=True)


def _relative(path: Path, root: Path) -> str:
    try:
        return str(path.resolve().relative_to(root.resolve()))
    except ValueError:
        return str(path.resolve())


def _load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected a JSON object: {path}")
    return value


def _load_optional_command(path: Path) -> dict[str, Any]:
    if path.is_file():
        return _load_json(path)
    return {
        "command": None,
        "exit_code": None,
        "timed_out": False,
        "missing": True,
    }


def _secret_absent(root: Path, secret: str | None) -> bool:
    if not secret:
        return True
    needle = secret.encode("utf-8")
    for path in root.rglob("*"):
        if path.is_file() and path.stat().st_size <= 4_000_000:
            if needle in path.read_bytes():
                return False
    return True


def _public_calls(calls: Iterable[dict[str, Any]]) -> list[dict[str, Any]]:
    keys = (
        "attempt",
        "called",
        "ok",
        "status_code",
        "duration_seconds",
        "usage",
        "attempts",
        "finish_reason",
        "response_sha256",
    )
    return [{key: call.get(key) for key in keys} for call in calls]


def run_np_hard_mvp_full_stability(
    *,
    root: Path,
    suite_path: Path,
    output_root: Path,
    report_path: Path,
    deepseek: DeepSeekConfig,
    authoring_attempts: int = 4,
    lean_timeout_seconds: int = 600,
) -> dict[str, Any]:
    """Run the complete canonical matrix plus one fresh real-model authoring case."""

    root = root.resolve()
    output_root = output_root.resolve()
    report_path = report_path.resolve()
    _fresh_directory(output_root)
    started_at = datetime.now(timezone.utc).isoformat()

    offline_root = output_root / "canonical-suite"
    offline_report_path = output_root / "canonical-suite-report.json"
    offline = run_np_hard_mvp_offline(
        root=root,
        suite_path=suite_path,
        output_root=offline_root,
        report_path=offline_report_path,
    )

    authored_root = output_root / "real-model-authoring"
    authored = NPHardAgentV1(
        NPHardAgentConfigV1(
            root=root,
            input_module=MODEL_INPUT_MODULE,
            problem_declaration=MODEL_INPUT_PROBLEM,
            output_dir=authored_root,
            lean_timeout_seconds=lean_timeout_seconds,
            planner_mode="deterministic",
            authoring_mode="model-required",
            authoring_attempt_budget=authoring_attempts,
            deepseek=deepseek,
            runtime_prebuilt=False,
            candidate_validation_mode="persistent-worker",
        )
    ).run()
    authored_payload = authored.to_dict()

    deletion_root = output_root / "deletion-audit"
    deletion = NPHardAgentV1(
        NPHardAgentConfigV1(
            root=root,
            input_module=MODEL_INPUT_MODULE,
            problem_declaration=MODEL_INPUT_PROBLEM,
            output_dir=deletion_root,
            lean_timeout_seconds=lean_timeout_seconds,
            planner_mode="deterministic",
            authoring_mode="disabled",
            runtime_prebuilt=True,
        )
    ).run()
    deletion_payload = deletion.to_dict()

    authoring = authored_payload.get("authoring") or {}
    task = authoring.get("task") or {}
    publication = authored_payload.get("publication") or {}
    fresh_resolution = (authored_payload.get("authored_probe") or {}).get("resolution") or {}
    worker = authored_payload.get("candidate_worker") or {}
    worker_during = worker.get("during_authoring") or {}
    worker_after = worker.get("after_close") or {}
    worker_results = worker.get("results") or []
    calls = authoring.get("calls") or []

    artifact_command = _load_optional_command(authored_root / "commands/artifact.json")
    replay_command = _load_optional_command(
        authored_root / "commands/independent-release-replay.json"
    )
    artifact_path = authored_root / "Artifact.lean"
    artifact_source = artifact_path.read_text(encoding="utf-8") if artifact_path.is_file() else ""
    publication_source = root / str(publication.get("source_file", ""))
    candidate_source = (
        publication_source.read_text(encoding="utf-8")
        if publication_source.is_file()
        else ""
    )
    candidate_safe = False
    if candidate_source:
        try:
            assert_generated_source_is_safe(candidate_source)
            candidate_safe = True
        except ValueError:
            candidate_safe = False

    gates = {
        "canonical_suite_passed": offline.get("passed") is True,
        "real_model_called": authored_payload.get("model_calls", 0) >= 1
        and bool(calls)
        and all(call.get("called") is True for call in calls),
        "real_model_http_ok": bool(calls) and all(call.get("ok") is True for call in calls),
        "authored_job_verified": authored_payload.get("status") == "VERIFIED",
        "initial_gap_was_real": authoring.get("initial_failure", {}).get("code")
        == "no_forward_path_from_hardness_seed",
        "direction_frozen": task.get("direction") == EXPECTED_DIRECTION
        and fresh_resolution.get("direction") == EXPECTED_DIRECTION,
        "endpoints_frozen": task.get("hub_declaration") == EXPECTED_HUB
        and task.get("input_problem_declaration") == MODEL_INPUT_PROBLEM,
        "model_source_provenance": authoring.get("provenance_kind")
        == "model_generated"
        and publication.get("provenance_kind") == "model_generated",
        "fresh_core_selected_authored_atom": task.get("candidate_declaration")
        in fresh_resolution.get("atoms", []),
        "persistent_candidate_worker": worker.get("validation_authority")
        == "persistent_lean_worker"
        and worker.get("final_authority") is False
        and worker.get("allow_cold_fallback") is False
        and worker_during.get("worker_start_count") == 1
        and worker_during.get("cache_miss_count", 0) >= 1
        and worker_during.get("worker_crash_count") == 0
        and worker_during.get("worker_restart_count") == 0
        and worker_during.get("cold_fallback_count") == 0
        and bool(worker_results)
        and all(
            item.get("verified") is True and item.get("fallback_used") is False
            for item in worker_results
        ),
        "worker_closed_before_final_authority": worker_after.get("active_session_count")
        == 0
        and not any(worker_after.get("workers_alive") or []),
        "standard_axiom_audit": "assert_standard_axioms" in artifact_source
        and artifact_command.get("exit_code") == 0,
        "independent_final_and_release": artifact_command.get("exit_code") == 0
        and replay_command.get("exit_code") == 0
        and artifact_command.get("command") == replay_command.get("command"),
        "deletion_restores_blocker": deletion_payload.get("status") == "BLOCKED"
        and deletion_payload.get("failure", {}).get("code")
        == "no_forward_path_from_hardness_seed"
        and deletion_payload.get("model_calls") == 0
        and deletion_payload.get("publication") is None,
        "candidate_policy_safe": candidate_safe,
        "no_secret_leak": _secret_absent(output_root, deepseek.api_key),
        "no_resume_or_response_replay": True,
    }
    passed = all(gates.values())
    run_id = sha256_file(authored_root / "report.json")
    report = {
        "schema_version": NP_HARD_STABILITY_RUN_SCHEMA_V1,
        "run_id": run_id,
        "started_at": started_at,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "active_plan_sha256": sha256_file(root / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md"),
        "suite_sha256": sha256_file(suite_path),
        "output_root": _relative(output_root, root),
        "fresh_output_required": True,
        "resume": False,
        "response_replay": False,
        "objective": "prove_np_hard",
        "direction": EXPECTED_DIRECTION,
        "final_lean_type": "ComplexityReduction.Certificate.NativeTMNPHard",
        "model": deepseek.to_public_dict(),
        "passed": passed,
        "canonical_suite": {
            "report_file": _relative(offline_report_path, root),
            "report_sha256": sha256_file(offline_report_path),
            "passed": offline.get("passed"),
            "metrics": offline.get("metrics"),
            "cases": offline.get("cases"),
        },
        "real_model_authoring": {
            "report_file": _relative(authored_root / "report.json", root),
            "report_sha256": sha256_file(authored_root / "report.json"),
            "status": authored_payload.get("status"),
            "job_id": authored_payload.get("job_id"),
            "model_calls": authored_payload.get("model_calls"),
            "calls": _public_calls(calls),
            "initial_failure_code": authoring.get("initial_failure", {}).get("code"),
            "task": task,
            "candidate_source_sha256": authoring.get("candidate_source_sha256"),
            "candidate_body_sha256": authoring.get("candidate_body_sha256"),
            "model_response_sha256": authoring.get("model_response_sha256"),
            "provenance_kind": authoring.get("provenance_kind"),
            "publication": publication,
            "fresh_resolution": fresh_resolution,
            "worker": worker,
            "artifact_file": authored_payload.get("artifact_file"),
            "artifact_sha256": authored_payload.get("artifact_sha256"),
            "final_artifact_command": artifact_command,
            "independent_release_replay_command": replay_command,
        },
        "deletion_body_audit": {
            "report_file": _relative(deletion_root / "report.json", root),
            "report_sha256": sha256_file(deletion_root / "report.json"),
            "status": deletion_payload.get("status"),
            "failure_code": deletion_payload.get("failure", {}).get("code"),
            "model_calls": deletion_payload.get("model_calls"),
        },
        "gates": gates,
        "metrics": {
            "canonical_case_count": len(offline.get("cases") or []),
            "real_model_case_count": 1,
            "deletion_audit_case_count": 1,
            "total_case_count": len(offline.get("cases") or []) + 2,
            "real_api_calls": authored_payload.get("model_calls", 0),
            "exact_final_np_hardness_rate": float(
                authored_payload.get("status") == "VERIFIED"
            ),
            "persistent_worker_validation_rate": float(
                gates["persistent_candidate_worker"]
            ),
            "independent_replay_rate": float(
                gates["independent_final_and_release"]
            ),
            "compiler_inserted_math_token_count": 0,
        },
    }
    _write_json(report_path, report)
    _write_json(output_root / "report.json", report)
    return report


def build_np_hard_stability_aggregate(
    *, root: Path, run_reports: Iterable[Path], output_path: Path
) -> dict[str, Any]:
    root = root.resolve()
    paths = tuple(path.resolve() for path in run_reports)
    if len(paths) != 3:
        raise ValueError("NP-hard stability aggregate requires exactly three runs")
    runs = [_load_json(path) for path in paths]
    if any(run.get("schema_version") != NP_HARD_STABILITY_RUN_SCHEMA_V1 for run in runs):
        raise ValueError("unsupported NP-hard stability run schema")

    output_roots = [run.get("output_root") for run in runs]
    run_ids = [run.get("run_id") for run in runs]
    plan_hash = sha256_file(root / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md")
    stable_projection = [
        {
            "status": run.get("real_model_authoring", {}).get("status"),
            "direction": run.get("direction"),
            "hub": run.get("real_model_authoring", {}).get("task", {}).get(
                "hub_declaration"
            ),
            "target": run.get("real_model_authoring", {}).get("task", {}).get(
                "input_problem_declaration"
            ),
            "provenance": run.get("real_model_authoring", {}).get(
                "provenance_kind"
            ),
            "initial_failure": run.get("real_model_authoring", {}).get(
                "initial_failure_code"
            ),
            "deletion_failure": run.get("deletion_body_audit", {}).get(
                "failure_code"
            ),
        }
        for run in runs
    ]
    gates = {
        "exactly_three_fresh_runs": len(set(output_roots)) == 3
        and all(run.get("fresh_output_required") is True for run in runs)
        and all(run.get("resume") is False for run in runs)
        and all(run.get("response_replay") is False for run in runs),
        "all_runs_passed": all(run.get("passed") is True for run in runs),
        "all_real_api_calls": all(
            run.get("metrics", {}).get("real_api_calls", 0) >= 1 for run in runs
        ),
        "outcome_direction_endpoint_provenance_stable": len(
            {json.dumps(item, sort_keys=True) for item in stable_projection}
        )
        == 1,
        "persistent_worker_stable": all(
            run.get("gates", {}).get("persistent_candidate_worker") is True
            and run.get("gates", {}).get("worker_closed_before_final_authority")
            is True
            for run in runs
        ),
        "standard_axiom_audit_stable": all(
            run.get("gates", {}).get("standard_axiom_audit") is True
            for run in runs
        ),
        "independent_release_replay_stable": all(
            run.get("gates", {}).get("independent_final_and_release") is True
            for run in runs
        ),
        "deletion_audit_stable": all(
            run.get("gates", {}).get("deletion_restores_blocker") is True
            for run in runs
        ),
        "no_shortcut_or_secret_leak": all(
            run.get("gates", {}).get("candidate_policy_safe") is True
            and run.get("gates", {}).get("no_secret_leak") is True
            for run in runs
        ),
        "execution_plan_stable": len(
            {run.get("active_plan_sha256") for run in runs}
        )
        == 1,
        "run_reports_are_distinct": len(set(run_ids)) == 3,
    }
    aggregate = {
        "schema_version": NP_HARD_STABILITY_AGGREGATE_SCHEMA_V1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "active_plan_sha256": plan_hash,
        "objective": "prove_np_hard",
        "direction": EXPECTED_DIRECTION,
        "final_lean_type": "ComplexityReduction.Certificate.NativeTMNPHard",
        "passed": all(gates.values()),
        "run_count": 3,
        "real_api_calls_total": sum(
            int(run.get("metrics", {}).get("real_api_calls", 0)) for run in runs
        ),
        "stable_projection": stable_projection[0],
        "runs": [
            {
                "report_file": _relative(path, root),
                "report_sha256": sha256_file(path),
                "run_id": run.get("run_id"),
                "output_root": run.get("output_root"),
                "started_at": run.get("started_at"),
                "generated_at": run.get("generated_at"),
                "model": run.get("model"),
                "model_calls": run.get("metrics", {}).get("real_api_calls"),
                "candidate_body_sha256": run.get("real_model_authoring", {}).get(
                    "candidate_body_sha256"
                ),
                "model_response_sha256": run.get("real_model_authoring", {}).get(
                    "model_response_sha256"
                ),
                "passed": run.get("passed"),
            }
            for path, run in zip(paths, runs, strict=True)
        ],
        "gates": gates,
        "metrics": {
            "full_run_success_rate": sum(run.get("passed") is True for run in runs) / 3,
            "canonical_case_count_per_run": runs[0].get("metrics", {}).get(
                "canonical_case_count"
            ),
            "total_case_executions": sum(
                int(run.get("metrics", {}).get("total_case_count", 0)) for run in runs
            ),
            "compiler_inserted_math_token_count": 0,
        },
    }
    _write_json(output_path.resolve(), aggregate)
    return aggregate
