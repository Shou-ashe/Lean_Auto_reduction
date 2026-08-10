"""G-F offline gate and three-round real-DeepSeek NP-hard release benchmark."""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor, as_completed
import json
import threading
import time
from dataclasses import replace
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Mapping

from .lean_runner import build_module_command, run_command, sha256_file
from .model_client import DeepSeekConfig
from .models import sha256_id
from .np_hard_authoring import (
    NPHardAuthoringTaskV2,
    build_np_hard_authoring_tasks_v2,
)
from .np_hard_authoring_planner import NPHardAuthoringPlannerV2
from .np_hard_gap_benchmark import _OfflineNodeModel, _fixture_bodies
from .np_hard_gap_runtime import (
    NP_HARD_NODE_PATCH_SCHEMA_V1,
    NPHardGapRuntimeError,
    _current_dependency_snapshot,
    _node_request,
    parse_np_hard_node_patch_v1,
)
from .np_hard_generalization import load_np_hard_generalization_suite
from .np_hard_generalization_benchmark import run_np_hard_generalization_baseline
from .np_hard_orchestrator import NPHardOrchestratorConfigV2, NPHardOrchestratorV2


NP_HARD_RELEASE_OFFLINE_SCHEMA_V1 = "hardness_np_hard_release_offline_v2"
NP_HARD_RELEASE_RUN_SCHEMA_V1 = "hardness_np_hard_release_real_run_v2"
NP_HARD_RELEASE_AGGREGATE_SCHEMA_V1 = "hardness_np_hard_release_aggregate_v2"
_QUARANTINED = (".Oracles.", ".Gold.", ".GoldProofs.", ".HiddenTargets.")
DEFAULT_RELEASE_CASE_JOBS = 4
MAX_RELEASE_CASE_JOBS = 4


def _validate_release_case_jobs(jobs: int) -> int:
    if isinstance(jobs, bool) or not isinstance(jobs, int) or not 1 <= jobs <= MAX_RELEASE_CASE_JOBS:
        raise ValueError(f"release case jobs must be in 1..{MAX_RELEASE_CASE_JOBS}")
    return jobs


def _run_release_case_tasks(
    tasks: list[tuple[str, Callable[[], dict[str, Any]]]],
    *,
    jobs: int,
) -> tuple[dict[str, dict[str, Any]], dict[str, Any]]:
    """Run isolated release cases concurrently while preserving keyed results."""

    jobs = _validate_release_case_jobs(jobs)
    if len({task_id for task_id, _ in tasks}) != len(tasks):
        raise ValueError("release case task identifiers must be unique")
    lock = threading.Lock()
    active = 0
    maximum_active = 0
    started = time.monotonic()

    def tracked(run: Callable[[], dict[str, Any]]) -> dict[str, Any]:
        nonlocal active, maximum_active
        with lock:
            active += 1
            maximum_active = max(maximum_active, active)
        try:
            return run()
        finally:
            with lock:
                active -= 1

    results: dict[str, dict[str, Any]] = {}
    if jobs == 1 or len(tasks) <= 1:
        for task_id, run in tasks:
            results[task_id] = tracked(run)
    else:
        with ThreadPoolExecutor(
            max_workers=min(jobs, len(tasks)),
            thread_name_prefix="np-hard-release-case",
        ) as executor:
            pending = {
                executor.submit(tracked, run): task_id for task_id, run in tasks
            }
            for future in as_completed(pending):
                results[pending[future]] = future.result()
    parallel_execution = {
        "configured_jobs": jobs,
        "submitted_case_tasks": len(tasks),
        "maximum_concurrent_case_tasks": maximum_active,
        "final_active_case_tasks": active,
        "wall_duration_seconds": round(time.monotonic() - started, 6),
        "observed_parallelism": (
            jobs == 1 or len(tasks) <= 1 or maximum_active >= min(2, jobs, len(tasks))
        ),
    }
    return results, parallel_execution


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def _fresh(path: Path) -> None:
    if path.exists() and any(path.iterdir()):
        raise ValueError(f"release output must be fresh and empty: {path}")
    path.mkdir(parents=True, exist_ok=True)


def _relative(path: Path, root: Path) -> str:
    try:
        return str(path.resolve().relative_to(root.resolve()))
    except ValueError:
        return str(path.resolve())


def _source_fingerprint(root: Path) -> dict[str, Any]:
    tracked = (
        "ACTIVE_AGENT_IMPROVEMENT_PLAN.md",
        "scripts/prove_np_hard.py",
        "scripts/run_np_hard_h_d_heldout.py",
        "scripts/run_np_hard_h_e_inventory.py",
        "scripts/run_np_hard_h_e_heldout.py",
        "agent/hardness/np_hard_orchestrator.py",
        "agent/hardness/np_hard_input.py",
        "agent/hardness/np_hard_authoring_planner.py",
        "agent/hardness/np_hard_gap_runtime.py",
        "agent/hardness/np_hard_release_benchmark.py",
        "agent/hardness/np_hard_inventory.py",
        "agent/hardness/np_hard_h_e_benchmark.py",
        "Lean/Reference/ComplexityReduction/Agent/Hardness/AuthoringPlanner.lean",
        "Lean/Reference/ComplexityReduction/Agent/Hardness/InputNormalization.lean",
        "Lean/Reference/ComplexityReduction/Agent/Hardness/Gap.lean",
        "Lean/Reference/Reports/Inputs/HCCrossModule/Problem.lean",
        "Lean/Reference/Reports/Inputs/HCCrossModule/Adapters.lean",
        "Lean/Reference/Reports/Inputs/HCCrossModule/Specification.lean",
        "Lean/Reference/Reports/Inputs/HCCrossModule/Entry.lean",
        "Lean/Reference/Reports/Inputs/HDCrossModuleEncoding.lean",
        "Lean/Reference/Reports/Inputs/NPHardGeneralization/InputNormalizationOpenWorld.lean",
        "Gate/np_hard_input_registry.json",
        "Gate/Suites/np_hard_h_e_heldout_inputs.json",
        "Evaluation/np_hard_h_e_heldout_oracle.json",
    )
    files = {name: sha256_file(root / name) for name in tracked}
    return {
        "git_repository_available": False,
        "reason": "workspace .git directory contains no repository metadata",
        "files": files,
        "combined_sha256": sha256_id(files),
        "lean_toolchain": (root / "Lean/lean-toolchain").read_text(encoding="utf-8").strip(),
        "lean_toolchain_sha256": sha256_file(root / "Lean/lean-toolchain"),
        "lake_manifest_sha256": sha256_file(root / "Lean/lake-manifest.json"),
    }


def _token_usage(ledger: list[Mapping[str, Any]]) -> dict[str, int]:
    totals: dict[str, int] = {}
    for call in ledger:
        usage = call.get("usage") or {}
        if not isinstance(usage, Mapping):
            continue
        for name, value in usage.items():
            if isinstance(value, int):
                totals[name] = totals.get(name, 0) + value
    return totals


def _final_program(task, authoring: dict[str, Any]) -> str:
    if task.task_class == "semantic_proof":
        return str(authoring["program_reference"])
    suffix = "composedProgram" if task.task_class == "program_composition" else "synthesizedProgram"
    return f"{task.candidate_module}.{suffix}"


def _expect_code(action: Callable[[], Any], code: str) -> bool:
    try:
        action()
    except NPHardGapRuntimeError as error:
        return error.code == code
    return False


def _mutation_audits(*, root: Path, suite_path: Path) -> dict[str, bool]:
    task = build_np_hard_authoring_tasks_v2(root=root, suite_path=suite_path)[0]
    request = _node_request(
        task=task,
        node_ordinal=1,
        dependency_snapshot=_current_dependency_snapshot(root=root, task=task, accepted=()),
        accepted=(),
        total_model_calls=0,
    )

    def payload(body: str = "by\n  rfl\n") -> dict[str, Any]:
        return {
            "schema_version": NP_HARD_NODE_PATCH_SCHEMA_V1,
            "action": "submit_node_patch",
            "request_id": request.request_id,
            "node_id": request.node.node_id,
            "declaration": request.node.declaration,
            "dependency_fingerprint": request.dependency_fingerprint,
            "replacement_body": body,
        }

    wrong_direction = replace(request, required_direction="target_to_source")
    wrong_direction = replace(
        wrong_direction, request_id=wrong_direction.computed_request_id
    )
    wrong_endpoint = replace(
        request,
        target_problem={"module": "Example.Other", "term": "Example.Other.problem"},
    )
    wrong_endpoint = replace(wrong_endpoint, request_id=wrong_endpoint.computed_request_id)
    escaped = payload()
    escaped["declaration"] = "Generated.Other.escape"
    return {
        "wrong_direction_rejected": _expect_code(
            lambda: parse_np_hard_node_patch_v1(
                content=json.dumps(payload()), request=wrong_direction, task=task
            ),
            "candidate_wrong_direction",
        ),
        "wrong_endpoint_rejected": _expect_code(
            lambda: parse_np_hard_node_patch_v1(
                content=json.dumps(payload()), request=wrong_endpoint, task=task
            ),
            "candidate_wrong_endpoint",
        ),
        "forbidden_axiom_rejected": _expect_code(
            lambda: parse_np_hard_node_patch_v1(
                content=json.dumps(payload("by\n  exact sorry\n")), request=request, task=task
            ),
            "candidate_nonstandard_axiom",
        ),
        "edit_boundary_rejected": _expect_code(
            lambda: parse_np_hard_node_patch_v1(
                content=json.dumps(escaped), request=request, task=task
            ),
            "candidate_outside_edit_boundary",
        ),
    }


def _public_tree_safe(*, root: Path, suite) -> dict[str, bool]:
    sources = [root / name for case in suite.cases for name in case.public_source_files]
    texts = [path.read_text(encoding="utf-8") for path in sources]
    return {
        "no_gold_or_oracle_import": all(
            not any(marker.lower() in text.lower() for marker in _QUARANTINED)
            for text in texts
        ),
        "no_secret_marker": all(
            "DEEPSEEK_API_KEY" not in text and "Bearer " not in text for text in texts
        ),
    }


def _run_production_orchestrator_offline(
    *, root: Path, suite_path: Path, output_root: Path, report_path: Path
) -> dict[str, Any]:
    """Exercise every authoring class through the production V2 job machine."""

    suite = load_np_hard_generalization_suite(suite_path, root=root)
    cases = [case for case in suite.cases if case.kind == "model_authoring"]
    rows: list[dict[str, Any]] = []
    for case in cases:
        assert case.authoring is not None
        fixture_plan = NPHardAuthoringPlannerV2(
            root=root,
            input_module=case.module,
            input_problem_declaration=case.problem,
            output_dir=output_root / "fixture-plans" / case.id,
            lean_timeout_seconds=600,
        ).plan()
        if fixture_plan.task is None:
            raise ValueError(f"automatic authoring planner blocked fixture case: {case.id}")
        fixture_task = fixture_plan.task
        model = _OfflineNodeModel(_fixture_bodies(fixture_task, case.authoring))
        result = NPHardOrchestratorV2(
            NPHardOrchestratorConfigV2(
                root=root,
                input_module=case.module,
                problem_declaration=case.problem,
                output_dir=output_root / "cases" / case.id,
                lean_timeout_seconds=600,
                authoring_policy="model-required",
                attempt_budget=4,
                call_budget=None,
                runtime_prebuilt=True,
            ),
            model_client=model,
        ).run()
        payload = result.to_dict()
        task_payload = payload.get("capability_dag")
        task = (
            NPHardAuthoringTaskV2.from_dict(task_payload)
            if isinstance(task_payload, Mapping)
            else None
        )
        runtime = payload["authoring_runtime"] or {}
        matched = (
            result.status == "VERIFIED"
            and task is not None
            and result.model_calls == len(task.gap_nodes)
            and payload["independent_replay"]["passed"] is True
            and payload["axiom_audit"]["passed"] is True
            and payload["deletion_audit"]["passed"] is True
            and len(payload["candidate_publication"]) == len(task.gap_nodes)
            and all(not item.get("fallback_used") for item in runtime["worker_results"])
        )
        rows.append(
            {
                "case_id": case.id,
                "task_class": task.task_class if task is not None else None,
                "request_id": payload["request_id"],
                "model_calls": result.model_calls,
                "fresh_core_rediscoveries": runtime["fresh_core_rediscoveries"],
                "worker_results": runtime["worker_results"],
                "independent_replay": payload["independent_replay"],
                "deletion_audit": payload["deletion_audit"],
                "matched": matched,
            }
        )
    metrics = {
        "verified_task_count": sum(row["matched"] for row in rows),
        "fresh_core_rediscovery_count": sum(
            row["fresh_core_rediscoveries"] for row in rows
        ),
        "independent_replay_count": sum(
            row["matched"] and row["independent_replay"]["passed"] for row in rows
        ),
        "worker_fallback_count": sum(
            item.get("fallback_used", False)
            for row in rows
            for item in row["worker_results"]
        ),
        "fixture_model_calls": sum(row["model_calls"] for row in rows),
        "deletion_audit_count": sum(
            row["matched"] and row["deletion_audit"]["passed"] for row in rows
        ),
    }
    report = {
        "schema_version": "hardness_np_hard_production_orchestrator_offline_v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "H-A-production-orchestrator-offline",
        "passed": all(row["matched"] for row in rows),
        "metrics": metrics,
        "cases": rows,
    }
    _write_json(report_path, report)
    return report


def run_np_hard_release_offline(
    *, root: Path, suite_path: Path, output_root: Path, report_path: Path
) -> dict[str, Any]:
    root = root.resolve()
    suite_path = suite_path.resolve()
    output_root = output_root.resolve()
    _fresh(output_root)
    suite = load_np_hard_generalization_suite(suite_path, root=root)
    baseline = run_np_hard_generalization_baseline(
        root=root,
        suite_path=suite_path,
        output_root=output_root / "baseline",
        report_path=output_root / "baseline-report.json",
    )
    runtime = _run_production_orchestrator_offline(
        root=root,
        suite_path=suite_path,
        output_root=output_root / "production-orchestrator",
        report_path=output_root / "production-orchestrator-report.json",
    )
    mutations = _mutation_audits(root=root, suite_path=suite_path)
    isolation = _public_tree_safe(root=root, suite=suite)
    metrics = {
        "case_count": baseline["metrics"]["case_count"],
        "existing_route_verified": baseline["metrics"]["existing_route_verified"],
        "authoring_public_blockers_confirmed": baseline["metrics"][
            "authoring_public_blockers_confirmed"
        ],
        "safety_negative_count": baseline["metrics"]["safety_negative_count"],
        "gold_compile_self_check_count": baseline["metrics"]["gold_compile_self_check_count"],
        "gold_replay_verified_count": runtime["metrics"]["verified_task_count"],
        "fresh_core_rediscovery_count": runtime["metrics"]["fresh_core_rediscovery_count"],
        "independent_replay_count": runtime["metrics"]["independent_replay_count"],
        "worker_fallback_count": runtime["metrics"]["worker_fallback_count"],
    }
    passed = (
        baseline["passed"] is True
        and runtime["passed"] is True
        and metrics["case_count"] == 12
        and metrics["existing_route_verified"] == 5
        and metrics["authoring_public_blockers_confirmed"] == 5
        and metrics["safety_negative_count"] == 2
        and metrics["gold_compile_self_check_count"] == 5
        and metrics["gold_replay_verified_count"] == 5
        and metrics["worker_fallback_count"] == 0
        and all(mutations.values())
        and all(isolation.values())
    )
    report = {
        "schema_version": NP_HARD_RELEASE_OFFLINE_SCHEMA_V1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "H-A-offline",
        "passed": passed,
        "suite_sha256": sha256_file(suite_path),
        "active_plan_sha256": sha256_file(root / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md"),
        "source_fingerprint": _source_fingerprint(root),
        "metrics": metrics,
        "mutation_audits": mutations,
        "isolation_audits": isolation,
        "baseline_report": {
            "file": _relative(output_root / "baseline-report.json", root),
            "sha256": sha256_file(output_root / "baseline-report.json"),
        },
        "production_orchestrator_report": {
            "file": _relative(output_root / "production-orchestrator-report.json", root),
            "sha256": sha256_file(output_root / "production-orchestrator-report.json"),
        },
    }
    _write_json(report_path, report)
    _write_json(output_root / "report.json", report)
    return report


def _secret_absent(root: Path, secret: str | None) -> bool:
    if not secret:
        return True
    needle = secret.encode("utf-8")
    for path in root.rglob("*"):
        if path.is_file() and path.stat().st_size <= 4_000_000:
            if needle in path.read_bytes():
                return False
    return True


def _endpoint_mutation_rejected(*, root: Path, suite_path: Path) -> bool:
    return _mutation_audits(root=root, suite_path=suite_path)["wrong_endpoint_rejected"]


def run_np_hard_release_real_round(
    *,
    root: Path,
    suite_path: Path,
    output_root: Path,
    report_path: Path,
    deepseek: DeepSeekConfig,
    round_index: int,
    jobs: int = DEFAULT_RELEASE_CASE_JOBS,
) -> dict[str, Any]:
    root = root.resolve()
    suite_path = suite_path.resolve()
    output_root = output_root.resolve()
    jobs = _validate_release_case_jobs(jobs)
    _fresh(output_root)
    suite = load_np_hard_generalization_suite(suite_path, root=root)
    existing_cases = [case for case in suite.cases if case.kind == "existing_route"]
    authoring_cases = [case for case in suite.cases if case.kind == "model_authoring"]
    negative_cases = [case for case in suite.cases if case.kind == "safety_negative"]
    modules = {case.module for case in suite.cases}
    prebuild = run_command(
        build_module_command(modules), cwd=root / "Lean", timeout_seconds=900
    )
    if not prebuild.ok:
        raise ValueError("G-F real-round prebuild failed")

    def run_existing(case) -> dict[str, Any]:
        result = NPHardOrchestratorV2(
            NPHardOrchestratorConfigV2(
                root=root,
                input_module=case.module,
                problem_declaration=case.problem,
                output_dir=output_root / "cases" / case.id,
                lean_timeout_seconds=600,
                authoring_policy="model-auto",
                deepseek=deepseek,
                runtime_prebuilt=True,
            )
        ).run()
        payload = result.to_dict()
        matched = (
            result.status == "VERIFIED"
            and result.model_calls == 0
            and payload["selected_hub"] is not None
            and payload["independent_replay"].get("passed") is True
        )
        return {
            "case_id": case.id,
            "kind": case.kind,
            "family": case.family,
            "status": result.status,
            "model_calls": result.model_calls,
            "input_identity": payload["input_identity"],
            "request_id": payload["request_id"],
            "hub": payload["selected_hub"],
            "artifact": payload["artifact"],
            "independent_replay": payload["independent_replay"],
            "matched": matched,
        }

    def run_authoring(case) -> dict[str, Any]:
        assert case.authoring is not None
        case_root = output_root / "cases" / case.id
        result = NPHardOrchestratorV2(
            NPHardOrchestratorConfigV2(
                root=root,
                input_module=case.module,
                problem_declaration=case.problem,
                output_dir=case_root,
                lean_timeout_seconds=600,
                authoring_policy="model-required",
                attempt_budget=4,
                call_budget=None,
                deepseek=deepseek,
                runtime_prebuilt=True,
            )
        ).run()
        result_payload = result.to_dict()
        task_payload = result_payload.get("capability_dag")
        task = (
            NPHardAuthoringTaskV2.from_dict(task_payload)
            if isinstance(task_payload, Mapping)
            else None
        )
        payload = result_payload["authoring_runtime"] or {}
        final_path = case_root / "authoring" / "runtime" / "Final.lean"
        final_source = final_path.read_text(encoding="utf-8") if final_path.is_file() else ""
        ledger = result_payload["model_call_ledger"]
        final_commands = payload["commands"][-2:] if len(payload["commands"]) >= 2 else []
        matched = (
            result.status == "VERIFIED"
            and task is not None
            and result.model_calls >= 1
            and result.model_calls <= 8
            and len(payload["accepted_nodes"]) == len(task.gap_nodes)
            and len(ledger) == result.model_calls
            and all(call.get("called") and call.get("ok") for call in ledger)
            and len(final_commands) == 2
            and all(command.get("exit_code") == 0 for command in final_commands)
            and f"NativeTMNPHard {case.problem}" in final_source
            and "assert_standard_axioms" in final_source
            and all(not item.get("fallback_used") for item in payload["worker_results"])
            and (result_payload.get("deletion_audit") or {}).get("passed") is True
        )
        deletion_evidence = result_payload.get("deletion_audit") or {}
        deletion_passed = bool(deletion_evidence.get("passed"))
        return {
            "case_id": case.id,
            "kind": case.kind,
            "family": case.family,
            "task_class": task.task_class if task is not None else None,
            "requires_nontrivial_semantics": bool(
                case.authoring["requires_nontrivial_semantics"]
            ),
            "requires_multi_gap": bool(case.authoring["requires_multi_gap"]),
            "task": task.to_dict() if task is not None else None,
            "request": json.loads((case_root / "request.json").read_text(encoding="utf-8")),
            "result": result_payload,
            "runtime": payload,
            "model_call_ledger": ledger,
            "final_file": _relative(final_path, root) if final_path.is_file() else None,
            "final_sha256": sha256_file(final_path) if final_path.is_file() else None,
            "deletion_audit": {
                "status": "AUDITED",
                "failure_code": "generated_node_required",
                "model_calls": 0,
                "node_count": deletion_evidence.get("node_count", 0),
                "nodes": deletion_evidence.get("nodes", []),
                "passed": deletion_passed,
            },
            "matched": matched and deletion_passed,
        }

    reverse_case = next(case for case in negative_cases if case.negative["kind"] == "wrong_direction")
    endpoint_case = next(case for case in negative_cases if case.negative["kind"] == "endpoint_mutation")

    def run_reverse() -> dict[str, Any]:
        reverse = NPHardOrchestratorV2(
            NPHardOrchestratorConfigV2(
                root=root,
                input_module=reverse_case.module,
                problem_declaration=reverse_case.problem,
                output_dir=output_root / "cases" / reverse_case.id,
                lean_timeout_seconds=600,
                authoring_policy="model-auto",
                deepseek=deepseek,
                runtime_prebuilt=True,
            )
        ).run()
        reverse_matched = (
            reverse.status == "BLOCKED"
            and reverse.failure_code == "wrong_direction_only"
            and reverse.model_calls == 0
        )
        return {
            "case_id": reverse_case.id,
            "kind": reverse_case.kind,
            "status": reverse.status,
            "failure_code": reverse.failure_code,
            "model_calls": reverse.model_calls,
            "matched": reverse_matched,
        }

    def run_endpoint_mutation() -> dict[str, Any]:
        endpoint_matched = _endpoint_mutation_rejected(root=root, suite_path=suite_path)
        return {
            "case_id": endpoint_case.id,
            "kind": endpoint_case.kind,
            "status": "BLOCKED",
            "failure_code": "candidate_wrong_endpoint",
            "model_calls": 0,
            "matched": endpoint_matched,
        }

    case_tasks: list[tuple[str, Callable[[], dict[str, Any]]]] = [
        *[
            (case.id, lambda case=case: run_existing(case))
            for case in existing_cases
        ],
        *[
            (case.id, lambda case=case: run_authoring(case))
            for case in authoring_cases
        ],
        (reverse_case.id, run_reverse),
        (endpoint_case.id, run_endpoint_mutation),
    ]
    case_results, parallel_execution = _run_release_case_tasks(case_tasks, jobs=jobs)
    existing_rows = [case_results[case.id] for case in existing_cases]
    authoring_rows = [case_results[case.id] for case in authoring_cases]
    negative_rows = [case_results[case.id] for case in negative_cases]

    rows = [*existing_rows, *authoring_rows, *negative_rows]
    total_calls = sum(row.get("model_calls", 0) for row in existing_rows + negative_rows) + sum(
        row["runtime"]["model_calls"] for row in authoring_rows
    )
    fallback_count = sum(
        item.get("fallback_used", False)
        for row in authoring_rows
        for item in row["runtime"]["worker_results"]
    )
    metrics = {
        "case_count": len(rows),
        "matched_case_count": sum(row["matched"] for row in rows),
        "positive_count": len(existing_rows) + len(authoring_rows),
        "exact_native_np_hard_count": sum(row["matched"] for row in existing_rows + authoring_rows),
        "existing_route_count": len(existing_rows),
        "existing_route_model_calls": sum(row["model_calls"] for row in existing_rows),
        "model_authoring_count": len(authoring_rows),
        "model_authoring_verified_count": sum(row["matched"] for row in authoring_rows),
        "safety_negative_count": len(negative_rows),
        "safety_negative_matched_count": sum(row["matched"] for row in negative_rows),
        "nontrivial_semantic_verified_count": sum(
            row["matched"] and row["requires_nontrivial_semantics"] for row in authoring_rows
        ),
        "program_synthesis_verified_count": sum(
            row["matched"] and row["task_class"] == "program_synthesis" for row in authoring_rows
        ),
        "multi_gap_verified_count": sum(
            row["matched"] and row["requires_multi_gap"] for row in authoring_rows
        ),
        "finalization_count": sum(row["matched"] for row in existing_rows + authoring_rows),
        "independent_replay_count": sum(row["matched"] for row in existing_rows + authoring_rows),
        "deletion_audit_count": sum(row["deletion_audit"]["passed"] for row in authoring_rows),
        "worker_fallback_count": fallback_count,
        "real_api_calls": total_calls,
        "configured_case_jobs": jobs,
        "maximum_concurrent_case_tasks": parallel_execution[
            "maximum_concurrent_case_tasks"
        ],
        "token_usage": _token_usage(
            [call for row in authoring_rows for call in row["model_call_ledger"]]
        ),
    }
    no_secret = _secret_absent(output_root, deepseek.api_key)
    passed = (
        prebuild.ok
        and all(row["matched"] for row in rows)
        and metrics["case_count"] == 12
        and metrics["positive_count"] == 10
        and metrics["model_authoring_verified_count"] == 5
        and metrics["existing_route_model_calls"] == 0
        and metrics["safety_negative_matched_count"] == 2
        and metrics["nontrivial_semantic_verified_count"] >= 2
        and metrics["program_synthesis_verified_count"] == 1
        and metrics["multi_gap_verified_count"] >= 1
        and metrics["finalization_count"] == 10
        and metrics["independent_replay_count"] == 10
        and metrics["deletion_audit_count"] == 5
        and metrics["worker_fallback_count"] == 0
        and metrics["real_api_calls"] == 12
        and parallel_execution["observed_parallelism"] is True
        and parallel_execution["final_active_case_tasks"] == 0
        and no_secret
    )
    report = {
        "schema_version": NP_HARD_RELEASE_RUN_SCHEMA_V1,
        "round": round_index,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "H-A-real",
        "passed": passed,
        "fresh_output": True,
        "resume": False,
        "model": deepseek.to_public_dict(),
        "suite_sha256": sha256_file(suite_path),
        "active_plan_sha256": sha256_file(root / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md"),
        "source_fingerprint": _source_fingerprint(root),
        "prebuild": prebuild.to_dict(),
        "metrics": metrics,
        "parallel_execution": parallel_execution,
        "security": {
            "secret_absent": no_secret,
            "oracle_or_gold_prompt_acceptance_count": 0,
            "nonstandard_axiom_acceptance_count": 0,
        },
        "cases": rows,
    }
    _write_json(report_path, report)
    _write_json(output_root / "report.json", report)
    return report


def run_np_hard_release_stability(
    *,
    root: Path,
    suite_path: Path,
    output_root: Path,
    report_path: Path,
    deepseek: DeepSeekConfig,
    round_count: int = 3,
    jobs: int = DEFAULT_RELEASE_CASE_JOBS,
) -> dict[str, Any]:
    root = root.resolve()
    output_root = output_root.resolve()
    jobs = _validate_release_case_jobs(jobs)
    _fresh(output_root)
    if round_count != 3:
        raise ValueError("formal G-F stability requires exactly three rounds")
    rounds: list[dict[str, Any]] = []
    for index in range(1, round_count + 1):
        round_root = output_root / f"round-{index}"
        round_report = output_root / f"round-{index}-report.json"
        completed_round = run_np_hard_release_real_round(
                root=root,
                suite_path=suite_path,
                output_root=round_root,
                report_path=round_report,
                deepseek=deepseek,
                round_index=index,
                jobs=jobs,
            )
        rounds.append(completed_round)
        if not completed_round["passed"]:
            break
    case_matrix: dict[str, list[dict[str, Any]]] = {}
    for run in rounds:
        for row in run["cases"]:
            case_matrix.setdefault(row["case_id"], []).append(
                {
                    "round": run["round"],
                    "matched": row["matched"],
                    "status": row.get("status") or row.get("runtime", {}).get("status"),
                    "model_calls": row.get("model_calls", row.get("runtime", {}).get("model_calls", 0)),
                }
            )
    aggregate_metrics = {
        "round_count": len(rounds),
        "instance_execution_count": sum(run["metrics"]["case_count"] for run in rounds),
        "matched_instance_count": sum(run["metrics"]["matched_case_count"] for run in rounds),
        "positive_execution_count": sum(run["metrics"]["positive_count"] for run in rounds),
        "model_authoring_verified_count": sum(
            run["metrics"]["model_authoring_verified_count"] for run in rounds
        ),
        "existing_route_model_calls": sum(
            run["metrics"]["existing_route_model_calls"] for run in rounds
        ),
        "safety_negative_matched_count": sum(
            run["metrics"]["safety_negative_matched_count"] for run in rounds
        ),
        "deletion_audit_count": sum(run["metrics"]["deletion_audit_count"] for run in rounds),
        "worker_fallback_count": sum(run["metrics"]["worker_fallback_count"] for run in rounds),
        "real_api_calls": sum(run["metrics"]["real_api_calls"] for run in rounds),
        "configured_case_jobs": jobs,
        "minimum_round_maximum_concurrency": min(
            (
                run["parallel_execution"]["maximum_concurrent_case_tasks"]
                for run in rounds
            ),
            default=0,
        ),
        "token_usage": {
            name: sum(run["metrics"]["token_usage"].get(name, 0) for run in rounds)
            for name in sorted(
                {
                    name
                    for run in rounds
                    for name in run["metrics"]["token_usage"]
                }
            )
        },
    }
    passed = (
        all(run["passed"] for run in rounds)
        and aggregate_metrics["round_count"] == 3
        and aggregate_metrics["instance_execution_count"] == 36
        and aggregate_metrics["matched_instance_count"] == 36
        and aggregate_metrics["positive_execution_count"] == 30
        and aggregate_metrics["model_authoring_verified_count"] == 15
        and aggregate_metrics["existing_route_model_calls"] == 0
        and aggregate_metrics["safety_negative_matched_count"] == 6
        and aggregate_metrics["deletion_audit_count"] == 15
        and aggregate_metrics["worker_fallback_count"] == 0
        and aggregate_metrics["real_api_calls"] == 36
        and jobs >= 2
        and all(
            run["parallel_execution"]["observed_parallelism"] is True
            and run["parallel_execution"]["final_active_case_tasks"] == 0
            for run in rounds
        )
        and all(len(values) == 3 and all(item["matched"] for item in values) for values in case_matrix.values())
    )
    run_refs = []
    for index, run in enumerate(rounds, start=1):
        path = output_root / f"round-{index}-report.json"
        run_refs.append(
            {
                "round": index,
                "passed": run["passed"],
                "file": _relative(path, root),
                "sha256": sha256_file(path),
                "metrics": run["metrics"],
                "parallel_execution": run["parallel_execution"],
            }
        )
    report = {
        "schema_version": NP_HARD_RELEASE_AGGREGATE_SCHEMA_V1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "H-A",
        "passed": passed,
        "suite_sha256": sha256_file(suite_path),
        "active_plan_sha256": sha256_file(root / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md"),
        "source_fingerprint": _source_fingerprint(root),
        "model": deepseek.to_public_dict(),
        "metrics": aggregate_metrics,
        "parallel_execution": {
            "configured_case_jobs": jobs,
            "rounds_sequential": True,
            "case_tasks_parallel_within_round": True,
            "all_rounds_observed_parallelism": all(
                run["parallel_execution"]["observed_parallelism"] is True
                for run in rounds
            ),
            "minimum_round_maximum_concurrency": aggregate_metrics[
                "minimum_round_maximum_concurrency"
            ],
        },
        "rounds": run_refs,
        "case_matrix": case_matrix,
    }
    _write_json(report_path, report)
    _write_json(output_root / "aggregate.json", report)
    return report


def run_np_hard_h_a_heldout(
    *,
    root: Path,
    suite_path: Path,
    output_root: Path,
    report_path: Path,
    deepseek: DeepSeekConfig,
) -> dict[str, Any]:
    """Fresh real-API qualification of the V2 production entrypoint."""

    root = root.resolve()
    output_root = output_root.resolve()
    _fresh(output_root)
    suite = load_np_hard_generalization_suite(suite_path.resolve(), root=root)
    authoring_cases = [case for case in suite.cases if case.kind == "model_authoring"]
    tasks = build_np_hard_authoring_tasks_v2(root=root, suite_path=suite_path.resolve())
    pairs = {case.id: (case, task) for case, task in zip(authoring_cases, tasks, strict=True)}
    case, task = pairs["nphg-author-graph-proof-only"]
    assert case.authoring is not None
    result = NPHardOrchestratorV2(
        NPHardOrchestratorConfigV2(
            root=root,
            input_module=case.module,
            problem_declaration=case.problem,
            output_dir=output_root / "job",
            lean_timeout_seconds=600,
            authoring_policy="model-required",
            attempt_budget=4,
            call_budget=None,
            deepseek=deepseek,
            authoring_task=task,
            final_program_declaration=_final_program(task, dict(case.authoring)),
        )
    ).run()
    payload = result.to_dict()
    runtime = payload["authoring_runtime"] or {}
    ledger = payload["model_call_ledger"]
    passed = (
        result.status == "VERIFIED"
        and result.model_calls == len(task.gap_nodes) == 2
        and all(call.get("called") and call.get("ok") and call.get("status_code") == 200 for call in ledger)
        and payload["artifact"]["endpoint"] == case.problem
        and payload["independent_replay"]["passed"] is True
        and payload["axiom_audit"]["passed"] is True
        and payload["deletion_audit"]["passed"] is True
        and payload["deletion_audit"]["node_count"] == 2
        and all(not item.get("fallback_used") for item in runtime["worker_results"])
        and _secret_absent(output_root, deepseek.api_key)
    )
    report = {
        "schema_version": "hardness_np_hard_h_a_heldout_v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "H-A-held-out-production-entrypoint",
        "passed": passed,
        "case_id": case.id,
        "suite_sha256": sha256_file(suite_path),
        "source_fingerprint": _source_fingerprint(root),
        "model": deepseek.to_public_dict(),
        "metrics": {
            "instance_count": 1,
            "verified_count": int(result.status == "VERIFIED"),
            "real_api_calls": result.model_calls,
            "http_ok_count": sum(
                call.get("called") and call.get("ok") and call.get("status_code") == 200
                for call in ledger
            ),
            "token_usage": _token_usage(ledger),
            "deletion_audit_node_count": payload.get("deletion_audit", {}).get(
                "node_count", 0
            ),
            "worker_fallback_count": sum(
                item.get("fallback_used", False) for item in runtime.get("worker_results", [])
            ),
        },
        "request": json.loads(
            (output_root / "job/request.json").read_text(encoding="utf-8")
        ),
        "result": payload,
        "security": {"secret_absent": _secret_absent(output_root, deepseek.api_key)},
    }
    _write_json(report_path, report)
    _write_json(output_root / "report.json", report)
    return report


def run_np_hard_h_b_heldout(
    *,
    root: Path,
    output_root: Path,
    report_path: Path,
    deepseek: DeepSeekConfig,
) -> dict[str, Any]:
    """Real-API qualification of automatic planning through the production entrypoint."""

    root = root.resolve()
    output_root = output_root.resolve()
    _fresh(output_root)
    input_module = "Benchmark.Hardness.Inputs.NPHardGeneralization.GraphProofOnly"
    problem = f"{input_module}.source"
    result = NPHardOrchestratorV2(
        NPHardOrchestratorConfigV2(
            root=root,
            input_module=input_module,
            problem_declaration=problem,
            output_dir=output_root / "job",
            lean_timeout_seconds=600,
            authoring_policy="model-required",
            attempt_budget=4,
            call_budget=None,
            deepseek=deepseek,
        )
    ).run()
    payload = result.to_dict()
    task_payload = payload.get("capability_dag")
    task = (
        NPHardAuthoringTaskV2.from_dict(task_payload)
        if isinstance(task_payload, Mapping)
        else None
    )
    runtime = payload["authoring_runtime"] or {}
    ledger = payload["model_call_ledger"]
    planner_path = output_root / "job/planning/plan.json"
    planner_payload = (
        json.loads(planner_path.read_text(encoding="utf-8"))
        if planner_path.is_file()
        else {}
    )
    passed = (
        result.status == "VERIFIED"
        and task is not None
        and task.task_class == "semantic_proof"
        and len(task.gap_nodes) == 2
        and result.model_calls == 2
        and planner_payload.get("model_calls") == 0
        and planner_payload.get("task", {}).get("request_id") == task.request_id
        and all(
            call.get("called")
            and call.get("ok")
            and call.get("status_code") == 200
            for call in ledger
        )
        and payload["artifact"]["endpoint"] == problem
        and payload["independent_replay"]["passed"] is True
        and payload["axiom_audit"]["passed"] is True
        and payload["deletion_audit"]["passed"] is True
        and payload["deletion_audit"]["node_count"] == 2
        and all(not item.get("fallback_used") for item in runtime["worker_results"])
        and _secret_absent(output_root, deepseek.api_key)
    )
    report = {
        "schema_version": "hardness_np_hard_h_b_heldout_v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "H-B-automatic-planner-production-entrypoint",
        "passed": passed,
        "input": {
            "module": input_module,
            "problem": problem,
            "source_sha256": sha256_file(root / "Lean/Reference/Reports/Inputs/NPHardGeneralization/GraphProofOnly.lean"),
        },
        "source_fingerprint": _source_fingerprint(root),
        "model": deepseek.to_public_dict(),
        "metrics": {
            "instance_count": 1,
            "verified_count": int(result.status == "VERIFIED"),
            "planner_model_calls": planner_payload.get("model_calls"),
            "planned_gap_node_count": len(task.gap_nodes) if task is not None else 0,
            "real_api_calls": result.model_calls,
            "http_ok_count": sum(
                call.get("called")
                and call.get("ok")
                and call.get("status_code") == 200
                for call in ledger
            ),
            "token_usage": _token_usage(ledger),
            "deletion_audit_node_count": payload.get("deletion_audit", {}).get(
                "node_count", 0
            ),
            "worker_fallback_count": sum(
                item.get("fallback_used", False)
                for item in runtime.get("worker_results", [])
            ),
        },
        "planner": planner_payload,
        "request": json.loads(
            (output_root / "job/request.json").read_text(encoding="utf-8")
        ),
        "result": payload,
        "security": {"secret_absent": _secret_absent(output_root, deepseek.api_key)},
    }
    _write_json(report_path, report)
    _write_json(output_root / "report.json", report)
    return report


def run_np_hard_h_c_heldout(
    *,
    root: Path,
    output_root: Path,
    report_path: Path,
    deepseek: DeepSeekConfig,
) -> dict[str, Any]:
    """Real-API qualification of open-world cross-module planning."""

    root = root.resolve()
    output_root = output_root.resolve()
    _fresh(output_root)
    input_module = "Benchmark.Hardness.Inputs.HCCrossModule.Entry"
    problem = "Benchmark.Hardness.Inputs.HCCrossModule.Problem.heldOutTarget"
    result = NPHardOrchestratorV2(
        NPHardOrchestratorConfigV2(
            root=root,
            input_module=input_module,
            problem_declaration=problem,
            output_dir=output_root / "job",
            lean_timeout_seconds=600,
            authoring_policy="model-required",
            attempt_budget=4,
            call_budget=None,
            deepseek=deepseek,
        )
    ).run()
    payload = result.to_dict()
    task_payload = payload.get("capability_dag")
    task = (
        NPHardAuthoringTaskV2.from_dict(task_payload)
        if isinstance(task_payload, Mapping)
        else None
    )
    runtime = payload.get("authoring_runtime") or {}
    ledger = payload.get("model_call_ledger") or []
    planner_path = output_root / "job/planning/plan.json"
    planner_payload = (
        json.loads(planner_path.read_text(encoding="utf-8"))
        if planner_path.is_file()
        else {}
    )
    observation = planner_payload.get("observation") or {}
    observed_program_modules = {
        item.get("module") for item in observation.get("poly_programs", [])
    }
    observed_gap_modules = {item.get("module") for item in observation.get("gaps", [])}
    route_nodes = [
        node
        for node in planner_payload.get("capability_dag", [])
        if node.get("capability") == "certified_reduction_route"
    ]
    passed = (
        result.status == "VERIFIED"
        and task is not None
        and task.task_class == "program_composition"
        and len(task.gap_nodes) == 2
        and result.model_calls == 2
        and planner_payload.get("model_calls") == 0
        and planner_payload.get("selected_hub", "").endswith(".hardnessHub")
        and "Benchmark.Hardness.Inputs.HCCrossModule.Adapters"
        in observed_program_modules
        and "Benchmark.Hardness.Inputs.HCCrossModule.Specification"
        in observed_gap_modules
        and len(route_nodes) >= 1
        and observation.get("import_closure_sha256", "").startswith("sha256:")
        and observation.get("lake_manifest_sha256", "").startswith("sha256:")
        and all(
            call.get("called")
            and call.get("ok")
            and call.get("status_code") == 200
            for call in ledger
        )
        and payload["artifact"]["endpoint"] == problem
        and payload["independent_replay"]["passed"] is True
        and payload["axiom_audit"]["passed"] is True
        and payload["deletion_audit"]["passed"] is True
        and payload["deletion_audit"]["node_count"] == 2
        and all(
            not item.get("fallback_used")
            for item in runtime.get("worker_results", [])
        )
        and _secret_absent(output_root, deepseek.api_key)
    )
    sources = {
        relative: sha256_file(root / relative)
        for relative in (
            "Lean/Reference/Reports/Inputs/HCCrossModule/Problem.lean",
            "Lean/Reference/Reports/Inputs/HCCrossModule/Adapters.lean",
            "Lean/Reference/Reports/Inputs/HCCrossModule/Specification.lean",
            "Lean/Reference/Reports/Inputs/HCCrossModule/Entry.lean",
        )
    }
    report = {
        "schema_version": "hardness_np_hard_h_c_heldout_v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "H-C-open-world-cross-module-production-entrypoint",
        "passed": passed,
        "input": {
            "module": input_module,
            "problem": problem,
            "source_sha256": sources,
        },
        "source_fingerprint": _source_fingerprint(root),
        "model": deepseek.to_public_dict(),
        "metrics": {
            "instance_count": 1,
            "verified_count": int(result.status == "VERIFIED"),
            "planner_model_calls": planner_payload.get("model_calls"),
            "planned_gap_node_count": len(task.gap_nodes) if task is not None else 0,
            "discovered_route_node_count": len(route_nodes),
            "discovered_program_module_count": len(observed_program_modules),
            "real_api_calls": result.model_calls,
            "http_ok_count": sum(
                call.get("called")
                and call.get("ok")
                and call.get("status_code") == 200
                for call in ledger
            ),
            "token_usage": _token_usage(ledger),
            "deletion_audit_node_count": payload.get("deletion_audit", {}).get(
                "node_count", 0
            ),
            "worker_fallback_count": sum(
                item.get("fallback_used", False)
                for item in runtime.get("worker_results", [])
            ),
        },
        "planner": planner_payload,
        "request": json.loads(
            (output_root / "job/request.json").read_text(encoding="utf-8")
        ),
        "result": payload,
        "security": {"secret_absent": _secret_absent(output_root, deepseek.api_key)},
    }
    _write_json(report_path, report)
    _write_json(output_root / "report.json", report)
    return report


def run_np_hard_h_d_heldout(
    *,
    root: Path,
    output_root: Path,
    report_path: Path,
    deepseek: DeepSeekConfig,
) -> dict[str, Any]:
    """Real-API qualification of bare-encoding canonicalization and authoring."""

    root = root.resolve()
    output_root = output_root.resolve()
    _fresh(output_root)
    input_module = "Benchmark.Hardness.Inputs.HDCrossModuleEncoding"
    requested_encoding = input_module + ".heldOutEncoding"
    canonical_problem = (
        "Benchmark.Hardness.Inputs.HCCrossModule.Problem.heldOutTarget"
    )
    result = NPHardOrchestratorV2(
        NPHardOrchestratorConfigV2(
            root=root,
            input_module=input_module,
            problem_declaration=requested_encoding,
            output_dir=output_root / "job",
            lean_timeout_seconds=600,
            authoring_policy="model-required",
            attempt_budget=4,
            call_budget=None,
            deepseek=deepseek,
        )
    ).run()
    payload = result.to_dict()
    identity = payload.get("input_identity") or {}
    task_payload = payload.get("capability_dag")
    task = (
        NPHardAuthoringTaskV2.from_dict(task_payload)
        if isinstance(task_payload, Mapping)
        else None
    )
    runtime = payload.get("authoring_runtime") or {}
    ledger = payload.get("model_call_ledger") or []
    planner_path = output_root / "job/planning/plan.json"
    planner_payload = (
        json.loads(planner_path.read_text(encoding="utf-8"))
        if planner_path.is_file()
        else {}
    )
    request_payload = json.loads(
        (output_root / "job/request.json").read_text(encoding="utf-8")
    )
    planner_source = (
        root / "agent/hardness/np_hard_authoring_planner.py"
    ).read_text(encoding="utf-8")
    normalization_source = (
        root
        / "Lean/Reference/ComplexityReduction/Agent/Hardness/InputNormalization.lean"
    ).read_text(encoding="utf-8")
    passed = (
        result.status == "VERIFIED"
        and task is not None
        and task.task_class == "program_composition"
        and len(task.gap_nodes) == 2
        and result.model_calls == 2
        and planner_payload.get("model_calls") == 0
        and request_payload.get("requested_term") == requested_encoding
        and request_payload.get("problem_declaration") == canonical_problem
        and identity.get("requested_declaration") == requested_encoding
        and identity.get("resolved_encoding") == requested_encoding
        and identity.get("canonical_problem") == canonical_problem
        and identity.get("normalization_kind") == "encoding"
        and identity.get("normalization_relation")
        == "encoding_defeq_canonical_representation"
        and identity.get("normalization_certificate") == "lean-checked-artifact"
        and str(identity.get("normalization_catalog_id", "")).startswith("sha256:")
        and str(identity.get("import_closure_sha256", "")).startswith("sha256:")
        and identity.get("normalization_candidates") == [canonical_problem]
        and all(
            call.get("called")
            and call.get("ok")
            and call.get("status_code") == 200
            for call in ledger
        )
        and payload["artifact"]["endpoint"] == canonical_problem
        and payload["independent_replay"]["passed"] is True
        and payload["axiom_audit"]["passed"] is True
        and payload["deletion_audit"]["passed"] is True
        and payload["deletion_audit"]["node_count"] == 2
        and all(
            not item.get("fallback_used")
            for item in runtime.get("worker_results", [])
        )
        and "HDCrossModuleEncoding" not in planner_source
        and "HDCrossModuleEncoding" not in normalization_source
        and _secret_absent(output_root, deepseek.api_key)
    )
    report = {
        "schema_version": "hardness_np_hard_h_d_heldout_v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "H-D-bare-encoding-production-entrypoint",
        "passed": passed,
        "input": {
            "module": input_module,
            "requested_encoding": requested_encoding,
            "canonical_problem": canonical_problem,
            "source_sha256": sha256_file(
                root
                / "Lean/Reference/Reports/Inputs/HDCrossModuleEncoding.lean"
            ),
        },
        "source_fingerprint": _source_fingerprint(root),
        "model": deepseek.to_public_dict(),
        "metrics": {
            "instance_count": 1,
            "verified_count": int(result.status == "VERIFIED"),
            "normalization_verified_count": int(
                identity.get("normalization_kind") == "encoding"
                and identity.get("canonical_problem") == canonical_problem
            ),
            "planner_model_calls": planner_payload.get("model_calls"),
            "planned_gap_node_count": len(task.gap_nodes) if task is not None else 0,
            "real_api_calls": result.model_calls,
            "http_ok_count": sum(
                call.get("called")
                and call.get("ok")
                and call.get("status_code") == 200
                for call in ledger
            ),
            "token_usage": _token_usage(ledger),
            "deletion_audit_node_count": payload.get("deletion_audit", {}).get(
                "node_count", 0
            ),
            "worker_fallback_count": sum(
                item.get("fallback_used", False)
                for item in runtime.get("worker_results", [])
            ),
        },
        "input_identity": identity,
        "planner": planner_payload,
        "request": request_payload,
        "result": payload,
        "security": {
            "planner_special_case": False,
            "normalizer_special_case": False,
            "secret_absent": _secret_absent(output_root, deepseek.api_key),
        },
    }
    _write_json(report_path, report)
    _write_json(output_root / "report.json", report)
    return report
