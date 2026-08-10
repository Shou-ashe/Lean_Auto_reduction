"""Frozen hardness benchmark runner for the direct one-shot LLM control."""

from __future__ import annotations

import hashlib
import json
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Mapping, Sequence

from agent.hardness.archon_blackbox_benchmark import (
    FORBIDDEN_BODY_RE,
    OBVIOUS_COMPOSITION_RE,
    REGISTRY_BENCHMARK_ID,
    ArchonBenchmarkCase,
    _command_evidence,
    _load_baseline_metrics,
    _load_postrun_policy,
    _public_goal_preflight_source,
    _verification_source,
    load_archon_benchmark_cases,
)
from agent.hardness.archon_runner import render_public_case_material
from agent.hardness.lean_runner import run_command
from agent.hardness.model_client import DeepSeekConfig
from agent.hardness.np_hard_production import is_formal_np_hard_qualification_config

from .client import OneShotLLMClient


SCHEMA_VERSION = "hardness_oneshot_llm_benchmark_v1"
CASE_SCHEMA_VERSION = "hardness_oneshot_llm_case_v1"
PUBLIC_INPUT_KEYS = {
    "case_id",
    "kind",
    "split",
    "statement",
    "requirement",
    "formal_goal",
}


def _sha256_text(value: str) -> str:
    return "sha256:" + hashlib.sha256(value.encode("utf-8")).hexdigest()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return "sha256:" + digest.hexdigest()


def _read_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        value = json.load(handle)
    if not isinstance(value, dict):
        raise ValueError(f"expected one JSON object in {path}")
    return value


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _public_input_is_clean(public_input: Mapping[str, Any]) -> bool:
    if set(public_input) != PUBLIC_INPUT_KEYS:
        return False
    serialized = json.dumps(public_input, ensure_ascii=False, sort_keys=True).lower()
    return not any(
        token in serialized
        for token in (
            "recommended_first_body",
            "recommended_proof",
            "oracle",
            "gold",
            "typed_dag",
            "dependency_body",
            "lean_diagnostic",
        )
    )


def _run_case(
    *,
    root: Path,
    output_root: Path,
    case: ArchonBenchmarkCase,
    client: OneShotLLMClient,
    lean_timeout_seconds: int,
) -> dict[str, Any]:
    started = time.monotonic()
    case_dir = output_root / "cases" / case.case_id
    case_dir.mkdir(parents=True, exist_ok=True)
    public_input = case.public_input()
    public_input_file = case_dir / "llm-input.json"
    _write_json(public_input_file, public_input)

    public_goal_file = case_dir / "PublicGoalPreflight.lean"
    public_goal_file.write_text(_public_goal_preflight_source(case), encoding="utf-8")
    public_goal_preflight = run_command(
        ["lake", "env", "lean", str(public_goal_file)],
        cwd=root / "Lean",
        timeout_seconds=lean_timeout_seconds,
    )
    if not public_goal_preflight.ok:
        row = {
            "schema_version": CASE_SCHEMA_VERSION,
            "ordinal": case.ordinal,
            "case_id": case.case_id,
            "kind": case.kind,
            "split": case.split,
            "statement_sha256": _sha256_text(case.statement),
            "public_input_file": str(public_input_file.resolve()),
            "public_input_sha256": _sha256_file(public_input_file),
            "public_material_sha256": None,
            "status": "BLOCKED_INPUT",
            "kernel_verified": False,
            "proof_sha256": None,
            "forbidden_token": None,
            "llm": {
                "called": False,
                "ok": False,
                "error": "public formal goal does not elaborate",
                "duration_seconds": 0.0,
                "usage": None,
                "status_code": None,
                "attempts": 0,
                "finish_reason": None,
                "prompt_sha256": None,
                "response_sha256": None,
            },
            "isolation": {
                "passed": _public_input_is_clean(public_input),
                "same_public_input_contract_as_archon": True,
                "shared_public_material_renderer": True,
                "single_api_request": True,
                "tools_enabled": False,
                "complexity_reduction_source_visible": False,
                "benchmark_recommendation_visible": False,
                "oracle_visible": False,
                "typed_dag_visible": False,
                "previous_diagnostics_visible": False,
                "compiled_dependencies": "not opened because the public goal failed",
            },
            "verification": {
                "public_goal_preflight": _command_evidence(public_goal_preflight),
            },
            "case_dir": str(case_dir.resolve()),
            "wall_duration_seconds": round(time.monotonic() - started, 3),
        }
        _write_json(case_dir / "result.json", row)
        return row

    material = render_public_case_material(
        case_id=case.case_id,
        statement=case.statement,
        requirement=case.requirement,
        imports=case.imports,
        exact_type=case.exact_type,
    )
    (case_dir / "USER_HINTS.md").write_text(material.user_hints, encoding="utf-8")
    (case_dir / "FormalGoal.lean").write_text(
        material.objective_source,
        encoding="utf-8",
    )
    attempt = client.complete(material)
    (case_dir / "prompt.txt").write_text(attempt.prompt, encoding="utf-8")
    (case_dir / "response.txt").write_text(attempt.raw_response, encoding="utf-8")

    body = attempt.body
    proof_sha256 = _sha256_text(body) if body is not None else None
    forbidden_token = None
    verification: dict[str, Any] = {}
    if body is not None:
        (case_dir / "ProofBody.txt").write_text(body + "\n", encoding="utf-8")
        match = FORBIDDEN_BODY_RE.search(body)
        forbidden_token = match.group(0) if match else None
        if forbidden_token is None:
            namespace, verify_source = _verification_source(case, body)
            verify_file = case_dir / "Verify.lean"
            replay_file = case_dir / "Replay.lean"
            verify_file.write_text(verify_source, encoding="utf-8")
            replay_file.write_text(verify_source, encoding="utf-8")
            kernel = run_command(
                ["lake", "env", "lean", str(verify_file)],
                cwd=root / "Lean",
                timeout_seconds=lean_timeout_seconds,
            )
            replay = run_command(
                ["lake", "env", "lean", str(replay_file)],
                cwd=root / "Lean",
                timeout_seconds=lean_timeout_seconds,
            )
            verification = {
                "namespace": namespace,
                "kernel_and_axiom": _command_evidence(kernel),
                "independent_replay": _command_evidence(replay),
                "source_sha256": _sha256_file(verify_file),
            }

    kernel_ok = bool(
        verification.get("kernel_and_axiom", {}).get("ok") is True
        and verification.get("independent_replay", {}).get("ok") is True
    )
    isolation_ok = bool(
        _public_input_is_clean(public_input)
        and attempt.called
        and attempt.attempts == 1
        and "recommended" not in material.user_hints.lower()
    )
    status = (
        "VERIFIED"
        if kernel_ok and isolation_ok
        else "FAILED_MODEL"
        if body is None
        else "FAILED_LEAN"
    )
    row = {
        "schema_version": CASE_SCHEMA_VERSION,
        "ordinal": case.ordinal,
        "case_id": case.case_id,
        "kind": case.kind,
        "split": case.split,
        "statement_sha256": _sha256_text(case.statement),
        "public_input_file": str(public_input_file.resolve()),
        "public_input_sha256": _sha256_file(public_input_file),
        "public_material_sha256": attempt.public_material_sha256,
        "status": status,
        "kernel_verified": kernel_ok,
        "proof_sha256": proof_sha256,
        "forbidden_token": forbidden_token,
        "llm": {
            "called": attempt.called,
            "ok": attempt.ok,
            "error": attempt.error,
            "duration_seconds": attempt.duration_seconds,
            "usage": attempt.usage,
            "status_code": attempt.status_code,
            "attempts": attempt.attempts,
            "finish_reason": attempt.finish_reason,
            "prompt_sha256": attempt.prompt_sha256,
            "response_sha256": attempt.response_sha256,
        },
        "isolation": {
            "passed": isolation_ok,
            "same_public_input_contract_as_archon": True,
            "shared_public_material_renderer": True,
            "single_api_request": attempt.attempts == 1,
            "tools_enabled": False,
            "complexity_reduction_source_visible": False,
            "benchmark_recommendation_visible": False,
            "oracle_visible": False,
            "typed_dag_visible": False,
            "previous_diagnostics_visible": False,
            "compiled_dependencies": "trusted post-response Lean verification only",
        },
        "verification": {
            "public_goal_preflight": _command_evidence(public_goal_preflight),
            **verification,
        },
        "case_dir": str(case_dir.resolve()),
        "wall_duration_seconds": round(time.monotonic() - started, 3),
    }
    _write_json(case_dir / "result.json", row)
    return row


def _apply_postrun_policy(
    rows: list[dict[str, Any]],
    *,
    capability_policy: Mapping[str, Any],
    exact_policy: Mapping[str, Any],
) -> None:
    """Open scorer-only data only after every direct LLM request has finished."""

    for row in rows:
        body_file = Path(str(row["case_dir"])) / "ProofBody.txt"
        body = body_file.read_text(encoding="utf-8") if body_file.is_file() else ""
        if row["kind"] in {"capability", "frontier"}:
            policy = capability_policy.get(row["case_id"])
            scored = bool(isinstance(policy, Mapping) and policy.get("scored") is True)
            row["postrun_policy"] = {
                "scored": scored,
                "eligible": scored,
                "expected_public_status": (
                    policy.get("expected_public_status")
                    if isinstance(policy, Mapping)
                    else None
                ),
                "verified_at_budget": bool(row["kernel_verified"]) if scored else None,
                "opened_after_llm_completed": True,
            }
        else:
            policy = exact_policy.get(row["case_id"])
            ready = bool(isinstance(policy, Mapping) and policy.get("status") == "ready")
            issues: list[str] = []
            if ready and not row["kernel_verified"]:
                issues.append("kernel_or_replay_failed")
            if ready and isinstance(policy, Mapping) and row["kernel_verified"]:
                existing_route = policy.get("existing_route")
                if isinstance(existing_route, str) and existing_route not in body:
                    issues.append("expected_existing_route_not_observed")
                for prefix in policy.get("forbidden_route_imports") or []:
                    if isinstance(prefix, str) and prefix in body:
                        issues.append("forbidden_route_reference")
                if policy.get("allow_composition") is False and OBVIOUS_COMPOSITION_RE.search(body):
                    issues.append("forbidden_composition")
            row["postrun_policy"] = {
                "scored": ready,
                "eligible": ready,
                "oracle_status": policy.get("status") if isinstance(policy, Mapping) else None,
                "verified_at_budget": (
                    bool(row["kernel_verified"] and not issues) if ready else None
                ),
                "issues": sorted(set(issues)),
                "opened_after_llm_completed": True,
            }
        _write_json(Path(str(row["case_dir"])) / "result.json", row)


def _sum_usage(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    totals: dict[str, int | float] = {}
    for row in rows:
        llm = row.get("llm")
        usage = llm.get("usage") if isinstance(llm, Mapping) else None
        if not isinstance(usage, Mapping):
            continue
        for key in (
            "prompt_tokens",
            "completion_tokens",
            "total_tokens",
            "prompt_cache_hit_tokens",
            "prompt_cache_miss_tokens",
            "direct_llm_requests",
        ):
            value = usage.get(key)
            if isinstance(value, int) and not isinstance(value, bool):
                totals[key] = int(totals.get(key, 0)) + value
        cost = usage.get("estimated_cost_usd")
        if isinstance(cost, (int, float)) and not isinstance(cost, bool):
            totals["estimated_cost_usd"] = round(
                float(totals.get("estimated_cost_usd", 0.0)) + float(cost), 9
            )
    return dict(totals)


def _lane_metrics(rows: Sequence[Mapping[str, Any]], lane: str) -> dict[str, Any]:
    selected = [row for row in rows if row.get("kind") == lane]
    eligible = [
        row
        for row in selected
        if isinstance(row.get("postrun_policy"), Mapping)
        and row["postrun_policy"].get("eligible") is True
    ]
    policy_verified = [
        row
        for row in eligible
        if row["postrun_policy"].get("verified_at_budget") is True
    ]
    return {
        "case_count": len(selected),
        "model_called_count": sum(
            isinstance(row.get("llm"), Mapping) and row["llm"].get("called") is True
            for row in selected
        ),
        "blocked_input_count": sum(row.get("status") == "BLOCKED_INPUT" for row in selected),
        "kernel_verified_count": sum(row.get("kernel_verified") is True for row in selected),
        "kernel_verified_rate": (
            sum(row.get("kernel_verified") is True for row in selected) / len(selected)
            if selected
            else None
        ),
        "eligible_count": len(eligible),
        "policy_verified_count": len(policy_verified),
        "policy_verified_rate": len(policy_verified) / len(eligible) if eligible else None,
        "usage": _sum_usage(selected),
    }


def _archon_comparison(
    *,
    archon_report_path: Path | None,
    rows: Sequence[Mapping[str, Any]],
    model_config: DeepSeekConfig,
) -> dict[str, Any] | None:
    if archon_report_path is None or not archon_report_path.is_file():
        return None
    report = _read_json(archon_report_path)
    archon_cases = {
        str(row.get("case_id")): row
        for row in report.get("cases") or []
        if isinstance(row, Mapping)
    }
    mismatches: list[str] = []
    matches = 0
    for row in rows:
        archon = archon_cases.get(str(row["case_id"]))
        if isinstance(archon, Mapping) and (
            archon.get("public_input_sha256") == row.get("public_input_sha256")
        ):
            matches += 1
        else:
            mismatches.append(str(row["case_id"]))
    return {
        "file": str(archon_report_path.resolve()),
        "run_valid": report.get("run_valid"),
        "model_configuration_matches": (
            report.get("model_configuration") == model_config.to_public_dict()
        ),
        "public_input_match_count": matches,
        "public_input_case_count": len(rows),
        "public_input_mismatches": mismatches,
        "metrics": report.get("metrics"),
        "usage": report.get("usage"),
    }


def run_oneshot_llm_benchmark(
    *,
    root: Path,
    output_root: Path,
    model_config: DeepSeekConfig,
    jobs: int = 4,
    lean_timeout_seconds: int = 600,
    lanes: Sequence[str] | None = None,
    selected_case_ids: Sequence[str] | None = None,
    baseline_root: Path | None = None,
    archon_report_path: Path | None = None,
    preflight: bool = True,
) -> dict[str, Any]:
    if not 1 <= jobs <= 4:
        raise ValueError("jobs must be in 1..4")
    if not model_config.api_key:
        raise ValueError("real API run requires DEEPSEEK_API_KEY")
    if not is_formal_np_hard_qualification_config(model_config):
        raise ValueError("one-shot LLM must use the formal production/Archon model profile")
    root = root.resolve()
    output_root = output_root.resolve()
    if output_root.exists() and any(output_root.iterdir()):
        raise ValueError(f"output root must be new or empty: {output_root}")
    output_root.mkdir(parents=True, exist_ok=True)

    cases = load_archon_benchmark_cases(
        root=root,
        lanes=lanes,
        selected_case_ids=selected_case_ids,
    )
    if not cases:
        raise ValueError("benchmark selection is empty")

    preflight_evidence: dict[str, Any] | None = None
    if preflight:
        command = run_command(
            ["lake", "build", "ComplexityReduction", "Benchmark"],
            cwd=root / "Lean",
            timeout_seconds=max(lean_timeout_seconds, 1800),
        )
        preflight_evidence = _command_evidence(command)
        _write_json(output_root / "preflight.json", preflight_evidence)
        if not command.ok:
            raise ValueError("Lean preflight failed; see preflight.json")

    client = OneShotLLMClient(model_config)
    activity_lock = threading.Lock()
    active = 0
    peak = 0
    completed = 0
    started = time.monotonic()

    def execute(case: ArchonBenchmarkCase) -> dict[str, Any]:
        nonlocal active, peak, completed
        with activity_lock:
            active += 1
            peak = max(peak, active)
        try:
            return _run_case(
                root=root,
                output_root=output_root,
                case=case,
                client=client,
                lean_timeout_seconds=lean_timeout_seconds,
            )
        finally:
            with activity_lock:
                active -= 1
                completed += 1

    rows: list[dict[str, Any]] = []
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = {pool.submit(execute, case): case for case in cases}
        for future in as_completed(futures):
            rows.append(future.result())
    rows.sort(key=lambda row: int(row["ordinal"]))

    capability_policy, exact_policy = _load_postrun_policy(root)
    _apply_postrun_policy(
        rows,
        capability_policy=capability_policy,
        exact_policy=exact_policy,
    )
    metrics = {
        lane: _lane_metrics(rows, lane)
        for lane in ("capability", "frontier", "exact_edge")
        if any(row["kind"] == lane for row in rows)
    }
    archon_comparison = _archon_comparison(
        archon_report_path=(
            archon_report_path.resolve() if archon_report_path is not None else None
        ),
        rows=rows,
        model_config=model_config,
    )
    run_valid = all(row["isolation"]["passed"] is True for row in rows)
    if archon_comparison is not None:
        run_valid = bool(
            run_valid
            and archon_comparison["model_configuration_matches"] is True
            and not archon_comparison["public_input_mismatches"]
        )
    report = {
        "schema_version": SCHEMA_VERSION,
        "benchmark_id": REGISTRY_BENCHMARK_ID,
        "agent": "compare/OneShotLLM",
        "run_valid": run_valid,
        "real_api_called": any(
            isinstance(row.get("llm"), Mapping) and row["llm"].get("called") is True
            for row in rows
        ),
        "model_configuration": model_config.to_public_dict(),
        "input_contract": {
            "visible_to_llm": [
                "public problem statement",
                "formal Lean goal",
                "proof-kind requirement",
            ],
            "hidden_from_llm": [
                "ComplexityReduction source files",
                "benchmark recommended proof body",
                "oracle and gold material",
                "typed DAG and route selection",
                "dependency proof bodies",
                "previous Lean diagnostics",
                "previous cases and worker state",
            ],
            "same_public_material_renderer_as_archon": True,
            "interaction": "one chat-completions request; no tools or follow-up",
            "compiled_dependencies": "trusted post-response Lean verification only",
        },
        "parallelism": {
            "configured_jobs": jobs,
            "observed_peak_active_cases": peak,
            "completed_cases": completed,
            "final_active_cases": active,
        },
        "one_shot": {
            "requests_per_model_called_case": 1,
            "tools": False,
            "reviewer": False,
            "compiler_feedback": False,
        },
        "preflight": preflight_evidence,
        "metrics": metrics,
        "usage": _sum_usage(rows),
        "production_baseline": _load_baseline_metrics(
            baseline_root.resolve() if baseline_root is not None else None
        ),
        "archon_comparison": archon_comparison,
        "cases": rows,
        "output_root": str(output_root),
        "wall_duration_seconds": round(time.monotonic() - started, 3),
    }
    _write_json(output_root / "report.json", report)
    return report


__all__ = ["run_oneshot_llm_benchmark"]
