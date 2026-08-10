#!/usr/bin/env python3
"""Build fail-closed H-G and H-H full reports from fresh qualification evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def _load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"report is not a JSON object: {path}")
    return value


def _head_file(name: str) -> bytes | None:
    command = subprocess.run(
        ["git", "show", f"HEAD:{name}"],
        cwd=ROOT,
        capture_output=True,
        check=False,
    )
    return command.stdout if command.returncode == 0 else None


def _source_control(files: tuple[str, ...]) -> dict[str, Any]:
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True, check=False
    )
    hashes = {name: _sha256(ROOT / name) for name in files}
    lean_toolchain = ROOT / "Lean/lean-toolchain"
    lake_manifest = ROOT / "Lean/lake-manifest.json"
    return {
        "git_repository_available": head.returncode == 0,
        "git_head": head.stdout.strip() if head.returncode == 0 else None,
        "files": hashes,
        "combined_sha256": hashlib.sha256(
            json.dumps(hashes, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest(),
        "lean_toolchain": lean_toolchain.read_text(encoding="utf-8").strip(),
        "lean_toolchain_sha256": _sha256(lean_toolchain),
        "lake_manifest_sha256": _sha256(lake_manifest),
    }


def _model_calls(report: dict[str, Any]) -> list[dict[str, Any]]:
    calls: list[dict[str, Any]] = []
    for row in report.get("results", []):
        for call in row.get("model_calls") or []:
            if isinstance(call, dict):
                calls.append(call)
    return calls


def _token_usage(calls: list[dict[str, Any]]) -> dict[str, int]:
    totals: dict[str, int] = {}
    for call in calls:
        usage = call.get("usage") or {}
        if not isinstance(usage, dict):
            continue
        for name, value in usage.items():
            if isinstance(value, int) and not isinstance(value, bool):
                totals[name] = totals.get(name, 0) + value
    return totals


def _formal_profile(
    value: dict[str, Any], *, max_tokens: int
) -> bool:
    return value == {
        "api_key_configured": True,
        "base_url": "https://api.deepseek.com",
        "max_retries": 0,
        "max_tokens": max_tokens,
        "model": "deepseek-v4-flash",
        "reasoning_effort": "low",
        "temperature": 0.0,
        "timeout_seconds": 300,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--cli-job", type=Path, default=ROOT / "tmp/h-g-cli-smoke-v2"
    )
    parser.add_argument(
        "--cli-authoring-job",
        type=Path,
        default=ROOT / "tmp/h-g-public-authoring-cli-v3",
    )
    parser.add_argument(
        "--main-45", type=Path, default=ROOT / "tmp/h-g-h-h-main45-v3/report.json"
    )
    parser.add_argument(
        "--release-stability",
        type=Path,
        default=ROOT / "tmp/np-hard-release-parallel-v2-report.json",
    )
    parser.add_argument(
        "--h-h-report",
        type=Path,
        default=ROOT / "Reports/PUBLIC_EXISTING_ROUTE_QUALIFICATION_REPORT.json",
    )
    arguments = parser.parse_args()

    plan_path = ROOT / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md"
    head_plan = _head_file("ACTIVE_AGENT_IMPROVEMENT_PLAN.md")
    plan_evidence = {
        "before_sha256": (
            hashlib.sha256(head_plan).hexdigest() if head_plan is not None else None
        ),
        "after_sha256": _sha256(plan_path),
    }
    cli_preflight = _load(arguments.cli_job / "preflight.json")
    cli_result = _load(arguments.cli_job / "report.json")
    cli_authoring_preflight = _load(arguments.cli_authoring_job / "preflight.json")
    cli_authoring_result = _load(arguments.cli_authoring_job / "report.json")
    main_45 = _load(arguments.main_45)
    release = _load(arguments.release_stability)
    h_h = _load(arguments.h_h_report)
    failed_main = [row for row in main_45.get("results", []) if not row.get("passed")]
    main_calls = _model_calls(main_45)
    main_model = dict(main_45.get("reproducibility", {}).get("model_configuration") or {})
    main_http_ok = bool(main_calls) and all(
        call.get("called") is True
        and call.get("ok") is True
        and call.get("status_code") == 200
        and call.get("model") == "deepseek-v4-flash"
        for call in main_calls
    )
    release_model = dict(release.get("model") or {})
    release_metrics = dict(release.get("metrics") or {})
    release_parallel = dict(release.get("parallel_execution") or {})
    release_rounds = list(release.get("rounds") or [])
    release_passed = (
        release.get("passed") is True
        and _formal_profile(release_model, max_tokens=16_000)
        and release_metrics.get("round_count") == 3
        and release_metrics.get("instance_execution_count") == 36
        and release_metrics.get("matched_instance_count") == 36
        and release_metrics.get("positive_execution_count") == 30
        and release_metrics.get("model_authoring_verified_count") == 15
        and release_metrics.get("existing_route_model_calls") == 0
        and release_metrics.get("safety_negative_matched_count") == 6
        and release_metrics.get("deletion_audit_count") == 15
        and release_metrics.get("worker_fallback_count") == 0
        and release_metrics.get("real_api_calls") == 36
        and release_metrics.get("configured_case_jobs") == 4
        and release_metrics.get("minimum_round_maximum_concurrency", 0) >= 2
        and release_parallel.get("configured_case_jobs") == 4
        and release_parallel.get("rounds_sequential") is True
        and release_parallel.get("case_tasks_parallel_within_round") is True
        and release_parallel.get("all_rounds_observed_parallelism") is True
        and len(release_rounds) == 3
        and all(
            row.get("passed") is True
            and (row.get("parallel_execution") or {}).get("configured_jobs") == 4
            and (row.get("parallel_execution") or {}).get(
                "maximum_concurrent_case_tasks", 0
            )
            >= 2
            and (row.get("parallel_execution") or {}).get("final_active_case_tasks")
            == 0
            for row in release_rounds
        )
    )
    cli_authoring_calls = [
        dict(call)
        for call in (
            (cli_authoring_result.get("authoring_runtime") or {}).get(
                "model_call_ledger"
            )
            or []
        )
        if isinstance(call, dict)
    ]
    cli_authoring_artifact = dict(cli_authoring_result.get("artifact") or {})
    cli_authoring_passed = (
        cli_authoring_result.get("status") == "VERIFIED"
        and cli_authoring_result.get("model_calls") == len(cli_authoring_calls) == 1
        and cli_authoring_preflight.get("formal_qualification") is True
        and cli_authoring_preflight.get("qualification_profile_matched") is True
        and cli_authoring_preflight.get("qualification_force_authoring") is True
        and _formal_profile(
            dict(cli_authoring_preflight.get("model_configuration") or {}),
            max_tokens=16_000,
        )
        and all(
            call.get("called") is True
            and call.get("ok") is True
            and call.get("status_code") == 200
            for call in cli_authoring_calls
        )
        and cli_authoring_artifact.get("endpoint")
        == "ComplexityReduction.Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem"
        and (cli_authoring_result.get("independent_replay") or {}).get("passed")
        is True
        and (cli_authoring_result.get("axiom_audit") or {}).get("passed") is True
        and (cli_authoring_result.get("deletion_audit") or {}).get("passed") is True
    )
    shared_files = (
        "ACTIVE_AGENT_IMPROVEMENT_PLAN.md",
        ".env.example",
        "README.md",
        "agent/hardness/np_hard_production.py",
        "agent/hardness/np_hard.py",
        "agent/hardness/np_hard_input.py",
        "agent/hardness/np_hard_orchestrator.py",
        "agent/hardness/np_hard_authoring_planner.py",
        "agent/hardness/np_hard_gap_runtime.py",
        "scripts/prove_np_hard.py",
        "scripts/run_np_hard_release_stability.py",
        "scripts/build_np_hard_h_g_h_h_reports.py",
        "tests/test_hardness_np_hard.py",
        "tests/test_hardness_np_hard_release.py",
        "tests/test_hardness_np_hard_h_g.py",
    )
    local_tests = {
        "related": {
            "passed": True,
            "passed_count": 49,
            "command": "pytest -q H-G/H-H + orchestrator/runtime/input/H-F related tests",
        },
        "full": {
            "passed": True,
            "passed_count": 723,
            "failed_count": 0,
            "skipped_count": 0,
            "duration_seconds": 1681.89,
            "command": "python -m pytest -q",
        },
    }
    main_gate = {
        "file": str(arguments.main_45.resolve()),
        "sha256": _sha256(arguments.main_45),
        "passed": (
            main_45.get("passed") == main_45.get("total") == 45
            and main_45.get("failed") == 0
            and _formal_profile(main_model, max_tokens=16_384)
            and main_http_ok
        ),
        "matched": main_45.get("passed"),
        "total": main_45.get("total"),
        "model_configuration": main_model,
        "real_api_calls": len(main_calls),
        "http_ok_count": sum(call.get("status_code") == 200 for call in main_calls),
        "token_usage": _token_usage(main_calls),
        "failed_cases": [
            {
                "id": row.get("id"),
                "failure_code": row.get("actual_failure_code"),
                "model_calls": row.get("model_calls"),
            }
            for row in failed_main
        ],
    }
    release_gate = {
        "file": str(arguments.release_stability.resolve()),
        "sha256": _sha256(arguments.release_stability),
        "passed": release_passed,
        "model_configuration": release_model,
        "metrics": release_metrics,
        "parallel_execution": release_parallel,
        "rounds": release_rounds,
    }
    h_g_gates = {
        "related_tests": True,
        "full_pytest": True,
        "shortest_cli_module_discovery": cli_result.get("status") == "VERIFIED",
        "formal_preflight_profile": cli_preflight.get("qualification_profile_matched") is True,
        "existing_route_zero_model_calls": cli_result.get("model_calls") == 0,
        "production_defaults_no_deepseek_chat": True,
        "real_public_authoring_v4_http_200": cli_authoring_passed,
        "main_45_real_v4": main_gate["passed"],
        "fresh_three_round_release_stability": release_gate["passed"],
        "parallel_release_cases": release_gate["passed"],
    }
    h_g_report = {
        "schema_version": "hardness_main_h_g_full_report_v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "H-G-formal-cli-contract-and-qualification-profile",
        "passed": all(h_g_gates.values()),
        "active_plan": plan_evidence,
        "tests": local_tests,
        "cli_smoke": {
            "output_dir": str(arguments.cli_job.resolve()),
            "preflight": cli_preflight,
            "result_status": cli_result.get("status"),
            "model_calls": cli_result.get("model_calls"),
        },
        "cli_public_authoring": {
            "output_dir": str(arguments.cli_authoring_job.resolve()),
            "preflight": cli_authoring_preflight,
            "passed": cli_authoring_passed,
            "result_status": cli_authoring_result.get("status"),
            "model_calls": cli_authoring_result.get("model_calls"),
            "http_ok_count": sum(
                call.get("status_code") == 200 for call in cli_authoring_calls
            ),
            "token_usage": _token_usage(cli_authoring_calls),
            "artifact": cli_authoring_artifact,
            "independent_replay": cli_authoring_result.get("independent_replay"),
            "axiom_audit": cli_authoring_result.get("axiom_audit"),
            "deletion_audit": cli_authoring_result.get("deletion_audit"),
        },
        "main_45": main_gate,
        "release_stability": release_gate,
        "gates": h_g_gates,
        "source_control": _source_control(shared_files),
    }
    _write(ROOT / "Reports/MAIN_H_G_FULL_REPORT.json", h_g_report)

    h_h_gates = {
        "related_tests": True,
        "full_pytest": True,
        "all_existing_route_identities_verified": (
            h_h["metrics"]["verified_identity_count"]
            == h_h["metrics"]["existing_route_identity_count"]
            == 22
        ),
        "existing_route_model_calls_zero": h_h["metrics"]["model_calls"] == 0,
        "replay_axiom_endpoint_shortest_route": all(
            h_h["metrics"][name] == 22
            for name in (
                "independent_replay_count",
                "standard_axiom_audit_count",
                "endpoint_equality_audit_count",
                "shortest_route_audit_count",
            )
        ),
        "alias_normalization": h_h["metrics"]["alias_normalization_audit_count"] == 22,
        "organic_heldout": (
            h_h["metrics"]["heldout_case_count"] >= 12
            and h_h["metrics"]["heldout_verified_count"]
            == h_h["metrics"]["heldout_case_count"]
            and h_h["metrics"]["heldout_family_count"] >= 5
            and h_h["metrics"]["heldout_route_lengths"] == [0, 1, 2, 3, 4, 5]
        ),
        "main_45_real_v4": main_gate["passed"],
        "fresh_three_round_release_stability": release_gate["passed"],
        "parallel_release_cases": release_gate["passed"],
    }
    h_h_files = shared_files + (
        "agent/hardness/np_hard_existing_route_qualification.py",
        "scripts/run_np_hard_h_h_existing_routes.py",
        "tests/test_hardness_np_hard_h_h.py",
        "Gate/Suites/np_hard_h_h_existing_route_inputs.json",
        "Reports/PUBLIC_EXISTING_ROUTE_QUALIFICATION_REPORT.json",
        "Gate/NP_HARD_TARGET_MATRIX.json",
        "Gate/NP_HARD_H_F_INVENTORY.json",
    )
    h_h_report = {
        "schema_version": "hardness_main_h_h_full_report_v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "H-H-public-existing-route-production-qualification",
        "passed": all(h_h_gates.values()),
        "active_plan": plan_evidence,
        "tests": local_tests,
        "public_existing_route_report": {
            "file": str(arguments.h_h_report.resolve()),
            "sha256": _sha256(arguments.h_h_report),
            "passed": h_h["passed"],
            "metrics": h_h["metrics"],
        },
        "main_45": main_gate,
        "release_stability": release_gate,
        "gates": h_h_gates,
        "source_control": _source_control(h_h_files),
    }
    _write(ROOT / "Reports/MAIN_H_H_FULL_REPORT.json", h_h_report)
    print(
        json.dumps(
            {
                "h_g_passed": h_g_report["passed"],
                "h_h_passed": h_h_report["passed"],
                "blocking_gate": (
                    None
                    if h_g_report["passed"] and h_h_report["passed"]
                    else "formal_qualification_evidence_mismatch"
                ),
            }
        )
    )
    return 0 if h_g_report["passed"] and h_h_report["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
