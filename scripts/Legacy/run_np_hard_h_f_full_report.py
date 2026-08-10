#!/usr/bin/env python3
"""Assemble the fail-closed H-F release report from fresh gate artifacts."""

from __future__ import annotations

import argparse
import json
import sys
import xml.etree.ElementTree as ET
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.lean_runner import sha256_file  # noqa: E402


SCHEMA = "hardness_main_h_f_full_report_v1"
SOURCE_FILES = (
    "ACTIVE_AGENT_IMPROVEMENT_PLAN.md",
    "agent/hardness/data/np_hard_scope_policy.json",
    "agent/hardness/np_hard_scope_policy.py",
    "agent/hardness/np_hard_target_matrix.py",
    "agent/hardness/np_hard_inventory.py",
    "agent/hardness/np_hard_orchestrator.py",
    "agent/hardness/np_hard_h_f_benchmark.py",
    "scripts/run_np_hard_h_f_qualification.py",
    "scripts/run_np_hard_h_f_heldout.py",
    "scripts/run_np_hard_h_f_full_report.py",
    "tests/test_hardness_np_hard_h_f.py",
    "Gate/Suites/np_hard_h_f_qualification_inputs.json",
    "Evaluation/np_hard_h_f_qualification_oracle.json",
    "Gate/NP_HARD_TARGET_MATRIX.json",
    "Gate/NP_HARD_H_F_INVENTORY.json",
    "Reports/NP_HARD_H_F_QUALIFICATION_HELDOUT_REPORT.json",
)


def _load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"JSON report is not an object: {path}")
    return value


def _relative(path: Path) -> str:
    resolved = path.resolve()
    try:
        return str(resolved.relative_to(ROOT))
    except ValueError:
        return str(resolved)


def _junit(path: Path) -> dict[str, Any]:
    root = ET.parse(path).getroot()
    if root.tag == "testsuite":
        suites = [root]
    else:
        suites = list(root.findall("testsuite"))
    tests = sum(int(suite.attrib.get("tests", 0)) for suite in suites)
    failures = sum(int(suite.attrib.get("failures", 0)) for suite in suites)
    errors = sum(int(suite.attrib.get("errors", 0)) for suite in suites)
    skipped = sum(int(suite.attrib.get("skipped", 0)) for suite in suites)
    duration = sum(float(suite.attrib.get("time", 0)) for suite in suites)
    return {
        "file": _relative(path),
        "sha256": sha256_file(path),
        "tests": tests,
        "failures": failures,
        "errors": errors,
        "skipped": skipped,
        "duration_seconds": round(duration, 3),
        "passed": tests > 0 and failures == 0 and errors == 0 and skipped == 0,
    }


def _model_calls(main: dict[str, Any]) -> list[dict[str, Any]]:
    return [
        dict(call)
        for row in main.get("results", [])
        for call in (row.get("model_calls") or [])
    ]


def _token_usage(calls: list[dict[str, Any]]) -> dict[str, int]:
    names = {
        key
        for call in calls
        for key, value in (call.get("usage") or {}).items()
        if isinstance(value, int) and not isinstance(value, bool)
    }
    return {
        name: sum(int((call.get("usage") or {}).get(name, 0)) for call in calls)
        for name in sorted(names)
    }


def _formal_model(config: dict[str, Any], *, max_tokens: int) -> bool:
    return (
        config.get("base_url") == "https://api.deepseek.com"
        and config.get("model") == "deepseek-v4-flash"
        and config.get("reasoning_effort") == "low"
        and config.get("temperature") == 0
        and config.get("max_retries") == 0
        and config.get("max_tokens") == max_tokens
        and config.get("timeout_seconds") == 300
        and config.get("api_key_configured") is True
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--related-junit", type=Path, required=True)
    parser.add_argument("--full-junit", type=Path, required=True)
    parser.add_argument("--main-45", type=Path, required=True)
    parser.add_argument("--stability", type=Path, required=True)
    parser.add_argument(
        "--heldout",
        type=Path,
        default=ROOT / "Reports/NP_HARD_H_F_QUALIFICATION_HELDOUT_REPORT.json",
    )
    parser.add_argument(
        "--matrix",
        type=Path,
        default=ROOT / "Gate/NP_HARD_TARGET_MATRIX.json",
    )
    parser.add_argument(
        "--inventory",
        type=Path,
        default=ROOT / "Gate/NP_HARD_H_F_INVENTORY.json",
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=ROOT / "Reports/MAIN_H_F_FULL_REPORT.json",
    )
    parser.add_argument("--tested-active-plan-sha256", required=True)
    arguments = parser.parse_args()

    related = _junit(arguments.related_junit.resolve())
    full = _junit(arguments.full_junit.resolve())
    main_45 = _load(arguments.main_45.resolve())
    stability = _load(arguments.stability.resolve())
    heldout = _load(arguments.heldout.resolve())
    matrix = _load(arguments.matrix.resolve())
    inventory = _load(arguments.inventory.resolve())
    calls = _model_calls(main_45)
    main_model = dict(main_45.get("reproducibility", {}).get("model_configuration") or {})
    stability_model = dict(stability.get("model") or {})
    main_gate = {
        "file": _relative(arguments.main_45),
        "sha256": sha256_file(arguments.main_45),
        "executed": main_45.get("total"),
        "matched": main_45.get("passed"),
        "failed": main_45.get("failed"),
        "model": main_model,
        "real_api_calls": len(calls),
        "http_ok_count": sum(
            call.get("called")
            and call.get("ok")
            and call.get("status_code") == 200
            and call.get("model") == "deepseek-v4-flash"
            for call in calls
        ),
        "token_usage": _token_usage(calls),
        "verified_replay_axiom_clean": all(
            row.get("actual_status") != "VERIFIED"
            or (row.get("deterministic_replay") is True and row.get("axiom_clean") is True)
            for row in main_45.get("results", [])
        ),
    }
    main_gate["passed"] = (
        main_gate["executed"] == 45
        and main_gate["matched"] == 45
        and main_gate["failed"] == 0
        and _formal_model(main_model, max_tokens=16384)
        and main_gate["real_api_calls"] == main_gate["http_ok_count"]
        and main_gate["real_api_calls"] >= 1
        and main_gate["verified_replay_axiom_clean"]
    )
    stability_metrics = dict(stability.get("metrics") or {})
    stability_gate = {
        "file": _relative(arguments.stability),
        "sha256": sha256_file(arguments.stability),
        "model": stability_model,
        "metrics": stability_metrics,
    }
    stability_gate["passed"] = (
        stability.get("passed") is True
        and _formal_model(stability_model, max_tokens=16000)
        and stability_metrics.get("round_count") == 3
        and stability_metrics.get("instance_execution_count") == 36
        and stability_metrics.get("matched_instance_count") == 36
        and stability_metrics.get("model_authoring_verified_count") == 15
        and stability_metrics.get("existing_route_model_calls") == 0
        and stability_metrics.get("deletion_audit_count") == 15
        and stability_metrics.get("worker_fallback_count") == 0
    )
    heldout_gate = {
        "file": _relative(arguments.heldout),
        "sha256": sha256_file(arguments.heldout),
        "passed": heldout.get("passed") is True,
        "model": heldout.get("model"),
        "metrics": heldout.get("metrics"),
        "security": heldout.get("security"),
    }
    matrix_gate = {
        "file": _relative(arguments.matrix),
        "sha256": sha256_file(arguments.matrix),
        "matrix_id": matrix.get("matrix_id"),
        "declaration_count": matrix.get("declaration_count"),
        "identity_count": matrix.get("identity_count"),
        "in_scope_count": matrix.get("in_scope_count"),
        "auxiliary_count": matrix.get("auxiliary_count"),
        "blocked_count": matrix.get("blocked_count"),
        "unclassified_count": matrix.get("unclassified_count"),
        "known_forward_route_identity_count": matrix.get(
            "known_forward_route_identity_count"
        ),
        "production_entry_observed_identity_count": matrix.get(
            "production_entry_observed_identity_count"
        ),
    }
    matrix_gate["passed"] = (
        matrix_gate["declaration_count"] == 253
        and matrix_gate["identity_count"] == 44
        and matrix_gate["in_scope_count"] == 22
        and matrix_gate["auxiliary_count"] == 8
        and matrix_gate["blocked_count"] == 14
        and matrix_gate["unclassified_count"] == 0
        and matrix_gate["known_forward_route_identity_count"] == 22
        and all(row.get("can_form_typed_authoring_dag") is not None for row in matrix["identities"])
        and all(row.get("disposition") for row in matrix["identities"])
    )
    inventory_gate = {
        "file": _relative(arguments.inventory),
        "sha256": sha256_file(arguments.inventory),
        "inventory_id": inventory.get("inventory_id"),
        "declaration_count": inventory.get("declaration_count"),
        "identity_count": inventory.get("identity_count"),
        "known_forward_route_declaration_count": inventory.get(
            "known_forward_route_declaration_count"
        ),
        "known_forward_route_identity_count": inventory.get(
            "known_forward_route_identity_count"
        ),
        "target_matrix_id": inventory.get("target_matrix_id"),
    }
    inventory_gate["passed"] = (
        inventory_gate["declaration_count"] == matrix_gate["declaration_count"]
        and inventory_gate["identity_count"] == matrix_gate["identity_count"]
        and inventory_gate["known_forward_route_identity_count"]
        == matrix_gate["known_forward_route_identity_count"]
        and inventory_gate["known_forward_route_declaration_count"]
        > inventory_gate["known_forward_route_identity_count"]
        and inventory_gate["target_matrix_id"] == matrix_gate["matrix_id"]
    )
    plan_text = (ROOT / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md").read_text(encoding="utf-8")
    completed_plan_sha256 = sha256_file(ROOT / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md")
    plan_gate = {
        "tested_active_plan_sha256": arguments.tested_active_plan_sha256,
        "completed_active_plan_sha256": completed_plan_sha256,
        "h_f_removed_after_completion": "## 四、H-F：" not in plan_text,
    }
    plan_gate["passed"] = plan_gate["h_f_removed_after_completion"]
    source_hashes = {
        relative: sha256_file(ROOT / relative)
        for relative in SOURCE_FILES
        if (ROOT / relative).is_file()
    }
    passed = all(
        gate["passed"]
        for gate in (
            related,
            full,
            main_gate,
            stability_gate,
            heldout_gate,
            matrix_gate,
            inventory_gate,
            plan_gate,
        )
    )
    report = {
        "schema_version": SCHEMA,
        "stage": "H-F",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "passed": passed,
        "source_control": {
            "git_available": False,
            "reason": (
                "workspace .git directory does not contain readable repository metadata; "
                "per-file SHA-256 evidence is authoritative"
            ),
            **plan_gate,
            "source_sha256": source_hashes,
        },
        "lean": {
            "toolchain": (ROOT / "Lean/lean-toolchain").read_text(encoding="utf-8").strip(),
            "toolchain_file_sha256": sha256_file(ROOT / "Lean/lean-toolchain"),
            "lake_manifest_sha256": sha256_file(ROOT / "Lean/lake-manifest.json"),
        },
        "inputs": {
            "suite_sha256": sha256_file(
                ROOT / "Gate/Suites/np_hard_h_f_qualification_inputs.json"
            ),
            "oracle_sha256": sha256_file(
                ROOT
                / "Evaluation/np_hard_h_f_qualification_oracle.json"
            ),
            "scope_policy_id": matrix.get("scope_policy", {}).get("policy_id"),
        },
        "gates": {
            "related_tests": related,
            "full_tests": full,
            "main_benchmark_45": main_gate,
            "release_stability_3_rounds": stability_gate,
            "h_f_qualification_heldout": heldout_gate,
            "target_matrix": matrix_gate,
            "inventory": inventory_gate,
            "active_plan_transition": plan_gate,
        },
        "fresh_output_paths": {
            "main_45": _relative(arguments.main_45.resolve().parent),
            "release_stability": _relative(arguments.stability.resolve().parent),
            "heldout": heldout.get("cases", [{}])[0].get("result", {}).get("output_dir"),
        },
    }
    arguments.report.parent.mkdir(parents=True, exist_ok=True)
    arguments.report.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps({"passed": passed, "report": _relative(arguments.report)}))
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
