"""Offline baseline gate for the dedicated NP-hard generalization suite."""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from .lean_runner import build_module_command, run_command, sha256_file
from .np_hard import NPHardAgentConfigV1, NPHardAgentV1
from .np_hard_generalization import load_np_hard_generalization_suite


NP_HARD_GENERALIZATION_BASELINE_REPORT_SCHEMA_V1 = (
    "hardness_np_hard_generalization_baseline_report_v1"
)


def _fresh_directory(path: Path) -> None:
    if path.exists() and any(path.iterdir()):
        raise ValueError(f"NP-hard generalization output must be fresh and empty: {path}")
    path.mkdir(parents=True, exist_ok=True)


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def run_np_hard_generalization_baseline(
    *, root: Path, suite_path: Path, output_root: Path, report_path: Path
) -> dict[str, Any]:
    """Verify public blockers, existing routes, and isolated gold compilation.

    This is the G-A gate, not the future model-authoring release run.  All agent
    invocations use authoring-disabled mode and therefore must make zero model
    calls.  Gold modules are compiled only as isolated benchmark self-checks.
    """

    root = root.resolve()
    suite_path = suite_path.resolve()
    output_root = output_root.resolve()
    report_path = report_path.resolve()
    _fresh_directory(output_root)
    suite = load_np_hard_generalization_suite(suite_path, root=root)

    input_modules = {case.module for case in suite.cases}
    gold_modules = {
        str(case.authoring["gold_module"])
        for case in suite.cases
        if case.authoring is not None
    }
    prebuild = run_command(
        build_module_command(input_modules | gold_modules),
        cwd=root / "Lean",
        timeout_seconds=900,
    )
    if not prebuild.ok:
        raise ValueError("NP-hard generalization public/gold prebuild failed")

    rows: list[dict[str, Any]] = []
    for case in suite.cases:
        result = NPHardAgentV1(
            NPHardAgentConfigV1(
                root=root,
                input_module=case.module,
                problem_declaration=case.problem,
                output_dir=output_root / case.id,
                lean_timeout_seconds=600,
                planner_mode="deterministic",
                authoring_mode="disabled",
                runtime_prebuilt=True,
            )
        ).run()
        resolution = result.probe.resolution if result.probe else None
        failure_code = result.failure.code if result.failure else None
        atoms = tuple(resolution.atoms) if resolution else ()
        route_matches = True
        if case.route is not None:
            route_matches = (
                resolution is not None
                and resolution.evidence_kind == case.route["expected_evidence_kind"]
                and int(case.route["minimum_atoms"])
                <= len(atoms)
                <= int(case.route["maximum_atoms"])
            )
        matched = (
            result.status == case.initial_expected_status
            and failure_code == case.initial_expected_failure_code
            and result.model_calls == 0
            and route_matches
        )
        rows.append(
            {
                "case_id": case.id,
                "case_kind": case.kind,
                "problem_id": case.problem_id,
                "module": case.module,
                "problem": case.problem,
                "family": case.family,
                "initial_expected_status": case.initial_expected_status,
                "actual_status": result.status,
                "initial_expected_failure_code": case.initial_expected_failure_code,
                "actual_failure_code": failure_code,
                "evidence_kind": resolution.evidence_kind if resolution else None,
                "direction": resolution.direction if resolution else (
                    result.goal.direction if result.goal else None
                ),
                "hub_declaration": resolution.hub_declaration if resolution else None,
                "route_atoms": list(atoms),
                "route_atom_count": len(atoms) if resolution else None,
                "model_calls": result.model_calls,
                "independent_replay": result.verified,
                "matched_baseline": matched,
            }
        )

    existing = [row for row in rows if row["case_kind"] == "existing_route"]
    authored = [row for row in rows if row["case_kind"] == "model_authoring"]
    negatives = [row for row in rows if row["case_kind"] == "safety_negative"]
    passed = prebuild.ok and all(row["matched_baseline"] for row in rows)
    report = {
        "schema_version": NP_HARD_GENERALIZATION_BASELINE_REPORT_SCHEMA_V1,
        "suite_schema_version": "hardness_np_hard_generalization_suite_v1",
        "suite_id": "np_hard_generalization_v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "objective": "prove_np_hard",
        "direction": "hardness_seed_to_problem",
        "final_lean_type": "ComplexityReduction.Certificate.NativeTMNPHard",
        "authoring_policy": "disabled",
        "planner": "deterministic",
        "passed": passed,
        "suite_sha256": sha256_file(suite_path),
        "inventory_sha256": sha256_file(root / suite.inventory_path),
        "active_plan_sha256": sha256_file(root / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md"),
        "prebuild": prebuild.to_dict(),
        "gold_modules": sorted(gold_modules),
        "metrics": {
            "case_count": len(rows),
            "existing_route_count": len(existing),
            "model_authoring_count": len(authored),
            "safety_negative_count": len(negatives),
            "family_count": len({row["family"] for row in rows}),
            "existing_route_verified": sum(
                row["actual_status"] == "VERIFIED" for row in existing
            ),
            "authoring_public_blockers_confirmed": sum(
                row["actual_failure_code"] == "no_forward_path_from_hardness_seed"
                for row in authored
            ),
            "multi_edge_existing_count": sum(
                (row["route_atom_count"] or 0) >= 2 for row in existing
            ),
            "membership_free_existing_count": sum(
                not case.membership_available
                for case in suite.cases
                if case.kind == "existing_route"
            ),
            "gold_compile_self_check_count": len(gold_modules),
            "model_calls": sum(row["model_calls"] for row in rows),
        },
        "cases": rows,
    }
    _write_json(report_path, report)
    _write_json(output_root / "report.json", report)
    return report

