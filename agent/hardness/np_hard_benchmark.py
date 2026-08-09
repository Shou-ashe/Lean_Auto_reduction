"""Formal offline benchmark for the versioned native NP-hardness MVP."""

from __future__ import annotations

import json
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from .lean_runner import RUNTIME_MODULE, build_module_command, run_command, sha256_file
from .np_hard import NPHardAgentConfigV1, NPHardAgentV1


NP_HARD_MVP_SUITE_SCHEMA = "hardness_np_hard_mvp_suite_v1"
NP_HARD_MVP_REPORT_SCHEMA = "hardness_np_hard_mvp_offline_report_v1"


@dataclass(frozen=True)
class NPHardBenchmarkCaseV1:
    id: str
    module: str
    problem: str
    expected_status: str
    expected_failure_code: str | None
    expected_evidence_kind: str | None
    minimum_route_atoms: int | None
    maximum_route_atoms: int | None
    tags: tuple[str, ...]


def load_np_hard_mvp_suite(path: Path) -> tuple[NPHardBenchmarkCaseV1, ...]:
    raw = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict) or raw.get("schema_version") != NP_HARD_MVP_SUITE_SCHEMA:
        raise ValueError("unsupported NP-hard MVP suite schema")
    if raw.get("suite_id") != "np_hard_mvp" or not isinstance(raw.get("cases"), list):
        raise ValueError("invalid NP-hard MVP suite identity")
    cases: list[NPHardBenchmarkCaseV1] = []
    seen: set[str] = set()
    for value in raw["cases"]:
        if not isinstance(value, dict):
            raise ValueError("NP-hard MVP case must be an object")
        case = NPHardBenchmarkCaseV1(
            id=value["id"],
            module=value["module"],
            problem=value["problem"],
            expected_status=value["expected_status"],
            expected_failure_code=value.get("expected_failure_code"),
            expected_evidence_kind=value.get("expected_evidence_kind"),
            minimum_route_atoms=value.get("minimum_route_atoms"),
            maximum_route_atoms=value.get("maximum_route_atoms"),
            tags=tuple(value.get("tags", ())),
        )
        if case.id in seen:
            raise ValueError("duplicate NP-hard MVP case id")
        seen.add(case.id)
        if case.expected_status not in {"VERIFIED", "BLOCKED"}:
            raise ValueError("NP-hard MVP case has an invalid expected status")
        if case.expected_status == "VERIFIED" and case.expected_failure_code is not None:
            raise ValueError("positive NP-hard MVP case declares a failure code")
        if case.expected_status == "BLOCKED" and not case.expected_failure_code:
            raise ValueError("negative NP-hard MVP case omits its typed failure code")
        cases.append(case)
    if not cases:
        raise ValueError("NP-hard MVP suite is empty")
    return tuple(cases)


def _prepare_fresh_directory(path: Path) -> None:
    if path.exists() and any(path.iterdir()):
        raise ValueError(f"NP-hard benchmark output must be fresh and empty: {path}")
    path.mkdir(parents=True, exist_ok=True)


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def run_np_hard_mvp_offline(
    *, root: Path, suite_path: Path, output_root: Path, report_path: Path
) -> dict[str, Any]:
    root = root.resolve()
    output_root = output_root.resolve()
    _prepare_fresh_directory(output_root)
    cases = load_np_hard_mvp_suite(suite_path)
    lean_root = root / "Lean"
    prebuild = run_command(
        build_module_command(case.module for case in cases),
        cwd=lean_root,
        timeout_seconds=900,
    )
    if not prebuild.ok:
        raise ValueError("NP-hard MVP runtime/input prebuild failed")

    rows: list[dict[str, Any]] = []
    total_model_calls = 0
    for case in cases:
        case_root = output_root / case.id
        result = NPHardAgentV1(
            NPHardAgentConfigV1(
                root=root,
                input_module=case.module,
                problem_declaration=case.problem,
                output_dir=case_root,
                lean_timeout_seconds=600,
                planner_mode="deterministic",
                authoring_mode="disabled",
                runtime_prebuilt=True,
            )
        ).run()
        resolution = result.probe.resolution if result.probe else None
        failure_code = result.failure.code if result.failure else None
        atom_count = len(resolution.atoms) if resolution else None
        matched = (
            result.status == case.expected_status
            and failure_code == case.expected_failure_code
            and (
                case.expected_evidence_kind is None
                or (
                    resolution is not None
                    and resolution.evidence_kind == case.expected_evidence_kind
                )
            )
            and (
                case.minimum_route_atoms is None
                or atom_count is not None
                and atom_count >= case.minimum_route_atoms
            )
            and (
                case.maximum_route_atoms is None
                or atom_count is not None
                and atom_count <= case.maximum_route_atoms
            )
            and result.model_calls == 0
        )
        total_model_calls += result.model_calls
        rows.append(
            {
                "case_id": case.id,
                "module": case.module,
                "problem_declaration": case.problem,
                "tags": list(case.tags),
                "expected_status": case.expected_status,
                "actual_status": result.status,
                "expected_failure_code": case.expected_failure_code,
                "actual_failure_code": failure_code,
                "evidence_kind": resolution.evidence_kind if resolution else None,
                "direction": resolution.direction if resolution else (
                    result.goal.direction if result.goal else None
                ),
                "hub_declaration": resolution.hub_declaration if resolution else None,
                "route_atoms": list(resolution.atoms) if resolution else [],
                "route_atom_count": atom_count,
                "registry_fingerprint": (
                    result.goal.registry_fingerprint if result.goal else None
                ),
                "artifact_file": result.artifact_file,
                "artifact_sha256": result.artifact_sha256,
                "independent_replay": result.verified,
                "model_calls": result.model_calls,
                "matched_expectation": matched,
            }
        )

    positives = [row for row in rows if row["expected_status"] == "VERIFIED"]
    negatives = [row for row in rows if row["expected_status"] == "BLOCKED"]
    reverse_cases = [row for row in rows if "reverse-only" in row["tags"]]
    membership_free = [row for row in rows if "membership-not-required" in row["tags"]]
    multi_edge = [row for row in rows if "multi-edge" in row["tags"]]
    passed = all(row["matched_expectation"] for row in rows)
    report = {
        "schema_version": NP_HARD_MVP_REPORT_SCHEMA,
        "suite_schema_version": NP_HARD_MVP_SUITE_SCHEMA,
        "suite_id": "np_hard_mvp",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "offline": True,
        "authoring_policy": "disabled",
        "planner": "deterministic",
        "objective": "prove_np_hard",
        "direction": "hardness_seed_to_problem",
        "final_lean_type": "ComplexityReduction.Certificate.NativeTMNPHard",
        "passed": passed,
        "suite_sha256": sha256_file(suite_path),
        "active_plan_sha256": sha256_file(root / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md"),
        "prebuild": prebuild.to_dict(),
        "metrics": {
            "case_count": len(rows),
            "positive_case_count": len(positives),
            "negative_case_count": len(negatives),
            "exact_final_hardness_rate": (
                sum(row["actual_status"] == "VERIFIED" for row in positives)
                / len(positives)
            ),
            "typed_negative_accuracy": (
                sum(row["matched_expectation"] for row in negatives) / len(negatives)
            ),
            "wrong_direction_rejection_rate": (
                sum(row["actual_failure_code"] == "wrong_direction_only" for row in reverse_cases)
                / len(reverse_cases)
            ),
            "target_membership_independence_rate": (
                sum(row["actual_status"] == "VERIFIED" for row in membership_free)
                / len(membership_free)
            ),
            "multi_edge_success_rate": (
                sum(row["actual_status"] == "VERIFIED" for row in multi_edge)
                / len(multi_edge)
            ),
            "independent_replay_rate": (
                sum(row["independent_replay"] for row in positives) / len(positives)
            ),
            "model_calls": total_model_calls,
            "reduce_to_known_hardness_counted_as_success": 0,
        },
        "cases": rows,
    }
    _write_json(report_path, report)
    _write_json(output_root / "report.json", report)
    return report
