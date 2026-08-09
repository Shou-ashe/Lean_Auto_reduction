"""Formal offline qualification for deterministic NP-hard hub selection."""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from .lean_runner import build_module_command, run_command, sha256_file
from .models import sha256_id
from .np_hard import NPHardAgentConfigV1, NPHardAgentV1
from .np_hard_hub_selection import (
    NPHardHubSwitchSessionV1,
    build_np_hard_hub_selection_request,
    project_np_hard_hub_candidates,
    rank_np_hard_hub_candidates,
)


NP_HARD_HUB_BENCHMARK_REPORT_SCHEMA_V1 = "hardness_np_hard_hub_selection_report_v1"
NP_HARD_HUB_SUITE_SCHEMA_V1 = "hardness_np_hard_hub_selection_suite_v1"


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def _profile(value: Any) -> dict[str, Any]:
    if not isinstance(value, list) or len(value) != 7:
        raise ValueError("G-D profile must contain exactly seven ordered fields")
    return {
        "eligibility": value[0],
        "unresolved_gap_count": value[1],
        "gap_risk": value[2],
        "existing_route_length": value[3],
        "representation_adapter_count": value[4],
        "estimated_authoring_nodes": value[5],
        "task_class": value[6],
    }


def load_np_hard_hub_selection_suite(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict) or value.get("schema_version") != NP_HARD_HUB_SUITE_SCHEMA_V1:
        raise ValueError("unsupported G-D hub-selection suite schema")
    if value.get("objective") != "prove_np_hard" or value.get("direction") != "hardness_seed_to_problem":
        raise ValueError("G-D suite changed the frozen objective or direction")
    cases = value.get("cases")
    if not isinstance(cases, list) or len(cases) != 4:
        raise ValueError("G-D suite must contain exactly four cases")
    ids: set[str] = set()
    for case in cases:
        if not isinstance(case, dict) or set(case) != {
            "id", "module", "problem", "expected_probe_failure", "expected_seed_count",
            "expected_selected_seed", "profiles",
        }:
            raise ValueError("G-D case has an invalid envelope")
        if case["id"] in ids:
            raise ValueError("G-D case IDs must be unique")
        ids.add(case["id"])
        if not isinstance(case["profiles"], dict) or len(case["profiles"]) < 3:
            raise ValueError("G-D cases must declare at least three candidate profiles")
        case["profiles"] = {
            declaration: _profile(profile)
            for declaration, profile in case["profiles"].items()
        }
    return value


def _axiom_audit(
    *, root: Path, case_root: Path, module: str, evidence_declaration: str
) -> dict[str, Any]:
    source = (
        f"import {module}\n"
        "import ComplexityReduction.AxiomGate\n\n"
        f"assert_standard_axioms {evidence_declaration}\n"
    )
    path = case_root / "SelectedHubAxiomAudit.lean"
    path.write_text(source, encoding="utf-8")
    command = run_command(
        ["lake", "env", "lean", str(path)],
        cwd=root / "Lean",
        timeout_seconds=300,
    )
    return {
        "passed": command.ok,
        "evidence_declaration": evidence_declaration,
        "file": str(path.relative_to(root)),
        "file_sha256": sha256_file(path),
        "command": command.to_dict(),
    }


def run_np_hard_hub_selection_benchmark(
    *, root: Path, suite_path: Path, output_root: Path, report_path: Path
) -> dict[str, Any]:
    root = root.resolve()
    suite_path = suite_path.resolve()
    output_root = output_root.resolve()
    report_path = report_path.resolve()
    if output_root.exists() and any(output_root.iterdir()):
        raise ValueError(f"G-D benchmark output must be fresh: {output_root}")
    output_root.mkdir(parents=True, exist_ok=True)
    suite = load_np_hard_hub_selection_suite(suite_path)
    modules = [case["module"] for case in suite["cases"]]
    build = run_command(
        build_module_command(modules), cwd=root / "Lean", timeout_seconds=600
    )
    if not build.ok:
        raise ValueError(f"G-D benchmark module build failed: {build.stderr}")

    rows: list[dict[str, Any]] = []
    switch_audit: dict[str, Any] | None = None
    ordering_checks = 0
    for case in suite["cases"]:
        case_root = output_root / "cases" / case["id"]
        agent = NPHardAgentV1(
            NPHardAgentConfigV1(
                root=root,
                input_module=case["module"],
                problem_declaration=case["problem"],
                output_dir=case_root / "probe",
                authoring_mode="disabled",
                runtime_prebuilt=True,
            )
        )
        agent_result = agent.run()
        probe = agent_result.probe
        if probe is None or probe.failure is None:
            raise ValueError(f"G-D case {case['id']} did not expose a blocked probe")
        candidates = project_np_hard_hub_candidates(
            seeds=probe.seeds,
            target_problem=case["problem"],
            profiles=case["profiles"],
        )
        request = build_np_hard_hub_selection_request(
            target_problem=case["problem"],
            registry_fingerprint=probe.registry_fingerprint,
            candidates=candidates,
        )
        selection = rank_np_hard_hub_candidates(request)
        selected = next(
            (
                candidate
                for candidate in candidates
                if candidate.candidate_id == selection.selected_candidate_id
            ),
            None,
        )
        permutations = (
            candidates,
            tuple(reversed(candidates)),
            candidates[1:] + candidates[:1],
            candidates[2:] + candidates[:2],
        )
        ordering_stable = True
        request_ids: list[str] = []
        for permutation in permutations:
            permuted_request = build_np_hard_hub_selection_request(
                target_problem=case["problem"],
                registry_fingerprint=probe.registry_fingerprint,
                candidates=permutation,
            )
            permuted_selection = rank_np_hard_hub_candidates(permuted_request)
            request_ids.append(permuted_request.request_id)
            ordering_stable = ordering_stable and (
                permuted_selection.ranked_candidate_ids == selection.ranked_candidate_ids
                and permuted_request.request_id == request.request_id
            )
            ordering_checks += 1
        expected_selected = case["expected_selected_seed"]
        reverse_case = expected_selected is None
        axiom = None
        if selected is not None:
            axiom = _axiom_audit(
                root=root,
                case_root=case_root,
                module=case["module"],
                evidence_declaration=selected.seed_evidence,
            )
        lower_risk_beats_shorter = reverse_case or any(
            candidate.unresolved_gap_count == selected.unresolved_gap_count
            and candidate.existing_route_length < selected.existing_route_length
            and candidate.ranking_key > selected.ranking_key
            for candidate in candidates
            if selected is not None and candidate.candidate_id != selected.candidate_id
        )
        matched = (
            agent_result.status == "BLOCKED"
            and probe.failure.code == case["expected_probe_failure"]
            and len(probe.seeds) == case["expected_seed_count"]
            and ordering_stable
            and (
                selected.seed_problem == expected_selected
                if selected is not None
                else expected_selected is None
                and selection.failure_code == "no_authorable_hardness_hub"
            )
            and (axiom is None or axiom["passed"])
            and lower_risk_beats_shorter
        )
        row = {
            "case_id": case["id"],
            "module": case["module"],
            "problem": case["problem"],
            "probe_status": agent_result.status,
            "probe_failure_code": probe.failure.code,
            "actual_seed_count": len(probe.seeds),
            "actual_seeds": [seed.to_dict() for seed in probe.seeds],
            "request": request.to_dict(),
            "selection": selection.to_dict(request),
            "permutation_request_ids": request_ids,
            "ordering_stable": ordering_stable,
            "lower_risk_beats_shorter_route": lower_risk_beats_shorter,
            "axiom_audit": axiom,
            "model_calls": agent_result.model_calls,
            "matched": matched,
        }
        rows.append(row)
        if switch_audit is None and selected is not None:
            session = NPHardHubSwitchSessionV1(request=request, selection=selection)
            before = session.current_request
            assert before is not None
            invalidated = sha256_id({"candidate_id": selected.candidate_id, "node": "accepted"})
            after = session.reject_current(
                failure_code="semantic_proof_failed",
                failure_class="budget_exhausted",
                model_calls=before.candidate_model_call_budget,
                accepted_node_hashes=(invalidated,),
            )
            switch_audit = {
                "passed": bool(
                    after is not None
                    and after.request_id != before.request_id
                    and after.candidate_id != before.candidate_id
                    and session.events[0]["endpoint_reuse"] is False
                    and invalidated in session.events[0]["invalidated_node_hashes"]
                    and session.consumed_model_calls <= 8
                ),
                "before": before.to_dict(),
                "after": after.to_dict() if after else None,
                "trace": session.to_dict(),
            }

    if switch_audit is None:
        raise ValueError("G-D suite contains no switchable positive case")
    metrics = {
        "case_count": len(rows),
        "matched_case_count": sum(row["matched"] for row in rows),
        "multi_seed_input_count": sum(row["actual_seed_count"] > 1 for row in rows),
        "minimum_actual_seed_count": min(row["actual_seed_count"] for row in rows),
        "stable_ordering_check_count": ordering_checks,
        "stable_ordering_failure_count": sum(not row["ordering_stable"] for row in rows),
        "selected_hub_axiom_audit_count": sum(
            bool(row["axiom_audit"] and row["axiom_audit"]["passed"]) for row in rows
        ),
        "reverse_only_selected_count": sum(
            row["case_id"].endswith("reverse-only")
            and row["selection"]["selected_candidate_id"] is not None
            for row in rows
        ),
        "no_authorable_hardness_hub_count": sum(
            row["selection"]["failure_code"] == "no_authorable_hardness_hub"
            for row in rows
        ),
        "shorter_higher_risk_overtake_count": sum(
            not row["lower_risk_beats_shorter_route"] for row in rows
        ),
        "candidate_switch_audit_count": int(switch_audit["passed"]),
        "model_calls": sum(row["model_calls"] for row in rows),
    }
    passed = (
        all(row["matched"] for row in rows)
        and switch_audit["passed"]
        and metrics["multi_seed_input_count"] >= 3
        and metrics["reverse_only_selected_count"] == 0
        and metrics["shorter_higher_risk_overtake_count"] == 0
        and metrics["model_calls"] == 0
    )
    report = {
        "schema_version": NP_HARD_HUB_BENCHMARK_REPORT_SCHEMA_V1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "G-D",
        "qualification_scope": "lean_observed_multi_seed_deterministic_hub_selection",
        "passed": passed,
        "suite_file": str(suite_path.relative_to(root)),
        "suite_sha256": sha256_file(suite_path),
        "active_plan_sha256": sha256_file(root / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md"),
        "module_build": build.to_dict(),
        "metrics": metrics,
        "switch_audit": switch_audit,
        "cases": rows,
    }
    _write_json(report_path, report)
    _write_json(output_root / "report.json", report)
    return report
