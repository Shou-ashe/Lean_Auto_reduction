#!/usr/bin/env python3
"""Run versioned hardness-agent benchmark suites."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from dataclasses import replace
import json
import shutil
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.benchmark import (  # noqa: E402
    RESULT_V2,
    BenchmarkManifestError,
    load_benchmark_manifest,
    select_benchmark_cases,
    summarize_benchmark_results,
)
from agent.hardness.model_client import DeepSeekConfig  # noqa: E402
from agent.hardness.authoring import (  # noqa: E402
    DETERMINISTIC_TEMPLATE_MODE,
    DISABLED_MODE,
    MODEL_AUTO_MODE,
    MODEL_MODES,
    MODEL_REQUIRED_MODE,
)
from agent.hardness.lean_runner import (  # noqa: E402
    build_module_command,
    run_command,
    sha256_file,
)
from agent.hardness.runner import HardnessAgent, HardnessAgentConfig  # noqa: E402


RUNNER_VERSION = "hardness_benchmark_runner_ir_v1"


def _last_failure_code(result: Any) -> str | None:
    if not result.failures:
        return None
    return result.failures[-1].code


def _has_successful_command(result: Any, filename: str) -> bool:
    return any(command.ok and command.command[-1].endswith(filename) for command in result.commands)


def _aggregate_model_usage(result: Any) -> dict[str, Any] | None:
    usage_rows = [
        call.usage
        for call in getattr(result, "model_calls", ())
        if isinstance(call.usage, dict)
    ]
    if not usage_rows:
        return None
    totals: dict[str, Any] = {}
    for usage in usage_rows:
        for key, value in usage.items():
            if isinstance(value, (int, float)) and not isinstance(value, bool):
                totals[key] = totals.get(key, 0) + value
    return totals or {"reported_calls": len(usage_rows)}


def _case_result(case: Any, result: Any, *, planner: str) -> dict[str, Any]:
    failure_code = _last_failure_code(result)
    expected = case.expected
    status_match = result.status == expected.final_status
    failure_match = (
        expected.final_failure_code is None or failure_code == expected.final_failure_code
    )
    selected_route = result.selected_route
    atom_count = len(selected_route.atoms) if selected_route else None
    coverage_failures: list[str] = []
    minimum_atoms = case.coverage.get("minimum_route_atoms")
    if result.status == "VERIFIED" and minimum_atoms is not None:
        if atom_count is None or atom_count < int(minimum_atoms):
            coverage_failures.append(
                f"route_atom_count={atom_count} is below minimum_route_atoms={minimum_atoms}"
            )
    maximum_atoms = case.coverage.get("maximum_route_atoms")
    if result.status == "VERIFIED" and maximum_atoms is not None:
        if atom_count is None or atom_count > int(maximum_atoms):
            coverage_failures.append(
                f"route_atom_count={atom_count} exceeds maximum_route_atoms={maximum_atoms}"
            )
    required_role = case.coverage.get("required_capability_role")
    if result.status == "VERIFIED" and required_role is not None:
        roles = selected_route.roles if selected_route else ()
        if required_role not in roles:
            coverage_failures.append(f"selected route does not contain role {required_role!r}")
    required_roles = case.coverage.get("required_route_roles")
    if result.status == "VERIFIED" and required_roles is not None:
        roles = selected_route.roles if selected_route else ()
        missing_roles = [role for role in required_roles if role not in roles]
        if missing_roles:
            coverage_failures.append(
                f"selected route lacks required_route_roles={missing_roles!r}"
            )
    if case.coverage.get("forbid_final_facade", False) and selected_route is not None:
        if selected_route.final_composition_edges != 0:
            coverage_failures.append("selected route unexpectedly used a final facade")
    required_resolution_class = case.coverage.get("required_resolution_class")
    if result.status == "VERIFIED" and required_resolution_class is not None:
        roles = selected_route.roles if selected_route else ()
        if required_resolution_class == "direct_or_final_facade":
            if selected_route is None or len(selected_route.atoms) != 1 or not (
                selected_route.final_composition_edges == 1 or roles == ("unannotated",)
            ):
                coverage_failures.append(
                    "selected route is not one exact direct/final-facade declaration"
                )
        elif required_resolution_class == "ir_components":
            if selected_route is None or selected_route.final_composition_edges != 0:
                coverage_failures.append("selected route is not an IR-component path")
        else:
            coverage_failures.append(
                f"unsupported required_resolution_class={required_resolution_class!r}"
            )
    required_evidence_kind = case.coverage.get("required_evidence_kind")
    actual_evidence_kind = selected_route.evidence_kind if selected_route else None
    if required_evidence_kind is not None and actual_evidence_kind != required_evidence_kind:
        coverage_failures.append(
            f"selected evidence kind {actual_evidence_kind!r} does not match "
            f"required_evidence_kind={required_evidence_kind!r}"
        )
    required_completeness = case.coverage.get("required_completeness_declaration")
    actual_completeness = selected_route.completeness_declaration if selected_route else None
    if required_completeness is not None and actual_completeness != required_completeness:
        coverage_failures.append(
            f"selected completeness declaration {actual_completeness!r} does not match "
            f"{required_completeness!r}"
        )
    required_hub = case.coverage.get("required_hub_declaration")
    actual_hub = selected_route.hub_declaration if selected_route else None
    if required_hub is not None and actual_hub != required_hub:
        coverage_failures.append(
            f"selected completeness hub {actual_hub!r} does not match {required_hub!r}"
        )
    required_blocker = case.coverage.get("required_blocker")
    if required_blocker is not None and failure_code != required_blocker:
        coverage_failures.append(
            f"actual failure code {failure_code!r} does not match required blocker {required_blocker!r}"
        )
    required_gap_reason = case.coverage.get("required_gap_reason")
    actual_gap_reason = result.gap.reason if result.gap else None
    if required_gap_reason is not None and actual_gap_reason != required_gap_reason:
        coverage_failures.append(
            f"actual gap reason {actual_gap_reason!r} does not match "
            f"required_gap_reason={required_gap_reason!r}"
        )
    required_capability_head = case.coverage.get("required_expected_capability_head")
    actual_capability_head = result.gap.expected_capability_head if result.gap else None
    if (
        required_capability_head is not None
        and actual_capability_head != required_capability_head
    ):
        coverage_failures.append(
            f"actual expected capability head {actual_capability_head!r} does not match "
            f"required_expected_capability_head={required_capability_head!r}"
        )
    required_baseline_blocker = case.coverage.get("required_baseline_blocker")
    actual_baseline_blocker = result.gap.failure_code if result.gap else None
    if (
        required_baseline_blocker is not None
        and actual_baseline_blocker != required_baseline_blocker
    ):
        coverage_failures.append(
            f"baseline blocker {actual_baseline_blocker!r} does not match "
            f"required_baseline_blocker={required_baseline_blocker!r}"
        )
    required_template = case.coverage.get("required_authoring_template")
    actual_template = result.authoring_task.template_kind if result.authoring_task else None
    if required_template is not None and actual_template != required_template:
        coverage_failures.append(
            f"authoring template {actual_template!r} does not match {required_template!r}"
        )
    minimum_attempts = case.coverage.get("minimum_authoring_attempts")
    if minimum_attempts is not None and len(result.authoring_attempts) < int(minimum_attempts):
        coverage_failures.append(
            f"authoring_attempt_count={len(result.authoring_attempts)} is below "
            f"minimum_authoring_attempts={minimum_attempts}"
        )
    maximum_attempts = case.coverage.get("maximum_authoring_attempts")
    if maximum_attempts is not None and len(result.authoring_attempts) > int(maximum_attempts):
        coverage_failures.append(
            f"authoring_attempt_count={len(result.authoring_attempts)} exceeds "
            f"maximum_authoring_attempts={maximum_attempts}"
        )
    if case.coverage.get("require_failed_authoring_attempt", False) and not any(
        not attempt.accepted for attempt in result.authoring_attempts
    ):
        coverage_failures.append("authoring did not record a rejected bounded attempt")
    required_failed_stages = case.coverage.get("required_failed_attempt_stage_names")
    if required_failed_stages is not None:
        failed_attempt = next(
            (attempt for attempt in result.authoring_attempts if not attempt.accepted),
            None,
        )
        failed_stage_attempts = tuple(
            getattr(failed_attempt, "stage_attempts", ()) if failed_attempt else ()
        )
        actual_failed_stages = tuple(stage.stage for stage in failed_stage_attempts)
        if actual_failed_stages != tuple(required_failed_stages):
            coverage_failures.append(
                f"rejected authoring stages {actual_failed_stages!r} do not match "
                f"required_failed_attempt_stage_names={tuple(required_failed_stages)!r}"
            )
        elif not failed_stage_attempts or failed_stage_attempts[-1].accepted or not all(
            stage.accepted for stage in failed_stage_attempts[:-1]
        ):
            coverage_failures.append(
                "rejected authoring attempt did not fail only at its final required stage"
            )
    accepted_attempt = next(
        (attempt for attempt in reversed(result.authoring_attempts) if attempt.accepted),
        None,
    )
    accepted_stages = tuple(
        stage.stage for stage in getattr(accepted_attempt, "stage_attempts", ())
    )
    required_stage_names = case.coverage.get("required_stage_names")
    if required_stage_names is not None and accepted_stages != tuple(required_stage_names):
        coverage_failures.append(
            f"accepted authoring stages {accepted_stages!r} do not match "
            f"required_stage_names={tuple(required_stage_names)!r}"
        )
    if case.coverage.get("require_all_stage_checkpoints", False):
        stage_attempts = tuple(getattr(accepted_attempt, "stage_attempts", ()))
        if not stage_attempts or not all(stage.accepted for stage in stage_attempts):
            coverage_failures.append("accepted bundle lacks successful per-stage checkpoints")
    if case.coverage.get("require_candidate_validation", False) and not _has_successful_command(
        result, "CandidateValidation.lean"
    ):
        coverage_failures.append("job-local candidate did not pass canonical-head validation")
    if case.coverage.get("require_program_indexed_bundle_validation", False):
        if actual_template not in {
            "program_indexed_reduction",
            "program_indexed_model",
        } or not _has_successful_command(
            result, "CandidateValidation.lean"
        ):
            coverage_failures.append(
                "program-indexed bundle did not pass its dedicated Lean validation command"
            )
    if case.coverage.get("require_native_membership_bundle_validation", False):
        if actual_template != "native_membership" or not _has_successful_command(
            result, "CandidateValidation.lean"
        ):
            coverage_failures.append(
                "native-membership bundle did not pass its dedicated Lean validation command"
            )
    required_family = case.coverage.get("required_family_declaration")
    actual_family = (
        result.authoring_attempts[-1].family_candidate.family_declaration
        if result.authoring_attempts
        and result.authoring_attempts[-1].family_candidate is not None
        else None
    )
    if required_family is not None and actual_family != required_family:
        coverage_failures.append(
            f"authored family {actual_family!r} does not match {required_family!r}"
        )
    required_provider = case.coverage.get("required_template_provider")
    actual_provider = (
        result.authoring_attempts[-1].template_candidate.provider_declaration
        if result.authoring_attempts
        and result.authoring_attempts[-1].template_candidate is not None
        else None
    )
    if required_provider is not None and actual_provider != required_provider:
        coverage_failures.append(
            f"template provider {actual_provider!r} does not match {required_provider!r}"
        )
    required_authored_head = case.coverage.get("required_authored_capability_head")
    if (
        required_authored_head is not None
        and result.authored_capability_head != required_authored_head
    ):
        coverage_failures.append(
            f"authored capability head {result.authored_capability_head!r} does not match "
            f"{required_authored_head!r}"
        )
    if case.coverage.get("require_authored_route", False):
        if not result.authored_route_declaration:
            coverage_failures.append("authoring bundle did not expose a derived route declaration")
    if case.coverage.get("require_job_local_candidate", False):
        candidate_file = result.authored_candidate_file or ""
        if not candidate_file or candidate_file.startswith("Lean/Reference/"):
            coverage_failures.append("authored candidate is not isolated in the job workspace")
    model_requests = tuple(getattr(result, "model_calls", ()))
    model_calls = tuple(call for call in model_requests if call.called)
    authored_source_origin = getattr(result, "authored_source_origin", None)
    model_called = any(call.called for call in model_calls)
    model_generated = authored_source_origin == "model_generated"
    if case.coverage.get("forbid_model_call", False) and model_called:
        coverage_failures.append("case unexpectedly called the model")
    if case.coverage.get("require_model_called", False) and not model_called:
        coverage_failures.append("case required a real model call")
    if case.coverage.get("require_model_generated_source", False) and not model_generated:
        coverage_failures.append("verified candidate was not produced by an accepted model patch")
    minimum_model_calls = case.coverage.get("minimum_model_calls")
    if minimum_model_calls is not None and len(model_calls) < int(minimum_model_calls):
        coverage_failures.append(
            f"model_call_count={len(model_calls)} is below "
            f"minimum_model_calls={minimum_model_calls}"
        )
    maximum_model_calls = case.coverage.get("maximum_model_calls")
    if maximum_model_calls is not None and len(model_calls) > int(maximum_model_calls):
        coverage_failures.append(
            f"model_call_count={len(model_calls)} exceeds "
            f"maximum_model_calls={maximum_model_calls}"
        )
    if case.coverage.get("require_resume_candidate_invalidation", False):
        if not result.resume_requested:
            coverage_failures.append("candidate-absence audit did not run in resume mode")
        if result.resumed_from_status != "VERIFIED":
            coverage_failures.append(
                f"resume started from {result.resumed_from_status!r}, expected 'VERIFIED'"
            )
        if result.resume_candidate_integrity != "missing":
            coverage_failures.append(
                "resume did not observe the job-local candidate as missing"
            )
    passed = status_match and failure_match and not coverage_failures
    selected_catalog = getattr(result, "selected_catalog", None)
    return {
        "id": case.id,
        "suite_id": case.suite_id,
        "group_id": getattr(case, "group_id", None),
        "expected_status": expected.final_status,
        "expected_failure_code": expected.final_failure_code,
        "actual_status": result.status,
        "actual_failure_code": failure_code,
        "passed": passed,
        "positive": case.is_positive,
        "objective": case.objective,
        "objective_direction": getattr(case, "objective_direction", "source_to_target"),
        "execution_layer": getattr(case, "execution_layer", "core_reuse"),
        "verification_profile": getattr(case, "verification_profile", "core"),
        "catalog_mode": getattr(case, "catalog_mode", "full"),
        "matched_pair_id": getattr(case, "matched_pair_id", None),
        "family_id": getattr(case, "family_id", None),
        "source_form_id": getattr(case, "source_form_id", None),
        "target_form_id": getattr(case, "target_form_id", None),
        "hub_ids": list(getattr(case, "hub_ids", ())),
        "requires_authoring": case.requires_authoring,
        "evaluation_lane": getattr(
            case, "evaluation_lane", "existing_route" if case.is_positive else "negative"
        ),
        "new_certified_reduction": (
            result.authored_capability_head
            == "ComplexityReduction.Certificate.CertifiedReduction"
        ),
        "new_native_membership": (
            result.authored_capability_head
            == "ComplexityReduction.Certificate.NativeTMInNP"
        ),
        "axiom_clean": result.status == "VERIFIED",
        "deterministic_replay": (
            result.status == "VERIFIED"
            and _has_successful_command(result, "Artifact.lean")
            and sum(
                1
                for command in result.commands
                if command.ok and command.command[-1].endswith("Artifact.lean")
            )
            >= 2
        ),
        "planner": planner,
        "authoring_policy": getattr(result, "authoring_policy", "disabled"),
        "model_called": model_called,
        "model_ok": model_generated and result.status == "VERIFIED",
        "model_usage": _aggregate_model_usage(result),
        "model_call_count": len(model_calls),
        "model_request_count": len(model_requests),
        "model_calls": [call.to_dict() for call in model_requests],
        "authored_source_origin": authored_source_origin,
        "route_atom_count": atom_count,
        "route_atoms": list(selected_route.atoms) if selected_route else [],
        "route_roles": list(selected_route.roles) if selected_route else [],
        "route_final_composition_edges": (
            selected_route.final_composition_edges if selected_route else None
        ),
        "catalog_id": selected_catalog.catalog_id if selected_catalog else None,
        "agent_interface_count": (
            selected_catalog.agent_interface_count if selected_catalog else None
        ),
        "semantic_atomic_interface_count": (
            selected_catalog.semantic_atomic_interface_count if selected_catalog else None
        ),
        "catalog_entries": (
            [
                {
                    "entry_id": entry.entry_id,
                    "declaration": entry.declaration,
                    "component_role": entry.component_role,
                    "is_final_facade": entry.is_final_facade,
                }
                for entry in selected_catalog.entries
            ]
            if selected_catalog
            else []
        ),
        "evidence_kind": actual_evidence_kind,
        "completeness_declaration": actual_completeness,
        "hub_declaration": actual_hub,
        "gap_id": result.gap.gap_id if result.gap else None,
        "gap_reason": actual_gap_reason,
        "gap_expected_capability_head": actual_capability_head,
        "authoring_template": actual_template,
        "authoring_attempt_count": len(result.authoring_attempts),
        "accepted_authoring_stages": list(accepted_stages),
        "authored_candidate_module": result.authored_candidate_module,
        "authored_candidate_declaration": result.authored_candidate_declaration,
        "authored_route_declaration": result.authored_route_declaration,
        "authored_capability_head": result.authored_capability_head,
        "authored_candidate_file": result.authored_candidate_file,
        "authored_stage_files": list(getattr(result, "authored_stage_files", ())),
        "resume_requested": result.resume_requested,
        "resumed_from_status": result.resumed_from_status,
        "resume_candidate_integrity": result.resume_candidate_integrity,
        "typed_gap_replay": (
            result.status == "BLOCKED"
            and result.gap is not None
            and _has_successful_command(result, "Probe.lean")
            and sum(
                1
                for command in result.commands
                if command.ok and command.command[-1].endswith("Probe.lean")
            )
            >= 2
        ),
        "coverage_failures": coverage_failures,
        "report": result.report_file,
    }


def _display_path(path: Path) -> str:
    try:
        return str(path.resolve().relative_to(ROOT.resolve()))
    except ValueError:
        return str(path.resolve())


def _resume_prerequisite_failure(case: Any, *, planner: str, reason: str) -> dict[str, Any]:
    return {
        "id": case.id,
        "suite_id": case.suite_id,
        "group_id": case.group_id,
        "expected_status": case.expected.final_status,
        "expected_failure_code": case.expected.final_failure_code,
        "actual_status": "FAILED",
        "actual_failure_code": "resume_prerequisite_failed",
        "passed": False,
        "positive": case.is_positive,
        "objective": case.objective,
        "objective_direction": case.objective_direction,
        "execution_layer": case.execution_layer,
        "verification_profile": case.verification_profile,
        "catalog_mode": case.catalog_mode,
        "matched_pair_id": case.matched_pair_id,
        "family_id": case.family_id,
        "source_form_id": case.source_form_id,
        "target_form_id": case.target_form_id,
        "hub_ids": list(case.hub_ids),
        "requires_authoring": case.requires_authoring,
        "evaluation_lane": case.evaluation_lane,
        "new_certified_reduction": False,
        "new_native_membership": False,
        "axiom_clean": False,
        "deterministic_replay": False,
        "planner": planner,
        "model_called": False,
        "model_ok": False,
        "model_usage": None,
        "model_call_count": 0,
        "model_request_count": 0,
        "model_calls": [],
        "authored_source_origin": None,
        "route_atom_count": None,
        "route_atoms": [],
        "route_roles": [],
        "route_final_composition_edges": None,
        "catalog_id": None,
        "agent_interface_count": None,
        "semantic_atomic_interface_count": None,
        "evidence_kind": None,
        "completeness_declaration": None,
        "hub_declaration": None,
        "gap_id": None,
        "gap_reason": None,
        "gap_expected_capability_head": None,
        "authoring_template": None,
        "authoring_attempt_count": 0,
        "accepted_authoring_stages": [],
        "authored_candidate_module": None,
        "authored_candidate_declaration": None,
        "authored_route_declaration": None,
        "authored_capability_head": None,
        "authored_candidate_file": None,
        "authored_stage_files": [],
        "resume_requested": True,
        "resumed_from_status": None,
        "resume_candidate_integrity": None,
        "typed_gap_replay": False,
        "coverage_failures": [reason],
        "report": None,
    }


def _remove_job_local_candidate(
    *, output_dir: Path, candidate_module: str
) -> tuple[Path, Path]:
    module_path = Path(*candidate_module.split("."))
    active_source = output_dir / "work" / module_path.with_suffix(".lean")
    active_olean = output_dir / "work" / module_path.with_suffix(".olean")
    if not active_source.is_file():
        raise ValueError(f"verified candidate source is already absent: {active_source}")

    receipt_dir = output_dir / "receipts" / "candidate-removal"
    receipt_dir.mkdir(parents=True, exist_ok=True)
    backup_source = receipt_dir / "candidate.lean"
    backup_olean = receipt_dir / "candidate.olean"
    active_source.replace(backup_source)
    if active_olean.is_file():
        active_olean.replace(backup_olean)
    receipt_path = receipt_dir / "receipt.json"
    receipt_path.write_text(
        json.dumps(
            {
                "schema_version": "hardness_candidate_removal_receipt_v1",
                "candidate_module": candidate_module,
                "active_source": str(active_source),
                "active_olean": str(active_olean),
                "backup_source": str(backup_source),
                "backup_olean": str(backup_olean) if backup_olean.is_file() else None,
                "source_absent": not active_source.exists(),
                "olean_absent": not active_olean.exists(),
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    return receipt_path, backup_source


def main() -> int:
    parser = argparse.ArgumentParser(description="Run hardness-agent benchmark suites")
    parser.add_argument(
        "--manifest",
        type=Path,
        default=ROOT / "Benchmark" / "Hardness" / "MANIFEST.json",
    )
    parser.add_argument(
        "--output-root", type=Path, default=ROOT / ".reduction-agent" / "benchmark"
    )
    parser.add_argument("--suite", action="append", default=[])
    parser.add_argument("--case", action="append", default=[])
    parser.add_argument("--agent-phase", type=int, default=1)
    parser.add_argument(
        "--planner",
        choices=("deterministic",),
        default=None,
        help="override each case's deterministic route planner",
    )
    parser.add_argument(
        "--authoring",
        choices=(
            DISABLED_MODE,
            DETERMINISTIC_TEMPLATE_MODE,
            MODEL_AUTO_MODE,
            MODEL_REQUIRED_MODE,
        ),
        default=None,
        help="override each case's typed-gap authoring policy",
    )
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument("--lean-timeout", type=int, default=None)
    parser.add_argument(
        "--jobs",
        type=int,
        default=1,
        help="number of isolated cases to execute concurrently after one runtime preflight",
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="validate the manifest and list runnable/skipped cases without executing Lean",
    )
    arguments = parser.parse_args()
    if arguments.jobs <= 0:
        parser.error("--jobs must be a positive integer")

    try:
        manifest = load_benchmark_manifest(arguments.manifest)
        selection = select_benchmark_cases(
            manifest,
            suite_ids=arguments.suite,
            case_ids=arguments.case,
            agent_phase=arguments.agent_phase,
        )
    except BenchmarkManifestError as error:
        print(
            json.dumps(
                {"schema_version": RESULT_V2, "error": error.code, "message": error.message},
                ensure_ascii=False,
            ),
            file=sys.stderr,
        )
        return 2

    skipped_rows = [
        {
            "id": skipped.case.id,
            "suite_id": skipped.case.suite_id,
            "code": skipped.code,
            "reason": skipped.reason,
            "min_agent_phase": skipped.case.min_agent_phase,
        }
        for skipped in selection.skipped
    ]
    if arguments.list:
        print(
            json.dumps(
                {
                    "schema_version": RESULT_V2,
                    "benchmark_id": manifest.benchmark_id,
                    "agent_phase": arguments.agent_phase,
                    "runnable": [
                        {"id": case.id, "suite_id": case.suite_id}
                        for case in selection.runnable
                    ],
                    "skipped_cases": skipped_rows,
                },
                ensure_ascii=False,
                sort_keys=True,
            )
        )
        return 0

    arguments.output_root.mkdir(parents=True, exist_ok=True)
    selected_authoring_modes = {
        arguments.authoring
        or str(
            case.authoring_policy.get(
                "mode",
                DETERMINISTIC_TEMPLATE_MODE
                if case.authoring_policy.get("enabled", False)
                else DISABLED_MODE,
            )
        )
        for case in selection.runnable
    }
    deepseek = (
        DeepSeekConfig.from_environment(env_file=arguments.env_file)
        if selected_authoring_modes & MODEL_MODES
        else None
    )
    preflight_timeout = arguments.lean_timeout or max(
        (int(case.resources.get("lean_timeout_seconds", 300)) for case in selection.runnable),
        default=300,
    )
    preflight = run_command(
        build_module_command(case.module for case in selection.runnable),
        cwd=ROOT / "Lean",
        timeout_seconds=preflight_timeout,
    )
    if not preflight.ok:
        report = {
            "schema_version": RESULT_V2,
            "benchmark_id": manifest.benchmark_id,
            "agent_phase": arguments.agent_phase,
            "error": "runtime_build_failed",
            "preflight": preflight.to_dict(),
            "skipped_cases": skipped_rows,
            "results": [],
        }
        (arguments.output_root / "report.json").write_text(
            json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        print(json.dumps(report, ensure_ascii=False, sort_keys=True))
        return 1

    def execute(
        case: Any, *, output_dir: Path | None = None, resume: bool = False
    ) -> tuple[dict[str, Any], Any]:
        planner = arguments.planner or case.planner
        timeout = arguments.lean_timeout or int(case.resources.get("lean_timeout_seconds", 300))
        authoring_enabled = bool(case.authoring_policy.get("enabled", False))
        authoring_mode = arguments.authoring or str(
            case.authoring_policy.get(
                "mode",
                DETERMINISTIC_TEMPLATE_MODE if authoring_enabled else DISABLED_MODE,
            )
        )
        authoring_attempt_budget = int(
            case.authoring_policy.get(
                "attempt_budget",
                case.resources.get("max_model_calls", 4 if authoring_mode in MODEL_MODES else 1),
            )
        )
        if authoring_mode in MODEL_MODES and "max_model_calls" in case.resources:
            authoring_attempt_budget = min(
                authoring_attempt_budget, int(case.resources["max_model_calls"])
            )
        case_deepseek = deepseek
        if case_deepseek is not None and authoring_mode in MODEL_MODES:
            case_deepseek = replace(
                case_deepseek,
                timeout_seconds=int(
                    case.resources.get(
                        "model_timeout_seconds", case_deepseek.timeout_seconds
                    )
                ),
                max_tokens=int(
                    case.resources.get("model_max_tokens", case_deepseek.max_tokens)
                ),
            )
        result = HardnessAgent(
            HardnessAgentConfig(
                root=ROOT,
                input_module=case.module,
                source_declaration=case.source,
                target_declaration=case.target,
                membership_declaration=case.membership,
                objective=case.objective,
                planner_mode=planner,
                catalog_mode=case.catalog_mode,
                output_dir=output_dir or (arguments.output_root / case.id),
                lean_timeout_seconds=timeout,
                deepseek=case_deepseek,
                runtime_prebuilt=True,
                authoring_mode=authoring_mode,
                authoring_attempt_budget=authoring_attempt_budget,
                resume=resume,
            )
        ).run()
        return _case_result(case, result, planner=planner), result

    primary_cases = [case for case in selection.runnable if case.resume_from_case is None]
    resume_cases = [case for case in selection.runnable if case.resume_from_case is not None]
    if arguments.jobs == 1:
        primary_runs = [execute(case) for case in primary_cases]
    else:
        with ThreadPoolExecutor(
            max_workers=min(arguments.jobs, max(1, len(primary_cases)))
        ) as executor:
            primary_runs = list(executor.map(execute, primary_cases))

    rows_by_id = {
        case.id: row for case, (row, _) in zip(primary_cases, primary_runs, strict=True)
    }
    agent_results_by_id = {
        case.id: result for case, (_, result) in zip(primary_cases, primary_runs, strict=True)
    }
    for case in resume_cases:
        planner = arguments.planner or case.planner
        source_id = case.resume_from_case
        source_result = agent_results_by_id.get(source_id or "")
        source_row = rows_by_id.get(source_id or "")
        if (
            source_result is None
            or source_row is None
            or source_result.status != "VERIFIED"
            or not source_result.authored_candidate_module
        ):
            rows_by_id[case.id] = _resume_prerequisite_failure(
                case,
                planner=planner,
                reason=f"resume source {source_id!r} did not produce a VERIFIED job-local candidate",
            )
            continue

        source_output_dir = arguments.output_root / str(source_id)
        verified_report = source_output_dir / "report.json"
        verified_receipt = source_output_dir / "receipts" / "verified-before-candidate-removal.json"
        verified_receipt.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(verified_report, verified_receipt)
        try:
            removal_receipt, _ = _remove_job_local_candidate(
                output_dir=source_output_dir,
                candidate_module=source_result.authored_candidate_module,
            )
        except (OSError, ValueError) as error:
            rows_by_id[case.id] = _resume_prerequisite_failure(
                case,
                planner=planner,
                reason=str(error),
            )
            continue

        source_row["report"] = _display_path(verified_receipt)
        row, resumed_result = execute(case, output_dir=source_output_dir, resume=True)
        row["resume_from_case"] = source_id
        row["candidate_removal_receipt"] = _display_path(removal_receipt)
        rows_by_id[case.id] = row
        agent_results_by_id[case.id] = resumed_result

    results = [rows_by_id[case.id] for case in selection.runnable]

    summary = summarize_benchmark_results(results=results, skipped=selection.skipped)
    report = {
        "schema_version": RESULT_V2,
        "runner_version": RUNNER_VERSION,
        "benchmark_id": manifest.benchmark_id,
        "manifest_schema": manifest.schema_version,
        "agent_phase": arguments.agent_phase,
        "jobs": arguments.jobs,
        "preflight": preflight.to_dict(),
        "reproducibility": {
            "public_manifest": _display_path(manifest.manifest_file),
            "public_manifest_sha256": sha256_file(manifest.manifest_file),
            "suite_sha256": {
                _display_path(Path(suite.source_file)): sha256_file(Path(suite.source_file))
                for suite in manifest.suites
            },
            "runner_sha256": sha256_file(Path(__file__)),
            "agent_runner_sha256": sha256_file(
                ROOT / "agent" / "hardness" / "runner.py"
            ),
            "lean_toolchain": (ROOT / "Lean" / "lean-toolchain")
            .read_text(encoding="utf-8")
            .strip(),
            "lean_toolchain_sha256": sha256_file(ROOT / "Lean" / "lean-toolchain"),
            "lake_manifest_sha256": sha256_file(ROOT / "Lean" / "lake-manifest.json"),
            "model_configuration": deepseek.to_public_dict() if deepseek else None,
        },
        **summary,
        "skipped_cases": skipped_rows,
        "results": results,
        "trust_boundary": {
            "manifest_is_observational": True,
            "legacy_schemas_are_not_executable": True,
            "oracle_modules_are_forbidden": True,
            "lean_reconstructs_each_final_result": True,
        },
    }
    (arguments.output_root / "report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(report, ensure_ascii=False, sort_keys=True))
    return 0 if results and summary["passed"] == summary["total"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
