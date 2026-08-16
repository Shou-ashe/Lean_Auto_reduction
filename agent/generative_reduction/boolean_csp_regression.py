"""Full recursive-agent regression over the frozen 20-case Boolean-CSP suite.

This driver intentionally lives outside ``scripts/`` so the repository keeps
one public benchmark runner.  It reads only the answer-free public suite while
cases are running and writes a separate recursive-agent report.
"""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import asdict, replace
from datetime import datetime, timezone
import json
from pathlib import Path
import time
from typing import Any, Mapping, Sequence

from agent.hardness.boolean_csp_np_hard_benchmark import load_suite
from agent.hardness.model_client import DeepSeekConfig

from .budgets import SearchBudget
from .models import ModelPolicy, Strategy
from .orchestrator import GenerativeReductionConfig, GenerativeReductionOrchestrator


FORBIDDEN_DICHOTOMY_DECLARATIONS = (
    "ComplexityReduction.Domain.BooleanCSP.Hardness.NativeTMNPHard_of_notSchaeferTractable",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.NativeTMNPHard_of_notSchaeferTractable_with_oneInThree",
    "ComplexityReduction.Domain.BooleanCSP.schaefer_dichotomy",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores.oneInThreeInterpretation",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores.naeInterpretation",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalDatabase.gadget",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores.exactlyOne_closed_of_notSchaeferTractable",
    "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores.nae_closed_of_notSchaeferTractable",
)
DEFAULT_REPORT_NAME = (
    "GENERAL_AGENT_BOOLEAN_CSP_RECURSIVE_DICHOTOMY_FREE_REAL_API_REPORT.json"
)


def recursive_benchmark_budget() -> SearchBudget:
    return SearchBudget(
        max_search_rounds=120,
        max_search_depth=16,
        max_expanded_states=512,
        max_frontier_width=24,
        max_capability_plans=512,
        max_exact_closure_candidates=16,
        max_guidance_candidates_per_goal=12,
        max_guidance_plans_per_goal=8,
        max_actions_per_provider=16,
        max_theorem_expansions_before_synthesis=4,
        min_synthesis_action_expansions=1,
        min_synthesis_materializations=1,
        synthesis_activation_deadline=2,
        stagnation_window=8,
        max_lean_checks=320,
        max_model_calls=20,
        max_strategy_calls=8,
        max_authoring_calls=12,
        max_synthesis_designs=8,
        max_authoring_attempts_per_stage=2,
        max_generated_files=24,
        max_branching_per_expansion=3,
        max_application_frames=64,
        max_data_witness_candidates=7,
        max_dependent_reinstantiations=160,
        max_action_failures_per_goal=32,
        max_frame_verification_checks=80,
        max_reconstruction_repairs=4,
        max_requeues_per_state=320,
        max_recursive_substep_plans=240,
        wall_clock_timeout_seconds=3600,
    )


def _read_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object at {path}")
    return value


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _case_label(module: str) -> str:
    return module.rsplit(".", 1)[-1]


def _run_case(
    *,
    root: Path,
    output_root: Path,
    case,
    deepseek: DeepSeekConfig,
    profile: str,
    lean_timeout_seconds: int,
    forbidden_declarations: Sequence[str],
    excluded_candidate_declarations: Sequence[str],
) -> dict[str, Any]:
    label = _case_label(case.module)
    case_output = output_root / "cases" / label
    started = time.monotonic()
    result = GenerativeReductionOrchestrator(
        GenerativeReductionConfig(
            root=root,
            input_module=case.module,
            problem_declaration=case.problem,
            output_dir=case_output,
            strategy=Strategy.BALANCED,
            profile=profile,
            model_policy=ModelPolicy.REQUIRED,
            plugins=("boolean_csp",),
            forbidden_declarations=tuple(forbidden_declarations),
            excluded_candidate_declarations=tuple(
                excluded_candidate_declarations
            ),
            budget=recursive_benchmark_budget(),
            lean_timeout_seconds=lean_timeout_seconds,
            deepseek=deepseek,
            runtime_prebuilt=True,
        )
    ).run()
    elapsed = time.monotonic() - started
    report_path = case_output / "report.json"
    search_path = case_output / "planner" / "search-outcome.json"
    search = _read_json(search_path) if search_path.is_file() else {}
    best_state = search.get("best_state") if isinstance(search.get("best_state"), dict) else {}
    generated_capabilities = (
        best_state.get("generated_capabilities", ())
        if isinstance(best_state, dict)
        else ()
    )
    capability_metrics = result.capability_metrics()
    return {
        "case_id": case.case_id,
        "case": label,
        "split": case.split,
        "module": case.module,
        "problem": case.problem,
        "proof_status": result.proof_status.value,
        "solution_classification": result.solution_classification.value,
        "qualification_status": result.qualification_status.value,
        "report": str(report_path),
        "artifact": result.artifact_file,
        "wall_seconds": elapsed,
        "expanded_state_count": result.expanded_state_count,
        "requeued_failure_state_count": result.requeued_failure_state_count,
        "pruned_cycle_count": result.pruned_cycle_count,
        "max_observed_search_depth": result.max_observed_search_depth,
        "application_frame_count": result.application_frame_count,
        "verified_application_frame_count": result.verified_application_frame_count,
        "data_binding_count": result.data_binding_count,
        "dependent_goal_activation_count": result.dependent_goal_activation_count,
        "recursive_substep_plan_count": result.recursive_substep_plan_count,
        "generated_capability_count": result.generated_capability_count,
        "strategy_valid_proposal_count": result.strategy_valid_proposal_count,
        "strategy_applied_decision_count": result.strategy_applied_decision_count,
        "strategy_fallback_count": result.strategy_fallback_count,
        "strategy_rejected_count": result.strategy_rejected_count,
        "unused_strategy_call_count": result.unused_strategy_call_count,
        "strategy_effect_receipts": [
            receipt.__dict__ for receipt in result.strategy_effect_receipts
        ],
        "finite_candidate_count": result.finite_candidate_count,
        "finite_counterexample_count": result.finite_counterexample_count,
        "finite_certificate_count": result.finite_certificate_count,
        "capability_compiler_candidate_count": (
            result.capability_compiler_candidate_count
        ),
        "capability_compiler_certificate_count": (
            result.capability_compiler_certificate_count
        ),
        "generated_lean_check_count": result.generated_lean_check_count,
        "generated_lean_success_count": result.generated_lean_success_count,
        "capability_registration_count": result.capability_registration_count,
        "synthesis_design_count": result.synthesis_design_count,
        "context_expansion_count": result.context_expansion_count,
        "repair_authoring_count": result.repair_authoring_count,
        "duplicate_candidate_rejection_count": (
            result.duplicate_candidate_rejection_count
        ),
        "repeated_diagnostic_count": result.repeated_diagnostic_count,
        "context_insufficient_count": result.context_insufficient_count,
        "unresolved_probe_handle_count": result.unresolved_probe_handle_count,
        "rejected_nonexecutable_design_count": (
            result.rejected_nonexecutable_design_count
        ),
        "synthesis_designs": list(result.synthesis_designs),
        "context_capsule_ids": [
            item.get("capsule_id")
            for item in result.context_capsules
            if isinstance(item, dict)
        ],
        "context_capsules": list(result.context_capsules),
        "generation_context_ready_count": sum(
            bool(item.get("generation_context_ready"))
            for item in result.context_capsules
            if isinstance(item, dict)
        ),
        "repair_lineage": list(result.repair_lineage),
        "capability_plans": [asdict(item) for item in result.capability_plans],
        "theorem_application_plans": [
            asdict(item) for item in result.theorem_application_plans
        ],
        "generator_briefs": [asdict(item) for item in result.generator_briefs],
        "generator_results": [asdict(item) for item in result.generator_results],
        "contribution_receipts": [
            asdict(item) for item in result.contribution_receipts
        ],
        "planner_effect_receipts": [
            asdict(item) for item in result.planner_effect_receipts
        ],
        "typed_capability_plans": list(result.typed_capability_plans),
        "capability_budget_reservations": list(
            ((search.get("budget") or {}).get("capacity_reservations") or ())
            if isinstance(search.get("budget"), dict)
            else ()
        ),
        "frontier_exhaustion_receipt": result.frontier_exhaustion_receipt,
        "blocker": result.blocker,
        "model_calls": [
            {
                "purpose": call.purpose,
                "provider": call.provider,
                "model": call.model,
                "called": call.called,
                "ok": call.ok,
                "status_code": call.status_code,
                "attempts": call.attempts,
                "duration_seconds": call.duration_seconds,
                "usage": call.usage,
                "response_sha256": call.response_sha256,
                "error": call.error,
                "proposal_id": call.proposal_id,
            }
            for call in result.model_calls
        ],
        "generated_capabilities": [
            {
                "declaration": item.get("declaration"),
                "exact_type": item.get("exact_type"),
                "source_hash": item.get("source_hash"),
                "action_id": item.get("action_id"),
            }
            for item in generated_capabilities
            if isinstance(item, dict)
        ],
        "generated_declaration_used_by_final_artifact": bool(
            result.generation_evidence.generated_edge_used_by_final_artifact
            or (
                result.proof_status.value == "VERIFIED"
                and result.generated_capability_count > 0
            )
        ),
        "verification": result.verification.__dict__,
        "final_route_audit_receipt": result.final_route_audit_receipt,
        "capability_metrics": capability_metrics,
        **capability_metrics,
        "model_call_accounting_complete": True,
    }


def _exception_case_row(*, output_root: Path, case, error: Exception) -> dict[str, Any]:
    label = _case_label(case.module)
    return {
        "case_id": case.case_id,
        "case": label,
        "split": case.split,
        "module": case.module,
        "problem": case.problem,
        "proof_status": "INTERNAL_ERROR",
        "solution_classification": "NONE",
        "qualification_status": "NOT_RUN",
        "report": str(output_root / "cases" / label / "report.json"),
        "artifact": None,
        "wall_seconds": 0.0,
        "expanded_state_count": 0,
        "requeued_failure_state_count": 0,
        "pruned_cycle_count": 0,
        "max_observed_search_depth": 0,
        "application_frame_count": 0,
        "verified_application_frame_count": 0,
        "data_binding_count": 0,
        "dependent_goal_activation_count": 0,
        "recursive_substep_plan_count": 0,
        "generated_capability_count": 0,
        "strategy_valid_proposal_count": 0,
        "strategy_applied_decision_count": 0,
        "strategy_fallback_count": 0,
        "strategy_rejected_count": 0,
        "unused_strategy_call_count": 0,
        "strategy_effect_receipts": [],
        "finite_candidate_count": 0,
        "finite_counterexample_count": 0,
        "finite_certificate_count": 0,
        "capability_compiler_candidate_count": 0,
        "capability_compiler_certificate_count": 0,
        "generated_lean_check_count": 0,
        "generated_lean_success_count": 0,
        "capability_registration_count": 0,
        "synthesis_design_count": 0,
        "context_expansion_count": 0,
        "repair_authoring_count": 0,
        "duplicate_candidate_rejection_count": 0,
        "repeated_diagnostic_count": 0,
        "context_insufficient_count": 0,
        "unresolved_probe_handle_count": 0,
        "rejected_nonexecutable_design_count": 0,
        "synthesis_designs": [],
        "context_capsule_ids": [],
        "context_capsules": [],
        "generation_context_ready_count": 0,
        "repair_lineage": [],
        "capability_plans": [],
        "theorem_application_plans": [],
        "generator_briefs": [],
        "generator_results": [],
        "contribution_receipts": [],
        "planner_effect_receipts": [],
        "typed_capability_plans": [],
        "capability_budget_reservations": [],
        "frontier_exhaustion_receipt": None,
        "blocker": f"{type(error).__name__}: {error}",
        "model_calls": [],
        "generated_capabilities": [],
        "generated_declaration_used_by_final_artifact": False,
        "verification": {
            "exact_type_verified": False,
            "kernel_verified": False,
            "independent_replay_passed": False,
            "axiom_audit_passed": False,
            "placeholder_scan_passed": False,
            "endpoint_equality_audit_passed": False,
            "same_index_audit_passed": False,
        },
        "final_route_audit_receipt": None,
        "capability_metrics": {},
        "model_call_accounting_complete": False,
        "exception_type": type(error).__name__,
    }


def _usage_totals(rows: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    totals: Counter[str] = Counter()
    for row in rows:
        for call in row.get("model_calls", ()):
            usage = call.get("usage") if isinstance(call, dict) else None
            if not isinstance(usage, dict):
                continue
            for key, value in usage.items():
                if isinstance(value, int):
                    totals[str(key)] += value
    return dict(totals)


def run_recursive_boolean_csp_regression(
    *,
    root: Path,
    output_root: Path,
    env_file: Path,
    jobs: int = 4,
    profile: str = "benchmark",
    lean_timeout_seconds: int = 600,
    model: str | None = None,
    model_timeout_seconds: int | None = None,
    model_max_tokens: int | None = None,
    model_max_retries: int | None = None,
    reasoning_effort: str | None = None,
    report_path: Path | None = None,
    extra_forbidden_declarations: Sequence[str] = (),
    excluded_candidate_declarations: Sequence[str] = (),
) -> dict[str, Any]:
    if jobs < 1 or jobs > 4:
        raise ValueError("jobs must be in 1..4")
    root = root.resolve()
    output_root = output_root.resolve()
    suite_path = root / "Benchmark" / "Hardness" / "Suites" / "boolean_csp_np_hard_public_v1.json"
    suite = load_suite(suite_path)
    configured = DeepSeekConfig.from_environment(env_file=env_file)
    deepseek = replace(
        configured,
        **{
            key: value
            for key, value in {
                "model": model,
                "timeout_seconds": model_timeout_seconds,
                "max_tokens": model_max_tokens,
                "max_retries": model_max_retries,
                "reasoning_effort": reasoning_effort,
            }.items()
            if value is not None
        },
    )
    if not deepseek.api_key:
        raise ValueError("real API regression requires DEEPSEEK_API_KEY")
    forbidden_declarations = tuple(
        dict.fromkeys(
            (
                *FORBIDDEN_DICHOTOMY_DECLARATIONS,
                *extra_forbidden_declarations,
            )
        )
    )
    output_root.mkdir(parents=True, exist_ok=True)
    started_at = datetime.now(timezone.utc)
    started = time.monotonic()
    rows: list[dict[str, Any]] = []
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        futures = {
            executor.submit(
                _run_case,
                root=root,
                output_root=output_root,
                case=case,
                deepseek=deepseek,
                profile=profile,
                lean_timeout_seconds=lean_timeout_seconds,
                forbidden_declarations=forbidden_declarations,
                excluded_candidate_declarations=excluded_candidate_declarations,
            ): case
            for case in suite.cases
        }
        for future in as_completed(futures):
            case = futures[future]
            try:
                row = future.result()
            except Exception as error:
                row = _exception_case_row(
                    output_root=output_root,
                    case=case,
                    error=error,
                )
            rows.append(row)
            rows.sort(key=lambda item: item["case_id"])
            _write_json(
                output_root / "progress.json",
                {
                    "schema_version": "general_recursive_boolean_csp_progress_v1",
                    "completed_case_count": len(rows),
                    "selected_case_count": len(suite.cases),
                    "cases": rows,
                },
            )
    completed_at = datetime.now(timezone.utc)
    model_calls = [call for row in rows for call in row["model_calls"]]
    status_counts = Counter(row["proof_status"] for row in rows)
    http_counts = Counter(
        str(call["status_code"])
        for call in model_calls
        if call.get("status_code") is not None
    )
    report = {
        "schema_version": "general_agent_boolean_csp_recursive_real_api_report_v1",
        "date": completed_at.date().isoformat(),
        "suite": {
            "suite_id": suite.suite_id,
            "suite_sha256": suite.sha256,
            "selected_case_count": len(suite.cases),
            "completed_case_count": len(rows),
            "oracle_accessed_during_run": False,
        },
        "route_policy": {
            "forbidden_declarations": list(forbidden_declarations),
            "excluded_candidate_declarations": list(
                excluded_candidate_declarations
            ),
            "final_transitive_dependency_audit_enabled": True,
        },
        "real_api": {
            **deepseek.to_public_dict(),
            "provider": "deepseek",
            "total_calls": sum(bool(call["called"]) for call in model_calls),
            "http_200_calls": sum(call.get("status_code") == 200 for call in model_calls),
            "accepted_response_count": sum(bool(call["ok"]) for call in model_calls),
            "http_status_counts": dict(http_counts),
            "call_purposes": dict(Counter(call["purpose"] for call in model_calls)),
            "usage": _usage_totals(rows),
            "call_accounting_complete": all(
                row.get("model_call_accounting_complete", True) for row in rows
            ),
            "external_payload_classes": [
                "exact Lean child goals",
                "candidate theorem names",
                "Lean diagnostics",
                "local construction contracts",
            ],
        },
        "results": {
            "status_counts": dict(status_counts),
            "verified_case_count": status_counts.get("VERIFIED", 0),
            "generated_capability_case_count": sum(
                row["generated_capability_count"] > 0 for row in rows
            ),
            "generated_capability_used_case_count": sum(
                row["generated_declaration_used_by_final_artifact"] for row in rows
            ),
            "total_expanded_states": sum(row["expanded_state_count"] for row in rows),
            "total_requeues": sum(row["requeued_failure_state_count"] for row in rows),
            "total_application_frames": sum(row["application_frame_count"] for row in rows),
            "total_verified_frames": sum(
                row["verified_application_frame_count"] for row in rows
            ),
            "total_data_bindings": sum(row["data_binding_count"] for row in rows),
            "total_dependent_goal_activations": sum(
                row["dependent_goal_activation_count"] for row in rows
            ),
            "total_strategy_valid_proposals": sum(
                row["strategy_valid_proposal_count"] for row in rows
            ),
            "total_strategy_applied_decisions": sum(
                row["strategy_applied_decision_count"] for row in rows
            ),
            "total_strategy_fallbacks": sum(
                row["strategy_fallback_count"] for row in rows
            ),
            "total_strategy_rejections": sum(
                row["strategy_rejected_count"] for row in rows
            ),
            "total_unused_strategy_calls": sum(
                row["unused_strategy_call_count"] for row in rows
            ),
            "total_finite_candidates": sum(
                row["finite_candidate_count"] for row in rows
            ),
            "total_finite_counterexamples": sum(
                row["finite_counterexample_count"] for row in rows
            ),
            "total_finite_certificates": sum(
                row["finite_certificate_count"] for row in rows
            ),
            "total_capability_compiler_candidates": sum(
                row["capability_compiler_candidate_count"] for row in rows
            ),
            "total_capability_compiler_certificates": sum(
                row["capability_compiler_certificate_count"] for row in rows
            ),
            "total_generated_lean_checks": sum(
                row["generated_lean_check_count"] for row in rows
            ),
            "total_generated_lean_successes": sum(
                row["generated_lean_success_count"] for row in rows
            ),
            "total_capability_registrations": sum(
                row["capability_registration_count"] for row in rows
            ),
            "total_synthesis_designs": sum(
                row["synthesis_design_count"] for row in rows
            ),
            "total_context_expansions": sum(
                row["context_expansion_count"] for row in rows
            ),
            "total_repair_authoring_calls": sum(
                row["repair_authoring_count"] for row in rows
            ),
            "total_duplicate_candidate_rejections": sum(
                row["duplicate_candidate_rejection_count"] for row in rows
            ),
            "total_repeated_diagnostics": sum(
                row["repeated_diagnostic_count"] for row in rows
            ),
            "total_context_insufficient_events": sum(
                row["context_insufficient_count"] for row in rows
            ),
            "total_unresolved_probe_handles": sum(
                row["unresolved_probe_handle_count"] for row in rows
            ),
            "total_rejected_nonexecutable_designs": sum(
                row["rejected_nonexecutable_design_count"] for row in rows
            ),
            "maximum_recursive_depth": max(
                (row["max_observed_search_depth"] for row in rows), default=0
            ),
        },
        "timing": {
            "jobs": jobs,
            "started_at_utc": started_at.isoformat(),
            "completed_at_utc": completed_at.isoformat(),
            "wall_seconds": time.monotonic() - started,
        },
        "cases": rows,
    }
    blocked_without_receipt = [
        row["case_id"]
        for row in rows
        if row["proof_status"] == "BLOCKED"
        and not row.get("frontier_exhaustion_receipt")
    ]
    failed_verified_audits = [
        row["case_id"]
        for row in rows
        if row["proof_status"] == "VERIFIED"
        and not bool((row.get("final_route_audit_receipt") or {}).get("passed"))
    ]
    report["validation"] = {
        "all_20_cases_completed": len(rows) == len(suite.cases) == 20,
        "blocked_frontier_receipts_complete": not blocked_without_receipt,
        "blocked_cases_missing_frontier_receipt": blocked_without_receipt,
        "verified_route_audits_passed": not failed_verified_audits,
        "verified_cases_with_failed_route_audit": failed_verified_audits,
        "all_called_requests_http_200": (
            report["real_api"]["total_calls"]
            == report["real_api"]["http_200_calls"]
        ),
        "forbidden_direct_or_transitive_dependency_count": len(
            failed_verified_audits
        ),
        "unused_strategy_call_count_is_zero": not any(
            row["unused_strategy_call_count"] for row in rows
        ),
        "strategy_accounting_complete": all(
            sum(
                bool(call.get("called")) and call.get("purpose") == "strategy-proposal"
                for call in row.get("model_calls", ())
            )
            == row["strategy_applied_decision_count"]
            + row["strategy_fallback_count"]
            + row["strategy_rejected_count"]
            for row in rows
        ),
        "repair_prompts_have_matching_base_hash": all(
            all(
                item.get("kind") != "repair" or bool(item.get("base_sha256"))
                for item in row.get("repair_lineage", ())
                if isinstance(item, dict)
            )
            for row in rows
        ),
        "context_capsule_receipts_present_for_authoring": all(
            not any(
                bool(call.get("called"))
                and call.get("purpose", "").startswith("lean-authoring-")
                for call in row.get("model_calls", ())
            )
            or bool(row.get("context_capsule_ids"))
            for row in rows
        ),
        "unresolved_probe_handle_count_is_zero": not any(
            row["unresolved_probe_handle_count"] for row in rows
        ),
        "empty_context_generator_call_count_is_zero": not any(
            row["context_insufficient_count"]
            and any(
                call.get("purpose", "").startswith("lean-authoring-")
                for call in row.get("model_calls", ())
            )
            for row in rows
        ),
        "planner_effect_receipts_cover_generator_briefs": all(
            {
                item.get("brief_id")
                for item in row.get("generator_briefs", ())
                if isinstance(item, dict)
            }
            <= {
                item.get("generated_brief_id")
                for item in row.get("planner_effect_receipts", ())
                if isinstance(item, dict)
            }
            for row in rows
        ),
        "planner_accounting_consistent": all(
            bool(row.get("planner_accounting_consistent", True)) for row in rows
        ),
        "generated_capability_accounting_consistent": all(
            bool(row.get("generated_capability_accounting_consistent", True))
            for row in rows
        ),
    }
    metric_names = tuple(
        key
        for key, value in (rows[0].get("capability_metrics", {}) if rows else {}).items()
        if isinstance(value, int) and not isinstance(value, bool)
    )
    report["capability_metrics"] = {
        key: sum(int(row.get(key, 0)) for row in rows) for key in metric_names
    }
    _write_json(output_root / "summary.json", report)
    if report_path is not None:
        _write_json(report_path.resolve(), report)
    return report


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Run the recursive general agent on all 20 public Boolean-CSP cases"
    )
    root = Path(__file__).resolve().parents[2]
    parser.add_argument("--root", type=Path, default=root)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--env-file", type=Path, default=root / ".env")
    parser.add_argument("--jobs", type=int, default=4)
    parser.add_argument("--profile", choices=("research", "strict-release", "benchmark"), default="benchmark")
    parser.add_argument("--lean-timeout", type=int, default=600)
    parser.add_argument("--model", default=None)
    parser.add_argument("--model-timeout", type=int, default=180)
    parser.add_argument("--model-max-tokens", type=int, default=12000)
    parser.add_argument("--model-max-retries", type=int, default=0)
    parser.add_argument("--reasoning-effort", default="low")
    parser.add_argument(
        "--forbid-declaration",
        action="append",
        default=[],
        help=(
            "additional fully-qualified Lean declaration forbidden from the selected "
            "or elaborated transitive proof route; may be repeated"
        ),
    )
    parser.add_argument(
        "--exclude-candidate-declaration",
        action="append",
        default=[],
        help=(
            "additional declaration excluded only from proof-search choices; "
            "may be repeated"
        ),
    )
    parser.add_argument(
        "--report-path",
        type=Path,
        default=root / "Reports" / DEFAULT_REPORT_NAME,
    )
    return parser


def main() -> int:
    arguments = build_parser().parse_args()
    report = run_recursive_boolean_csp_regression(
        root=arguments.root,
        output_root=arguments.output_root,
        env_file=arguments.env_file,
        jobs=arguments.jobs,
        profile=arguments.profile,
        lean_timeout_seconds=arguments.lean_timeout,
        model=arguments.model,
        model_timeout_seconds=arguments.model_timeout,
        model_max_tokens=arguments.model_max_tokens,
        model_max_retries=arguments.model_max_retries,
        reasoning_effort=arguments.reasoning_effort,
        report_path=arguments.report_path,
        extra_forbidden_declarations=tuple(arguments.forbid_declaration),
        excluded_candidate_declarations=tuple(
            arguments.exclude_candidate_declaration
        ),
    )
    print(json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True))
    return 0 if report["suite"]["completed_case_count"] == 20 else 2


if __name__ == "__main__":
    raise SystemExit(main())


__all__ = [
    "FORBIDDEN_DICHOTOMY_DECLARATIONS",
    "DEFAULT_REPORT_NAME",
    "recursive_benchmark_budget",
    "run_recursive_boolean_csp_regression",
]
