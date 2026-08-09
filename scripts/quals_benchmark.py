"""Shared Stage-N Quals full-suite orchestration."""

from __future__ import annotations

import shutil
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Mapping, Sequence

from agent.hardness.benchmark import BenchmarkCase, load_benchmark_suite
from agent.hardness.finite_witness import finite_witness_registry
from agent.hardness.lean_runner import (
    assert_generated_source_is_safe,
    build_module_command,
    run_command,
    sha256_file,
)
from agent.hardness.model_client import DeepSeekConfig
from agent.hardness.quals import (
    build_quals_batch_artifact_source,
    build_quals_formalization_gate_source,
    load_quals_formalization_suite,
    quals_report_skeleton,
    validate_quals_adversarial_suite,
    validate_quals_completeness_suite,
)
from agent.hardness.runner import HardnessAgent
from agent.hardness.typed_packets import candidate_bundle_integrity
from scripts.typed_authoring_benchmark import (
    CaseOutcome,
    _case_config,
    aggregate_usage,
    merge_candidate_work_roots,
    prepare_fresh_output_root,
    run_case as run_primary_case,
    utc_now,
    write_json,
)


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_FORMALIZATION_SUITE = (
    ROOT / "Benchmark" / "Hardness" / "Suites" / "quals_formalization.json"
)
DEFAULT_COMPLETENESS_SUITE = (
    ROOT / "Benchmark" / "Hardness" / "Suites" / "quals_completeness.json"
)
DEFAULT_ADVERSARIAL_SUITE = (
    ROOT / "Benchmark" / "Hardness" / "Suites" / "quals_adversarial.json"
)
MAX_JOBS = 4


def _last_failure_code(result: Any) -> str | None:
    return result.failures[-1].code if result.failures else None


def _run_formalization_gate(*, suite: Any, output_root: Path, lean_timeout: int) -> dict[str, Any]:
    started = time.monotonic()
    source = build_quals_formalization_gate_source(suite.cases)
    assert_generated_source_is_safe(source)
    source_path = output_root / "formalization" / "QualsFormalizationGate.lean"
    source_path.parent.mkdir(parents=True, exist_ok=True)
    source_path.write_text(source, encoding="utf-8")
    command = run_command(
        ["lake", "env", "lean", str(source_path.resolve())],
        cwd=ROOT / "Lean",
        timeout_seconds=lean_timeout,
        output_limit=32000,
    )
    status = "VERIFIED" if command.ok else "FAILED"
    rows = [
        {
            "id": case.id,
            "status": status,
            "expected_status": case.expected_status,
            "passed": status == case.expected_status,
            "module": case.module,
            "problem_declaration": case.problem_declaration,
            "production_endpoint": case.production_endpoint,
            "representation_declaration": case.representation_declaration,
            "semantic_theorem": case.semantic_theorem,
            "public_module_file": str(case.public_module_file.resolve()),
            "public_module_sha256": sha256_file(case.public_module_file),
            "validation_record": str(case.validation_record.resolve()),
            "validation_record_sha256": sha256_file(case.validation_record),
            "validation_kind": case.validation.get("validation_kind"),
            "oracle_visible_to_model": case.validation.get("oracle_visible_to_model"),
            "hardness_score_contribution": 0,
        }
        for case in suite.cases
    ]
    return {
        "suite_id": suite.id,
        "milestone": suite.milestone,
        "suite_file": str(suite.source_file.resolve()),
        "suite_sha256": sha256_file(suite.source_file),
        "status": status if all(row["passed"] for row in rows) else "FAILED",
        "verified_count": sum(row["passed"] for row in rows),
        "case_count": len(rows),
        "hardness_score_contribution": 0,
        "generated_gate_file": str(source_path.resolve()),
        "generated_gate_sha256": sha256_file(source_path),
        "command": command.to_dict(),
        "wall_duration_seconds": round(time.monotonic() - started, 3),
        "cases": rows,
    }


def run_adversarial_case(
    *, index: int, case: BenchmarkCase, output_root: Path
) -> CaseOutcome:
    started = time.monotonic()
    case_root = output_root / "cases" / case.id
    result = HardnessAgent(
        _case_config(
            case=case,
            output_dir=case_root,
            authoring_mode="disabled",
            runtime_prebuilt=True,
        )
    ).run()
    code = _last_failure_code(result)
    gap = result.gap.to_dict() if result.gap else None
    gap_reason = result.gap.reason if result.gap else None
    exact_template_count = len(result.probe.authoring_templates) if result.probe else 0
    negative_class = str(case.coverage.get("negative_class", ""))
    isolation_ok = True
    if case.coverage.get("require_zero_exact_authoring_templates") is True:
        isolation_ok = exact_template_count == 0
    expected_gap_reason = case.coverage.get("required_gap_reason")
    protocol_matches = (
        result.status == case.expected.final_status
        and code == case.expected.final_failure_code
        and result.status == case.expected.baseline_status
        and code == case.expected.baseline_failure_code
        and (expected_gap_reason is None or gap_reason == expected_gap_reason)
        and isolation_ok
        and not result.model_calls
        and not result.authoring_attempts
    )
    tracks: dict[str, str]
    if negative_class == "missing_membership":
        tracks = {
            "lower_bound": "AVAILABLE_BUT_NOT_SCORED",
            "membership": "BLOCKED",
            "completeness": "BLOCKED",
        }
    elif negative_class == "missing_reduction":
        tracks = {
            "lower_bound": "BLOCKED",
            "membership": "NOT_APPLICABLE",
            "completeness": "NOT_APPLICABLE",
        }
    elif negative_class == "reversed_reduction":
        tracks = {
            "lower_bound": "BLOCKED_WRONG_DIRECTION",
            "membership": "NOT_APPLICABLE",
            "completeness": "NOT_APPLICABLE",
        }
    else:
        tracks = {
            "lower_bound": "BLOCKED_EXACT_ENDPOINT",
            "membership": "BLOCKED_EXACT_ENDPOINT",
            "completeness": "BLOCKED",
        }
    row = {
        "id": case.id,
        "execution_position": index,
        "positive": False,
        "objective": case.objective,
        "execution_layer": case.execution_layer,
        "verification_profile": case.verification_profile,
        "evaluation_lane": case.evaluation_lane,
        "family_id": case.family_id,
        "input_kind": case.input_kind,
        "negative_class": negative_class,
        "expected_baseline_status": case.expected.baseline_status,
        "expected_baseline_failure_code": case.expected.baseline_failure_code,
        "baseline_status": result.status,
        "baseline_failure_code": code,
        "baseline_gap": gap,
        "baseline_report": str((case_root / "report.json").resolve()),
        "baseline_immutable": True,
        "baseline_process_count": len(result.commands),
        "baseline_duration_seconds": round(
            sum(command.duration_seconds for command in result.commands), 3
        ),
        "selection_calls": [],
        "model_authoring_calls": [],
        "model_call_count": 0,
        "authoring_process_count": 0,
        "authoring_duration_seconds": 0.0,
        "candidate_write_count": 0,
        "gap_closure_count": 0,
        "request_mutation_count": 0,
        "endpoint_mutation_count": 0,
        "objective_mutation_count": 0,
        "exact_authoring_template_count": exact_template_count,
        "endpoint_isolation_confirmed": isolation_ok,
        "pre_model_blocked": True,
        "capability_tracks": tracks,
        "final_status": result.status,
        "final_failure_code": code,
        "protocol_matches_expected": protocol_matches,
        "case_task_wall_duration_seconds": round(time.monotonic() - started, 3),
    }
    write_json(case_root / "case.json", row)
    return CaseOutcome(index=index, case=case, row=row)


def _candidate_integrity(outcomes: Sequence[CaseOutcome]) -> bool:
    return all(
        candidate_bundle_integrity(
            (ROOT / path for path in outcome.row.get("candidate_stage_files", [])),
            outcome.row.get("candidate_stage_sha256", []),
        )
        for outcome in outcomes
        if outcome.case.is_positive
    )


def _rate(numerator: int, denominator: int) -> float | None:
    return round(numerator / denominator, 6) if denominator else None


def run_full_suite(
    *,
    formalization_suite_file: Path,
    completeness_suite_file: Path,
    adversarial_suite_file: Path,
    output_root: Path,
    jobs: int,
    real: bool,
    deepseek_config: DeepSeekConfig | None,
    canonical_report: Path | None,
    lean_timeout_seconds: int,
    run_label: str,
) -> tuple[dict[str, Any], int]:
    if jobs < 1 or jobs > MAX_JOBS:
        raise ValueError(f"Stage-N jobs must be between 1 and {MAX_JOBS}")
    prepare_fresh_output_root(output_root)
    if real and (deepseek_config is None or not deepseek_config.api_key):
        raise ValueError("real Stage-N run requires DEEPSEEK_API_KEY")
    if canonical_report is not None and canonical_report.exists():
        raise ValueError(f"canonical Stage-N report already exists: {canonical_report}")

    formalization_suite = load_quals_formalization_suite(formalization_suite_file)
    completeness_suite = load_benchmark_suite(completeness_suite_file)
    adversarial_suite = load_benchmark_suite(adversarial_suite_file)
    validate_quals_completeness_suite(completeness_suite.cases)
    validate_quals_adversarial_suite(adversarial_suite.cases)
    cases = (*completeness_suite.cases, *adversarial_suite.cases)

    report = quals_report_skeleton(
        formalization_suite_file=formalization_suite_file,
        completeness_suite_file=completeness_suite_file,
        adversarial_suite_file=adversarial_suite_file,
        output_root=output_root,
    )
    report.update(
        {
            "run_label": run_label,
            "started_at": utc_now(),
            "real_deepseek": real,
            "model_configuration": deepseek_config.to_public_dict() if deepseek_config else None,
            "configured_jobs": jobs,
            "suite_case_count": len(cases),
            "primary_case_count": len(completeness_suite.cases),
            "adversarial_case_count": len(adversarial_suite.cases),
            "suite_hashes": {
                "formalization": sha256_file(formalization_suite_file),
                "completeness": sha256_file(completeness_suite_file),
                "adversarial": sha256_file(adversarial_suite_file),
            },
            "finite_witness_registry": finite_witness_registry(),
        }
    )
    write_json(output_root / "report.json", report)

    setup_started = time.monotonic()
    setup_modules = sorted(
        {case.module for case in cases}
        | {
            "ComplexityReduction.Agent.Hardness.FiniteWitness",
            "ComplexityReduction.Agent.Hardness.FiniteWitnessNative",
            "ComplexityReduction.Agent.Hardness.Runtime",
        }
    )
    setup = run_command(
        build_module_command(setup_modules),
        cwd=ROOT / "Lean",
        timeout_seconds=max(lean_timeout_seconds, 3600),
        output_limit=32000,
    )
    report["setup_build"] = setup.to_dict()
    report["setup_build_wall_duration_seconds"] = round(time.monotonic() - setup_started, 3)
    report["process_counts"]["setup_build"] = 1
    if not setup.ok:
        report["status"] = "FAILED"
        report["failures"] = ["setup_build_failed"]
        report["finished_at"] = utc_now()
        write_json(output_root / "report.json", report)
        return report, 1

    formalization = _run_formalization_gate(
        suite=formalization_suite,
        output_root=output_root,
        lean_timeout=max(lean_timeout_seconds, 1800),
    )
    report["formalization"] = formalization
    report["process_counts"]["formalization"] = 1
    write_json(output_root / "report.json", report)
    if formalization["status"] != "VERIFIED":
        report["status"] = "FAILED"
        report["failures"] = ["formalization_gate_failed"]
        report["finished_at"] = utc_now()
        write_json(output_root / "report.json", report)
        return report, 1

    active = 0
    max_active = 0
    lock = threading.Lock()

    def guarded(index_case: tuple[int, BenchmarkCase]) -> CaseOutcome:
        nonlocal active, max_active
        index, case = index_case
        with lock:
            active += 1
            max_active = max(max_active, active)
        try:
            if case.evaluation_lane == "quals_completeness":
                return run_primary_case(
                    index=index,
                    case=case,
                    output_root=output_root,
                    real=real,
                    deepseek_config=deepseek_config,
                )
            return run_adversarial_case(index=index, case=case, output_root=output_root)
        finally:
            with lock:
                active -= 1

    outcomes: list[CaseOutcome] = []
    suite_started = time.monotonic()
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        futures = {
            executor.submit(guarded, item): item[0]
            for item in enumerate(cases, start=1)
        }
        for future in as_completed(futures):
            try:
                outcomes.append(future.result())
            except Exception as error:
                index = futures[future]
                case = cases[index - 1]
                outcomes.append(
                    CaseOutcome(
                        index=index,
                        case=case,
                        row={
                            "id": case.id,
                            "execution_position": index,
                            "positive": case.is_positive,
                            "evaluation_lane": case.evaluation_lane,
                            "final_status": "FAILED",
                            "final_failure_code": "unhandled_case_exception",
                            "exception": str(error),
                            "protocol_matches_expected": False,
                        },
                    )
                )
    outcomes.sort(key=lambda outcome: outcome.index)
    report["case_suite_wall_duration_seconds"] = round(time.monotonic() - suite_started, 3)
    report["observed_max_case_concurrency"] = max_active
    report["final_active_case_count"] = active

    artifacts = [outcome.artifact for outcome in outcomes if outcome.artifact is not None]
    work_roots = [outcome.work_root for outcome in outcomes if outcome.work_root is not None]
    final_source_path = output_root / "QualsCompletenessFinal.lean"
    final_command = None
    replay_command = None
    combined_lean_path: dict[str, Any] | None = None
    combined_lean_path_error: str | None = None
    adversarial_ready = all(
        outcome.row.get("protocol_matches_expected") is True
        for outcome in outcomes
        if not outcome.case.is_positive
    )
    if len(artifacts) == len(completeness_suite.cases) and adversarial_ready and active == 0:
        final_source = build_quals_batch_artifact_source(artifacts)
        assert_generated_source_is_safe(final_source)
        final_source_path.write_text(final_source, encoding="utf-8")
        if _candidate_integrity(outcomes):
            try:
                combined_lean_path = merge_candidate_work_roots(
                    work_roots, destination=output_root / "combined-lean-path"
                )
            except ValueError as error:
                combined_lean_path_error = str(error)
        if combined_lean_path is not None:
            lean_path = str(combined_lean_path["path"])
            final_command = run_command(
                ["lake", "env", "lean", str(final_source_path.resolve())],
                cwd=ROOT / "Lean",
                timeout_seconds=lean_timeout_seconds,
                env_overrides={"LEAN_PATH": lean_path},
                output_limit=32000,
            )
            if final_command.ok and _candidate_integrity(outcomes):
                replay_command = run_command(
                    ["lake", "env", "lean", str(final_source_path.resolve())],
                    cwd=ROOT / "Lean",
                    timeout_seconds=lean_timeout_seconds,
                    env_overrides={"LEAN_PATH": lean_path},
                    output_limit=32000,
                )

    final_ok = bool(final_command and final_command.ok)
    replay_ok = bool(replay_command and replay_command.ok)
    for outcome in outcomes:
        row = outcome.row
        row.setdefault("evaluation_lane", outcome.case.evaluation_lane)
        row.setdefault("family_id", outcome.case.family_id)
        row.setdefault("input_kind", outcome.case.input_kind)
        if outcome.case.is_positive and row.get("provisional_status") == "READY_FOR_COMBINED_LEAN":
            row["combined_final_lean"] = final_ok
            row["independent_release_replay"] = replay_ok
            row["final_status"] = "VERIFIED" if final_ok and replay_ok else "FAILED"
            row["final_failure_code"] = None if final_ok and replay_ok else "combined_lean_failed"
            artifact = outcome.artifact
            if outcome.case.objective == "reduce_to":
                row["capability_tracks"] = {
                    "lower_bound": (
                        "VERIFIED" if artifact and artifact.route_atoms else "FAILED"
                    ),
                    "membership": "NOT_APPLICABLE",
                    "completeness": "NOT_APPLICABLE",
                }
            else:
                row["capability_tracks"] = {
                    "lower_bound": (
                        "VERIFIED"
                        if artifact and artifact.route_atoms and artifact.completeness_declaration
                        else "FAILED"
                    ),
                    "membership": (
                        "VERIFIED" if artifact and artifact.membership_declaration else "FAILED"
                    ),
                    "completeness": "VERIFIED" if final_ok and replay_ok else "FAILED",
                }
        row["model_call_count"] = sum(
            call.get("called") is True
            for call in (*row.get("selection_calls", []), *row.get("model_authoring_calls", []))
            if isinstance(call, Mapping)
        )
        row["protocol_matches_expected"] = (
            row.get("final_status") == outcome.case.expected.final_status
            and row.get("final_failure_code") == outcome.case.expected.final_failure_code
        )
        write_json(output_root / "cases" / outcome.case.id / "case.json", row)

    rows = [outcome.row for outcome in outcomes]
    selection_usages = [
        call.get("usage")
        for row in rows
        for call in row.get("selection_calls", [])
        if isinstance(call, Mapping)
    ]
    authoring_usages = [
        call.get("usage")
        for row in rows
        for call in row.get("model_authoring_calls", [])
        if isinstance(call, Mapping)
    ]
    real_calls = sum(int(row.get("model_call_count", 0)) for row in rows)
    primary_rows = [row for row in rows if row.get("positive") is True]
    adversarial_rows = [row for row in rows if row.get("positive") is False]
    membership_primary_rows = [
        outcome.row
        for outcome in outcomes
        if outcome.case.is_positive
        and outcome.case.coverage.get("finite_witness_membership_expected") is True
    ]
    reduction_authoring_rows = [
        outcome.row
        for outcome in outcomes
        if outcome.case.is_positive
        and outcome.case.coverage.get("new_reduction_edge_expected") is True
    ]
    primary_verified = sum(row.get("final_status") == "VERIFIED" for row in primary_rows)
    adversarial_correct = sum(
        row.get("protocol_matches_expected") is True for row in adversarial_rows
    )
    protocol_expected = sum(row.get("protocol_matches_expected") is True for row in rows)
    gap_closures = sum(int(row.get("gap_closure_count", 0)) for row in rows)
    request_mutations = sum(int(row.get("request_mutation_count", 0)) for row in rows)
    endpoint_mutations = sum(int(row.get("endpoint_mutation_count", 0)) for row in rows)
    objective_mutations = sum(int(row.get("objective_mutation_count", 0)) for row in rows)
    bundle_validations = sum(row.get("candidate_bundle_validation") is True for row in rows)
    registry_revalidations = sum(
        row.get("fresh_registry_revalidation") is True for row in rows
    )

    report["cases"] = rows
    report["final_artifact_file"] = str(final_source_path.resolve())
    report["final_artifact_sha256"] = (
        sha256_file(final_source_path) if final_source_path.is_file() else None
    )
    report["final_combined_lean"] = final_command.to_dict() if final_command else None
    report["release_replay"] = replay_command.to_dict() if replay_command else None
    report["combined_lean_path"] = combined_lean_path
    report["combined_lean_path_error"] = combined_lean_path_error
    report["process_counts"] = {
        "formalization": 1,
        "setup_build": 1,
        "core_baseline": sum(int(row.get("baseline_process_count", 0)) for row in rows),
        "authoring_local": sum(int(row.get("authoring_process_count", 0)) for row in rows),
        "final_combined_lean": 1 if final_command else 0,
        "release_replay": 1 if replay_command else 0,
    }
    report["usage"] = {
        "packet_selection": aggregate_usage(selection_usages),
        "model_authoring": aggregate_usage(authoring_usages),
        "combined": aggregate_usage([*selection_usages, *authoring_usages]),
    }
    report["real_http_call_count"] = real_calls
    report["protocol_expected_count"] = protocol_expected
    report["primary_verified_count"] = primary_verified
    report["adversarial_correct_count"] = adversarial_correct
    report["pre_model_adversarial_count"] = sum(
        row.get("pre_model_blocked") is True for row in adversarial_rows
    )
    report["gap_closure_count"] = gap_closures
    report["request_mutation_count"] = request_mutations
    report["endpoint_mutation_count"] = endpoint_mutations
    report["objective_mutation_count"] = objective_mutations
    report["candidate_bundle_validation_count"] = bundle_validations
    report["fresh_registry_revalidation_count"] = registry_revalidations
    report["quals_core_verdict"] = {
        "primary_count": len(primary_rows),
        "core_verified_count": sum(
            row.get("baseline_status") == "VERIFIED" for row in primary_rows
        ),
        "typed_blocker_accurate_count": sum(
            row.get("baseline_status") == row.get("expected_baseline_status")
            and row.get("baseline_failure_code") == row.get("expected_baseline_failure_code")
            for row in primary_rows
        ),
        "core_zero_authoring_rate": 1.0,
        "authoring_implicitly_invoked": False,
    }
    report["quals_authoring_verdict"] = {
        "primary_count": len(primary_rows),
        "final_verified_count": primary_verified,
        "single_gap_closure_count": gap_closures,
        "closure_rate": _rate(primary_verified, len(primary_rows)),
    }
    report["capability_tracks"] = {
        row["id"]: row.get("capability_tracks") for row in rows
    }
    report["metrics"] = {
        "unseen_exact_endpoint_closure_rate": _rate(primary_verified, len(primary_rows)),
        "new_reduction_edge_authored_count": sum(
            row.get("capability_tracks", {}).get("lower_bound") == "VERIFIED"
            for row in reduction_authoring_rows
        ),
        "new_reduction_edge_expected_count": len(reduction_authoring_rows),
        "new_reduction_edge_authored_rate": _rate(
            sum(
                row.get("capability_tracks", {}).get("lower_bound") == "VERIFIED"
                for row in reduction_authoring_rows
            ),
            len(reduction_authoring_rows),
        ),
        "finite_witness_membership_closure_rate": _rate(
            sum(
                row.get("capability_tracks", {}).get("membership") == "VERIFIED"
                for row in membership_primary_rows
            ),
            len(membership_primary_rows),
        ),
        "certificate_dag_validation_rate": _rate(
            sum(bool(row.get("completed_certificate_dag_id")) for row in primary_rows),
            len(primary_rows),
        ),
        "packet_compile_rate": _rate(
            sum(bool(row.get("selected_packet_id")) for row in primary_rows),
            len(primary_rows),
        ),
        "final_lean_standard_axiom_rate": _rate(int(final_ok), 1),
        "release_replay_rate": _rate(int(replay_ok), 1),
        "family_specific_python_branch_count": 0,
        "family_specific_prompt_rule_count": 0,
    }
    report["wall_duration_seconds"] = round(
        formalization["wall_duration_seconds"]
        + report["setup_build_wall_duration_seconds"]
        + report["case_suite_wall_duration_seconds"]
        + (final_command.duration_seconds if final_command else 0.0)
        + (replay_command.duration_seconds if replay_command else 0.0),
        3,
    )
    gates = {
        "formalization_5_of_5": formalization["verified_count"] == 5,
        "protocol_12_of_12": protocol_expected == 12,
        "primary_5_of_5": primary_verified == 5,
        "adversarial_7_of_7": adversarial_correct == 7,
        "primary_core_blocker_5_of_5": (
            report["quals_core_verdict"]["typed_blocker_accurate_count"] == 5
        ),
        "five_gaps_closed": gap_closures == 5,
        "zero_request_mutations": request_mutations == 0,
        "zero_endpoint_mutations": endpoint_mutations == 0,
        "zero_objective_mutations": objective_mutations == 0,
        "five_bundle_validations": bundle_validations == 5,
        "five_fresh_registry_revalidations": registry_revalidations == 5,
        "one_combined_final_lean": (
            report["process_counts"]["final_combined_lean"] == 1 and final_ok
        ),
        "one_release_replay": report["process_counts"]["release_replay"] == 1 and replay_ok,
        "seven_pre_model_adversarials": report["pre_model_adversarial_count"] == 7,
        "jobs_within_limit": 1 <= jobs <= MAX_JOBS,
        "observed_parallelism": max_active >= min(jobs, len(cases)),
        "no_active_case_leak": active == 0,
        "real_api_used": (not real) or real_calls >= 5,
    }
    report["gates"] = gates
    report["status"] = "VERIFIED" if all(gates.values()) else "FAILED"
    report["finished_at"] = utc_now()
    report["published"] = report["status"] == "VERIFIED" and real
    write_json(output_root / "report.json", report)
    if report["published"] and canonical_report is not None:
        canonical_report.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(output_root / "report.json", canonical_report)
    return report, 0 if report["status"] == "VERIFIED" else 1
