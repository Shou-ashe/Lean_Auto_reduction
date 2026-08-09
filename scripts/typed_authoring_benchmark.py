"""Shared Stage-M typed-authoring full-suite orchestration."""

from __future__ import annotations

import hashlib
import json
import shutil
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, replace
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Mapping, Sequence

from agent.hardness.benchmark import BenchmarkCase, load_benchmark_suite
from agent.hardness.certificate_dag import (
    build_certificate_dag,
    complete_certificate_dag,
)
from agent.hardness.finite_witness import finite_witness_registry
from agent.hardness.lean_runner import (
    assert_generated_source_is_safe,
    build_module_command,
    run_command,
    sha256_file,
)
from agent.hardness.model_client import DeepSeekClient, DeepSeekConfig, ModelResponse
from agent.hardness.runner import HardnessAgent, HardnessAgentConfig
from agent.hardness.typed_authoring import (
    TYPED_AUTHORING_SYSTEM_PROMPT,
    TypedAuthoringArtifactCase,
    TypedAuthoringRequest,
    build_packet_selection_prompt,
    build_typed_authoring_batch_artifact_source,
    parse_packet_selection,
    typed_authoring_report_skeleton,
    typed_authoring_task_id,
    validate_typed_authoring_suite,
)
from agent.hardness.typed_authoring_simulation import (
    SimulatedSemanticProofClient,
    SimulatedTypedAuthoringClient,
)
from agent.hardness.typed_packets import (
    PacketValidationError,
    adversarial_packet,
    build_packet_index,
    candidate_bundle_integrity,
    candidate_set_source_hash,
    compile_packet_selection,
    validate_packet,
)


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_SUITE = ROOT / "Benchmark" / "Hardness" / "Suites" / "typed_authoring.json"
MAX_JOBS = 4


@dataclass
class CaseOutcome:
    index: int
    case: BenchmarkCase
    row: dict[str, Any]
    artifact: TypedAuthoringArtifactCase | None = None
    work_root: Path | None = None


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def last_failure_code(result: Any) -> str | None:
    failures = getattr(result, "failures", ())
    return failures[-1].code if failures else None


def aggregate_usage(rows: Sequence[Mapping[str, Any] | None]) -> dict[str, int]:
    totals: dict[str, int] = {}
    for row in rows:
        if not isinstance(row, Mapping):
            continue
        for key, value in row.items():
            if isinstance(value, int) and not isinstance(value, bool):
                totals[key] = totals.get(key, 0) + value
    return totals


def prepare_fresh_output_root(path: Path) -> None:
    if path.exists() and any(path.iterdir()):
        raise ValueError(f"Stage-M output root must be fresh and empty: {path}")
    path.mkdir(parents=True, exist_ok=True)


def merge_candidate_work_roots(
    work_roots: Sequence[Path], *, destination: Path
) -> dict[str, Any]:
    """Merge generated module trees so one top-level namespace cannot shadow another."""

    if destination.exists() and any(destination.iterdir()):
        raise ValueError(f"combined Lean path must be fresh and empty: {destination}")
    destination.mkdir(parents=True, exist_ok=True)
    copied_files = 0
    duplicate_files = 0
    for work_root in work_roots:
        generated = work_root / "Generated"
        if not generated.is_dir():
            raise ValueError(f"candidate work root has no Generated tree: {work_root}")
        for source in sorted(path for path in generated.rglob("*") if path.is_file()):
            relative = source.relative_to(work_root)
            target = destination / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.exists():
                if sha256_file(target) != sha256_file(source):
                    raise ValueError(f"conflicting generated module artifact: {relative}")
                duplicate_files += 1
                continue
            shutil.copy2(source, target)
            copied_files += 1
    return {
        "path": str(destination.resolve()),
        "work_root_count": len(work_roots),
        "copied_file_count": copied_files,
        "identical_duplicate_count": duplicate_files,
    }


def _case_config(
    *,
    case: BenchmarkCase,
    output_dir: Path,
    authoring_mode: str,
    runtime_prebuilt: bool,
    selected_candidate_id: str | None = None,
    defer_final: bool = False,
    deepseek: DeepSeekConfig | None = None,
    model_client: object | None = None,
) -> HardnessAgentConfig:
    return HardnessAgentConfig(
        root=ROOT,
        input_module=case.module,
        source_declaration=case.source,
        membership_declaration=case.membership,
        target_declaration=case.target,
        objective=case.objective,
        planner_mode=case.planner,
        output_dir=output_dir,
        lean_timeout_seconds=int(case.resources.get("lean_timeout_seconds", 1200)),
        deepseek=deepseek,
        model_client=model_client,
        runtime_prebuilt=runtime_prebuilt,
        authoring_mode=authoring_mode,
        authoring_attempt_budget=int(case.authoring_policy.get("attempt_budget", 1)),
        authoring_candidate_id=selected_candidate_id,
        defer_final_verification=defer_final,
    )


def _selection_record(
    *,
    case_root: Path,
    number: int,
    prompt: str,
    response: ModelResponse,
    config: DeepSeekConfig | None,
) -> dict[str, Any]:
    prompt_path = case_root / "selection" / f"round-{number:02d}-prompt.json"
    response_path = case_root / "selection" / f"round-{number:02d}-response.json"
    write_json(
        prompt_path,
        {
            "system": TYPED_AUTHORING_SYSTEM_PROMPT,
            "system_sha256": sha256_text(TYPED_AUTHORING_SYSTEM_PROMPT),
            "prompt": prompt,
            "prompt_sha256": sha256_text(prompt),
        },
    )
    write_json(
        response_path,
        {
            "called": response.called,
            "ok": response.ok,
            "status_code": response.status_code,
            "duration_seconds": response.duration_seconds,
            "attempts": response.attempts,
            "finish_reason": response.finish_reason,
            "usage": response.usage,
            "error": config.redact(response.error or "") if config else response.error,
            "content": response.content,
            "content_sha256": sha256_text(response.content),
            "replayed": False,
        },
    )
    return {
        "round": number,
        "called": response.called,
        "ok": response.ok,
        "status_code": response.status_code,
        "duration_seconds": response.duration_seconds,
        "attempts": response.attempts,
        "finish_reason": response.finish_reason,
        "usage": response.usage,
        "prompt_sha256": sha256_text(prompt),
        "response_sha256": sha256_text(response.content),
        "prompt_file": str(prompt_path.resolve()),
        "response_file": str(response_path.resolve()),
    }


def _artifact_case(case: BenchmarkCase, result: Any) -> TypedAuthoringArtifactCase:
    route = result.selected_route
    if route is None:
        raise ValueError(f"{case.id} has no fresh post-authoring route")
    modules = (result.authored_candidate_module,) if result.authored_candidate_module else ()
    return TypedAuthoringArtifactCase(
        case_id=case.id,
        input_module=case.module,
        objective=case.objective,
        source_declaration=case.source,
        target_declaration=case.target or case.source,
        route_atoms=tuple(route.atoms),
        membership_declaration=route.membership_declaration,
        hub_declaration=route.hub_declaration,
        completeness_declaration=route.completeness_declaration,
        candidate_modules=modules,
    )


def run_case(
    *,
    index: int,
    case: BenchmarkCase,
    output_root: Path,
    real: bool,
    deepseek_config: DeepSeekConfig | None,
) -> CaseOutcome:
    started = time.monotonic()
    case_root = output_root / "cases" / case.id
    case_root.mkdir(parents=True, exist_ok=True)
    request = TypedAuthoringRequest.from_case(case)
    baseline = HardnessAgent(
        _case_config(
            case=case,
            output_dir=case_root / "baseline",
            authoring_mode="disabled",
            runtime_prebuilt=True,
        )
    ).run()
    baseline_code = last_failure_code(baseline)
    row: dict[str, Any] = {
        "id": case.id,
        "execution_position": index,
        "positive": case.is_positive,
        "objective": case.objective,
        "execution_layer": case.execution_layer,
        "verification_profile": case.verification_profile,
        "request": request.to_dict(),
        "expected_baseline_status": case.expected.baseline_status,
        "expected_baseline_failure_code": case.expected.baseline_failure_code,
        "baseline_status": baseline.status,
        "baseline_failure_code": baseline_code,
        "baseline_gap": baseline.gap.to_dict() if baseline.gap else None,
        "baseline_report": str((case_root / "baseline" / "report.json").resolve()),
        "baseline_immutable": True,
        "baseline_process_count": len(baseline.commands),
        "baseline_duration_seconds": round(
            sum(command.duration_seconds for command in baseline.commands), 3
        ),
        "selection_calls": [],
        "authoring_process_count": 0,
        "authoring_duration_seconds": 0.0,
        "model_authoring_calls": [],
        "request_mutation_count": 0,
        "endpoint_mutation_count": 0,
        "objective_mutation_count": 0,
        "gap_closure_count": 0,
        "candidate_write_count": 0,
        "final_status": "FAILED",
        "final_failure_code": "baseline_mismatch",
    }
    if (
        baseline.status != case.expected.baseline_status
        or baseline_code != case.expected.baseline_failure_code
        or baseline.gap is None
        or baseline.probe is None
    ):
        row["case_task_wall_duration_seconds"] = round(time.monotonic() - started, 3)
        write_json(case_root / "case.json", row)
        return CaseOutcome(index=index, case=case, row=row)

    source_hash = candidate_set_source_hash(
        root=ROOT,
        probe=baseline.probe,
        allowed_packet_kinds=request.allowed_packet_kinds,
    )
    dag = build_certificate_dag(
        source_declaration=request.source_declaration,
        target_declaration=case.target,
        objective=request.objective,
        active_node=request.active_node,
        candidate_source_hash=source_hash,
    )
    packet_index = build_packet_index(
        root=ROOT,
        dag=dag,
        probe=baseline.probe,
        allowed_packet_kinds=request.allowed_packet_kinds,
        required_combinators=request.required_checker_combinators,
    )
    write_json(case_root / "certificate-dag-baseline.json", dag.to_dict())
    write_json(case_root / "packet-index.json", packet_index.to_dict())
    row["certificate_dag_id"] = dag.dag_id
    row["packet_index_id"] = packet_index.index_id
    row["packet_count"] = len(packet_index.packets)

    negative_class = case.coverage.get("negative_class")
    if negative_class in {"typed_blocker", "unsupported_checker"}:
        row["pre_model_blocked"] = True
        row["final_status"] = "BLOCKED"
        row["final_failure_code"] = baseline_code
        row["protocol_matches_expected"] = (
            row["final_status"] == case.expected.final_status
            and row["final_failure_code"] == case.expected.final_failure_code
        )
        row["case_task_wall_duration_seconds"] = round(time.monotonic() - started, 3)
        write_json(case_root / "case.json", row)
        return CaseOutcome(index=index, case=case, row=row)

    if negative_class == "adversarial_packet":
        if not packet_index.packets:
            row["final_failure_code"] = "missing_adversarial_seed_packet"
        else:
            seed = packet_index.packets[0]
            rejections: list[dict[str, str]] = []
            for mutation in case.coverage.get("required_rejection_codes", []):
                try:
                    validate_packet(adversarial_packet(seed, str(mutation)), dag=dag)
                except PacketValidationError as error:
                    rejections.append({"mutation": str(mutation), "code": error.code})
            row["adversarial_rejections"] = rejections
            required = [str(value) for value in case.coverage.get("required_rejection_codes", [])]
            if [entry["code"] for entry in rejections] == required:
                row["final_status"] = "BLOCKED"
                row["final_failure_code"] = "candidate_packet_rejected"
                row["pre_model_blocked"] = True
        row["protocol_matches_expected"] = (
            row["final_status"] == case.expected.final_status
            and row["final_failure_code"] == case.expected.final_failure_code
        )
        row["case_task_wall_duration_seconds"] = round(time.monotonic() - started, 3)
        write_json(case_root / "case.json", row)
        return CaseOutcome(index=index, case=case, row=row)

    if not packet_index.packets:
        row["final_failure_code"] = "no_typed_packet_available"
        row["case_task_wall_duration_seconds"] = round(time.monotonic() - started, 3)
        write_json(case_root / "case.json", row)
        return CaseOutcome(index=index, case=case, row=row)

    task_id = typed_authoring_task_id(
        request=request,
        gap_id=baseline.gap.gap_id,
        dag=dag,
        index=packet_index,
    )
    selector: Any = (
        DeepSeekClient(deepseek_config)
        if real and deepseek_config is not None
        else SimulatedTypedAuthoringClient()
    )
    selection = None
    protocol_error = ""
    selection_records: list[dict[str, Any]] = []
    for number in range(1, 3):
        prompt = build_packet_selection_prompt(
            task_id=task_id,
            request=request,
            gap=baseline.gap.to_dict(),
            dag=dag,
            index=packet_index,
            last_protocol_error=protocol_error,
        )
        response = selector.complete_json(system=TYPED_AUTHORING_SYSTEM_PROMPT, prompt=prompt)
        selection_records.append(
            _selection_record(
                case_root=case_root,
                number=number,
                prompt=prompt,
                response=response,
                config=deepseek_config if real else None,
            )
        )
        try:
            if not response.ok:
                raise PacketValidationError(
                    "packet_selection_http_error", response.error or "packet selection failed"
                )
            selection = parse_packet_selection(
                response.content, task_id=task_id, index=packet_index
            )
            break
        except PacketValidationError as error:
            protocol_error = str(error)
    row["selection_calls"] = selection_records
    if selection is None:
        row["final_failure_code"] = "packet_selection_budget_exhausted"
        row["case_task_wall_duration_seconds"] = round(time.monotonic() - started, 3)
        write_json(case_root / "case.json", row)
        return CaseOutcome(index=index, case=case, row=row)

    compiled = compile_packet_selection(
        dag=dag, index=packet_index, packet_id=selection.packet_id
    )
    write_json(case_root / "packet-selection.json", selection.to_dict())
    write_json(case_root / "compiled-packet.json", compiled.to_dict())
    row["selected_packet_id"] = selection.packet_id
    row["selected_candidate_id"] = compiled.candidate_id
    row["selected_template_kind"] = compiled.template_kind
    row["selected_packet_kind"] = compiled.packet_kind
    row["compiler_insertions"] = list(compiled.compiler_insertions)

    per_case_config = None
    proof_client: object | None = None
    if request.authoring_mode == "model-required":
        if real and deepseek_config is not None:
            per_case_config = replace(
                deepseek_config,
                timeout_seconds=int(case.resources.get("model_timeout_seconds", 300)),
                max_tokens=int(case.resources.get("model_max_tokens", 8192)),
            )
        else:
            proof_client = SimulatedSemanticProofClient()
    authoring_root = case_root / "authoring"
    authored = HardnessAgent(
        _case_config(
            case=case,
            output_dir=authoring_root,
            authoring_mode=request.authoring_mode,
            runtime_prebuilt=True,
            selected_candidate_id=compiled.candidate_id,
            defer_final=True,
            deepseek=per_case_config,
            model_client=proof_client,
        )
    ).run()
    row["authoring_report"] = str((authoring_root / "report.json").resolve())
    row["authoring_status"] = authored.status
    row["authoring_failure_code"] = last_failure_code(authored)
    row["authoring_process_count"] = len(authored.commands)
    row["authoring_duration_seconds"] = round(
        sum(command.duration_seconds for command in authored.commands), 3
    )
    row["model_authoring_calls"] = [call.to_dict() for call in authored.model_calls]
    row["candidate_write_count"] = len(authored.authored_stage_files)
    row["candidate_bundle_validation"] = any(
        command.ok and command.command[-1].endswith("CandidateValidation.lean")
        for command in authored.commands
    )
    row["fresh_registry_revalidation"] = sum(
        command.ok and command.command[-1].endswith("PostAuthoringProbe.lean")
        for command in authored.commands
    ) >= 2
    if (
        authored.status != "REGISTRY_REVALIDATED"
        or authored.gap is None
        or authored.gap.gap_id != baseline.gap.gap_id
        or authored.selected_route is None
        or not authored.authored_candidate_sha256
        or not row["candidate_bundle_validation"]
    ):
        row["final_failure_code"] = last_failure_code(authored) or "authoring_not_ready"
        row["case_task_wall_duration_seconds"] = round(time.monotonic() - started, 3)
        write_json(case_root / "case.json", row)
        return CaseOutcome(index=index, case=case, row=row)

    completed_dag = complete_certificate_dag(
        dag, candidate_source_hash=f"sha256:{authored.authored_candidate_sha256}"
    )
    write_json(case_root / "certificate-dag-completed.json", completed_dag.to_dict())
    row["completed_certificate_dag_id"] = completed_dag.dag_id
    row["gap_closure_count"] = 1
    row["candidate_sha256"] = authored.authored_candidate_sha256
    row["candidate_stage_files"] = list(authored.authored_stage_files)
    row["candidate_stage_sha256"] = list(authored.authored_stage_sha256)
    row["candidate_integrity_revalidated"] = candidate_bundle_integrity(
        (ROOT / path for path in authored.authored_stage_files),
        authored.authored_stage_sha256,
    )
    row["provisional_status"] = "READY_FOR_COMBINED_LEAN"
    row["final_status"] = "READY_FOR_COMBINED_LEAN"
    row["final_failure_code"] = None
    row["case_task_wall_duration_seconds"] = round(time.monotonic() - started, 3)
    artifact = _artifact_case(case, authored)
    write_json(case_root / "case.json", row)
    return CaseOutcome(
        index=index,
        case=case,
        row=row,
        artifact=artifact,
        work_root=authoring_root / "work",
    )


def run_full_suite(
    *,
    suite_file: Path,
    output_root: Path,
    jobs: int,
    real: bool,
    deepseek_config: DeepSeekConfig | None,
    canonical_report: Path | None,
    lean_timeout_seconds: int,
    run_label: str,
) -> tuple[dict[str, Any], int]:
    if jobs < 1 or jobs > MAX_JOBS:
        raise ValueError(f"Stage-M jobs must be between 1 and {MAX_JOBS}")
    prepare_fresh_output_root(output_root)
    if real and (deepseek_config is None or not deepseek_config.api_key):
        raise ValueError("real Stage-M run requires DEEPSEEK_API_KEY")
    if canonical_report is not None and canonical_report.exists():
        raise ValueError(f"canonical Stage-M report already exists: {canonical_report}")

    suite = load_benchmark_suite(suite_file)
    cases = tuple(suite.cases)
    validate_typed_authoring_suite(cases)
    report = typed_authoring_report_skeleton(suite_file=suite_file, output_root=output_root)
    report.update(
        {
            "run_label": run_label,
            "started_at": utc_now(),
            "real_deepseek": real,
            "model_configuration": deepseek_config.to_public_dict() if deepseek_config else None,
            "configured_jobs": jobs,
            "suite_id": suite.id,
            "suite_sha256": sha256_file(suite_file),
            "finite_witness_registry": finite_witness_registry(),
        }
    )
    write_json(output_root / "report.json", report)

    setup_started = time.monotonic()
    setup_modules = sorted({case.module for case in cases} | {
        "ComplexityReduction.Agent.Hardness.FiniteWitness",
        "ComplexityReduction.Agent.Hardness.FiniteWitnessNative",
        "ComplexityReduction.Agent.Hardness.Runtime",
    })
    setup = run_command(
        build_module_command(setup_modules),
        cwd=ROOT / "Lean",
        timeout_seconds=max(lean_timeout_seconds, 3600),
        output_limit=32000,
    )
    report["setup_build"] = setup.to_dict()
    report["setup_build_wall_duration_seconds"] = round(time.monotonic() - setup_started, 3)
    if not setup.ok:
        report["status"] = "FAILED"
        report["finished_at"] = utc_now()
        report["failures"] = ["setup_build_failed"]
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
            return run_case(
                index=index,
                case=case,
                output_root=output_root,
                real=real,
                deepseek_config=deepseek_config,
            )
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
            except Exception as error:  # fail closed while preserving the full report
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
    final_source_path = output_root / "TypedAuthoringFinal.lean"
    final_command = None
    replay_command = None
    combined_lean_path: dict[str, Any] | None = None
    combined_lean_path_error: str | None = None
    if len(artifacts) == 5:
        final_source = build_typed_authoring_batch_artifact_source(artifacts)
        assert_generated_source_is_safe(final_source)
        final_source_path.write_text(final_source, encoding="utf-8")
        integrity_ok = all(
            candidate_bundle_integrity(
                (ROOT / path for path in outcome.row.get("candidate_stage_files", [])),
                outcome.row.get("candidate_stage_sha256", []),
            )
            for outcome in outcomes
            if outcome.case.is_positive
        )
        if integrity_ok:
            try:
                combined_lean_path = merge_candidate_work_roots(
                    work_roots,
                    destination=output_root / "combined-lean-path",
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
            if final_command.ok:
                integrity_ok = all(
                    candidate_bundle_integrity(
                        (ROOT / path for path in outcome.row.get("candidate_stage_files", [])),
                        outcome.row.get("candidate_stage_sha256", []),
                    )
                    for outcome in outcomes
                    if outcome.case.is_positive
                )
                if integrity_ok:
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
        if outcome.case.is_positive and row.get("provisional_status") == "READY_FOR_COMBINED_LEAN":
            row["combined_final_lean"] = final_ok
            row["independent_release_replay"] = replay_ok
            row["final_status"] = "VERIFIED" if final_ok and replay_ok else "FAILED"
            row["final_failure_code"] = None if final_ok and replay_ok else "combined_lean_failed"
        row["protocol_matches_expected"] = (
            row.get("final_status") == outcome.case.expected.final_status
            and row.get("final_failure_code") == outcome.case.expected.final_failure_code
        )

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
    real_calls = sum(
        call.get("called") is True
        for row in rows
        for call in (*row.get("selection_calls", []), *row.get("model_authoring_calls", []))
        if isinstance(call, Mapping)
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
    report["positive_verified_count"] = sum(
        row.get("final_status") == "VERIFIED" for row in rows if row.get("positive") is True
    )
    report["negative_correct_count"] = sum(
        row.get("protocol_matches_expected") is True for row in rows if row.get("positive") is False
    )
    report["protocol_expected_count"] = sum(
        row.get("protocol_matches_expected") is True for row in rows
    )
    report["gap_closure_count"] = sum(int(row.get("gap_closure_count", 0)) for row in rows)
    report["request_mutation_count"] = sum(int(row.get("request_mutation_count", 0)) for row in rows)
    report["endpoint_mutation_count"] = sum(int(row.get("endpoint_mutation_count", 0)) for row in rows)
    report["objective_mutation_count"] = sum(int(row.get("objective_mutation_count", 0)) for row in rows)
    report["pre_model_block_count"] = sum(row.get("pre_model_blocked") is True for row in rows)
    report["candidate_bundle_validation_count"] = sum(
        row.get("candidate_bundle_validation") is True for row in rows
    )
    report["fresh_registry_revalidation_count"] = sum(
        row.get("fresh_registry_revalidation") is True for row in rows
    )
    report["wall_duration_seconds"] = round(
        report["setup_build_wall_duration_seconds"]
        + report["case_suite_wall_duration_seconds"]
        + (final_command.duration_seconds if final_command else 0.0)
        + (replay_command.duration_seconds if replay_command else 0.0),
        3,
    )
    gates = {
        "protocol_8_of_8": report["protocol_expected_count"] == 8,
        "positive_5_of_5": report["positive_verified_count"] == 5,
        "negative_3_of_3": report["negative_correct_count"] == 3,
        "one_gap_per_positive": report["gap_closure_count"] == 5,
        "zero_request_mutations": report["request_mutation_count"] == 0,
        "zero_endpoint_mutations": report["endpoint_mutation_count"] == 0,
        "zero_objective_mutations": report["objective_mutation_count"] == 0,
        "five_bundle_validations": report["candidate_bundle_validation_count"] == 5,
        "five_fresh_registry_revalidations": report["fresh_registry_revalidation_count"] == 5,
        "one_combined_final_lean": report["process_counts"]["final_combined_lean"] == 1 and final_ok,
        "one_release_replay": report["process_counts"]["release_replay"] == 1 and replay_ok,
        "jobs_within_limit": 1 <= jobs <= MAX_JOBS,
        "observed_parallelism": max_active >= min(jobs, len(cases)),
        "no_active_case_leak": active == 0,
        "three_pre_model_negatives": report["pre_model_block_count"] == 3,
        "real_api_used": (not real) or real_calls >= 6,
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
