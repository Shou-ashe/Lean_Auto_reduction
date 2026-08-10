#!/usr/bin/env python3
"""Run the fresh 16-case Stage-L suite with real DeepSeek API calls."""

from __future__ import annotations

import argparse
import json
import sys
import time
from collections import Counter
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, replace
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.artifact import (  # noqa: E402
    CoreGeneralizationArtifactCase,
    build_core_generalization_batch_artifact_source,
)
from agent.hardness.benchmark import BenchmarkCase, load_benchmark_suite  # noqa: E402
from agent.hardness.connection_catalog import (  # noqa: E402
    load_connection_catalog_snapshot,
)
from agent.hardness.core_capability_catalog import (  # noqa: E402
    load_core_native_evidence_catalog,
    load_core_reduction_catalog,
)
from agent.hardness.core_generalization import (  # noqa: E402
    CORE_GENERALIZATION_MAX_JOBS,
    core_generalization_report_skeleton,
    validate_core_generalization_suite,
)
from agent.hardness.core_generalization_planner import (  # noqa: E402
    CORE_GENERALIZATION_SYSTEM_PROMPT,
    CoreGeneralizationRequest,
    audit_core_generalization_prompt,
    generate_core_generalization_evidence,
)
from agent.hardness.hardness_target_catalog import (  # noqa: E402
    load_hardness_target_catalog_snapshot,
)
from agent.hardness.input_grounding import observation_snapshot_path  # noqa: E402
from agent.hardness.input_observation import (  # noqa: E402
    LeanInputObservation,
    load_input_observation_snapshot,
)
from agent.hardness.input_planner import ObservedInputPlannerResult  # noqa: E402
from agent.hardness.lean_runner import (  # noqa: E402
    assert_generated_source_is_safe,
    module_file,
    run_command,
    sha256_file,
)
from agent.hardness.model_client import (  # noqa: E402
    DEFAULT_MODEL,
    DeepSeekClient,
    DeepSeekConfig,
    extract_json_object,
)
from agent.hardness.problem_catalog import load_problem_catalog_snapshot  # noqa: E402
from scripts.run_deepseek_open_target_benchmark import (  # noqa: E402
    aggregate_usage,
    command_record,
    completed_action_counts,
    finalize_report,
    preflight_canonical_report,
    prepare_fresh_output_root,
    sha256_text,
    usage_contract_errors,
    utc_now,
    write_json,
)
from scripts.run_deepseek_stage_i_expansion_benchmark import (  # noqa: E402
    parallel_execution_errors,
    run_case_tasks,
    validate_case_concurrency,
)


DEFAULT_MODEL_TIMEOUT = 900
DEFAULT_MODEL_MAX_TOKENS = 32768
DEFAULT_JOBS = 4


@dataclass(frozen=True)
class CaseExecutionOutcome:
    index: int
    case_id: str
    row: dict[str, Any]
    artifact: CoreGeneralizationArtifactCase | None


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description=(
            "Run all 16 Stage-L Core-generalization cases with fresh DeepSeek "
            "calls and one combined final Lean process"
        )
    )
    command.add_argument(
        "--suite",
        type=Path,
        default=ROOT / "Gate" / "Suites" / "core_generalization.json",
    )
    command.add_argument(
        "--snapshots-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "core-generalization-snapshots",
    )
    command.add_argument("--env-file", type=Path, default=ROOT / ".env")
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "deepseek-core-generalization-full",
    )
    command.add_argument(
        "--canonical-report",
        type=Path,
        default=ROOT / "Reports" / "CORE_GENERALIZATION_REPORT.json",
    )
    command.add_argument("--run-label", default="stage-l-core-generalization-full-real-deepseek")
    command.add_argument("--model", default=DEFAULT_MODEL)
    command.add_argument("--lean-timeout", type=int, default=1200)
    command.add_argument("--model-timeout", type=int, default=DEFAULT_MODEL_TIMEOUT)
    command.add_argument("--model-max-tokens", type=int, default=DEFAULT_MODEL_MAX_TOKENS)
    command.add_argument("--jobs", type=int, default=DEFAULT_JOBS)
    command.add_argument(
        "--minimum-observed-parallelism",
        type=int,
        default=DEFAULT_JOBS,
    )
    return command


def request_for_case(case: BenchmarkCase) -> CoreGeneralizationRequest:
    if case.maximum_route_atoms is None or case.maximum_dependencies is None:
        raise ValueError(f"case {case.id} has no Stage-L route bounds")
    open_objective = case.objective in {
        "reduce_to_known_np",
        "reduce_to_known_hardness",
    }
    return CoreGeneralizationRequest(
        objective=case.objective,
        minimum_route_atoms=case.minimum_route_atoms,
        maximum_route_atoms=case.maximum_route_atoms,
        maximum_dependencies=case.maximum_dependencies,
        allow_reflexive_target=case.allow_reflexive_target,
        require_simple_path=case.require_simple_path,
        required_hardness=case.required_hardness if open_objective else None,
        allowed_target_evidence=(
            case.allowed_target_evidence if open_objective else ()
        ),
    )


def expected_protocol(case: BenchmarkCase, result: ObservedInputPlannerResult) -> bool:
    if case.is_positive:
        return bool(result.protocol_accepted and result.plan and result.lean_term)
    return bool(
        result.plan is None
        and result.lean_term is None
        and result.failure_code == case.expected.final_failure_code
    )


def normalize_action_payload(payload: Mapping[str, Any]) -> dict[str, Any]:
    if isinstance(payload.get("action"), str):
        return dict(payload)
    candidates: list[dict[str, Any]] = []
    for action in (
        "inspect_architecture",
        "search_problems",
        "search_connections",
        "search_reductions",
        "search_native_evidence",
        "search_hardness_targets",
        "finish",
        "stop",
    ):
        nested = payload.get(action)
        if isinstance(nested, Mapping):
            candidate = dict(nested)
            candidate.setdefault("action", action)
            candidates.append(candidate)
    return candidates[0] if len(candidates) == 1 else dict(payload)


def submitted_objective_term(
    result: ObservedInputPlannerResult, objective: str
) -> str | None:
    field = {
        "prove_in_np": "membership_lean_term",
        "prove_np_complete": "completeness_lean_term",
    }.get(objective, "lean_term")
    for response in reversed(result.model_responses):
        payload = extract_json_object(response.content)
        normalized = normalize_action_payload(payload) if isinstance(payload, Mapping) else {}
        if normalized.get("action") == "finish":
            value = normalized.get(field)
            return value if isinstance(value, str) else None
    return None


def reduction_entry_ids(result: ObservedInputPlannerResult) -> tuple[str, ...]:
    if result.plan is None or not result.plan.outputs:
        return ()
    raw = result.plan.outputs[0].metadata.get("reduction_entry_ids", [])
    if not isinstance(raw, list):
        return ()
    return tuple(item for item in raw if isinstance(item, str))


def artifact_case(
    case: BenchmarkCase,
    observation: LeanInputObservation,
    result: ObservedInputPlannerResult,
) -> CoreGeneralizationArtifactCase:
    if result.plan is None or result.lean_term is None:
        raise ValueError(f"case {case.id} has no accepted Stage-L evidence")
    evidence = result.plan.target_evidence
    return CoreGeneralizationArtifactCase(
        case_id=case.id,
        input_module=case.module,
        objective=case.objective,
        source_declaration=result.plan.source_declaration,
        proof_term=result.lean_term,
        target_declaration=result.plan.target_declaration,
        predicate_declaration=(
            case.effective_input_declaration
            if observation.input_kind == "predicate"
            else None
        ),
        target_evidence_kind=(
            str(evidence.get("evidence_kind"))
            if evidence.get("evidence_kind") is not None
            else None
        ),
        target_evidence_term=(
            str(evidence.get("evidence_lean_term"))
            if evidence.get("evidence_lean_term")
            else None
        ),
        target_membership_term=(
            str(evidence.get("membership_lean_term"))
            if evidence.get("membership_lean_term")
            else None
        ),
    )


def prompt_oracle_errors(prompts: Sequence[str]) -> tuple[str, ...]:
    errors: list[str] = []
    for turn, prompt in enumerate(prompts, start=1):
        try:
            payload = json.loads(prompt)
            if not isinstance(payload, dict):
                raise ValueError("prompt is not one JSON object")
            audit_core_generalization_prompt(payload)
        except (json.JSONDecodeError, ValueError) as error:
            errors.append(f"turn {turn}: {error}")
    return tuple(errors)


def build_round_records(
    *,
    case_id: str,
    prompts: Sequence[str],
    responses: Sequence[Any],
    output_root: Path,
    config: DeepSeekConfig,
) -> list[dict[str, Any]]:
    if len(prompts) != len(responses):
        raise ValueError("model prompt and response counts differ")
    call_root = output_root / "calls" / case_id
    records: list[dict[str, Any]] = []
    for number, (prompt, response) in enumerate(
        zip(prompts, responses, strict=True), start=1
    ):
        payload = json.loads(prompt)
        if not isinstance(payload, dict):
            raise ValueError("Stage-L prompt is not one JSON object")
        audit_core_generalization_prompt(payload)
        prompt_path = call_root / f"round-{number:02d}-prompt.json"
        response_path = call_root / f"round-{number:02d}-response.json"
        usage_errors = usage_contract_errors(
            response.usage,
            label=f"{case_id}.round-{number}",
        )
        write_json(
            prompt_path,
            {
                "system": CORE_GENERALIZATION_SYSTEM_PROMPT,
                "system_sha256": sha256_text(CORE_GENERALIZATION_SYSTEM_PROMPT),
                "prompt": prompt,
                "prompt_sha256": sha256_text(prompt),
                "payload": payload,
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
                "usage_contract_ok": not usage_errors,
                "usage_contract_errors": list(usage_errors),
                "error": config.redact(response.error or "") or None,
                "content": response.content,
                "content_sha256": sha256_text(response.content),
                "replayed": False,
            },
        )
        retrieved = payload.get("retrieved", {})
        retrieved = retrieved if isinstance(retrieved, Mapping) else {}
        terminal = payload.get("terminal_guidance")
        records.append(
            {
                "round": number,
                "called": response.called,
                "http_ok": response.ok,
                "status_code": response.status_code,
                "duration_seconds": response.duration_seconds,
                "attempts": response.attempts,
                "finish_reason": response.finish_reason,
                "usage": response.usage,
                "usage_contract_ok": not usage_errors,
                "usage_contract_errors": list(usage_errors),
                "error": config.redact(response.error or "") or None,
                "system_sha256": sha256_text(CORE_GENERALIZATION_SYSTEM_PROMPT),
                "prompt_sha256": sha256_text(prompt),
                "response_sha256": sha256_text(response.content),
                "prompt_characters": len(prompt),
                "retrieved_counts": {
                    key: len(value) if isinstance(value, list) else 0
                    for key, value in retrieved.items()
                },
                "terminal_guidance": terminal if isinstance(terminal, Mapping) else None,
                "prompt_file": str(prompt_path),
                "response_file": str(response_path),
                "replayed": False,
            }
        )
    return records


def interaction_metrics(
    prompts: Sequence[str], responses: Sequence[Any]
) -> dict[str, int]:
    ignored = 0
    repeated = 0
    seen_reduction_searches: set[str] = set()
    for prompt, response in zip(prompts, responses, strict=True):
        payload = json.loads(prompt)
        raw_model_payload = extract_json_object(response.content) or {}
        model_payload = normalize_action_payload(raw_model_payload)
        terminal = payload.get("terminal_guidance")
        if isinstance(terminal, Mapping):
            expected_action = "finish" if terminal.get("mode") == "finish_now" else "stop"
            if model_payload.get("action") != expected_action:
                ignored += 1
        if model_payload.get("action") == "search_reductions":
            searches = model_payload.get("searches", [])
            signature = json.dumps(searches, sort_keys=True, separators=(",", ":"))
            if signature in seen_reduction_searches:
                repeated += 1
            seen_reduction_searches.add(signature)
    return {
        "terminal_guidance_ignored_count": ignored,
        "repeated_reduction_search_count": repeated,
    }


def candidate_metrics(trace: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    result_sets: dict[str, set[str]] = {
        "problems": set(),
        "connections": set(),
        "reductions": set(),
        "native_evidence": set(),
        "hardness_targets": set(),
    }
    action_to_key = {
        "search_problems": ("problems", "entry_id"),
        "search_connections": ("connections", "entry_id"),
        "search_reductions": ("reductions", "entry_id"),
        "search_native_evidence": ("native_evidence", "entry_id"),
        "search_hardness_targets": ("hardness_targets", "target_entry_id"),
    }
    for row in trace:
        action = row.get("action")
        if action not in action_to_key:
            continue
        bucket, id_field = action_to_key[str(action)]
        results = row.get("results", [])
        if not isinstance(results, list):
            continue
        for result in results:
            if isinstance(result, Mapping) and isinstance(result.get(id_field), str):
                result_sets[bucket].add(str(result[id_field]))
    return {f"retrieved_{key}_count": len(values) for key, values in result_sets.items()}


def grouped_metrics(
    rows: Sequence[Mapping[str, Any]], cases: Sequence[BenchmarkCase]
) -> dict[str, Any]:
    by_id = {case.id: case for case in cases}
    dimensions = {
        "family": lambda case: str(case.coverage["family"]),
        "input_kind": lambda case: case.input_kind,
        "objective": lambda case: case.objective,
        "route_band": lambda case: str(case.coverage["route_band"]),
        "outcome_class": lambda case: "positive" if case.is_positive else "negative",
        "comparable_subset": lambda case: (
            "selected" if case.coverage["comparable_subset"] else "not_selected"
        ),
    }
    grouped: dict[str, Any] = {}
    for dimension, selector in dimensions.items():
        buckets: dict[str, list[Mapping[str, Any]]] = {}
        for row in rows:
            buckets.setdefault(selector(by_id[str(row["id"])]), []).append(row)
        grouped[dimension] = {}
        for key, bucket in sorted(buckets.items()):
            grouped[dimension][key] = {
                "case_count": len(bucket),
                "protocol_expected_count": sum(
                    row.get("protocol_matches_expected") is True for row in bucket
                ),
                "verified_or_correctly_blocked_count": sum(
                    row.get("final_status") in {"VERIFIED", "BLOCKED"}
                    for row in bucket
                ),
                "model_api_turn_count": sum(
                    int(row.get("external_api_calls_this_run") or 0) for row in bucket
                ),
                "usage": aggregate_usage(
                    row.get("usage") if isinstance(row.get("usage"), Mapping) else None
                    for row in bucket
                ),
                "wall_duration_seconds": round(
                    sum(float(row.get("case_task_wall_duration_seconds") or 0.0) for row in bucket),
                    3,
                ),
            }
    return grouped


def case_row(
    *,
    case: BenchmarkCase,
    observation: LeanInputObservation,
    observation_path: Path,
    input_sha256: str,
    result: ObservedInputPlannerResult,
    rounds: list[dict[str, Any]],
) -> dict[str, Any]:
    protocol_ok = expected_protocol(case, result)
    entry_ids = reduction_entry_ids(result)
    atom_count = len(entry_ids) + int(result.selected_connection is not None)
    raw_term = submitted_objective_term(result, case.objective)
    usage = aggregate_usage(
        response.usage for response in result.model_responses
    )
    interactions = interaction_metrics(result.model_prompts, result.model_responses)
    return {
        "id": case.id,
        "family": case.coverage["family"],
        "input_kind": observation.input_kind,
        "objective": case.objective,
        "objective_class": case.coverage["objective_class"],
        "route_band": case.coverage["route_band"],
        "comparable_subset": case.coverage["comparable_subset"],
        "execution_layer": case.execution_layer,
        "expected_status": case.expected.final_status,
        "expected_failure_code": case.expected.final_failure_code,
        "input_declaration": case.effective_input_declaration,
        "input_observation_id": observation.observation_id,
        "input_observation_path": str(observation_path),
        "input_source_sha256": input_sha256,
        "requires_model_call": observation.supported,
        "protocol_accepted": result.protocol_accepted,
        "protocol_matches_expected": protocol_ok,
        "failure_code": result.failure_code,
        "explanation": result.explanation,
        "problem_match": result.problem_match.to_dict() if result.problem_match else None,
        "selected_connection_entry_id": (
            result.selected_connection.entry_id if result.selected_connection else None
        ),
        "selected_target_declaration": (
            result.plan.target_declaration if result.plan else None
        ),
        "selected_target_evidence_kind": (
            result.plan.target_evidence.get("evidence_kind")
            if result.plan
            else None
        ),
        "selected_reduction_entry_ids": list(entry_ids),
        "selected_reduction_declarations": list(result.reduction_declarations),
        "selected_route_atom_count": atom_count,
        "selected_route_within_public_range": (
            case.minimum_route_atoms
            <= atom_count
            <= int(case.maximum_route_atoms or 0)
            if result.protocol_accepted
            else None
        ),
        "objective_term": result.lean_term,
        "submitted_model_term": raw_term,
        "model_term_changed_by_agent": bool(
            result.lean_term is not None and raw_term != result.lean_term
        ),
        "model_turn_count": len(result.model_responses),
        "external_api_calls_this_run": sum(
            response.called for response in result.model_responses
        ),
        "http_ok_count_this_run": sum(
            response.called and response.ok for response in result.model_responses
        ),
        "http_request_attempts_this_run": sum(
            response.attempts for response in result.model_responses
        ),
        "usage": usage,
        "round_usage_complete": all(
            not response.called or isinstance(response.usage, Mapping)
            for response in result.model_responses
        ),
        "model_rounds": rounds,
        "query_action_counts": completed_action_counts(result.query_trace),
        "candidate_metrics": candidate_metrics(result.query_trace),
        "prompt_oracle_errors": list(prompt_oracle_errors(result.model_prompts)),
        **interactions,
        "unretrieved_declaration_count": sum(
            row.get("failure_code")
            in {
                "lean_term_uses_unretrieved_declaration",
                "reduction_not_retrieved",
                "native_evidence_not_retrieved",
                "hardness_target_not_retrieved",
            }
            for row in result.query_trace
            if row.get("action") == "protocol_feedback"
        ),
        "replayed_from_resume": False,
        "authoring_attempt_count": 0,
        "authoring_candidate_file_count": 0,
        "authoring_lean_precheck_count": 0,
        "final_status": (
            "PENDING"
            if case.is_positive
            else ("BLOCKED" if protocol_ok else "FAILED")
        ),
    }


def contract_errors(
    *,
    rows: Sequence[Mapping[str, Any]],
    cases: Sequence[BenchmarkCase],
    artifacts: Sequence[CoreGeneralizationArtifactCase],
    lean_ok: bool,
    lean_process_count: int,
    lean_started_after_all_tasks: bool,
    model_task_count_at_lean_start: int,
    parallel_execution: Mapping[str, Any],
    configured_jobs: int,
) -> tuple[str, ...]:
    errors: list[str] = []
    if len(rows) != 16 or len(artifacts) != 8:
        errors.append("Stage L must report 16 cases and emit all eight positives")
    for case, row in zip(cases, rows, strict=True):
        label = case.id
        if row.get("id") != label:
            errors.append(f"{label}: deterministic result ordering changed")
        if row.get("protocol_matches_expected") is not True:
            errors.append(f"{label}: protocol outcome differs from Expected")
        if row.get("replayed_from_resume") is not False:
            errors.append(f"{label}: prior model output was replayed")
        if row.get("prompt_oracle_errors") != []:
            errors.append(f"{label}: prompt oracle audit failed")
        calls = row.get("external_api_calls_this_run")
        if row.get("requires_model_call") is True:
            if not isinstance(calls, int) or isinstance(calls, bool) or calls <= 0:
                errors.append(f"{label}: no fresh DeepSeek call was recorded")
        elif calls != 0:
            errors.append(f"{label}: pre-model rejection unexpectedly called DeepSeek")
        if row.get("http_ok_count_this_run") != calls:
            errors.append(f"{label}: not every DeepSeek call succeeded")
        if calls and row.get("round_usage_complete") is not True:
            errors.append(f"{label}: token usage is incomplete")
        if row.get("model_turn_count", 0) > int(case.resources["max_model_calls"]):
            errors.append(f"{label}: model-turn cap was exceeded")
        if row.get("unretrieved_declaration_count") != 0:
            errors.append(f"{label}: an unretrieved declaration was attempted")
        if row.get("repeated_reduction_search_count") != 0:
            errors.append(f"{label}: an identical reduction query was repeated")
        if row.get("terminal_guidance_ignored_count") != 0:
            errors.append(f"{label}: terminal guidance was ignored")
        for field in (
            "authoring_attempt_count",
            "authoring_candidate_file_count",
            "authoring_lean_precheck_count",
        ):
            if row.get(field) != 0:
                errors.append(f"{label}: Core unexpectedly used authoring")
        if case.is_positive:
            if row.get("final_status") != "VERIFIED":
                errors.append(f"{label}: positive case failed final Lean")
            if row.get("model_term_changed_by_agent") is not False:
                errors.append(f"{label}: model objective term was rewritten")
            if row.get("selected_route_within_public_range") is not True:
                errors.append(f"{label}: selected route is outside its public band")
        else:
            if row.get("final_status") != "BLOCKED":
                errors.append(f"{label}: negative case was not correctly blocked")
            if row.get("failure_code") != case.expected.final_failure_code:
                errors.append(f"{label}: wrong stable blocker")
    if not lean_ok or lean_process_count != 1:
        errors.append("Stage L must pass exactly one combined final Lean process")
    if not lean_started_after_all_tasks or model_task_count_at_lean_start != 16:
        errors.append("final Lean started before every Core case task completed")
    if configured_jobs != CORE_GENERALIZATION_MAX_JOBS:
        errors.append("canonical Stage-L run must configure four case jobs")
    errors.extend(
        parallel_execution_errors(
            parallel_execution,
            expected_case_ids=[case.id for case in cases],
            minimum_observed_parallelism=CORE_GENERALIZATION_MAX_JOBS,
        )
    )
    return tuple(errors)


def main() -> int:
    command = parser()
    args = command.parse_args()
    try:
        validate_case_concurrency(args.jobs, args.minimum_observed_parallelism)
    except ValueError as error:
        command.error(str(error))
    output_root = args.output_root.resolve()
    report_path = output_root / "report.json"
    canonical_report = args.canonical_report.resolve()
    started_monotonic = time.monotonic()
    active_config: DeepSeekConfig | None = None
    report = core_generalization_report_skeleton(offline=False)
    report.update(
        {
            "run_label": args.run_label,
            "started_at": utc_now(),
            "runner": {
                "resume_supported": False,
                "replay_supported": False,
                "fresh_output_required": True,
                "configured_jobs": args.jobs,
                "maximum_allowed_jobs": CORE_GENERALIZATION_MAX_JOBS,
                "minimum_observed_parallelism": args.minimum_observed_parallelism,
            },
        }
    )

    def finish(status: str, *, exit_code: int, error: str | None = None) -> int:
        redactor = active_config.redact if active_config is not None else (lambda value: value)
        return finalize_report(
            report=report,
            report_path=report_path,
            canonical_report=canonical_report,
            status=status,
            exit_code=exit_code,
            run_label=args.run_label,
            error=error,
            redactor=redactor,
        )

    try:
        prepare_fresh_output_root(output_root)
        preflight_canonical_report(canonical_report)
        plans_root = output_root / "plans"
        transcripts_root = output_root / "transcripts"
        plans_root.mkdir()
        transcripts_root.mkdir()
        suite = load_benchmark_suite(args.suite)
        cases = validate_core_generalization_suite(suite)
        lean_root = ROOT / "Lean"
        toolchain = (lean_root / "lean-toolchain").read_text(encoding="utf-8").strip()
        manifest_sha256 = sha256_file(lean_root / "lake-manifest.json")
        problem_catalog = load_problem_catalog_snapshot(
            args.snapshots_root / "problem-catalog.json",
            expected_toolchain=toolchain,
            expected_lake_manifest_sha256=manifest_sha256,
        )
        fingerprint = problem_catalog.registry_fingerprint
        connection_catalog = load_connection_catalog_snapshot(
            args.snapshots_root / "connection-catalog.json",
            expected_registry_fingerprint=fingerprint,
            expected_toolchain=toolchain,
            expected_lake_manifest_sha256=manifest_sha256,
        )
        reduction_catalog = load_core_reduction_catalog(
            args.snapshots_root / "core-reduction-catalog.json",
            expected_registry_fingerprint=fingerprint,
            expected_toolchain=toolchain,
            expected_lake_manifest_sha256=manifest_sha256,
        )
        native_evidence_catalog = load_core_native_evidence_catalog(
            args.snapshots_root / "native-evidence-catalog.json",
            expected_registry_fingerprint=fingerprint,
            expected_toolchain=toolchain,
            expected_lake_manifest_sha256=manifest_sha256,
        )
        hardness_target_catalog = load_hardness_target_catalog_snapshot(
            args.snapshots_root / "hardness-target-catalog.json",
            expected_registry_fingerprint=fingerprint,
            expected_toolchain=toolchain,
            expected_lake_manifest_sha256=manifest_sha256,
        )
        snapshot_summary = json.loads(
            (args.snapshots_root / "snapshot-summary.json").read_text(encoding="utf-8")
        )
        input_file = module_file(lean_root, cases[0].module)
        input_sha256 = sha256_file(input_file)
        observation_cache: dict[str, tuple[LeanInputObservation, Path]] = {}

        def load_observation(declaration: str) -> tuple[LeanInputObservation, Path]:
            cached = observation_cache.get(declaration)
            if cached is not None:
                return cached
            path = observation_snapshot_path(
                args.snapshots_root / "observations",
                module=cases[0].module,
                declaration=declaration,
            )
            observation = load_input_observation_snapshot(
                path,
                expected_input_module=cases[0].module,
                expected_input_declaration=declaration,
                expected_input_module_sha256=input_sha256,
                expected_toolchain=toolchain,
                expected_lake_manifest_sha256=manifest_sha256,
                expected_registry_fingerprint=fingerprint,
            )
            observation_cache[declaration] = (observation, path)
            return observation, path

        prepared: list[
            tuple[
                BenchmarkCase,
                LeanInputObservation,
                Path,
                LeanInputObservation | None,
            ]
        ] = []
        for case in cases:
            observation, observation_path = load_observation(
                case.effective_input_declaration
            )
            target_observation = load_observation(case.target)[0] if case.target else None
            prepared.append(
                (case, observation, observation_path, target_observation)
            )
        config = DeepSeekConfig.from_environment(env_file=args.env_file)
        config = replace(
            config,
            model=args.model,
            timeout_seconds=args.model_timeout,
            max_tokens=args.model_max_tokens,
        )
        active_config = config
        if not config.api_key:
            raise ValueError("DEEPSEEK_API_KEY is not configured")
    except Exception as error:
        return finish("FAILED", exit_code=1, error=f"Stage-L preflight failed: {error}")

    report.update(
        {
            "benchmark": {
                "suite_id": suite.id,
                "suite_file": str(args.suite.resolve()),
                "suite_sha256": sha256_file(args.suite.resolve()),
                "case_count": 16,
                "positive_count": 8,
                "negative_count": 8,
                "case_ids": [case.id for case in cases],
                "work_package": "stage_l_core_generalization",
            },
            "model": {
                **config.to_public_dict(),
                "system_prompt_sha256": sha256_text(CORE_GENERALIZATION_SYSTEM_PROMPT),
            },
            "catalogs": {
                "registry_fingerprint": fingerprint,
                "problem_catalog_id": problem_catalog.catalog_id,
                "connection_catalog_id": connection_catalog.catalog_id,
                "core_reduction_catalog_id": reduction_catalog.catalog_id,
                "native_evidence_catalog_id": native_evidence_catalog.catalog_id,
                "hardness_target_catalog_id": hardness_target_catalog.catalog_id,
                "toolchain": toolchain,
                "lake_manifest_sha256": manifest_sha256,
                "snapshot_validation": snapshot_summary.get("validation"),
                "resume_or_replay_used": snapshot_summary.get("resume_or_replay_used"),
            },
            "observations": {
                "all_loaded_before_http": True,
                "count": len(observation_cache),
                "ids_by_case": {
                    case.id: observation.observation_id
                    for case, observation, _, _ in prepared
                },
            },
        }
    )
    write_json(report_path, report)

    def execute_case(
        index: int,
        prepared_case: tuple[
            BenchmarkCase,
            LeanInputObservation,
            Path,
            LeanInputObservation | None,
        ],
    ) -> CaseExecutionOutcome:
        case, observation, observation_path, target_observation = prepared_case
        result: ObservedInputPlannerResult | None = None
        try:
            print(
                json.dumps(
                    {
                        "phase": "deepseek_core_generalization",
                        "event": "started",
                        "case": case.id,
                        "index": index,
                        "total": 16,
                        "configured_jobs": args.jobs,
                    },
                    ensure_ascii=False,
                    sort_keys=True,
                ),
                flush=True,
            )
            result = generate_core_generalization_evidence(
                observation=observation,
                target_observation=target_observation,
                problem_catalog=problem_catalog,
                connection_catalog=connection_catalog,
                reduction_catalog=reduction_catalog,
                native_evidence_catalog=native_evidence_catalog,
                hardness_target_catalog=hardness_target_catalog,
                request=request_for_case(case),
                client=DeepSeekClient(config),
                maximum_model_turns=int(case.resources.get("max_model_calls", 14)),
            )
            rounds = build_round_records(
                case_id=case.id,
                prompts=result.model_prompts,
                responses=result.model_responses,
                output_root=output_root,
                config=config,
            )
            row = case_row(
                case=case,
                observation=observation,
                observation_path=observation_path,
                input_sha256=input_sha256,
                result=result,
                rounds=rounds,
            )
            row["execution_position"] = index
            if result.plan is not None:
                write_json(plans_root / f"{case.id}.json", result.plan.to_dict())
            artifact = (
                artifact_case(case, observation, result)
                if case.is_positive and result.protocol_accepted
                else None
            )
            write_json(transcripts_root / f"{case.id}.json", row)
            return CaseExecutionOutcome(index, case.id, row, artifact)
        except Exception as error:
            prompts = result.model_prompts if result is not None else ()
            responses = result.model_responses if result is not None else ()
            row = {
                "id": case.id,
                "execution_position": index,
                "family": case.coverage["family"],
                "input_kind": observation.input_kind,
                "objective": case.objective,
                "objective_class": case.coverage["objective_class"],
                "route_band": case.coverage["route_band"],
                "comparable_subset": case.coverage["comparable_subset"],
                "expected_status": case.expected.final_status,
                "expected_failure_code": case.expected.final_failure_code,
                "requires_model_call": observation.supported,
                "runner_error": config.redact(f"{type(error).__name__}: {error}"),
                "protocol_accepted": False,
                "protocol_matches_expected": False,
                "failure_code": "runner_internal_error",
                "external_api_calls_this_run": sum(response.called for response in responses),
                "http_ok_count_this_run": sum(response.called and response.ok for response in responses),
                "http_request_attempts_this_run": sum(response.attempts for response in responses),
                "usage": aggregate_usage(response.usage for response in responses),
                "round_usage_complete": all(
                    not response.called or isinstance(response.usage, Mapping)
                    for response in responses
                ),
                "model_turn_count": len(responses),
                "query_action_counts": {},
                "candidate_metrics": {},
                "prompt_oracle_errors": list(prompt_oracle_errors(prompts)),
                "terminal_guidance_ignored_count": 0,
                "repeated_reduction_search_count": 0,
                "unretrieved_declaration_count": 0,
                "replayed_from_resume": False,
                "authoring_attempt_count": 0,
                "authoring_candidate_file_count": 0,
                "authoring_lean_precheck_count": 0,
                "model_term_changed_by_agent": None,
                "selected_route_within_public_range": None,
                "final_status": "FAILED",
            }
            write_json(transcripts_root / f"{case.id}.json", row)
            return CaseExecutionOutcome(index, case.id, row, None)

    def progress(
        completed: tuple[CaseExecutionOutcome, ...],
        concurrency: Mapping[str, Any],
    ) -> None:
        completed_rows = [outcome.row for outcome in completed]
        report["cases"] = completed_rows
        report["parallel_execution"] = {
            **dict(concurrency),
            "minimum_observed_parallelism": args.minimum_observed_parallelism,
        }
        report["summary"] = {
            "completed_model_tasks": len(completed_rows),
            "model_api_turns_this_run": sum(
                int(row.get("external_api_calls_this_run") or 0)
                for row in completed_rows
            ),
            "usage": aggregate_usage(
                row.get("usage") if isinstance(row.get("usage"), Mapping) else None
                for row in completed_rows
            ),
            "lean_process_count": 0,
        }
        write_json(report_path, report)

    tasks = [
        (index, prepared_case[0].id, prepared_case)
        for index, prepared_case in enumerate(prepared, start=1)
    ]
    outcomes, parallel_execution = run_case_tasks(
        tasks,
        jobs=args.jobs,
        worker=execute_case,
        on_progress=progress,
    )
    rows = [outcome.row for outcome in outcomes]
    artifacts = [outcome.artifact for outcome in outcomes if outcome.artifact is not None]
    report["parallel_execution"] = {
        **parallel_execution,
        "minimum_observed_parallelism": args.minimum_observed_parallelism,
    }

    artifact_path = output_root / "CoreGeneralizationBatch.lean"
    model_tasks_at_lean_start = len(rows)
    lean_started_after_all_tasks = bool(
        model_tasks_at_lean_start == len(cases)
        and parallel_execution.get("active_case_task_count") == 0
    )
    artifact_source: str | None = None
    lean_command: Any = None
    lean_error: str | None = None
    try:
        artifact_source = build_core_generalization_batch_artifact_source(artifacts)
        assert_generated_source_is_safe(artifact_source)
        artifact_path.write_text(artifact_source, encoding="utf-8")
        lean_command = run_command(
            ["lake", "env", "lean", str(artifact_path.resolve())],
            cwd=lean_root,
            timeout_seconds=args.lean_timeout,
            output_limit=256 * 1024,
        )
    except Exception as error:
        lean_error = config.redact(f"{type(error).__name__}: {error}")
    lean_ok = bool(lean_command is not None and lean_command.ok)
    lean_process_count = int(lean_command is not None)
    accepted_ids = {artifact.case_id for artifact in artifacts}
    for case, row in zip(cases, rows, strict=True):
        if row.get("runner_error") is not None:
            row["final_status"] = "FAILED"
            row["final_failure_code"] = "runner_internal_error"
            row["final_explanation"] = row["runner_error"]
        elif case.is_positive:
            row["final_status"] = (
                "VERIFIED"
                if case.id in accepted_ids and lean_ok
                else "FAILED"
            )
            row["final_failure_code"] = (
                None
                if row["final_status"] == "VERIFIED"
                else row.get("failure_code")
                or ("final_lean_artifact_failed" if not lean_ok else "model_protocol_failed")
            )
            row["final_explanation"] = (
                "The untouched objective term passed the single combined Lean and axiom gate."
                if row["final_status"] == "VERIFIED"
                else row.get("explanation") or lean_error
            )
        elif row.get("protocol_matches_expected") is True:
            row["final_status"] = "BLOCKED"
            row["final_failure_code"] = row.get("failure_code")
            row["final_explanation"] = row.get("explanation")
        else:
            row["final_status"] = "FAILED"
            row["final_failure_code"] = row.get("failure_code") or "wrong_negative_failure"
            row["final_explanation"] = row.get("explanation")
        write_json(transcripts_root / f"{case.id}.json", row)

    source = artifact_source or ""
    report["artifact"] = {
        "path": str(artifact_path),
        "generated": artifact_source is not None,
        "sha256": sha256_text(source) if source else None,
        "accepted_positive_case_count": len(artifacts),
        "assert_standard_axioms_count": source.count("assert_standard_axioms"),
        "objective_counts": dict(Counter(artifact.objective for artifact in artifacts)),
        "authoring_candidate_file_count": 0,
    }
    report["lean"] = {
        "process_count": lean_process_count,
        "started_after_all_model_tasks": lean_started_after_all_tasks,
        "model_task_count_at_start": model_tasks_at_lean_start,
        "command": command_record(lean_command) if lean_command is not None else None,
        "not_started_reason": lean_error if lean_command is None else None,
    }
    report["parallel_execution"]["final_lean_started_after_case_tasks"] = (
        lean_started_after_all_tasks
    )
    report["execution_layers"] = {
        "core_reuse": {
            "case_count": 16,
            "model_calls": sum(
                int(row.get("external_api_calls_this_run") or 0) for row in rows
            ),
            "lean_process_count": lean_process_count,
        },
        "optional_authoring": {
            "attempt_count": 0,
            "candidate_file_count": 0,
            "lean_precheck_count": 0,
        },
    }
    report["cases"] = rows
    report["grouped_metrics"] = grouped_metrics(rows, cases)
    longest = max(
        rows,
        key=lambda row: float(row.get("case_task_wall_duration_seconds") or 0.0),
    )
    comparable = [row for row in rows if row.get("comparable_subset") is True]
    errors = contract_errors(
        rows=rows,
        cases=cases,
        artifacts=artifacts,
        lean_ok=lean_ok,
        lean_process_count=lean_process_count,
        lean_started_after_all_tasks=lean_started_after_all_tasks,
        model_task_count_at_lean_start=model_tasks_at_lean_start,
        parallel_execution=report["parallel_execution"],
        configured_jobs=args.jobs,
    )
    wall_duration = time.monotonic() - started_monotonic
    report["summary"] = {
        "protocol_expected_count": sum(
            row.get("protocol_matches_expected") is True for row in rows
        ),
        "positive_lean_verified_count": sum(
            row.get("expected_status") == "VERIFIED"
            and row.get("final_status") == "VERIFIED"
            for row in rows
        ),
        "negative_correctly_blocked_count": sum(
            row.get("expected_status") == "BLOCKED"
            and row.get("final_status") == "BLOCKED"
            for row in rows
        ),
        "model_api_turns_this_run": sum(
            int(row.get("external_api_calls_this_run") or 0) for row in rows
        ),
        "real_http_request_count_this_run": sum(
            int(row.get("http_request_attempts_this_run") or 0) for row in rows
        ),
        "usage": aggregate_usage(
            row.get("usage") if isinstance(row.get("usage"), Mapping) else None
            for row in rows
        ),
        "objective_usage": {
            objective: aggregate_usage(
                row.get("usage") if isinstance(row.get("usage"), Mapping) else None
                for row in rows
                if row.get("objective") == objective
            )
            for objective in sorted({case.objective for case in cases})
        },
        "family_usage": {
            family: aggregate_usage(
                row.get("usage") if isinstance(row.get("usage"), Mapping) else None
                for row in rows
                if row.get("family") == family
            )
            for family in sorted({str(case.coverage["family"]) for case in cases})
        },
        "comparable_subset": {
            "case_count": len(comparable),
            "protocol_expected_count": sum(
                row.get("protocol_matches_expected") is True for row in comparable
            ),
            "verified_or_correctly_blocked_count": sum(
                row.get("final_status") in {"VERIFIED", "BLOCKED"}
                for row in comparable
            ),
            "usage": aggregate_usage(
                row.get("usage") if isinstance(row.get("usage"), Mapping) else None
                for row in comparable
            ),
        },
        "lean_process_count": lean_process_count,
        "authoring_attempt_count": 0,
        "authoring_candidate_file_count": 0,
        "authoring_lean_precheck_count": 0,
        "model_term_rewrite_count": sum(
            row.get("model_term_changed_by_agent") is True for row in rows
        ),
        "unretrieved_declaration_count": sum(
            int(row.get("unretrieved_declaration_count") or 0) for row in rows
        ),
        "repeated_reduction_search_count": sum(
            int(row.get("repeated_reduction_search_count") or 0) for row in rows
        ),
        "terminal_guidance_ignored_count": sum(
            int(row.get("terminal_guidance_ignored_count") or 0) for row in rows
        ),
        "oracle_audit_error_count": sum(
            len(row.get("prompt_oracle_errors") or []) for row in rows
        ),
        "configured_case_jobs": args.jobs,
        "maximum_concurrent_case_tasks": parallel_execution.get(
            "maximum_concurrent_case_tasks", 0
        ),
        "final_active_case_task_count": parallel_execution.get(
            "active_case_task_count", 0
        ),
        "wall_duration_seconds": round(wall_duration, 3),
        "longest_case": {
            "id": longest.get("id"),
            "wall_duration_seconds": longest.get("case_task_wall_duration_seconds"),
        },
        "parallel_throughput_cases_per_second": round(16 / wall_duration, 6),
        "contract_errors": list(errors),
        "all_core_generalization_thresholds_met": not errors,
    }
    if not errors:
        return finish("VERIFIED", exit_code=0)
    return finish(
        "FAILED",
        exit_code=1,
        error="Stage-L full run failed its report contract: " + "; ".join(errors[:10]),
    )


if __name__ == "__main__":
    raise SystemExit(main())
