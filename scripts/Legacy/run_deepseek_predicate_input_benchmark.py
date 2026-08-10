#!/usr/bin/env python3
"""Run the complete Stage H predicate-input suite with fresh DeepSeek calls."""

from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Mapping, Sequence
from dataclasses import replace
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.artifact import OpenTargetArtifactCase  # noqa: E402
from agent.hardness.benchmark import BenchmarkCase, load_benchmark_suite  # noqa: E402
from agent.hardness.connection_catalog import (  # noqa: E402
    build_reduction_catalog,
    load_connection_catalog_snapshot,
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
from agent.hardness.lean_runner import module_file, sha256_file  # noqa: E402
from agent.hardness.model_client import DeepSeekClient, DeepSeekConfig  # noqa: E402
from agent.hardness.open_target_planner import (  # noqa: E402
    MAX_OPEN_TARGET_QUERY_ROUNDS,
    OPEN_TARGET_SYSTEM_PROMPT,
    OpenTargetRequestPolicy,
    generate_lean_path_to_open_target,
)
from agent.hardness.predicate_input import (  # noqa: E402
    find_predicate_input_prompt_forbidden_keys,
    validate_predicate_input_suite,
)
from agent.hardness.problem_catalog import load_problem_catalog_snapshot  # noqa: E402
from scripts.run_deepseek_open_target_benchmark import (  # noqa: E402
    aggregate_usage,
    build_case_runner_error_row,
    build_round_records,
    command_record,
    completed_action_counts,
    finalize_report,
    model_term_changed_by_agent,
    open_target_candidate_metrics,
    preflight_canonical_report,
    prepare_fresh_output_root,
    prompt_oracle_errors,
    query_round_count,
    result_row as base_result_row,
    run_final_lean_after_all_model_tasks,
    selected_fact_audit,
    sha256_text,
    submitted_model_term,
    usage_contract_errors,
    utc_now,
    write_json,
)


SCHEMA_VERSION = "hardness_predicate_input_deepseek_report_v1"


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description=(
            "Run all Stage H predicate-input cases with fresh real DeepSeek calls, "
            "then verify one combined Lean artifact"
        )
    )
    command.add_argument(
        "--suite",
        type=Path,
        default=ROOT / "Gate" / "Suites" / "predicate_input.json",
    )
    command.add_argument(
        "--snapshots-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "stage-h-snapshots",
    )
    command.add_argument("--env-file", type=Path, default=ROOT / ".env")
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "deepseek-predicate-input-full",
    )
    command.add_argument(
        "--canonical-report",
        type=Path,
        default=ROOT / "Reports" / "PREDICATE_INPUT_REPORT.json",
    )
    command.add_argument("--run-label", default="stage-h-full-real-deepseek")
    command.add_argument("--lean-timeout", type=int, default=900)
    command.add_argument("--model-timeout", type=int, default=None)
    command.add_argument("--model-max-tokens", type=int, default=8192)
    command.add_argument(
        "--query-rounds", type=int, default=MAX_OPEN_TARGET_QUERY_ROUNDS
    )
    return command


def request_policy(case: BenchmarkCase) -> OpenTargetRequestPolicy:
    if (
        case.required_hardness is None
        or case.maximum_route_atoms is None
        or case.maximum_dependencies is None
    ):
        raise ValueError(f"case {case.id} has incomplete Stage H target policy")
    return OpenTargetRequestPolicy(
        required_hardness=case.required_hardness,
        allowed_target_evidence=case.allowed_target_evidence,
        minimum_route_atoms=case.minimum_route_atoms,
        maximum_route_atoms=case.maximum_route_atoms,
        maximum_dependencies=case.maximum_dependencies,
        allow_reflexive_target=case.allow_reflexive_target,
        require_simple_path=case.require_simple_path,
        objective=case.objective,
    )


def _predicate_model_case(observation: LeanInputObservation) -> bool:
    return bool(observation.supported and observation.input_kind == "predicate")


def _predicate_prompt_oracle_errors(prompts: Sequence[str]) -> tuple[str, ...]:
    """Apply both the Stage G target audit and the stricter Stage H audit."""

    errors = list(prompt_oracle_errors(prompts))
    for turn, prompt in enumerate(prompts, start=1):
        try:
            payload = json.loads(prompt)
        except json.JSONDecodeError:
            continue
        if not isinstance(payload, Mapping):
            continue
        leaked = find_predicate_input_prompt_forbidden_keys(payload)
        if leaked:
            errors.append(
                f"turn {turn}: predicate-input prompt contains oracle fields: "
                + ", ".join(leaked)
            )
    return tuple(dict.fromkeys(errors))


def _artifact_case(
    case: BenchmarkCase, result: ObservedInputPlannerResult
) -> OpenTargetArtifactCase:
    if result.plan is None or result.lean_term is None:
        raise ValueError(f"case {case.id} has no accepted Stage H plan")
    evidence = result.plan.target_evidence
    return OpenTargetArtifactCase(
        case_id=case.id,
        input_module=case.module,
        source_declaration=result.plan.source_declaration,
        predicate_declaration=case.effective_input_declaration,
        target_declaration=result.plan.target_declaration or "",
        lean_term=result.lean_term,
        required_hardness=case.required_hardness or "",
        target_evidence_kind=str(evidence.get("evidence_kind") or ""),
        target_evidence_lean_term=str(evidence.get("evidence_lean_term") or ""),
    )


def _stage_h_row(
    *,
    case: BenchmarkCase,
    observation: LeanInputObservation,
    observation_snapshot: Path,
    input_source_sha256: str,
    result: ObservedInputPlannerResult,
    round_records: list[dict[str, Any]],
    model_term: str | None,
    problem_catalog_id: str,
    connection_catalog_id: str,
    reduction_catalog: Any,
    target_catalog_id: str,
) -> dict[str, Any]:
    row = base_result_row(
        case=case,
        observation=observation,
        observation_snapshot=observation_snapshot,
        input_source_sha256=input_source_sha256,
        result=result,
        round_records=round_records,
        model_term=model_term,
        problem_catalog_id=problem_catalog_id,
        connection_catalog_id=connection_catalog_id,
        reduction_catalog=reduction_catalog,
        target_catalog_id=target_catalog_id,
    )
    row.update(
        {
            "input_kind": observation.input_kind,
            "predicate_node_id": observation.predicate_node_id,
            "predicate_domain_node_id": observation.predicate_domain_node_id,
            "lean_confirmed_predicate_match_count": len(
                observation.predicate_presentation_matches
            ),
            "path_source_declaration": (
                result.plan.source_declaration if result.plan is not None else None
            ),
            "requires_model_call": _predicate_model_case(observation),
            "prompt_oracle_errors": list(
                _predicate_prompt_oracle_errors(result.model_prompts)
            ),
        }
    )
    return row


def _routing_rule_audit(cases: tuple[BenchmarkCase, ...]) -> dict[str, Any]:
    """Detect benchmark literals accidentally embedded in production routing."""

    paths = (
        ROOT / "agent" / "hardness" / "input_observation.py",
        ROOT / "agent" / "hardness" / "problem_catalog.py",
        ROOT / "agent" / "hardness" / "input_planner.py",
        ROOT / "agent" / "hardness" / "open_target_planner.py",
        ROOT / "agent" / "hardness" / "open_target_simulation.py",
    )
    markers = tuple(
        sorted(
            {
                value
                for case in cases
                for value in (case.id, case.module, case.effective_input_declaration)
            }
        )
    )
    evidence: list[dict[str, Any]] = []
    for path in paths:
        text = path.read_text(encoding="utf-8")
        for marker in markers:
            if marker in text:
                evidence.append({"path": str(path.relative_to(ROOT)), "marker": marker})
    return {
        "audited_files": [str(path.relative_to(ROOT)) for path in paths],
        "benchmark_marker_count": len(markers),
        "python_family_specific_rule_count": len(evidence),
        "evidence": evidence,
    }


def _contract_errors(
    rows: list[Mapping[str, Any]],
    *,
    lean_process_count: int,
    lean_ok: bool,
    lean_started_after_all_model_tasks: bool,
    model_task_count_at_lean_start: int,
    artifact_sha256: str | None,
    accepted_positive_case_count: int,
    assert_standard_axioms_count: int,
    predicate_grounding_count: int,
    predicate_grounding_audit_reference_count: int,
    routing_rule_count: int,
) -> tuple[str, ...]:
    errors: list[str] = []
    if len(rows) != 8:
        errors.append("Stage H report must contain exactly eight cases")
    positives = [row for row in rows if row.get("expected_status") == "VERIFIED"]
    negatives = [row for row in rows if row.get("expected_status") == "BLOCKED"]
    if len(positives) != 4 or len(negatives) != 4:
        errors.append("Stage H report must contain four positives and four negatives")
    for row in rows:
        label = str(row.get("id") or "<missing-case-id>")
        if row.get("protocol_matches_expected") is not True:
            errors.append(f"{label}: protocol outcome differs from Expected")
        if row.get("replayed_from_resume") is not False:
            errors.append(f"{label}: a prior model answer was replayed")
        if row.get("prompt_oracle_errors") != []:
            errors.append(f"{label}: prompt contains oracle data")
        requires_model = row.get("requires_model_call") is True
        calls = row.get("external_api_calls_this_run")
        if requires_model:
            if not isinstance(calls, int) or isinstance(calls, bool) or calls <= 0:
                errors.append(f"{label}: no fresh DeepSeek call was recorded")
            if row.get("http_ok_count_this_run") != calls:
                errors.append(f"{label}: not every DeepSeek turn succeeded")
            if row.get("round_usage_complete") is not True:
                errors.append(f"{label}: token usage is incomplete")
            usage = row.get("usage")
            errors.extend(
                usage_contract_errors(
                    usage if isinstance(usage, Mapping) else None,
                    label=f"{label}.aggregate",
                )
            )
        elif calls not in (0, None):
            errors.append(f"{label}: structural rejection unexpectedly called DeepSeek")
        if row.get("expected_status") == "VERIFIED":
            if row.get("final_status") != "VERIFIED":
                errors.append(f"{label}: positive case did not pass final Lean")
            if row.get("protocol_accepted") is not True:
                errors.append(f"{label}: positive case was not accepted")
            if row.get("model_term_changed_by_agent") is not False:
                errors.append(f"{label}: model Lean term was rewritten")
            match = row.get("problem_match")
            if not isinstance(match, Mapping) or match.get(
                "accepts_exact_defeq"
            ) is not True:
                errors.append(f"{label}: no Lean-confirmed predicate grounding")
            if row.get("path_source_declaration") == row.get("source_declaration"):
                errors.append(f"{label}: raw predicate was used as CertifiedPath source")
            for field in (
                "selected_target_from_search",
                "selected_evidence_from_search",
                "selected_evidence_policy_satisfied",
                "matched_problem_from_search",
                "route_declarations_all_retrieved",
                "all_selected_facts_retrieved",
            ):
                if row.get(field) is not True:
                    errors.append(f"{label}: {field} is not true")
        else:
            if row.get("final_status") != "BLOCKED":
                errors.append(f"{label}: negative case was not correctly blocked")
            if row.get("final_failure_code") != row.get("expected_failure_code"):
                errors.append(f"{label}: wrong stable failure code")
    if lean_process_count != 1 or not lean_ok:
        errors.append("Stage H must pass exactly one final Lean process")
    if not lean_started_after_all_model_tasks or model_task_count_at_lean_start != 8:
        errors.append("final Lean started before all Stage H tasks completed")
    if not isinstance(artifact_sha256, str) or len(artifact_sha256) != 64:
        errors.append("combined Stage H artifact SHA-256 is missing")
    if accepted_positive_case_count != 4:
        errors.append("combined Stage H artifact does not contain all positives")
    if assert_standard_axioms_count != 1:
        errors.append("combined Stage H artifact must contain one axiom gate")
    if predicate_grounding_count != 4:
        errors.append("combined Stage H artifact must declare four predicate groundings")
    if predicate_grounding_audit_reference_count != 4:
        errors.append("combined Stage H axiom gate must audit four predicate groundings")
    if routing_rule_count != 0:
        errors.append("production routing contains Stage H benchmark-specific literals")
    return tuple(errors)


def main() -> int:
    args = parser().parse_args()
    output_root = args.output_root.resolve()
    report_path = output_root / "report.json"
    canonical_report = args.canonical_report.resolve()
    active_config: DeepSeekConfig | None = None
    report: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "run_label": args.run_label,
        "started_at": utc_now(),
        "status": "RUNNING",
        "runner": {
            "resume_supported": False,
            "replay_supported": False,
            "fresh_output_required": True,
        },
    }

    def finish(status: str, *, exit_code: int, error: str | None = None) -> int:
        redactor = active_config.redact if active_config is not None else (lambda v: v)
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
        cases = validate_predicate_input_suite(suite)
        lean_root = ROOT / "Lean"
        toolchain = (lean_root / "lean-toolchain").read_text(encoding="utf-8").strip()
        manifest_sha256 = sha256_file(lean_root / "lake-manifest.json")
        problem_catalog = load_problem_catalog_snapshot(
            args.snapshots_root / "problem-catalog.json",
            expected_toolchain=toolchain,
            expected_lake_manifest_sha256=manifest_sha256,
        )
        connection_catalog = load_connection_catalog_snapshot(
            args.snapshots_root / "connection-catalog.json",
            expected_registry_fingerprint=problem_catalog.registry_fingerprint,
            expected_toolchain=toolchain,
            expected_lake_manifest_sha256=manifest_sha256,
        )
        target_catalog = load_hardness_target_catalog_snapshot(
            args.snapshots_root / "hardness-target-catalog.json",
            expected_registry_fingerprint=problem_catalog.registry_fingerprint,
            expected_toolchain=toolchain,
            expected_lake_manifest_sha256=manifest_sha256,
        )
        reduction_catalog = build_reduction_catalog(connection_catalog, mode="full")

        prepared: list[tuple[BenchmarkCase, LeanInputObservation, Path, str]] = []
        for case in cases:
            input_path = module_file(lean_root, case.module)
            input_sha256 = sha256_file(input_path)
            snapshot = observation_snapshot_path(
                args.snapshots_root / "observations",
                module=case.module,
                declaration=case.effective_input_declaration,
            )
            observation = load_input_observation_snapshot(
                snapshot,
                expected_input_module=case.module,
                expected_input_declaration=case.effective_input_declaration,
                expected_input_module_sha256=input_sha256,
                expected_toolchain=toolchain,
                expected_lake_manifest_sha256=manifest_sha256,
                expected_registry_fingerprint=problem_catalog.registry_fingerprint,
            )
            prepared.append((case, observation, snapshot, input_sha256))

        config = DeepSeekConfig.from_environment(env_file=args.env_file)
        config = replace(config, max_tokens=args.model_max_tokens)
        if args.model_timeout is not None:
            config = replace(config, timeout_seconds=args.model_timeout)
        active_config = config
        if not config.api_key:
            raise ValueError("DEEPSEEK_API_KEY is not configured")
    except Exception as error:
        return finish("FAILED", exit_code=1, error=f"Stage H preflight failed: {error}")

    report.update(
        {
            "benchmark": {
                "suite_id": suite.id,
                "suite_file": str(args.suite.resolve()),
                "suite_sha256": sha256_file(args.suite.resolve()),
                "case_count": len(cases),
                "positive_count": sum(case.is_positive for case in cases),
                "negative_count": sum(not case.is_positive for case in cases),
                "case_ids": [case.id for case in cases],
            },
            "model": {
                **config.to_public_dict(),
                "system_prompt_sha256": sha256_text(OPEN_TARGET_SYSTEM_PROMPT),
            },
            "catalogs": {
                "registry_fingerprint": problem_catalog.registry_fingerprint,
                "problem_catalog_id": problem_catalog.catalog_id,
                "connection_catalog_id": connection_catalog.catalog_id,
                "reduction_catalog_id": reduction_catalog.catalog_id,
                "hardness_target_catalog_id": target_catalog.catalog_id,
                "toolchain": toolchain,
                "lake_manifest_sha256": manifest_sha256,
            },
            "observations": {
                "all_loaded_before_http": True,
                "count": len(prepared),
                "ids_by_case": {
                    case.id: observation.observation_id
                    for case, observation, _, _ in prepared
                },
            },
        }
    )
    write_json(report_path, report)

    client = DeepSeekClient(config)
    rows: list[dict[str, Any]] = []
    artifacts: list[OpenTargetArtifactCase] = []
    for index, (case, observation, snapshot, input_sha256) in enumerate(
        prepared, start=1
    ):
        result: ObservedInputPlannerResult | None = None
        try:
            print(
                json.dumps(
                    {
                        "phase": "deepseek_predicate_input",
                        "case": case.id,
                        "index": index,
                        "total": len(prepared),
                    },
                    ensure_ascii=False,
                    sort_keys=True,
                ),
                flush=True,
            )
            result = generate_lean_path_to_open_target(
                observation=observation,
                problem_catalog=problem_catalog,
                connection_catalog=connection_catalog,
                reduction_catalog=reduction_catalog,
                target_catalog=target_catalog,
                request_policy=request_policy(case),
                client=client,
                maximum_query_rounds=args.query_rounds,
            )
            model_term = submitted_model_term(result.model_responses)
            round_records = build_round_records(
                case_id=case.id,
                prompts=result.model_prompts,
                responses=result.model_responses,
                output_root=output_root,
                config=config,
            )
            row = _stage_h_row(
                case=case,
                observation=observation,
                observation_snapshot=snapshot,
                input_source_sha256=input_sha256,
                result=result,
                round_records=round_records,
                model_term=model_term,
                problem_catalog_id=problem_catalog.catalog_id,
                connection_catalog_id=connection_catalog.catalog_id,
                reduction_catalog=reduction_catalog,
                target_catalog_id=target_catalog.catalog_id,
            )
            row["execution_position"] = index
            rows.append(row)
            if result.plan is not None:
                write_json(plans_root / f"{case.id}.json", result.plan.to_dict())
            if case.is_positive and result.protocol_accepted:
                artifacts.append(_artifact_case(case, result))
            write_json(transcripts_root / f"{case.id}.json", row)
        except Exception as error:
            error_row = build_case_runner_error_row(
                case=case,
                execution_position=index,
                error=error,
                config=config,
                result=result,
            )
            error_row.update(
                {
                    "input_kind": observation.input_kind,
                    "predicate_node_id": observation.predicate_node_id,
                    "predicate_domain_node_id": observation.predicate_domain_node_id,
                    "lean_confirmed_predicate_match_count": len(
                        observation.predicate_presentation_matches
                    ),
                    "requires_model_call": _predicate_model_case(observation),
                    "path_source_declaration": None,
                    "prompt_oracle_errors": list(
                        _predicate_prompt_oracle_errors(
                            result.model_prompts if result is not None else ()
                        )
                    ),
                }
            )
            rows.append(error_row)
            write_json(transcripts_root / f"{case.id}.json", error_row)
        report["cases"] = rows
        report["progress"] = {
            "completed_model_tasks": len(rows),
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
            "lean_process_count": 0,
        }
        write_json(report_path, report)

    artifact_path = output_root / "PredicateInputBatch.lean"
    try:
        lean_execution = run_final_lean_after_all_model_tasks(
            artifacts=artifacts,
            completed_model_task_count=len(rows),
            expected_model_task_count=len(cases),
            artifact_path=artifact_path,
            lean_root=lean_root,
            timeout_seconds=args.lean_timeout,
        )
    except Exception as error:
        lean_execution = {
            "source": None,
            "artifact_sha256": None,
            "process_count": 0,
            "started_after_all_model_tasks": False,
            "model_task_count_at_start": len(rows),
            "command": None,
            "error": config.redact(f"{type(error).__name__}: {error}"),
        }
    final_command = lean_execution.get("command")
    lean_ok = bool(final_command is not None and final_command.ok)
    artifact_source = lean_execution.get("source")
    axiom_count = (
        str(artifact_source).count("assert_standard_axioms")
        if artifact_source is not None
        else 0
    )
    grounding_count = (
        str(artifact_source).count("theorem inputPredicateGrounding")
        if artifact_source is not None
        else 0
    )
    grounding_audit_reference_count = (
        str(artifact_source).count(".inputPredicateGrounding")
        if artifact_source is not None
        else 0
    )
    report["artifact"] = {
        "path": str(artifact_path),
        "generated": artifact_source is not None,
        "sha256": lean_execution.get("artifact_sha256"),
        "accepted_positive_case_count": len(artifacts),
        "assert_standard_axioms_count": axiom_count,
        "predicate_grounding_count": grounding_count,
        "predicate_grounding_audit_reference_count": (
            grounding_audit_reference_count
        ),
    }
    report["lean"] = {
        "process_count": lean_execution.get("process_count", 0),
        "started_after_all_model_tasks": lean_execution.get(
            "started_after_all_model_tasks", False
        ),
        "model_task_count_at_start": lean_execution.get(
            "model_task_count_at_start", 0
        ),
        "command": command_record(final_command) if final_command is not None else None,
        "not_started_reason": (
            None
            if final_command is not None
            else lean_execution.get("error")
            or "no accepted Stage H positive artifact"
        ),
    }

    for case, row in zip(cases, rows, strict=True):
        if row.get("runner_error") is not None:
            row["final_status"] = "FAILED"
            row["final_failure_code"] = "runner_internal_error"
            row["final_explanation"] = row["runner_error"]
        elif case.is_positive:
            if row.get("protocol_accepted") is True and lean_ok:
                row["final_status"] = "VERIFIED"
                row["final_failure_code"] = None
                row["final_explanation"] = (
                    "The untouched model path, target evidence, and real predicate "
                    "grounding all passed the single combined Lean axiom gate."
                )
            else:
                row["final_status"] = "FAILED"
                row["final_failure_code"] = row.get("failure_code") or (
                    "final_lean_artifact_failed" if not lean_ok else "model_protocol_failed"
                )
                row["final_explanation"] = row.get("explanation")
        elif row.get("protocol_matches_expected") is True:
            row["final_status"] = "BLOCKED"
            row["final_failure_code"] = row.get("failure_code")
            row["final_explanation"] = row.get("explanation")
        else:
            row["final_status"] = "FAILED"
            row["final_failure_code"] = row.get("failure_code") or "wrong_negative_failure"
            row["final_explanation"] = row.get("explanation")
        write_json(transcripts_root / f"{case.id}.json", row)

    routing_audit = _routing_rule_audit(cases)
    report["python_family_rule_audit"] = routing_audit
    errors = _contract_errors(
        rows,
        lean_process_count=int(lean_execution.get("process_count", 0)),
        lean_ok=lean_ok,
        lean_started_after_all_model_tasks=bool(
            lean_execution.get("started_after_all_model_tasks", False)
        ),
        model_task_count_at_lean_start=int(
            lean_execution.get("model_task_count_at_start", 0)
        ),
        artifact_sha256=lean_execution.get("artifact_sha256"),
        accepted_positive_case_count=len(artifacts),
        assert_standard_axioms_count=axiom_count,
        predicate_grounding_count=grounding_count,
        predicate_grounding_audit_reference_count=(
            grounding_audit_reference_count
        ),
        routing_rule_count=int(routing_audit["python_family_specific_rule_count"]),
    )
    report["cases"] = rows
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
        "model_eligible_case_count": sum(
            row.get("requires_model_call") is True for row in rows
        ),
        "model_api_turns_this_run": sum(
            int(row.get("external_api_calls_this_run") or 0) for row in rows
        ),
        "real_http_request_count_this_run": sum(
            int(row.get("http_request_attempts_this_run") or 0) for row in rows
        ),
        "replayed_case_count": sum(
            row.get("replayed_from_resume") is not False for row in rows
        ),
        "usage": aggregate_usage(
            row.get("usage") if isinstance(row.get("usage"), Mapping) else None
            for row in rows
        ),
        "lean_process_count": int(lean_execution.get("process_count", 0)),
        "model_term_rewrite_count": sum(
            row.get("model_term_changed_by_agent") is True for row in rows
        ),
        "contract_errors": list(errors),
        "all_stage_h_thresholds_met": not errors,
    }
    if not errors:
        return finish("VERIFIED", exit_code=0)
    return finish(
        "FAILED",
        exit_code=1,
        error="Stage H full run failed its report contract: " + "; ".join(errors[:8]),
    )


if __name__ == "__main__":
    raise SystemExit(main())
