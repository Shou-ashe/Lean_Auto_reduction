#!/usr/bin/env python3
"""Run the complete Stage-I expansion suite with fresh DeepSeek calls."""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import sys
import threading
import time
from collections import Counter
from collections.abc import Callable, Mapping, Sequence
from dataclasses import dataclass, replace
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
from agent.hardness.frontier_efficiency import (  # noqa: E402
    FRONTIER_EFFICIENCY_SUITE_ID,
    analyze_frontier_interactions,
    validate_frontier_efficiency_suite,
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
)
from agent.hardness.problem_catalog import load_problem_catalog_snapshot  # noqa: E402
from agent.hardness.stage_i_expansion import (  # noqa: E402
    STAGE_I_SUITE_ID,
    validate_stage_i_expansion_suite,
)
from scripts.run_deepseek_open_target_benchmark import (  # noqa: E402
    aggregate_usage,
    build_case_runner_error_row,
    build_round_records,
    command_record,
    finalize_report,
    preflight_canonical_report,
    prepare_fresh_output_root,
    prompt_oracle_errors,
    result_row as base_result_row,
    run_final_lean_after_all_model_tasks,
    sha256_text,
    submitted_model_term,
    usage_contract_errors,
    utc_now,
    write_json,
)


SCHEMA_VERSION = "hardness_stage_i_expansion_deepseek_report_v1"
FRONTIER_SCHEMA_VERSION = "hardness_frontier_efficiency_deepseek_report_v1"
PARALLEL_SCHEMA_VERSION = "hardness_frontier_efficiency_parallel_deepseek_report_v1"
DEFAULT_STAGE_I_MODEL_TIMEOUT = 900
DEFAULT_STAGE_I_MODEL_MAX_TOKENS = 32768
DEFAULT_CASE_JOBS = 1
MAX_CASE_JOBS = 4


@dataclass(frozen=True)
class CaseExecutionOutcome:
    index: int
    case_id: str
    row: dict[str, Any]
    artifact: OpenTargetArtifactCase | None


def validate_case_concurrency(
    jobs: int, minimum_observed_parallelism: int
) -> tuple[int, int]:
    if isinstance(jobs, bool) or not isinstance(jobs, int) or not 1 <= jobs <= MAX_CASE_JOBS:
        raise ValueError(f"--jobs must be in 1..{MAX_CASE_JOBS}")
    if (
        isinstance(minimum_observed_parallelism, bool)
        or not isinstance(minimum_observed_parallelism, int)
        or not 1 <= minimum_observed_parallelism <= jobs
    ):
        raise ValueError(
            "--minimum-observed-parallelism must be in 1..--jobs"
        )
    return jobs, minimum_observed_parallelism


def run_case_tasks(
    tasks: Sequence[tuple[int, str, Any]],
    *,
    jobs: int,
    worker: Callable[[int, Any], CaseExecutionOutcome],
    on_progress: Callable[
        [tuple[CaseExecutionOutcome, ...], Mapping[str, Any]], None
    ]
    | None = None,
) -> tuple[tuple[CaseExecutionOutcome, ...], dict[str, Any]]:
    """Run independent case sessions with bounded, auditable concurrency."""

    if not tasks:
        raise ValueError("case task list must not be empty")
    validate_case_concurrency(jobs, 1)
    worker_count = min(jobs, len(tasks))
    lock = threading.Lock()
    active = 0
    maximum_active = 0
    started = 0
    completed = 0
    start_order: list[str] = []
    completion_order: list[str] = []
    outcomes: dict[int, CaseExecutionOutcome] = {}

    def snapshot() -> dict[str, Any]:
        with lock:
            return {
                "execution_model": "bounded_case_thread_pool",
                "configured_jobs": jobs,
                "maximum_allowed_jobs": MAX_CASE_JOBS,
                "worker_count": worker_count,
                "active_case_task_count": active,
                "started_case_task_count": started,
                "completed_case_task_count": completed,
                "maximum_concurrent_case_tasks": maximum_active,
                "case_start_order": list(start_order),
                "case_completion_order": list(completion_order),
            }

    def tracked(task: tuple[int, str, Any]) -> CaseExecutionOutcome:
        nonlocal active, maximum_active, started, completed
        index, case_id, payload = task
        started_at = utc_now()
        started_monotonic = time.monotonic()
        with lock:
            active += 1
            started += 1
            maximum_active = max(maximum_active, active)
            start_order.append(case_id)
        try:
            outcome = worker(index, payload)
            outcome.row["case_task_started_at"] = started_at
            outcome.row["case_task_finished_at"] = utc_now()
            outcome.row["case_task_wall_duration_seconds"] = round(
                time.monotonic() - started_monotonic, 3
            )
            return outcome
        finally:
            with lock:
                active -= 1
                completed += 1
                completion_order.append(case_id)

    with concurrent.futures.ThreadPoolExecutor(
        max_workers=worker_count,
        thread_name_prefix="hardness-case",
    ) as executor:
        futures = {
            executor.submit(tracked, task): task[0]
            for task in tasks
        }
        for future in concurrent.futures.as_completed(futures):
            outcome = future.result()
            outcomes[outcome.index] = outcome
            ordered = tuple(outcomes[index] for index in sorted(outcomes))
            if on_progress is not None:
                on_progress(ordered, snapshot())

    ordered = tuple(outcomes[index] for index, _, _ in tasks)
    return ordered, snapshot()


def parallel_execution_errors(
    audit: Mapping[str, Any],
    *,
    expected_case_ids: Sequence[str],
    minimum_observed_parallelism: int,
) -> tuple[str, ...]:
    errors: list[str] = []
    configured = audit.get("configured_jobs")
    worker_count = audit.get("worker_count")
    maximum = audit.get("maximum_concurrent_case_tasks")
    expected_count = len(expected_case_ids)
    if (
        not isinstance(configured, int)
        or isinstance(configured, bool)
        or not 1 <= configured <= MAX_CASE_JOBS
    ):
        errors.append("case concurrency configured_jobs is outside 1..4")
    expected_workers = min(int(configured or 0), expected_count)
    if worker_count != expected_workers:
        errors.append("case concurrency worker_count does not match the bounded request")
    if (
        not isinstance(maximum, int)
        or isinstance(maximum, bool)
        or maximum < minimum_observed_parallelism
        or maximum > int(worker_count or 0)
    ):
        errors.append("case concurrency did not meet the observed parallelism contract")
    if audit.get("started_case_task_count") != expected_count:
        errors.append("not every case task was started")
    if audit.get("completed_case_task_count") != expected_count:
        errors.append("not every case task was completed")
    if audit.get("active_case_task_count") != 0:
        errors.append("case tasks were still active before final Lean")
    for field in ("case_start_order", "case_completion_order"):
        values = audit.get(field)
        if (
            not isinstance(values, list)
            or len(values) != expected_count
            or set(values) != set(expected_case_ids)
        ):
            errors.append(f"{field} does not cover every case exactly once")
    return tuple(errors)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description=(
            "Run all Stage-I expansion cases with fresh real DeepSeek calls, "
            "then verify one combined Lean artifact"
        )
    )
    command.add_argument(
        "--suite",
        type=Path,
        default=ROOT / "Gate" / "Suites" / "stage_i_expansion.json",
    )
    command.add_argument(
        "--snapshots-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "stage-i-expansion-snapshots",
    )
    command.add_argument("--env-file", type=Path, default=ROOT / ".env")
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "deepseek-stage-i-expansion-full",
    )
    command.add_argument(
        "--canonical-report",
        type=Path,
        default=ROOT / "Reports" / "STAGE_I_EXPANSION_REPORT.json",
    )
    command.add_argument("--run-label", default="stage-i-expansion-full-real-deepseek")
    command.add_argument("--lean-timeout", type=int, default=1200)
    command.add_argument(
        "--model-timeout",
        type=int,
        default=DEFAULT_STAGE_I_MODEL_TIMEOUT,
    )
    command.add_argument(
        "--model-max-tokens",
        type=int,
        default=DEFAULT_STAGE_I_MODEL_MAX_TOKENS,
    )
    command.add_argument(
        "--query-rounds",
        type=int,
        default=MAX_OPEN_TARGET_QUERY_ROUNDS,
    )
    command.add_argument(
        "--jobs",
        type=int,
        default=DEFAULT_CASE_JOBS,
        help=f"Run 1..{MAX_CASE_JOBS} independent cases concurrently.",
    )
    command.add_argument(
        "--minimum-observed-parallelism",
        type=int,
        default=1,
        help=(
            "Report-contract lower bound for actually overlapping case tasks; "
            "must not exceed --jobs."
        ),
    )
    command.add_argument(
        "--efficiency-baseline-report",
        type=Path,
        default=ROOT / "Reports" / "STAGE_I_PROMPT_COMPACTION_REPORT.json",
    )
    return command


def request_policy(case: BenchmarkCase) -> OpenTargetRequestPolicy:
    if (
        case.required_hardness is None
        or case.maximum_route_atoms is None
        or case.maximum_dependencies is None
    ):
        raise ValueError(f"case {case.id} has incomplete Stage-I target policy")
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


def validate_suite(suite: Any) -> tuple[BenchmarkCase, ...]:
    if suite.id == STAGE_I_SUITE_ID:
        return validate_stage_i_expansion_suite(suite)
    if suite.id == FRONTIER_EFFICIENCY_SUITE_ID:
        return validate_frontier_efficiency_suite(suite)
    raise ValueError(f"unsupported expansion suite: {suite.id}")


def _prompt_oracle_errors(prompts: Sequence[str]) -> tuple[str, ...]:
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
                f"turn {turn}: Stage-I prompt contains oracle fields: "
                + ", ".join(leaked)
            )
    return tuple(dict.fromkeys(errors))


def _artifact_case(
    case: BenchmarkCase,
    observation: LeanInputObservation,
    result: ObservedInputPlannerResult,
) -> OpenTargetArtifactCase:
    if result.plan is None or result.lean_term is None:
        raise ValueError(f"case {case.id} has no accepted Stage-I plan")
    evidence = result.plan.target_evidence
    return OpenTargetArtifactCase(
        case_id=case.id,
        input_module=case.module,
        source_declaration=result.plan.source_declaration,
        predicate_declaration=(
            case.effective_input_declaration
            if observation.input_kind == "predicate"
            else None
        ),
        target_declaration=result.plan.target_declaration or "",
        lean_term=result.lean_term,
        required_hardness=case.required_hardness or "",
        target_evidence_kind=str(evidence.get("evidence_kind") or ""),
        target_evidence_lean_term=str(evidence.get("evidence_lean_term") or ""),
    )


def _route_metrics(
    case: BenchmarkCase,
    result: ObservedInputPlannerResult,
    reduction_catalog: Any,
) -> dict[str, Any]:
    by_declaration = {entry.declaration: entry for entry in reduction_catalog.entries}
    roles = Counter(
        by_declaration[declaration].component_role
        for declaration in result.reduction_declarations
        if declaration in by_declaration
    )
    endpoint_nodes: list[str] = []
    if result.problem_match is not None:
        endpoint_nodes.append(result.problem_match.route_source_node_id)
    for declaration in result.reduction_declarations:
        entry = by_declaration.get(declaration)
        if entry is not None:
            endpoint_nodes.append(entry.target_node_id)
    if result.selected_connection is not None:
        roles[result.selected_connection.component_role] += 1
    atom_count = len(result.reduction_declarations) + (
        1 if result.selected_connection is not None else 0
    )
    simple = len(endpoint_nodes) == len(set(endpoint_nodes))
    return {
        "selected_route_atom_count": atom_count,
        "selected_route_within_public_range": bool(
            case.minimum_route_atoms
            <= atom_count
            <= int(case.maximum_route_atoms or 0)
        ),
        "selected_path_is_simple": simple,
        "selected_component_role_counts": dict(sorted(roles.items())),
        "selected_shared_gadget_count": roles.get("sharedGadget", 0),
    }


def _stage_i_row(
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
            "requires_model_call": bool(observation.supported),
            "prompt_oracle_errors": list(_prompt_oracle_errors(result.model_prompts)),
            "compact_retrieved_view_all_rounds": bool(round_records)
            and all(
                record.get("retrieved_view_mode")
                == "authorization_complete_compact"
                for record in round_records
            ),
            "compact_retrieved_view_errors": [
                str(error)
                for record in round_records
                for error in (
                    record.get("compact_view_errors")
                    if isinstance(record.get("compact_view_errors"), list)
                    else ["round has no compact-view audit"]
                )
            ],
            "frontier_interactions": analyze_frontier_interactions(
                prompts=result.model_prompts,
                responses=result.model_responses,
            ),
            "maximum_prompt_characters": max(
                (int(record.get("prompt_characters") or 0) for record in round_records),
                default=0,
            ),
            "maximum_retrieved_characters": max(
                (
                    int(record.get("retrieved_characters") or 0)
                    for record in round_records
                ),
                default=0,
            ),
            **_route_metrics(case, result, reduction_catalog),
        }
    )
    return row


def _routing_rule_audit(cases: tuple[BenchmarkCase, ...]) -> dict[str, Any]:
    paths = (
        ROOT / "agent" / "hardness" / "input_observation.py",
        ROOT / "agent" / "hardness" / "problem_catalog.py",
        ROOT / "agent" / "hardness" / "input_planner.py",
        ROOT / "agent" / "hardness" / "open_target_planner.py",
        ROOT / "agent" / "hardness" / "open_target_simulation.py",
        ROOT / "agent" / "hardness" / "frontier_guidance.py",
        ROOT / "agent" / "hardness" / "transported_hardness_catalog.py",
        ROOT / "agent" / "hardness" / "artifact.py",
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
        source = path.read_text(encoding="utf-8")
        for marker in markers:
            if marker in source:
                evidence.append({"path": str(path.relative_to(ROOT)), "marker": marker})
    system_prompt_markers = [
        marker for marker in markers if marker in OPEN_TARGET_SYSTEM_PROMPT
    ]
    return {
        "audited_files": [str(path.relative_to(ROOT)) for path in paths],
        "benchmark_marker_count": len(markers),
        "python_family_specific_rule_count": len(evidence),
        "system_prompt_family_specific_rule_count": len(system_prompt_markers),
        "evidence": evidence,
        "system_prompt_evidence": system_prompt_markers,
    }


def _contract_errors(
    rows: list[Mapping[str, Any]],
    cases: tuple[BenchmarkCase, ...],
    *,
    lean_process_count: int,
    lean_ok: bool,
    lean_started_after_all_model_tasks: bool,
    model_task_count_at_lean_start: int,
    artifact_sha256: str | None,
    accepted_positive_case_count: int,
    assert_standard_axioms_count: int,
    predicate_grounding_count: int,
    target_hardness_count: int,
    routing_rule_count: int,
    prompt_rule_count: int,
) -> tuple[str, ...]:
    errors: list[str] = []
    by_case = {case.id: case for case in cases}
    if len(rows) != 8:
        errors.append("Stage I report must contain exactly eight cases")
    positives = [row for row in rows if row.get("expected_status") == "VERIFIED"]
    negatives = [row for row in rows if row.get("expected_status") == "BLOCKED"]
    if len(positives) != 4 or len(negatives) != 4:
        errors.append("Stage I report must contain four positives and four negatives")
    for row in rows:
        label = str(row.get("id") or "<missing-case-id>")
        case = by_case.get(label)
        if row.get("protocol_matches_expected") is not True:
            errors.append(f"{label}: protocol outcome differs from Expected")
        if row.get("replayed_from_resume") is not False:
            errors.append(f"{label}: a prior model answer was replayed")
        if row.get("prompt_oracle_errors") != []:
            errors.append(f"{label}: prompt contains oracle data")
        if row.get("compact_retrieved_view_all_rounds") is not True:
            errors.append(f"{label}: not every prompt used the compact retrieved view")
        if row.get("compact_retrieved_view_errors") != []:
            errors.append(f"{label}: compact retrieved view failed its field audit")
        calls = row.get("external_api_calls_this_run")
        if not isinstance(calls, int) or isinstance(calls, bool) or calls <= 0:
            errors.append(f"{label}: no fresh DeepSeek call was recorded")
        elif row.get("http_ok_count_this_run") != calls:
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
        if row.get("expected_status") == "VERIFIED":
            if row.get("final_status") != "VERIFIED":
                errors.append(f"{label}: positive case did not pass final Lean")
            if row.get("model_term_changed_by_agent") is not False:
                errors.append(f"{label}: model Lean term was rewritten")
            if row.get("selected_target_evidence_kind") != "transported_native_hardness":
                errors.append(f"{label}: target did not use transported native hardness")
            if row.get("selected_route_within_public_range") is not True:
                errors.append(f"{label}: selected route is outside the public atom range")
            if row.get("selected_path_is_simple") is not True:
                errors.append(f"{label}: selected route is not simple")
            if not isinstance(row.get("selected_shared_gadget_count"), int) or int(
                row.get("selected_shared_gadget_count") or 0
            ) < 1:
                errors.append(f"{label}: selected route reused no shared gadget")
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
            required_targets = int(
                case.coverage.get("minimum_policy_allowed_target_count", 0)
                if case is not None
                else 0
            )
            metrics = row.get("candidate_metrics")
            visible_targets = (
                int(metrics.get("unique_policy_route_allowed_targets", 0))
                if isinstance(metrics, Mapping)
                else 0
            )
            if visible_targets < required_targets:
                errors.append(f"{label}: target ambiguity coverage is below contract")
            if row.get("input_kind") == "predicate":
                match = row.get("problem_match")
                if not isinstance(match, Mapping) or match.get(
                    "accepts_exact_defeq"
                ) is not True:
                    errors.append(f"{label}: predicate grounding lacks Lean defeq evidence")
        else:
            if row.get("final_status") != "BLOCKED":
                errors.append(f"{label}: negative case was not correctly blocked")
            if row.get("final_failure_code") != row.get("expected_failure_code"):
                errors.append(f"{label}: wrong stable failure code")
            metrics = row.get("candidate_metrics")
            if label == "stage-i-no-eligible-transport-dependency-limit":
                if not isinstance(metrics, Mapping) or int(
                    metrics.get("unique_eligible_target_evidences", -1)
                ) != 0:
                    errors.append(f"{label}: dependency limit left eligible evidence")
            if label in {
                "stage-i-forward-route-absent",
                "stage-i-reverse-only-hard-target",
            }:
                if not isinstance(metrics, Mapping) or int(
                    metrics.get("unique_eligible_target_evidences", 0)
                ) <= 0:
                    errors.append(f"{label}: no eligible evidence was exposed")
                if isinstance(metrics, Mapping) and int(
                    metrics.get("unique_policy_route_allowed_targets", 0)
                ) != 0:
                    errors.append(f"{label}: a policy-allowed forward route remained")
            if label == "stage-i-reverse-only-hard-target":
                if not isinstance(metrics, Mapping) or int(
                    metrics.get("unique_reverse_route_targets", 0)
                ) <= 0:
                    errors.append(f"{label}: reverse route was not observed")
    if lean_process_count != 1 or not lean_ok:
        errors.append("Stage I must pass exactly one final Lean process")
    if not lean_started_after_all_model_tasks or model_task_count_at_lean_start != 8:
        errors.append("final Lean started before all Stage-I model tasks completed")
    if not isinstance(artifact_sha256, str) or len(artifact_sha256) != 64:
        errors.append("combined Stage-I artifact SHA-256 is missing")
    if accepted_positive_case_count != 4:
        errors.append("combined Stage-I artifact does not contain all positives")
    if assert_standard_axioms_count != 1:
        errors.append("combined Stage-I artifact must contain one axiom gate")
    if predicate_grounding_count != 2:
        errors.append("combined Stage-I artifact must contain two predicate groundings")
    if target_hardness_count != 4:
        errors.append("combined Stage-I artifact must contain four hardness proofs")
    if routing_rule_count != 0:
        errors.append("production routing contains Stage-I benchmark-specific literals")
    if prompt_rule_count != 0:
        errors.append("system prompt contains Stage-I benchmark-specific literals")
    return tuple(errors)


def _efficiency_baseline(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    cases = payload.get("cases")
    if not isinstance(cases, list) or len(cases) != 8:
        raise ValueError("efficiency baseline must contain the canonical eight cases")
    return {
        "path": str(path.resolve()),
        "sha256": sha256_file(path.resolve()),
        "status": payload.get("status"),
        "registry_fingerprint": (
            payload.get("catalogs", {}).get("registry_fingerprint")
            if isinstance(payload.get("catalogs"), Mapping)
            else None
        ),
        "model_turn_count": sum(int(row.get("model_turn_count", 0)) for row in cases),
        "reduction_search_action_count": sum(
            int(row.get("query_action_counts", {}).get("search_reductions", 0))
            for row in cases
            if isinstance(row, Mapping)
            and isinstance(row.get("query_action_counts"), Mapping)
        ),
        "protocol_feedback_count": sum(
            int(row.get("query_action_counts", {}).get("protocol_feedback", 0))
            for row in cases
            if isinstance(row, Mapping)
            and isinstance(row.get("query_action_counts"), Mapping)
        ),
    }


def _frontier_contract_errors(
    rows: list[Mapping[str, Any]],
    cases: tuple[BenchmarkCase, ...],
    *,
    baseline: Mapping[str, Any],
    registry_fingerprint: str,
) -> tuple[str, ...]:
    errors: list[str] = []
    by_case = {case.id: case for case in cases}
    if baseline.get("status") != "VERIFIED":
        errors.append("Stage-J efficiency baseline is not a VERIFIED canonical report")
    if baseline.get("registry_fingerprint") != registry_fingerprint:
        errors.append("Stage-J efficiency baseline uses a different registry fingerprint")
    total_turns = sum(int(row.get("model_turn_count", 0)) for row in rows)
    reduction_searches = sum(
        int(row.get("query_action_counts", {}).get("search_reductions", 0))
        for row in rows
        if isinstance(row.get("query_action_counts"), Mapping)
    )
    protocol_feedback = sum(
        int(row.get("query_action_counts", {}).get("protocol_feedback", 0))
        for row in rows
        if isinstance(row.get("query_action_counts"), Mapping)
    )
    if total_turns >= int(baseline.get("model_turn_count", 0)):
        errors.append("Stage-J did not reduce total model turns below the matched baseline")
    if reduction_searches >= int(baseline.get("reduction_search_action_count", 0)):
        errors.append("Stage-J did not reduce reduction-search actions below baseline")
    if protocol_feedback >= int(baseline.get("protocol_feedback_count", 0)):
        errors.append("Stage-J did not reduce protocol feedback below baseline")

    total_terminal_ignored = 0
    total_repeated_searches = 0
    for row in rows:
        label = str(row.get("id") or "<missing-case-id>")
        case = by_case.get(label)
        interactions = row.get("frontier_interactions")
        if not isinstance(interactions, Mapping):
            errors.append(f"{label}: frontier interaction metrics are missing")
            continue
        if int(interactions.get("frontier_guidance_error_count", -1)) != 0:
            errors.append(f"{label}: frontier guidance failed its no-oracle audit")
        rounds = row.get("model_rounds")
        if not isinstance(rounds, list) or not rounds:
            errors.append(f"{label}: model round records are missing")
        else:
            if any(record.get("frontier_guidance_present") is not True for record in rounds):
                errors.append(f"{label}: a known-hardness prompt omitted frontier guidance")
            if any(record.get("frontier_guidance_errors") != [] for record in rounds):
                errors.append(f"{label}: a prompt-level frontier audit failed")
        terminal_counts = interactions.get("terminal_guidance_counts")
        terminal_counts = terminal_counts if isinstance(terminal_counts, Mapping) else {}
        if row.get("expected_status") == "VERIFIED":
            if int(
                interactions.get("frontier_suggestion_followed_round_count", 0)
            ) < 1:
                errors.append(f"{label}: positive case never followed frontier guidance")
            if int(terminal_counts.get("finish_now", 0)) < 1:
                errors.append(f"{label}: positive case never received finish_now")
        else:
            if int(terminal_counts.get("stop_now", 0)) < 1:
                errors.append(f"{label}: negative case never received stop_now")
        total_terminal_ignored += int(
            interactions.get("terminal_guidance_ignored_count", 0)
        )
        total_repeated_searches += int(
            interactions.get("repeated_reduction_search_count", 0)
        )
        if case is not None and int(row.get("model_turn_count", 0)) > int(
            case.resources.get("max_model_calls", 0)
        ):
            errors.append(f"{label}: exceeded the Stage-J per-case model-turn cap")
    if total_terminal_ignored > 2:
        errors.append("Stage-J ignored terminal guidance more than twice")
    if total_repeated_searches > 1:
        errors.append("Stage-J repeated more than one identical reduction search")
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
    run_started_monotonic = time.monotonic()
    active_config: DeepSeekConfig | None = None
    frontier_mode = False
    parallel_contract = args.minimum_observed_parallelism > 1
    efficiency_baseline: dict[str, Any] | None = None
    report: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "run_label": args.run_label,
        "started_at": utc_now(),
        "status": "RUNNING",
        "runner": {
            "resume_supported": False,
            "replay_supported": False,
            "fresh_output_required": True,
            "case_execution_model": "bounded_case_thread_pool",
            "configured_jobs": args.jobs,
            "maximum_allowed_jobs": MAX_CASE_JOBS,
            "minimum_observed_parallelism": args.minimum_observed_parallelism,
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
        cases = validate_suite(suite)
        frontier_mode = suite.id == FRONTIER_EFFICIENCY_SUITE_ID
        report["schema_version"] = (
            PARALLEL_SCHEMA_VERSION
            if frontier_mode and parallel_contract
            else (FRONTIER_SCHEMA_VERSION if frontier_mode else SCHEMA_VERSION)
        )
        if frontier_mode:
            efficiency_baseline = _efficiency_baseline(
                args.efficiency_baseline_report.resolve()
            )
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
        snapshot_summary = json.loads(
            (args.snapshots_root / "snapshot-summary.json").read_text(encoding="utf-8")
        )

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
        return finish("FAILED", exit_code=1, error=f"Stage I preflight failed: {error}")

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
                "work_package": (
                    "stage_k_parallel_case_execution"
                    if parallel_contract
                    else (
                        "stage_j_frontier_efficiency"
                        if frontier_mode
                        else "stage_i_expansion"
                    )
                ),
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
                "snapshot_validation": snapshot_summary.get("validation"),
                "transported_hardness": snapshot_summary.get(
                    "transported_hardness"
                ),
            },
            "observations": {
                "all_loaded_before_http": True,
                "count": len(prepared),
                "ids_by_case": {
                    case.id: observation.observation_id
                    for case, observation, _, _ in prepared
                },
            },
            "efficiency_baseline": efficiency_baseline,
        }
    )
    write_json(report_path, report)

    def execute_case(
        index: int,
        prepared_case: tuple[BenchmarkCase, LeanInputObservation, Path, str],
    ) -> CaseExecutionOutcome:
        case, observation, snapshot, input_sha256 = prepared_case
        result: ObservedInputPlannerResult | None = None
        try:
            print(
                json.dumps(
                    {
                        "phase": "deepseek_stage_i_expansion",
                        "case": case.id,
                        "index": index,
                        "total": len(prepared),
                        "event": "started",
                        "configured_jobs": args.jobs,
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
                client=DeepSeekClient(config),
                maximum_query_rounds=args.query_rounds,
                maximum_model_turns=int(
                    case.resources.get("max_model_calls", 14)
                ),
            )
            model_term = submitted_model_term(result.model_responses)
            round_records = build_round_records(
                case_id=case.id,
                prompts=result.model_prompts,
                responses=result.model_responses,
                output_root=output_root,
                config=config,
            )
            row = _stage_i_row(
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
            if result.plan is not None:
                write_json(plans_root / f"{case.id}.json", result.plan.to_dict())
            artifact = None
            if case.is_positive and result.protocol_accepted:
                artifact = _artifact_case(case, observation, result)
            write_json(transcripts_root / f"{case.id}.json", row)
            return CaseExecutionOutcome(
                index=index,
                case_id=case.id,
                row=row,
                artifact=artifact,
            )
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
                    "requires_model_call": bool(observation.supported),
                    "path_source_declaration": None,
                    "prompt_oracle_errors": list(
                        _prompt_oracle_errors(
                            result.model_prompts if result is not None else ()
                        )
                    ),
                    "selected_route_atom_count": 0,
                    "selected_route_within_public_range": False,
                    "selected_path_is_simple": False,
                    "selected_component_role_counts": {},
                    "selected_shared_gadget_count": 0,
                    "frontier_interactions": (
                        analyze_frontier_interactions(
                            prompts=result.model_prompts,
                            responses=result.model_responses,
                        )
                        if result is not None
                        else None
                    ),
                }
            )
            write_json(transcripts_root / f"{case.id}.json", error_row)
            return CaseExecutionOutcome(
                index=index,
                case_id=case.id,
                row=error_row,
                artifact=None,
            )

    def record_case_progress(
        completed: tuple[CaseExecutionOutcome, ...],
        concurrency_audit: Mapping[str, Any],
    ) -> None:
        completed_rows = [outcome.row for outcome in completed]
        report["cases"] = completed_rows
        report["parallel_execution"] = {
            **dict(concurrency_audit),
            "minimum_observed_parallelism": args.minimum_observed_parallelism,
        }
        report["progress"] = {
            "completed_model_tasks": len(completed_rows),
            "model_api_turns_this_run": sum(
                int(row.get("external_api_calls_this_run") or 0)
                for row in completed_rows
            ),
            "real_http_request_count_this_run": sum(
                int(row.get("http_request_attempts_this_run") or 0)
                for row in completed_rows
            ),
            "usage": aggregate_usage(
                row.get("usage") if isinstance(row.get("usage"), Mapping) else None
                for row in completed_rows
            ),
            "lean_process_count": 0,
            "active_case_task_count": concurrency_audit.get(
                "active_case_task_count", 0
            ),
            "maximum_concurrent_case_tasks": concurrency_audit.get(
                "maximum_concurrent_case_tasks", 0
            ),
        }
        write_json(report_path, report)

    task_inputs = [
        (index, case.id, prepared_case)
        for index, prepared_case in enumerate(prepared, start=1)
        for case in (prepared_case[0],)
    ]
    outcomes, parallel_execution = run_case_tasks(
        task_inputs,
        jobs=args.jobs,
        worker=execute_case,
        on_progress=record_case_progress,
    )
    rows = [outcome.row for outcome in outcomes]
    artifacts = [
        outcome.artifact
        for outcome in outcomes
        if outcome.artifact is not None
    ]
    report["parallel_execution"] = {
        **parallel_execution,
        "minimum_observed_parallelism": args.minimum_observed_parallelism,
    }

    artifact_path = output_root / "StageIExpansionBatch.lean"
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
    source_text = str(artifact_source) if artifact_source is not None else ""
    axiom_count = source_text.count("assert_standard_axioms")
    grounding_count = source_text.count("theorem inputPredicateGrounding")
    target_hardness_count = source_text.count("noncomputable def targetHardness")
    report["artifact"] = {
        "path": str(artifact_path),
        "generated": artifact_source is not None,
        "sha256": lean_execution.get("artifact_sha256"),
        "accepted_positive_case_count": len(artifacts),
        "assert_standard_axioms_count": axiom_count,
        "predicate_grounding_count": grounding_count,
        "target_hardness_count": target_hardness_count,
        "dynamic_targets": [artifact.target_declaration for artifact in artifacts],
        "dynamic_target_evidence_kinds": [
            artifact.target_evidence_kind for artifact in artifacts
        ],
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
            else lean_execution.get("error") or "no accepted Stage-I positive artifact"
        ),
    }
    report["parallel_execution"]["final_lean_started_after_case_tasks"] = bool(
        lean_execution.get("started_after_all_model_tasks", False)
    )

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
                    "The untouched long path, transported native-hardness evidence, "
                    "and any predicate grounding passed the single combined Lean gate."
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
        cases,
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
        target_hardness_count=target_hardness_count,
        routing_rule_count=int(routing_audit["python_family_specific_rule_count"]),
        prompt_rule_count=int(
            routing_audit["system_prompt_family_specific_rule_count"]
        ),
    )
    if frontier_mode:
        assert efficiency_baseline is not None
        errors = (
            *errors,
            *_frontier_contract_errors(
                rows,
                cases,
                baseline=efficiency_baseline,
                registry_fingerprint=problem_catalog.registry_fingerprint,
            ),
        )
    errors = (
        *errors,
        *parallel_execution_errors(
            report["parallel_execution"],
            expected_case_ids=[case.id for case in cases],
            minimum_observed_parallelism=args.minimum_observed_parallelism,
        ),
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
        "selected_shared_gadget_count": sum(
            int(row.get("selected_shared_gadget_count") or 0) for row in rows
        ),
        "reduction_search_action_count": sum(
            int(row.get("query_action_counts", {}).get("search_reductions", 0))
            for row in rows
            if isinstance(row.get("query_action_counts"), Mapping)
        ),
        "protocol_feedback_count": sum(
            int(row.get("query_action_counts", {}).get("protocol_feedback", 0))
            for row in rows
            if isinstance(row.get("query_action_counts"), Mapping)
        ),
        "terminal_guidance_ignored_count": sum(
            int(row.get("frontier_interactions", {}).get(
                "terminal_guidance_ignored_count", 0
            ))
            for row in rows
            if isinstance(row.get("frontier_interactions"), Mapping)
        ),
        "repeated_reduction_search_count": sum(
            int(row.get("frontier_interactions", {}).get(
                "repeated_reduction_search_count", 0
            ))
            for row in rows
            if isinstance(row.get("frontier_interactions"), Mapping)
        ),
        "configured_case_jobs": args.jobs,
        "maximum_concurrent_case_tasks": parallel_execution.get(
            "maximum_concurrent_case_tasks", 0
        ),
        "minimum_observed_parallelism": args.minimum_observed_parallelism,
        "wall_duration_seconds": round(time.monotonic() - run_started_monotonic, 3),
        "contract_errors": list(errors),
        "all_stage_i_thresholds_met": not errors,
        "all_frontier_efficiency_thresholds_met": (
            not errors if frontier_mode else None
        ),
    }
    if not errors:
        return finish("VERIFIED", exit_code=0)
    return finish(
        "FAILED",
        exit_code=1,
        error="Stage I full run failed its report contract: " + "; ".join(errors[:8]),
    )


if __name__ == "__main__":
    raise SystemExit(main())
