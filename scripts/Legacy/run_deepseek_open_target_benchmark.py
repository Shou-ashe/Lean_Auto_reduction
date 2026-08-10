#!/usr/bin/env python3
"""Run the seven-case Stage G open-target suite with real DeepSeek.

Every observation and catalog is loaded from a pre-generated, fingerprint-bound
snapshot before the first HTTP request.  The formal runner has no resume or
replay mode: every case must make a fresh DeepSeek call in this process.  Lean
is not started during planning; all accepted positive paths and their dynamic
target evidence are merged into one artifact and checked by one final process.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import tempfile
from collections import Counter, defaultdict
from collections.abc import Callable, Iterable, Mapping, Sequence
from dataclasses import replace
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.artifact import (  # noqa: E402
    OpenTargetArtifactCase,
    build_open_target_batch_artifact_source,
)
from agent.hardness.benchmark import (  # noqa: E402
    BenchmarkCase,
    BenchmarkManifestError,
    load_benchmark_suite,
)
from agent.hardness.connection_catalog import (  # noqa: E402
    ConnectionCatalogError,
    build_reduction_catalog,
    load_connection_catalog_snapshot,
)
from agent.hardness.hardness_target_catalog import (  # noqa: E402
    HardnessTargetCatalogError,
    load_hardness_target_catalog_snapshot,
)
from agent.hardness.input_grounding import observation_snapshot_path  # noqa: E402
from agent.hardness.input_observation import (  # noqa: E402
    InputObservationError,
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
    DeepSeekClient,
    DeepSeekConfig,
    ModelResponse,
    extract_json_object,
)
from agent.hardness.models import TypedCatalog  # noqa: E402
from agent.hardness.open_target import (  # noqa: E402
    EXPECTED_CASE_POLICIES,
    EXPECTED_NEGATIVE_FAILURES,
    OPEN_TARGET_CASE_COUNT,
    OPEN_TARGET_NEGATIVE_COUNT,
    OPEN_TARGET_POSITIVE_COUNT,
    audit_open_target_prompt,
    find_open_target_prompt_forbidden_keys,
    validate_open_target_suite,
)
from agent.hardness.open_target_planner import (  # noqa: E402
    MAX_OPEN_TARGET_QUERY_ROUNDS,
    OPEN_TARGET_SYSTEM_PROMPT,
    OpenTargetRequestPolicy,
    generate_lean_path_to_open_target,
)
from agent.hardness.problem_catalog import (  # noqa: E402
    ProblemCatalogError,
    load_problem_catalog_snapshot,
)
from agent.hardness.retrieved_view import retrieved_prompt_metrics  # noqa: E402


SCHEMA_VERSION = "hardness_open_target_deepseek_report_v1"
REQUIRED_USAGE_FIELDS = (
    "prompt_tokens",
    "completion_tokens",
    "total_tokens",
    "prompt_cache_hit_tokens",
    "prompt_cache_miss_tokens",
)
POSITIVE_USAGE_FIELDS = frozenset(
    {"prompt_tokens", "completion_tokens", "total_tokens"}
)
QUERY_ACTIONS = frozenset(
    {
        "inspect_architecture",
        "search_problems",
        "search_connections",
        "search_hardness_targets",
        "search_reductions",
    }
)
REVERSE_ONLY_CASE_ID = "open-target-exact-cover-reverse-only"
NO_ELIGIBLE_FAILURE_CODE = "no_eligible_hardness_target"
NO_ROUTE_FAILURE_CODE = "eligible_target_has_no_existing_route"


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def preflight_canonical_report(path: Path) -> None:
    """Prove the canonical destination is writable before any paid HTTP call."""

    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() and not path.is_file():
        raise ValueError(f"canonical report is not a regular file: {path}")
    descriptor, probe_name = tempfile.mkstemp(
        prefix=f".{path.name}.preflight-",
        suffix=".tmp",
        dir=path.parent,
    )
    os.close(descriptor)
    Path(probe_name).unlink()


def atomic_write_json(path: Path, value: Any) -> None:
    """Publish JSON atomically using a same-directory temporary file."""

    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.",
        suffix=".tmp",
        dir=path.parent,
    )
    temporary_path = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as destination:
            json.dump(
                value,
                destination,
                ensure_ascii=False,
                indent=2,
                sort_keys=True,
            )
            destination.write("\n")
            destination.flush()
            os.fsync(destination.fileno())
        os.replace(temporary_path, path)
    except Exception:
        try:
            temporary_path.unlink(missing_ok=True)
        finally:
            raise


def finalize_report(
    *,
    report: dict[str, Any],
    report_path: Path,
    canonical_report: Path,
    status: str,
    exit_code: int,
    run_label: str,
    error: str | None = None,
    redactor: Callable[[str], str] = lambda value: value,
    atomic_publisher: Callable[[Path, Any], None] = atomic_write_json,
    emit: Callable[[str], Any] = print,
) -> int:
    """Finish locally, then atomically publish only a verified report."""

    safe_error = redactor(error) if error is not None else None
    report["status"] = status
    report["finished_at"] = utc_now()
    if safe_error is not None:
        report["error"] = safe_error
    elif status == "VERIFIED":
        report.pop("error", None)
    report["canonical_publish"] = {
        "path": str(canonical_report),
        "attempted": status == "VERIFIED",
        "published": status == "VERIFIED",
        "atomic_same_directory_replace": True,
    }
    write_json(report_path, report)

    canonical_published = False
    if status == "VERIFIED":
        try:
            atomic_publisher(canonical_report, report)
            canonical_published = True
        except Exception as publish_error:
            safe_publish_error = redactor(
                "canonical report publish failed: "
                f"{type(publish_error).__name__}: {publish_error}"
            )
            status = "FAILED"
            exit_code = 1
            report["status"] = status
            report["finished_at"] = utc_now()
            report["error"] = safe_publish_error
            report["canonical_publish"] = {
                "path": str(canonical_report),
                "attempted": True,
                "published": False,
                "atomic_same_directory_replace": True,
                "error": safe_publish_error,
            }
            write_json(report_path, report)

    emit(
        json.dumps(
            {
                "status": status,
                "run_label": run_label,
                "report": str(report_path),
                "canonical_report": str(canonical_report),
                "canonical_report_published": canonical_published,
                "summary": report.get("summary"),
                "error": report.get("error"),
            },
            ensure_ascii=False,
            sort_keys=True,
        )
    )
    return exit_code


def aggregate_usage(
    usages: Iterable[Mapping[str, Any] | None],
) -> dict[str, int]:
    totals: dict[str, int] = defaultdict(int)
    for usage in usages:
        if not isinstance(usage, Mapping):
            continue
        for key, value in usage.items():
            if isinstance(value, int) and not isinstance(value, bool):
                totals[str(key)] += value
    return dict(sorted(totals.items()))


def _valid_integer(value: Any, *, positive: bool = False) -> bool:
    return (
        isinstance(value, int)
        and not isinstance(value, bool)
        and value >= (1 if positive else 0)
    )


def usage_contract_errors(
    usage: Mapping[str, Any] | None,
    *,
    label: str,
) -> tuple[str, ...]:
    if not isinstance(usage, Mapping):
        return (f"{label}: usage is missing",)
    errors = []
    for field in REQUIRED_USAGE_FIELDS:
        if not _valid_integer(usage.get(field), positive=field in POSITIVE_USAGE_FIELDS):
            errors.append(f"{label}: usage.{field} is missing or invalid")
    return tuple(errors)


def prepare_fresh_output_root(path: Path) -> None:
    """Create an empty output root and reject all implicit reuse."""

    if path.exists():
        if not path.is_dir():
            raise ValueError(f"output root is not a directory: {path}")
        if any(path.iterdir()):
            raise ValueError(
                "output root is not empty; the formal Stage G run cannot resume, "
                "replay, or reuse prior model answers"
            )
    path.mkdir(parents=True, exist_ok=True)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description=(
            "Run all seven Stage G open-target cases with fresh real DeepSeek "
            "calls, then run one final Lean process"
        )
    )
    snapshot_root = ROOT / ".reduction-agent" / "stage-g-snapshots"
    command.add_argument(
        "--suite",
        type=Path,
        default=ROOT / "Gate" / "Suites" / "open_target.json",
    )
    command.add_argument(
        "--observations-root",
        type=Path,
        default=snapshot_root / "observations",
    )
    command.add_argument(
        "--problem-catalog",
        type=Path,
        default=snapshot_root / "problem-catalog.json",
    )
    command.add_argument(
        "--connection-catalog",
        type=Path,
        default=snapshot_root / "connection-catalog.json",
    )
    command.add_argument(
        "--target-catalog",
        type=Path,
        default=snapshot_root / "hardness-target-catalog.json",
    )
    command.add_argument("--env-file", type=Path, default=ROOT / ".env")
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "deepseek-open-target-full",
    )
    command.add_argument(
        "--canonical-report",
        type=Path,
        default=ROOT / "Reports" / "OPEN_TARGET_REPORT.json",
    )
    command.add_argument("--run-label", default="stage-g-full-real-deepseek")
    command.add_argument("--lean-timeout", type=int, default=900)
    command.add_argument("--model-timeout", type=int, default=None)
    command.add_argument("--model-max-tokens", type=int, default=4096)
    command.add_argument(
        "--query-rounds",
        type=int,
        default=MAX_OPEN_TARGET_QUERY_ROUNDS,
    )
    return command


def request_policy(case: BenchmarkCase) -> OpenTargetRequestPolicy:
    if case.required_hardness is None:
        raise ValueError(f"case {case.id} has no required hardness policy")
    if case.maximum_route_atoms is None or case.maximum_dependencies is None:
        raise ValueError(f"case {case.id} has incomplete open-target limits")
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


def expected_protocol(
    case: BenchmarkCase,
    result: ObservedInputPlannerResult,
) -> bool:
    if case.is_positive:
        return bool(
            result.protocol_accepted
            and result.plan is not None
            and result.lean_term is not None
        )
    return bool(
        result.failure_code == case.expected.final_failure_code
        and result.plan is None
        and result.lean_term is None
    )


def normalize_model_action(payload: dict[str, Any]) -> dict[str, Any]:
    if isinstance(payload.get("action"), str):
        return payload
    candidates: list[dict[str, Any]] = []
    for action in (
        "inspect_architecture",
        "search_problems",
        "search_connections",
        "search_hardness_targets",
        "search_reductions",
        "finish",
        "stop",
    ):
        nested = payload.get(action)
        if isinstance(nested, dict):
            candidate = dict(nested)
            candidate.setdefault("action", action)
            candidates.append(candidate)
    return candidates[0] if len(candidates) == 1 else payload


def submitted_model_term(responses: Iterable[ModelResponse]) -> str | None:
    """Return the exact raw finish field, including its surrounding whitespace."""

    for response in reversed(tuple(responses)):
        payload = extract_json_object(response.content)
        if payload is None:
            continue
        normalized = normalize_model_action(payload)
        if normalized.get("action") == "finish" and isinstance(
            normalized.get("lean_term"), str
        ):
            return str(normalized["lean_term"])
    return None


def model_term_changed_by_agent(
    model_term: str | None,
    accepted_term: str | None,
) -> bool:
    """Require byte-for-byte model term preservation, including whitespace."""

    return bool(
        accepted_term is not None
        and (model_term is None or model_term != accepted_term)
    )


def completed_action_counts(
    trace: Sequence[Mapping[str, Any]],
) -> dict[str, int]:
    counts = Counter(
        str(row.get("action"))
        for row in trace
        if row.get("status") != "started" and isinstance(row.get("action"), str)
    )
    return dict(sorted(counts.items()))


def query_round_count(trace: Sequence[Mapping[str, Any]]) -> int:
    return sum(
        row.get("status") == "started" and row.get("action") in QUERY_ACTIONS
        for row in trace
    )


def open_target_candidate_metrics(
    trace: Sequence[Mapping[str, Any]],
) -> dict[str, int]:
    """Count bounded candidates and public reachability facts returned to the model."""

    problem_ids: set[str] = set()
    connection_ids: set[str] = set()
    reduction_declarations: set[str] = set()
    target_ids: set[str] = set()
    evidence_ids: set[str] = set()
    eligible_evidence_ids: set[str] = set()
    reachable_target_ids: set[str] = set()
    reachable_eligible_target_ids: set[str] = set()
    policy_route_allowed_target_ids: set[str] = set()
    policy_route_metric_observed = False
    within_limit_target_ids: set[str] = set()
    reverse_route_target_ids: set[str] = set()
    returned = Counter()
    for row in trace:
        action = row.get("action")
        results = row.get("results")
        if not isinstance(results, list):
            continue
        if action == "search_problems":
            returned["problem_results"] += len(results)
            for item in results:
                if isinstance(item, Mapping):
                    identifier = item.get("entry_id") or item.get("declaration")
                    if isinstance(identifier, str):
                        problem_ids.add(identifier)
        elif action == "search_connections":
            returned["connection_results"] += len(results)
            for item in results:
                if isinstance(item, Mapping) and isinstance(item.get("entry_id"), str):
                    connection_ids.add(str(item["entry_id"]))
        elif action == "search_reductions":
            returned["reduction_results"] += len(results)
            for item in results:
                if isinstance(item, Mapping) and isinstance(
                    item.get("declaration"), str
                ):
                    reduction_declarations.add(str(item["declaration"]))
        elif action == "search_hardness_targets":
            returned["hardness_target_results"] += len(results)
            for item in results:
                if not isinstance(item, Mapping):
                    continue
                target_id = item.get("target_entry_id")
                if not isinstance(target_id, str):
                    continue
                target_ids.add(target_id)
                reachable = item.get("reachable_from_input") is True
                within_limit = item.get("within_route_atom_limit") is True
                if reachable:
                    reachable_target_ids.add(target_id)
                if within_limit:
                    within_limit_target_ids.add(target_id)
                if item.get("reverse_route_exists") is True:
                    reverse_route_target_ids.add(target_id)
                if "policy_route_allowed" in item:
                    policy_route_metric_observed = True
                    if item.get("policy_route_allowed") is True:
                        policy_route_allowed_target_ids.add(target_id)
                eligible_on_target = False
                evidences = item.get("evidences")
                if not isinstance(evidences, list):
                    continue
                returned["target_evidence_results"] += len(evidences)
                for evidence in evidences:
                    if not isinstance(evidence, Mapping):
                        continue
                    evidence_id = evidence.get("evidence_id")
                    if isinstance(evidence_id, str):
                        evidence_ids.add(evidence_id)
                        if evidence.get("request_eligible") is True:
                            eligible_evidence_ids.add(evidence_id)
                            eligible_on_target = True
                if reachable and within_limit and eligible_on_target:
                    reachable_eligible_target_ids.add(target_id)
    metrics = {
        **dict(sorted(returned.items())),
        "unique_problem_candidates": len(problem_ids),
        "unique_connection_candidates": len(connection_ids),
        "unique_reduction_candidates": len(reduction_declarations),
        "unique_hardness_target_candidates": len(target_ids),
        "unique_target_evidence_candidates": len(evidence_ids),
        "unique_eligible_target_evidences": len(eligible_evidence_ids),
        "unique_reachable_targets": len(reachable_target_ids),
        "unique_reachable_eligible_targets": len(reachable_eligible_target_ids),
        "unique_targets_within_route_limit": len(within_limit_target_ids),
        "unique_reverse_route_targets": len(reverse_route_target_ids),
    }
    if policy_route_metric_observed:
        metrics["unique_policy_route_allowed_targets"] = len(
            policy_route_allowed_target_ids
        )
    return metrics


def negative_semantic_audit(row: Mapping[str, Any]) -> dict[str, Any]:
    """Independently gate the four public Stage G negative-case semantics."""

    case_id = row.get("id")
    expected_failure = (
        EXPECTED_NEGATIVE_FAILURES.get(case_id)
        if isinstance(case_id, str)
        else None
    )
    if expected_failure is None:
        return {
            "applicable": False,
            "ok": True,
            "errors": [],
            "forward_metric_source": None,
            "forward_metric_fallback_used": False,
        }

    label = case_id
    raw_metrics = row.get("candidate_metrics")
    metrics = raw_metrics if isinstance(raw_metrics, Mapping) else {}
    eligible = metrics.get("unique_eligible_target_evidences")
    policy_allowed = metrics.get("unique_policy_route_allowed_targets")
    reachable_eligible = metrics.get("unique_reachable_eligible_targets")
    reverse = metrics.get("unique_reverse_route_targets")
    if _valid_integer(policy_allowed):
        forward_count = int(policy_allowed)
        forward_source = "unique_policy_route_allowed_targets"
        fallback_used = False
    else:
        forward_count = (
            int(reachable_eligible)
            if _valid_integer(reachable_eligible)
            else None
        )
        forward_source = "unique_reachable_eligible_targets"
        fallback_used = True

    errors: list[str] = []
    if not _valid_integer(eligible):
        errors.append(f"{label}: eligible target evidence metric is missing")
    elif expected_failure == NO_ELIGIBLE_FAILURE_CODE and int(eligible) != 0:
        errors.append(
            f"{label}: no-eligible negative returned eligible target evidence"
        )
    elif expected_failure == NO_ROUTE_FAILURE_CODE and int(eligible) <= 0:
        errors.append(
            f"{label}: no-route negative did not expose eligible target evidence"
        )

    if expected_failure == NO_ROUTE_FAILURE_CODE:
        if forward_count is None:
            errors.append(f"{label}: allowed forward-route metric is missing")
        elif forward_count != 0:
            errors.append(
                f"{label}: no-route negative still has a policy-allowed forward target"
            )
    if case_id == REVERSE_ONLY_CASE_ID:
        if not _valid_integer(reverse, positive=True):
            errors.append(
                f"{label}: reverse-only negative has no recorded reverse route"
            )

    return {
        "applicable": True,
        "expected_failure_code": expected_failure,
        "eligible_target_evidence_count": (
            int(eligible) if _valid_integer(eligible) else None
        ),
        "policy_allowed_forward_target_count": forward_count,
        "forward_metric_source": forward_source,
        "forward_metric_fallback_used": fallback_used,
        "reverse_route_target_count": (
            int(reverse) if _valid_integer(reverse) else None
        ),
        "ok": not errors,
        "errors": errors,
    }


def _retrieved_facts(
    trace: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    problems: set[str] = set()
    connections: set[str] = set()
    reductions: set[str] = set()
    targets: dict[str, Mapping[str, Any]] = {}
    evidences: dict[tuple[str, str], Mapping[str, Any]] = {}
    for row in trace:
        action = row.get("action")
        results = row.get("results")
        if not isinstance(results, list):
            continue
        for item in results:
            if not isinstance(item, Mapping):
                continue
            if action == "search_problems" and isinstance(
                item.get("declaration"), str
            ):
                problems.add(str(item["declaration"]))
            elif action == "search_connections" and isinstance(
                item.get("entry_id"), str
            ):
                connections.add(str(item["entry_id"]))
            elif action == "search_reductions" and isinstance(
                item.get("declaration"), str
            ):
                reductions.add(str(item["declaration"]))
            elif action == "search_hardness_targets" and isinstance(
                item.get("target_entry_id"), str
            ):
                target_id = str(item["target_entry_id"])
                targets[target_id] = item
                raw_evidences = item.get("evidences")
                if isinstance(raw_evidences, list):
                    for evidence in raw_evidences:
                        if isinstance(evidence, Mapping) and isinstance(
                            evidence.get("evidence_id"), str
                        ):
                            evidences[(target_id, str(evidence["evidence_id"]))] = evidence
    return {
        "problems": problems,
        "connections": connections,
        "reductions": reductions,
        "targets": targets,
        "evidences": evidences,
    }


def selected_fact_audit(
    case: BenchmarkCase,
    result: ObservedInputPlannerResult,
) -> dict[str, Any]:
    """Independently re-check every selected fact against this session's trace."""

    retrieved = _retrieved_facts(result.query_trace)
    if result.plan is None:
        return {
            "selected_target_from_search": None,
            "selected_evidence_from_search": None,
            "selected_evidence_policy_satisfied": None,
            "matched_problem_from_search": None,
            "selected_connection_from_search": None,
            "route_declarations_all_retrieved": None,
            "all_selected_facts_retrieved": None,
            "selected_target_reachability": None,
        }
    evidence = dict(result.plan.target_evidence)
    target_id = evidence.get("target_entry_id")
    evidence_id = evidence.get("evidence_id")
    target = retrieved["targets"].get(target_id)
    searched_evidence = retrieved["evidences"].get((target_id, evidence_id))
    selected_target_from_search = bool(
        target is not None
        and target.get("target_declaration") == result.plan.target_declaration
    )
    selected_evidence_from_search = bool(searched_evidence is not None)
    required_hardness = case.required_hardness or ""
    satisfied_policies = evidence.get("satisfied_policies")
    provenance = evidence.get("provenance_declarations")
    selected_evidence_policy_satisfied = bool(
        evidence.get("policy_satisfied") is True
        and evidence.get("requested_hardness") == required_hardness
        and evidence.get("evidence_kind") in case.allowed_target_evidence
        and isinstance(satisfied_policies, list)
        and required_hardness in satisfied_policies
        and isinstance(provenance, list)
        and case.maximum_dependencies is not None
        and len(set(provenance)) <= case.maximum_dependencies
        and searched_evidence is not None
        and searched_evidence.get("request_eligible") is True
    )
    matched_problem = (
        result.problem_match.candidate_declaration
        if result.problem_match is not None
        else None
    )
    matched_problem_from_search = bool(
        isinstance(matched_problem, str) and matched_problem in retrieved["problems"]
    )
    selected_connection_from_search = bool(
        result.selected_connection is None
        or result.selected_connection.entry_id in retrieved["connections"]
    )
    route_declarations_all_retrieved = set(
        result.reduction_declarations
    ).issubset(retrieved["reductions"])
    all_selected_facts_retrieved = bool(
        selected_target_from_search
        and selected_evidence_from_search
        and matched_problem_from_search
        and selected_connection_from_search
        and route_declarations_all_retrieved
    )
    reachability = None
    if target is not None:
        reachability = {
            "reachable_from_input": target.get("reachable_from_input"),
            "shortest_route_length_from_input": target.get(
                "shortest_route_length_from_input"
            ),
            "within_route_atom_limit": target.get("within_route_atom_limit"),
            "reverse_route_exists": target.get("reverse_route_exists"),
        }
    return {
        "selected_target_from_search": selected_target_from_search,
        "selected_evidence_from_search": selected_evidence_from_search,
        "selected_evidence_policy_satisfied": selected_evidence_policy_satisfied,
        "matched_problem_from_search": matched_problem_from_search,
        "selected_connection_from_search": selected_connection_from_search,
        "route_declarations_all_retrieved": route_declarations_all_retrieved,
        "all_selected_facts_retrieved": all_selected_facts_retrieved,
        "selected_target_reachability": reachability,
    }


def prompt_oracle_errors(prompts: Sequence[str]) -> tuple[str, ...]:
    errors: list[str] = []
    for round_number, prompt in enumerate(prompts, start=1):
        try:
            payload = json.loads(prompt)
            if not isinstance(payload, dict):
                raise ValueError("prompt is not a JSON object")
            leaked = find_open_target_prompt_forbidden_keys(payload)
            if leaked:
                errors.append(
                    f"round {round_number}: forbidden prompt keys: {', '.join(leaked)}"
                )
            audit_open_target_prompt(payload)
        except (json.JSONDecodeError, ValueError) as error:
            message = f"round {round_number}: {error}"
            if message not in errors:
                errors.append(message)
    return tuple(errors)


def build_round_records(
    *,
    case_id: str,
    prompts: Sequence[str],
    responses: Sequence[ModelResponse],
    output_root: Path,
    config: DeepSeekConfig,
) -> list[dict[str, Any]]:
    if len(prompts) != len(responses):
        raise ValueError("model prompt and response counts differ")
    call_dir = output_root / "calls" / case_id
    records: list[dict[str, Any]] = []
    for number, (prompt, response) in enumerate(
        zip(prompts, responses, strict=True), start=1
    ):
        prompt_payload = json.loads(prompt)
        if not isinstance(prompt_payload, dict):
            raise ValueError("model prompt is not a JSON object")
        audit_open_target_prompt(prompt_payload)
        prompt_metrics = retrieved_prompt_metrics(prompt_payload)
        usage_errors = usage_contract_errors(
            response.usage,
            label=f"{case_id}.round-{number}",
        )
        prompt_path = call_dir / f"round-{number:02d}-prompt.json"
        response_path = call_dir / f"round-{number:02d}-response.json"
        write_json(
            prompt_path,
            {
                "system": OPEN_TARGET_SYSTEM_PROMPT,
                "system_sha256": sha256_text(OPEN_TARGET_SYSTEM_PROMPT),
                "prompt": prompt,
                "prompt_sha256": sha256_text(prompt),
                "payload": prompt_payload,
            },
        )
        response_payload = {
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
        }
        write_json(response_path, response_payload)
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
                "prompt_characters": len(prompt),
                **prompt_metrics,
                "system_sha256": sha256_text(OPEN_TARGET_SYSTEM_PROMPT),
                "prompt_sha256": sha256_text(prompt),
                "response_sha256": sha256_text(response.content),
                "response_content": response.content,
                "prompt_file": str(prompt_path),
                "response_file": str(response_path),
                "replayed": False,
            }
        )
    return records


def artifact_case_from_result(
    case: BenchmarkCase,
    result: ObservedInputPlannerResult,
) -> OpenTargetArtifactCase:
    """Build a final artifact row from the model-selected target, never the suite."""

    if result.plan is None or result.lean_term is None:
        raise ValueError(f"case {case.id} has no accepted open-target plan")
    evidence = result.plan.target_evidence
    target = result.plan.target_declaration
    if not isinstance(target, str) or not target:
        raise ValueError(f"case {case.id} plan has no dynamic target")
    return OpenTargetArtifactCase(
        case_id=case.id,
        input_module=case.module,
        source_declaration=case.effective_input_declaration,
        target_declaration=target,
        lean_term=result.lean_term,
        required_hardness=case.required_hardness or "",
        target_evidence_kind=str(evidence.get("evidence_kind") or ""),
        target_evidence_lean_term=str(evidence.get("evidence_lean_term") or ""),
    )


def command_record(command: Any) -> dict[str, Any]:
    return {
        "command": list(command.command),
        "exit_code": command.exit_code,
        "ok": command.ok,
        "timed_out": command.timed_out,
        "duration_seconds": command.duration_seconds,
        "stdout_sha256": sha256_text(command.stdout),
        "stderr_sha256": sha256_text(command.stderr),
        "stdout_tail": command.stdout[-4000:],
        "stderr_tail": command.stderr[-8000:],
    }


def run_final_lean_after_all_model_tasks(
    *,
    artifacts: Sequence[OpenTargetArtifactCase],
    completed_model_task_count: int,
    expected_model_task_count: int,
    artifact_path: Path,
    lean_root: Path,
    timeout_seconds: int,
    command_runner: Callable[..., Any] = run_command,
) -> dict[str, Any]:
    """Gate the only Lean process on completion of every model task."""

    if completed_model_task_count != expected_model_task_count:
        raise ValueError("final Lean cannot start before every model task has finished")
    if not artifacts:
        return {
            "source": None,
            "artifact_sha256": None,
            "process_count": 0,
            "started_after_all_model_tasks": False,
            "model_task_count_at_start": completed_model_task_count,
            "command": None,
        }
    source = build_open_target_batch_artifact_source(artifacts)
    assert_generated_source_is_safe(source)
    artifact_path.write_text(source, encoding="utf-8")
    command = command_runner(
        ["lake", "env", "lean", str(artifact_path.resolve())],
        cwd=lean_root,
        timeout_seconds=timeout_seconds,
        output_limit=128 * 1024,
    )
    return {
        "source": source,
        "artifact_sha256": sha256_text(source),
        "process_count": 1,
        "started_after_all_model_tasks": True,
        "model_task_count_at_start": completed_model_task_count,
        "command": command,
    }


def result_row(
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
    reduction_catalog: TypedCatalog,
    target_catalog_id: str,
) -> dict[str, Any]:
    evidence = dict(result.plan.target_evidence) if result.plan is not None else {}
    audit = selected_fact_audit(case, result)
    usage = aggregate_usage(response.usage for response in result.model_responses)
    prompt_errors = prompt_oracle_errors(result.model_prompts)
    candidate_metrics = open_target_candidate_metrics(result.query_trace)
    negative_audit = negative_semantic_audit(
        {"id": case.id, "candidate_metrics": candidate_metrics}
    )
    return {
        "id": case.id,
        "module": case.module,
        "source_declaration": case.effective_input_declaration,
        "input_observation_id": observation.observation_id,
        "input_observation_snapshot": str(observation_snapshot),
        "input_observation_snapshot_sha256": sha256_file(observation_snapshot),
        "input_source_sha256": input_source_sha256,
        "input_node_id": observation.normalized_problem_node_id,
        "registry_fingerprint": observation.registry_fingerprint,
        "problem_catalog_id": problem_catalog_id,
        "connection_catalog_id": connection_catalog_id,
        "reduction_catalog_id": reduction_catalog.catalog_id,
        "hardness_target_catalog_id": target_catalog_id,
        "required_hardness": case.required_hardness,
        "allowed_target_evidence": list(case.allowed_target_evidence),
        "minimum_route_atoms": case.minimum_route_atoms,
        "maximum_route_atoms": case.maximum_route_atoms,
        "maximum_dependencies": case.maximum_dependencies,
        "allow_reflexive_target": case.allow_reflexive_target,
        "require_simple_path": case.require_simple_path,
        "expected_status": case.expected.final_status,
        "expected_failure_code": case.expected.final_failure_code,
        "protocol_accepted": result.protocol_accepted,
        "protocol_matches_expected": expected_protocol(case, result),
        "failure_code": result.failure_code,
        "explanation": result.explanation,
        "problem_match": (
            result.problem_match.to_dict() if result.problem_match is not None else None
        ),
        "selected_connection": (
            result.selected_connection.to_dict()
            if result.selected_connection is not None
            else None
        ),
        "selected_target_declaration": (
            result.plan.target_declaration if result.plan is not None else None
        ),
        "selected_target_entry_id": evidence.get("target_entry_id"),
        "selected_target_evidence_id": evidence.get("evidence_id"),
        "selected_target_evidence_kind": evidence.get("evidence_kind"),
        "selected_target_evidence_declaration": evidence.get(
            "evidence_declaration"
        ),
        "selected_target_evidence_lean_term": evidence.get("evidence_lean_term"),
        "selected_target_evidence_policies": evidence.get("satisfied_policies"),
        "selected_target_evidence_provenance": evidence.get(
            "provenance_declarations"
        ),
        **audit,
        "selected_reduction_declarations": list(result.reduction_declarations),
        "model_raw_lean_term": model_term,
        "lean_term": result.lean_term,
        "model_term_changed_by_agent": model_term_changed_by_agent(
            model_term, result.lean_term
        ),
        "plan": result.plan.to_dict() if result.plan is not None else None,
        "query_trace": list(result.query_trace),
        "query_action_counts": completed_action_counts(result.query_trace),
        "candidate_metrics": candidate_metrics,
        "negative_semantic_audit": negative_audit,
        "query_round_count": query_round_count(result.query_trace),
        "model_turn_count": len(result.model_responses),
        "external_api_calls_this_run": sum(
            response.called for response in result.model_responses
        ),
        "http_ok_count_this_run": sum(
            response.called and response.ok for response in result.model_responses
        ),
        "http_request_attempts_this_run": sum(
            response.attempts for response in result.model_responses if response.called
        ),
        "duration_seconds_this_run": round(
            sum(response.duration_seconds for response in result.model_responses), 3
        ),
        "usage": usage,
        "usage_contract_errors": list(
            usage_contract_errors(usage, label=f"{case.id}.aggregate")
        ),
        "round_usage_complete": bool(
            round_records
            and all(record.get("usage_contract_ok") is True for record in round_records)
        ),
        "prompt_characters": sum(len(prompt) for prompt in result.model_prompts),
        "prompt_oracle_errors": list(prompt_errors),
        "model_rounds": round_records,
        "called_this_run": any(
            response.called for response in result.model_responses
        ),
        "replayed_from_resume": False,
        "final_status": None,
        "final_failure_code": None,
        "final_explanation": None,
    }


def recovery_round_records(
    result: ObservedInputPlannerResult | None,
    *,
    config: DeepSeekConfig,
) -> list[dict[str, Any]]:
    """Preserve already-paid response telemetry without performing more I/O."""

    if result is None:
        return []
    prompts = tuple(result.model_prompts)
    records: list[dict[str, Any]] = []
    for number, response in enumerate(result.model_responses, start=1):
        prompt = prompts[number - 1] if number <= len(prompts) else None
        usage_errors = usage_contract_errors(
            response.usage,
            label=f"recovery.round-{number}",
        )
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
                "prompt_characters": len(prompt) if isinstance(prompt, str) else None,
                "system_sha256": sha256_text(OPEN_TARGET_SYSTEM_PROMPT),
                "prompt_sha256": (
                    sha256_text(prompt) if isinstance(prompt, str) else None
                ),
                "response_sha256": sha256_text(response.content),
                "response_content": response.content,
                "prompt_file": None,
                "response_file": None,
                "replayed": False,
                "runner_recovery_record": True,
            }
        )
    return records


def build_case_runner_error_row(
    *,
    case: BenchmarkCase,
    execution_position: int,
    error: Exception,
    config: DeepSeekConfig,
    result: ObservedInputPlannerResult | None,
) -> dict[str, Any]:
    """Build a redacted, contract-failing row and retain any paid call telemetry."""

    safe_error = config.redact(f"{type(error).__name__}: {error}")
    responses = tuple(result.model_responses) if result is not None else ()
    prompts = tuple(result.model_prompts) if result is not None else ()
    trace = tuple(result.query_trace) if result is not None else ()
    rounds = recovery_round_records(result, config=config)
    usage = aggregate_usage(response.usage for response in responses)
    try:
        candidate_metrics = open_target_candidate_metrics(trace)
    except Exception:
        candidate_metrics = {}
    try:
        prompt_errors = list(prompt_oracle_errors(prompts))
    except Exception as audit_error:
        prompt_errors = [
            config.redact(
                f"runner prompt audit failed: {type(audit_error).__name__}: {audit_error}"
            )
        ]
    model_term = submitted_model_term(responses)
    negative_audit = negative_semantic_audit(
        {"id": case.id, "candidate_metrics": candidate_metrics}
    )
    return {
        "id": case.id,
        "module": case.module,
        "source_declaration": case.effective_input_declaration,
        "required_hardness": case.required_hardness,
        "allowed_target_evidence": list(case.allowed_target_evidence),
        "maximum_route_atoms": case.maximum_route_atoms,
        "maximum_dependencies": case.maximum_dependencies,
        "allow_reflexive_target": case.allow_reflexive_target,
        "expected_status": case.expected.final_status,
        "expected_failure_code": case.expected.final_failure_code,
        "protocol_accepted": (
            result.protocol_accepted if result is not None else False
        ),
        "protocol_matches_expected": False,
        "failure_code": "runner_internal_error",
        "explanation": safe_error,
        "problem_match": (
            result.problem_match.to_dict()
            if result is not None and result.problem_match is not None
            else None
        ),
        "selected_connection": (
            result.selected_connection.to_dict()
            if result is not None and result.selected_connection is not None
            else None
        ),
        "selected_target_declaration": (
            result.plan.target_declaration
            if result is not None and result.plan is not None
            else None
        ),
        "selected_target_from_search": None,
        "selected_evidence_from_search": None,
        "selected_evidence_policy_satisfied": None,
        "matched_problem_from_search": None,
        "selected_connection_from_search": None,
        "route_declarations_all_retrieved": None,
        "all_selected_facts_retrieved": None,
        "selected_target_reachability": None,
        "selected_reduction_declarations": (
            list(result.reduction_declarations) if result is not None else []
        ),
        "model_raw_lean_term": model_term,
        "lean_term": result.lean_term if result is not None else None,
        "model_term_changed_by_agent": model_term_changed_by_agent(
            model_term,
            result.lean_term if result is not None else None,
        ),
        "plan": (
            result.plan.to_dict()
            if result is not None and result.plan is not None
            else None
        ),
        "query_trace": list(trace),
        "query_action_counts": completed_action_counts(trace),
        "candidate_metrics": candidate_metrics,
        "negative_semantic_audit": negative_audit,
        "query_round_count": query_round_count(trace),
        "model_turn_count": len(responses),
        "external_api_calls_this_run": sum(response.called for response in responses),
        "http_ok_count_this_run": sum(
            response.called and response.ok for response in responses
        ),
        "http_request_attempts_this_run": sum(
            response.attempts for response in responses if response.called
        ),
        "duration_seconds_this_run": round(
            sum(response.duration_seconds for response in responses), 3
        ),
        "usage": usage,
        "usage_contract_errors": list(
            usage_contract_errors(usage, label=f"{case.id}.aggregate")
        ),
        "round_usage_complete": bool(
            rounds and all(row.get("usage_contract_ok") is True for row in rounds)
        ),
        "prompt_characters": sum(len(prompt) for prompt in prompts),
        "prompt_oracle_errors": prompt_errors,
        "model_rounds": rounds,
        "called_this_run": any(response.called for response in responses),
        "replayed_from_resume": False,
        "execution_position": execution_position,
        "runner_error": safe_error,
        "final_status": "FAILED",
        "final_failure_code": "runner_internal_error",
        "final_explanation": safe_error,
    }


def validate_stage_g_report_contract(
    rows: Sequence[Mapping[str, Any]],
    *,
    lean_process_count: int,
    lean_ok: bool,
    lean_started_after_all_model_tasks: bool,
    model_task_count_at_lean_start: int,
    artifact_sha256: str | None,
    accepted_positive_case_count: int,
    assert_standard_axioms_count: int,
) -> tuple[str, ...]:
    errors: list[str] = []
    if len(rows) != OPEN_TARGET_CASE_COUNT:
        errors.append(f"report must contain exactly {OPEN_TARGET_CASE_COUNT} cases")
    case_ids = [row.get("id") for row in rows]
    string_case_ids = [value for value in case_ids if isinstance(value, str)]
    duplicate_case_ids = sorted(
        case_id
        for case_id, count in Counter(string_case_ids).items()
        if count > 1
    )
    expected_case_ids = set(EXPECTED_CASE_POLICIES)
    actual_case_ids = set(string_case_ids)
    if len(string_case_ids) != len(case_ids):
        errors.append("report contains a missing or malformed case ID")
    if duplicate_case_ids:
        errors.append(
            "report contains duplicate case IDs: " + ", ".join(duplicate_case_ids)
        )
    if actual_case_ids != expected_case_ids:
        missing = sorted(expected_case_ids - actual_case_ids)
        unexpected = sorted(actual_case_ids - expected_case_ids)
        errors.append(
            "report case IDs differ from the Stage G suite"
            f"; missing={missing}; unexpected={unexpected}"
        )
    positives = [row for row in rows if row.get("expected_status") == "VERIFIED"]
    negatives = [row for row in rows if row.get("expected_status") == "BLOCKED"]
    if len(positives) != OPEN_TARGET_POSITIVE_COUNT:
        errors.append("report must contain exactly three expected positive cases")
    if len(negatives) != OPEN_TARGET_NEGATIVE_COUNT:
        errors.append("report must contain exactly four expected negative cases")
    for row in rows:
        case_id = row.get("id")
        label = case_id if isinstance(case_id, str) else "<missing-case-id>"
        canonical_negative_failure = (
            EXPECTED_NEGATIVE_FAILURES.get(case_id)
            if isinstance(case_id, str)
            else None
        )
        canonical_status = (
            "BLOCKED" if canonical_negative_failure is not None else "VERIFIED"
        )
        if row.get("expected_status") != canonical_status:
            errors.append(f"{label}: expected status differs from the Stage G suite")
        if row.get("expected_failure_code") != canonical_negative_failure:
            errors.append(
                f"{label}: expected failure code differs from the Stage G suite"
            )
        rounds = row.get("model_rounds")
        if not isinstance(rounds, list) or not rounds:
            errors.append(f"{label}: no fresh model rounds were recorded")
            rounds = []
        if row.get("called_this_run") is not True:
            errors.append(f"{label}: no current-run DeepSeek call")
        if row.get("replayed_from_resume") is not False:
            errors.append(f"{label}: formal Stage G run replayed a prior answer")
        if not _valid_integer(row.get("external_api_calls_this_run"), positive=True):
            errors.append(f"{label}: external API call count is invalid")
        if row.get("http_ok_count_this_run") != row.get(
            "external_api_calls_this_run"
        ):
            errors.append(f"{label}: not every model API turn succeeded")
        if not _valid_integer(
            row.get("http_request_attempts_this_run"), positive=True
        ) or row.get("http_request_attempts_this_run", 0) < row.get(
            "external_api_calls_this_run", 0
        ):
            errors.append(f"{label}: HTTP request attempt count is inconsistent")
        if row.get("model_turn_count") != len(rounds):
            errors.append(f"{label}: model turn count disagrees with round records")
        round_usages: list[Mapping[str, Any] | None] = []
        for round_index, round_row in enumerate(rounds, start=1):
            if not isinstance(round_row, Mapping):
                errors.append(f"{label}: round {round_index} is malformed")
                continue
            if round_row.get("called") is not True or round_row.get("http_ok") is not True:
                errors.append(f"{label}: round {round_index} was not a successful fresh call")
            if round_row.get("replayed") is not False:
                errors.append(f"{label}: round {round_index} was replayed")
            if not _valid_integer(round_row.get("attempts"), positive=True):
                errors.append(f"{label}: round {round_index} attempts are invalid")
            round_usage = round_row.get("usage")
            round_usages.append(round_usage if isinstance(round_usage, Mapping) else None)
            errors.extend(
                usage_contract_errors(
                    round_usage if isinstance(round_usage, Mapping) else None,
                    label=f"{label}.round-{round_index}",
                )
            )
            for hash_field in ("system_sha256", "prompt_sha256", "response_sha256"):
                value = round_row.get(hash_field)
                if not isinstance(value, str) or len(value) != 64:
                    errors.append(
                        f"{label}: round {round_index} {hash_field} is missing"
                    )
        usage = row.get("usage")
        errors.extend(
            usage_contract_errors(
                usage if isinstance(usage, Mapping) else None,
                label=f"{label}.aggregate",
            )
        )
        if isinstance(usage, Mapping) and aggregate_usage(round_usages) != dict(
            sorted(usage.items())
        ):
            errors.append(f"{label}: round usage does not equal aggregate usage")
        if row.get("round_usage_complete") is not True:
            errors.append(f"{label}: round usage contract is incomplete")
        if row.get("prompt_oracle_errors") != []:
            errors.append(f"{label}: prompt contains oracle or fixed-target data")
        action_counts = row.get("query_action_counts")
        if not isinstance(action_counts, Mapping) or not _valid_integer(
            action_counts.get("search_hardness_targets"), positive=True
        ):
            errors.append(f"{label}: no completed hardness target search")
        if row.get("protocol_matches_expected") is not True:
            errors.append(f"{label}: protocol outcome does not match Expected")
        if row.get("expected_status") == "VERIFIED":
            for field in (
                "selected_target_from_search",
                "selected_evidence_from_search",
                "selected_evidence_policy_satisfied",
                "matched_problem_from_search",
                "selected_connection_from_search",
                "route_declarations_all_retrieved",
                "all_selected_facts_retrieved",
            ):
                if row.get(field) is not True:
                    errors.append(f"{label}: {field} is not true")
            if row.get("protocol_accepted") is not True:
                errors.append(f"{label}: positive case was not protocol accepted")
            if row.get("final_status") != "VERIFIED":
                errors.append(f"{label}: positive case did not pass final Lean")
            if row.get("model_term_changed_by_agent") is not False:
                errors.append(f"{label}: model Lean term was rewritten")
            if not isinstance(row.get("model_raw_lean_term"), str):
                errors.append(f"{label}: raw model Lean term is missing")
            if not isinstance(row.get("plan"), Mapping):
                errors.append(f"{label}: accepted positive plan is missing")
        elif row.get("expected_status") == "BLOCKED":
            if row.get("final_status") != "BLOCKED":
                errors.append(f"{label}: negative case was not correctly blocked")
            if row.get("final_failure_code") != row.get("expected_failure_code"):
                errors.append(f"{label}: negative failure code differs from Expected")
            errors.extend(negative_semantic_audit(row)["errors"])
    if lean_process_count != 1:
        errors.append("formal Stage G run must start exactly one final Lean process")
    if not lean_ok:
        errors.append("the combined Stage G Lean artifact did not verify")
    if not lean_started_after_all_model_tasks:
        errors.append("final Lean did not start after all model tasks")
    if model_task_count_at_lean_start != OPEN_TARGET_CASE_COUNT:
        errors.append("final Lean started before all seven model tasks completed")
    if not isinstance(artifact_sha256, str) or len(artifact_sha256) != 64:
        errors.append("combined open-target artifact SHA-256 is missing")
    if accepted_positive_case_count != OPEN_TARGET_POSITIVE_COUNT:
        errors.append("combined artifact does not contain all three positive cases")
    if assert_standard_axioms_count != 1:
        errors.append("combined Stage G artifact must contain exactly one axiom gate")
    return tuple(errors)


def build_stage_g_summary(
    rows: Sequence[Mapping[str, Any]],
    *,
    lean_process_count: int,
    lean_ok: bool,
    lean_started_after_all_model_tasks: bool,
    model_task_count_at_lean_start: int,
    artifact_sha256: str | None,
    accepted_positive_case_count: int,
    assert_standard_axioms_count: int,
) -> dict[str, Any]:
    errors = validate_stage_g_report_contract(
        rows,
        lean_process_count=lean_process_count,
        lean_ok=lean_ok,
        lean_started_after_all_model_tasks=lean_started_after_all_model_tasks,
        model_task_count_at_lean_start=model_task_count_at_lean_start,
        artifact_sha256=artifact_sha256,
        accepted_positive_case_count=accepted_positive_case_count,
        assert_standard_axioms_count=assert_standard_axioms_count,
    )
    action_totals: Counter[str] = Counter()
    candidate_totals: Counter[str] = Counter()
    for row in rows:
        action_counts = row.get("query_action_counts")
        if isinstance(action_counts, Mapping):
            action_totals.update(
                {
                    str(key): int(value)
                    for key, value in action_counts.items()
                    if _valid_integer(value)
                }
            )
        candidate_metrics = row.get("candidate_metrics")
        if isinstance(candidate_metrics, Mapping):
            candidate_totals.update(
                {
                    str(key): int(value)
                    for key, value in candidate_metrics.items()
                    if _valid_integer(value)
                }
            )
    usage = aggregate_usage(
        row.get("usage") if isinstance(row.get("usage"), Mapping) else None
        for row in rows
    )
    return {
        "case_count": len(rows),
        "expected_positive_count": sum(
            row.get("expected_status") == "VERIFIED" for row in rows
        ),
        "expected_negative_count": sum(
            row.get("expected_status") == "BLOCKED" for row in rows
        ),
        "positive_protocol_accepted": sum(
            row.get("expected_status") == "VERIFIED"
            and row.get("protocol_accepted") is True
            for row in rows
        ),
        "positive_lean_verified": sum(
            row.get("expected_status") == "VERIFIED"
            and row.get("final_status") == "VERIFIED"
            for row in rows
        ),
        "negative_correctly_rejected": sum(
            row.get("expected_status") == "BLOCKED"
            and row.get("final_status") == "BLOCKED"
            and row.get("final_failure_code") == row.get("expected_failure_code")
            for row in rows
        ),
        "fresh_real_api_case_count": sum(
            row.get("called_this_run") is True
            and row.get("replayed_from_resume") is False
            for row in rows
        ),
        "model_api_turn_count_this_run": sum(
            int(row.get("external_api_calls_this_run", 0)) for row in rows
        ),
        "successful_model_api_turn_count_this_run": sum(
            int(row.get("http_ok_count_this_run", 0)) for row in rows
        ),
        "real_http_request_count_this_run": sum(
            int(row.get("http_request_attempts_this_run", 0)) for row in rows
        ),
        "model_turn_count": sum(int(row.get("model_turn_count", 0)) for row in rows),
        "query_round_count": sum(int(row.get("query_round_count", 0)) for row in rows),
        "query_action_counts": dict(sorted(action_totals.items())),
        "candidate_metrics": dict(sorted(candidate_totals.items())),
        "prompt_oracle_error_count": sum(
            len(row.get("prompt_oracle_errors", [])) for row in rows
        ),
        "model_term_rewrite_count": sum(
            row.get("model_term_changed_by_agent") is True for row in rows
        ),
        "selected_evidence_from_search_count": sum(
            row.get("selected_evidence_from_search") is True for row in rows
        ),
        "policy_satisfied_target_count": sum(
            row.get("selected_evidence_policy_satisfied") is True for row in rows
        ),
        "retrieved_route_count": sum(
            row.get("route_declarations_all_retrieved") is True for row in rows
        ),
        "usage": usage,
        "prompt_cache_hit_tokens": usage.get("prompt_cache_hit_tokens", 0),
        "prompt_cache_miss_tokens": usage.get("prompt_cache_miss_tokens", 0),
        "lean_process_count": lean_process_count,
        "artifact_sha256": artifact_sha256,
        "assert_standard_axioms_count": assert_standard_axioms_count,
        "negative_semantic_forward_metric_sources": {
            str(row.get("id")): negative_semantic_audit(row).get(
                "forward_metric_source"
            )
            for row in rows
            if negative_semantic_audit(row).get("applicable") is True
        },
        "negative_semantic_fallback_case_count": sum(
            negative_semantic_audit(row).get("forward_metric_fallback_used") is True
            for row in rows
        ),
        "contract_error_count": len(errors),
        "contract_errors": list(errors),
        "all_stage_g_thresholds_met": not errors,
    }


def main() -> int:
    arguments = parser().parse_args()
    if arguments.lean_timeout <= 0:
        parser().error("--lean-timeout must be positive")
    if arguments.model_timeout is not None and arguments.model_timeout <= 0:
        parser().error("--model-timeout must be positive")
    if arguments.model_max_tokens <= 0:
        parser().error("--model-max-tokens must be positive")
    if not 1 <= arguments.query_rounds <= MAX_OPEN_TARGET_QUERY_ROUNDS:
        parser().error(
            f"--query-rounds must be in 1..{MAX_OPEN_TARGET_QUERY_ROUNDS}"
        )
    if not arguments.run_label.strip():
        parser().error("--run-label must be non-empty")

    output_root = arguments.output_root.resolve()
    canonical_report = arguments.canonical_report.resolve()
    try:
        prepare_fresh_output_root(output_root)
    except (OSError, ValueError) as error:
        print(json.dumps({"status": "FAILED", "error": str(error)}), flush=True)
        return 1

    report_path = output_root / "report.json"
    transcript_root = output_root / "transcripts"
    plan_root = output_root / "plans"
    artifact_path = output_root / "OpenTargetDeepSeekBatch.lean"
    lean_root = ROOT / "Lean"
    report: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "started_at": utc_now(),
        "status": "RUNNING",
        "run_label": arguments.run_label.strip(),
        "scope": {
            "real_deepseek": True,
            "formal_stage_g": True,
            "resume_supported": False,
            "replay_supported": False,
            "every_case_requires_current_http": True,
            "llm_selects_problem_target_evidence_route_and_term": True,
            "full_catalogs_sent_to_model": False,
            "lean_during_model_tasks": False,
            "final_lean_processes_expected": 1,
            "standard_axiom_gate": True,
            "maximum_query_rounds_per_case": arguments.query_rounds,
        },
        "output_root": str(output_root),
        "cases": [],
    }
    active_config: DeepSeekConfig | None = None

    def redact_for_report(value: str) -> str:
        return active_config.redact(value) if active_config is not None else value

    def finish(status: str, *, exit_code: int, error: str | None = None) -> int:
        return finalize_report(
            report=report,
            report_path=report_path,
            canonical_report=canonical_report,
            status=status,
            exit_code=exit_code,
            run_label=report["run_label"],
            error=error,
            redactor=redact_for_report,
            emit=lambda value: print(value, flush=True),
        )

    try:
        preflight_canonical_report(canonical_report)
        report["canonical_preflight"] = {
            "path": str(canonical_report),
            "same_directory_atomic_replace": True,
            "writable_before_http": True,
        }
    except (OSError, UnicodeError, ValueError) as error:
        report["canonical_preflight"] = {
            "path": str(canonical_report),
            "same_directory_atomic_replace": True,
            "writable_before_http": False,
        }
        return finish(
            "FAILED",
            exit_code=1,
            error=f"Stage G canonical report preflight failed before DeepSeek: {error}",
        )

    try:
        suite = load_benchmark_suite(arguments.suite)
        cases = validate_open_target_suite(suite)
        toolchain = (lean_root / "lean-toolchain").read_text(
            encoding="utf-8"
        ).strip()
        manifest_sha256 = sha256_file(lean_root / "lake-manifest.json")
        problem_catalog = load_problem_catalog_snapshot(
            arguments.problem_catalog,
            expected_toolchain=toolchain,
            expected_lake_manifest_sha256=manifest_sha256,
        )
        connection_catalog = load_connection_catalog_snapshot(
            arguments.connection_catalog,
            expected_registry_fingerprint=problem_catalog.registry_fingerprint,
            expected_toolchain=toolchain,
            expected_lake_manifest_sha256=manifest_sha256,
        )
        target_catalog = load_hardness_target_catalog_snapshot(
            arguments.target_catalog,
            expected_registry_fingerprint=problem_catalog.registry_fingerprint,
            expected_toolchain=toolchain,
            expected_lake_manifest_sha256=manifest_sha256,
        )
        reduction_catalog = build_reduction_catalog(connection_catalog, mode="full")
        if reduction_catalog.registry_fingerprint != problem_catalog.registry_fingerprint:
            raise ValueError("derived reduction catalog registry fingerprint changed")
    except (
        BenchmarkManifestError,
        ProblemCatalogError,
        ConnectionCatalogError,
        HardnessTargetCatalogError,
        OSError,
        UnicodeError,
        ValueError,
        json.JSONDecodeError,
    ) as error:
        return finish(
            "FAILED",
            exit_code=1,
            error=f"Stage G real-run snapshot preflight failed: {error}",
        )

    report["benchmark"] = {
        "suite_id": suite.id,
        "case_count": len(cases),
        "positive_count": sum(case.is_positive for case in cases),
        "negative_count": sum(not case.is_positive for case in cases),
        "case_ids": [case.id for case in cases],
        "suite_file": str(arguments.suite.resolve()),
        "suite_sha256": sha256_file(arguments.suite.resolve()),
        "expected_contract": "3 VERIFIED positives and 4 correctly BLOCKED negatives",
    }
    report["catalogs"] = {
        "registry_fingerprint": problem_catalog.registry_fingerprint,
        "problem_catalog_path": str(arguments.problem_catalog.resolve()),
        "problem_catalog_snapshot_sha256": sha256_file(
            arguments.problem_catalog.resolve()
        ),
        "problem_catalog_id": problem_catalog.catalog_id,
        "problem_count": len(problem_catalog.entries),
        "connection_catalog_path": str(arguments.connection_catalog.resolve()),
        "connection_catalog_snapshot_sha256": sha256_file(
            arguments.connection_catalog.resolve()
        ),
        "connection_catalog_id": connection_catalog.catalog_id,
        "connection_count": len(connection_catalog.entries),
        "reduction_catalog_id": reduction_catalog.catalog_id,
        "reduction_count": len(reduction_catalog.entries),
        "hardness_target_catalog_path": str(arguments.target_catalog.resolve()),
        "hardness_target_catalog_snapshot_sha256": sha256_file(
            arguments.target_catalog.resolve()
        ),
        "hardness_target_catalog_id": target_catalog.catalog_id,
        "hardness_target_count": len(target_catalog.entries),
        "hardness_target_evidence_count": target_catalog.evidence_count,
        "toolchain": toolchain,
        "lake_manifest_sha256": manifest_sha256,
    }

    prepared_cases: list[
        tuple[BenchmarkCase, LeanInputObservation, Path, str]
    ] = []
    observation_cache: dict[tuple[str, str], tuple[LeanInputObservation, Path, str]] = {}
    try:
        for case in cases:
            key = (case.module, case.effective_input_declaration)
            cached = observation_cache.get(key)
            if cached is None:
                input_path = module_file(lean_root, case.module)
                input_sha256 = sha256_file(input_path)
                snapshot = observation_snapshot_path(
                    arguments.observations_root,
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
                cached = (observation, snapshot, input_sha256)
                observation_cache[key] = cached
            prepared_cases.append((case, *cached))
    except (InputObservationError, OSError, UnicodeError, ValueError) as error:
        return finish(
            "FAILED",
            exit_code=1,
            error=f"Stage G input observation preflight failed before DeepSeek: {error}",
        )

    report["observations"] = {
        "root": str(arguments.observations_root.resolve()),
        "unique_observation_count": len(observation_cache),
        "all_source_hashes_checked_before_http": True,
        "observation_ids_by_case": {
            case.id: observation.observation_id
            for case, observation, _, _ in prepared_cases
        },
    }

    try:
        config = DeepSeekConfig.from_environment(env_file=arguments.env_file)
        config = replace(config, max_tokens=arguments.model_max_tokens)
        if arguments.model_timeout is not None:
            config = replace(config, timeout_seconds=arguments.model_timeout)
        active_config = config
        report["model"] = config.to_public_dict()
        report["model"]["system_prompt_sha256"] = sha256_text(
            OPEN_TARGET_SYSTEM_PROMPT
        )
    except (OSError, UnicodeError, ValueError) as error:
        return finish(
            "FAILED",
            exit_code=1,
            error=f"Stage G DeepSeek configuration preflight failed: {error}",
        )
    if not config.api_key:
        return finish(
            "FAILED",
            exit_code=1,
            error="DEEPSEEK_API_KEY is not configured; no formal Stage G HTTP calls occurred.",
        )
    write_json(report_path, report)

    client = DeepSeekClient(config)
    rows: list[dict[str, Any]] = []
    artifacts: list[OpenTargetArtifactCase] = []
    report["runner_errors"] = []

    def refresh_running_progress() -> None:
        report["cases"] = rows
        report["progress"] = {
            "completed_model_tasks": len(rows),
            "model_api_turns_this_run": sum(
                item["external_api_calls_this_run"] for item in rows
            ),
            "real_http_request_count_this_run": sum(
                item["http_request_attempts_this_run"] for item in rows
            ),
            "usage": aggregate_usage(
                item.get("usage") if isinstance(item.get("usage"), Mapping) else None
                for item in rows
            ),
            "lean_process_count": 0,
            "runner_error_count": len(report["runner_errors"]),
        }

    try:
        for index, (case, observation, snapshot, input_sha256) in enumerate(
            prepared_cases, start=1
        ):
            result: ObservedInputPlannerResult | None = None
            rows_before = len(rows)
            artifacts_before = len(artifacts)
            try:
                print(
                    json.dumps(
                        {
                            "phase": "deepseek_open_target",
                            "case": case.id,
                            "index": index,
                            "total": len(prepared_cases),
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
                    maximum_query_rounds=arguments.query_rounds,
                )
                model_term = submitted_model_term(result.model_responses)
                round_records = build_round_records(
                    case_id=case.id,
                    prompts=result.model_prompts,
                    responses=result.model_responses,
                    output_root=output_root,
                    config=config,
                )
                row = result_row(
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
                pending_artifact = (
                    artifact_case_from_result(case, result)
                    if case.is_positive and result.protocol_accepted
                    else None
                )
                if result.plan is not None:
                    write_json(plan_root / f"{case.id}.json", result.plan.to_dict())
                write_json(transcript_root / f"{case.id}.json", row)
                rows.append(row)
                if pending_artifact is not None:
                    artifacts.append(pending_artifact)
                refresh_running_progress()
                write_json(report_path, report)
            except Exception as case_error:
                del rows[rows_before:]
                del artifacts[artifacts_before:]
                safe_case_error = config.redact(
                    f"{type(case_error).__name__}: {case_error}"
                )
                try:
                    error_row = build_case_runner_error_row(
                        case=case,
                        execution_position=index,
                        error=case_error,
                        config=config,
                        result=result,
                    )
                except Exception as recovery_error:
                    safe_recovery_error = config.redact(
                        f"{type(recovery_error).__name__}: {recovery_error}"
                    )
                    error_row = {
                        "id": case.id,
                        "expected_status": case.expected.final_status,
                        "expected_failure_code": case.expected.final_failure_code,
                        "protocol_accepted": False,
                        "protocol_matches_expected": False,
                        "failure_code": "runner_internal_error",
                        "explanation": safe_case_error,
                        "model_rounds": [],
                        "model_turn_count": 0,
                        "external_api_calls_this_run": 0,
                        "http_ok_count_this_run": 0,
                        "http_request_attempts_this_run": 0,
                        "called_this_run": False,
                        "replayed_from_resume": False,
                        "usage": {},
                        "round_usage_complete": False,
                        "prompt_oracle_errors": [],
                        "query_action_counts": {},
                        "candidate_metrics": {},
                        "negative_semantic_audit": negative_semantic_audit(
                            {"id": case.id, "candidate_metrics": {}}
                        ),
                        "model_term_changed_by_agent": False,
                        "execution_position": index,
                        "runner_error": safe_case_error,
                        "runner_recovery_error": safe_recovery_error,
                        "final_status": "FAILED",
                        "final_failure_code": "runner_internal_error",
                        "final_explanation": safe_case_error,
                    }
                rows.append(error_row)
                report["runner_errors"].append(
                    {
                        "case_id": case.id,
                        "execution_position": index,
                        "error": safe_case_error,
                    }
                )
                refresh_running_progress()
                try:
                    write_json(transcript_root / f"{case.id}.json", error_row)
                except Exception as transcript_error:
                    report["runner_errors"].append(
                        {
                            "case_id": case.id,
                            "execution_position": index,
                            "phase": "error_transcript_write",
                            "error": config.redact(
                                f"{type(transcript_error).__name__}: {transcript_error}"
                            ),
                        }
                    )
                try:
                    write_json(report_path, report)
                except Exception as progress_error:
                    report["runner_errors"].append(
                        {
                            "case_id": case.id,
                            "execution_position": index,
                            "phase": "progress_report_write",
                            "error": config.redact(
                                f"{type(progress_error).__name__}: {progress_error}"
                            ),
                        }
                    )
                continue
    except Exception as loop_error:
        safe_loop_error = config.redact(
            f"{type(loop_error).__name__}: {loop_error}"
        )
        report["runner_fatal_error"] = safe_loop_error
        report["cases"] = rows
        return finish(
            "FAILED",
            exit_code=1,
            error=f"Stage G case-loop failure: {safe_loop_error}",
        )

    try:
        lean_execution = run_final_lean_after_all_model_tasks(
            artifacts=artifacts,
            completed_model_task_count=len(rows),
            expected_model_task_count=len(cases),
            artifact_path=artifact_path,
            lean_root=lean_root,
            timeout_seconds=arguments.lean_timeout,
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
    assert_standard_axioms_count = (
        str(lean_execution.get("source")).count("assert_standard_axioms")
        if lean_execution.get("source") is not None
        else 0
    )
    report["artifact"] = {
        "path": str(artifact_path),
        "generated": lean_execution.get("source") is not None,
        "sha256": lean_execution.get("artifact_sha256"),
        "accepted_positive_case_count": len(artifacts),
        "assert_standard_axioms_count": assert_standard_axioms_count,
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
            else lean_execution.get("error")
            or "no protocol-accepted positive artifacts were available"
        ),
    }

    for case, row in zip(cases, rows, strict=True):
        if row.get("runner_error") is not None:
            row["final_status"] = "FAILED"
            row["final_failure_code"] = "runner_internal_error"
            row["final_explanation"] = row["runner_error"]
        elif case.is_positive:
            if row["protocol_accepted"] and lean_ok:
                row["final_status"] = "VERIFIED"
                row["final_failure_code"] = None
                row["final_explanation"] = (
                    "The model-selected target evidence and untouched path term passed "
                    "the single combined Lean elaboration and standard axiom gate."
                )
            elif row["protocol_accepted"]:
                row["final_status"] = "FAILED"
                row["final_failure_code"] = "final_lean_artifact_failed"
                row["final_explanation"] = (
                    "The open-target protocol accepted the answer, but the single "
                    "combined Lean artifact did not verify."
                )
            else:
                row["final_status"] = "FAILED"
                row["final_failure_code"] = row["failure_code"] or "model_protocol_failed"
                row["final_explanation"] = row["explanation"]
        elif row["protocol_matches_expected"]:
            row["final_status"] = "BLOCKED"
            row["final_failure_code"] = row["failure_code"]
            row["final_explanation"] = row["explanation"]
        elif row["protocol_accepted"]:
            row["final_status"] = "FAILED"
            row["final_failure_code"] = "negative_case_unexpectedly_accepted"
            row["final_explanation"] = (
                "The negative case was unexpectedly accepted by the open-target protocol."
            )
        else:
            row["final_status"] = "FAILED"
            row["final_failure_code"] = row["failure_code"] or "wrong_negative_failure"
            row["final_explanation"] = row["explanation"]
        try:
            write_json(transcript_root / f"{case.id}.json", row)
        except Exception as transcript_error:
            safe_transcript_error = config.redact(
                f"{type(transcript_error).__name__}: {transcript_error}"
            )
            row["runner_error"] = safe_transcript_error
            row["final_status"] = "FAILED"
            row["final_failure_code"] = "runner_internal_error"
            row["final_explanation"] = safe_transcript_error
            row["protocol_matches_expected"] = False
            report["runner_errors"].append(
                {
                    "case_id": case.id,
                    "execution_position": row.get("execution_position"),
                    "phase": "final_transcript_write",
                    "error": safe_transcript_error,
                }
            )

    report["cases"] = rows
    report["summary"] = build_stage_g_summary(
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
        assert_standard_axioms_count=assert_standard_axioms_count,
    )
    if report["summary"]["all_stage_g_thresholds_met"]:
        return finish("VERIFIED", exit_code=0)
    return finish(
        "FAILED",
        exit_code=1,
        error=(
            "Stage G full run did not meet the formal report contract: "
            + "; ".join(report["summary"]["contract_errors"][:8])
        ),
    )


if __name__ == "__main__":
    raise SystemExit(main())
