#!/usr/bin/env python3
"""Run a fixed-target observed-input suite with real DeepSeek.

All observations and catalogs come from fingerprint-bound offline snapshots.
No Lean process is started during model work.  After every model task has
finished, all accepted positive terms are checked in one combined Lean process.

The default suite is the 24-case input-grounding regression.  The same audited
runner also executes the phase-F 36-case flat-vs-library-representation study;
each case receives only the reduction catalog view named by ``catalog_mode``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter, defaultdict
from dataclasses import replace
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Mapping


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.artifact import (  # noqa: E402
    CertifiedPathArtifactCase,
    build_certified_path_batch_artifact_source,
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
from agent.hardness.family_rule_audit import (  # noqa: E402
    audit_python_family_specific_rules,
)
from agent.hardness.input_grounding import (  # noqa: E402
    REPRESENTATION_COMPARISON_CATALOG_MODES,
    REPRESENTATION_COMPARISON_STUDY_FAMILIES,
    REPRESENTATION_COMPARISON_SUITE_ID,
    find_prompt_forbidden_keys,
    observation_snapshot_path,
    validate_input_grounding_suite,
    validate_representation_comparison_suite,
)
from agent.hardness.input_observation import (  # noqa: E402
    InputObservationError,
    LeanInputObservation,
    load_input_observation_snapshot,
)
from agent.hardness.input_planner import (  # noqa: E402
    MAX_INPUT_QUERY_ROUNDS,
    OBSERVED_INPUT_SYSTEM_PROMPT,
    ObservedInputPlannerResult,
    generate_lean_path_from_observed_input,
)
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
from agent.hardness.problem_catalog import (  # noqa: E402
    ProblemCatalogError,
    load_problem_catalog_snapshot,
)


SCHEMA_VERSION = "hardness_input_grounding_deepseek_report_v1"
STAGE_F_BASELINE_CATALOG_MODE = "flat_api"
STAGE_F_COMPONENT_CATALOG_MODE = "component_catalog"
STAGE_F_RULE_AUDIT_PATHS = (
    ROOT / "agent" / "hardness" / "input_planner.py",
    ROOT / "agent" / "hardness" / "problem_catalog.py",
    ROOT / "agent" / "hardness" / "connection_catalog.py",
    ROOT / "agent" / "hardness" / "catalog.py",
    ROOT / "agent" / "hardness" / "retrieval.py",
    ROOT / "agent" / "hardness" / "planner.py",
    ROOT / "agent" / "hardness" / "model_client.py",
    Path(__file__).resolve(),
)
STAGE_F_BENCHMARK_VALIDATION_PATHS = (
    ROOT / "agent" / "hardness" / "input_grounding.py",
)
STAGE_F_REQUIRED_CASE_INTEGER_METRICS = (
    "retrieved_ingress_count",
    "selected_ingress_count",
    "selected_shared_gadget_count",
    "selected_final_facade_count",
    "independent_lean_adapter_count",
    "specialized_lean_interface_count",
    "query_round_count",
    "model_turn_count",
    "prompt_characters",
    "external_api_calls_this_run",
    "http_ok_count_this_run",
    "http_request_attempts_this_run",
)
STAGE_F_REQUIRED_USAGE_METRICS = (
    "prompt_tokens",
    "completion_tokens",
    "total_tokens",
    "prompt_cache_hit_tokens",
    "prompt_cache_miss_tokens",
)
UNRETRIEVED_FAILURE_CODES = {
    "problem_not_retrieved",
    "connection_not_retrieved",
    "reduction_not_retrieved",
    "lean_term_uses_unselected_declaration",
}


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


def aggregate_usage(usages: Iterable[Mapping[str, Any] | None]) -> dict[str, int]:
    totals: dict[str, int] = defaultdict(int)
    for usage in usages:
        if not isinstance(usage, Mapping):
            continue
        for key, value in usage.items():
            if isinstance(value, int) and not isinstance(value, bool):
                totals[str(key)] += value
    return dict(sorted(totals.items()))


def counterbalanced_representation_cases(
    cases: Iterable[BenchmarkCase],
) -> tuple[BenchmarkCase, ...]:
    """Alternate which treatment runs first inside successive matched pairs."""

    materialized = tuple(cases)
    grouped: dict[str, list[BenchmarkCase]] = {}
    group_order: list[str] = []
    for case in materialized:
        group_id = case.comparison_group_id or case.matched_pair_id
        if not group_id:
            raise ValueError("Stage F counterbalancing requires comparison_group_id")
        if group_id not in grouped:
            grouped[group_id] = []
            group_order.append(group_id)
        grouped[group_id].append(case)
    ordered: list[BenchmarkCase] = []
    for pair_index, group_id in enumerate(group_order):
        by_mode = {case.catalog_mode: case for case in grouped[group_id]}
        if set(by_mode) != REPRESENTATION_COMPARISON_CATALOG_MODES:
            raise ValueError(
                f"comparison group {group_id} does not contain both Stage F modes"
            )
        mode_order = (
            (STAGE_F_BASELINE_CATALOG_MODE, STAGE_F_COMPONENT_CATALOG_MODE)
            if pair_index % 2 == 0
            else (STAGE_F_COMPONENT_CATALOG_MODE, STAGE_F_BASELINE_CATALOG_MODE)
        )
        ordered.extend(by_mode[mode] for mode in mode_order)
    return tuple(ordered)


def representation_catalog_scope(
    catalogs: Mapping[str, TypedCatalog],
) -> dict[str, Any]:
    """Prove observationally that the component treatment keeps the flat view."""

    flat = catalogs[STAGE_F_BASELINE_CATALOG_MODE]
    component = catalogs[STAGE_F_COMPONENT_CATALOG_MODE]
    flat_by_id = {entry.entry_id: entry for entry in flat.entries}
    component_by_id = {entry.entry_id: entry for entry in component.entries}
    missing_ids = sorted(set(flat_by_id) - set(component_by_id))
    extra_ids = sorted(set(component_by_id) - set(flat_by_id))
    return {
        "baseline_mode": STAGE_F_BASELINE_CATALOG_MODE,
        "component_mode": STAGE_F_COMPONENT_CATALOG_MODE,
        "baseline_entry_count": len(flat_by_id),
        "component_entry_count": len(component_by_id),
        "shared_entry_count": len(set(flat_by_id) & set(component_by_id)),
        "component_only_entry_count": len(extra_ids),
        "baseline_is_subset_of_component": not missing_ids,
        "missing_baseline_declarations": sorted(
            flat_by_id[entry_id].declaration for entry_id in missing_ids
        ),
        "component_only_role_counts": dict(
            sorted(
                Counter(
                    component_by_id[entry_id].component_role for entry_id in extra_ids
                ).items()
            )
        ),
    }


def _integer_metric(value: Any, *, positive: bool = False) -> bool:
    return (
        isinstance(value, int)
        and not isinstance(value, bool)
        and value >= (1 if positive else 0)
    )


def validate_representation_comparison_report_contract(
    rows: Iterable[Mapping[str, Any]],
    *,
    comparison_metrics: Mapping[str, Any],
    python_rule_audit: Mapping[str, Any],
    catalog_scope: Mapping[str, Any],
) -> tuple[str, ...]:
    """Return every Stage-F report-contract violation without defaulting to zero."""

    materialized = list(rows)
    errors: list[str] = []
    grouped: dict[str, list[Mapping[str, Any]]] = defaultdict(list)
    for row in materialized:
        case_id = row.get("id")
        label = case_id if isinstance(case_id, str) else "<missing-case-id>"
        group_id = row.get("comparison_group_id")
        if not isinstance(group_id, str) or not group_id:
            errors.append(f"{label}: missing comparison_group_id")
        else:
            grouped[group_id].append(row)
        if row.get("catalog_mode") not in REPRESENTATION_COMPARISON_CATALOG_MODES:
            errors.append(f"{label}: invalid catalog_mode")
        if row.get("study_family") not in REPRESENTATION_COMPARISON_STUDY_FAMILIES:
            errors.append(f"{label}: invalid or missing study_family")
        if row.get("final_status") != "VERIFIED":
            errors.append(f"{label}: final_status is not VERIFIED")
        for field in STAGE_F_REQUIRED_CASE_INTEGER_METRICS:
            if not _integer_metric(
                row.get(field),
                positive=field
                in {
                    "query_round_count",
                    "model_turn_count",
                    "prompt_characters",
                    "external_api_calls_this_run",
                    "http_ok_count_this_run",
                    "http_request_attempts_this_run",
                },
            ):
                errors.append(f"{label}: missing or invalid integer metric {field}")

        declarations = row.get("selected_reduction_declarations")
        if not isinstance(declarations, list) or not all(
            isinstance(value, str) for value in declarations
        ):
            errors.append(f"{label}: selected_reduction_declarations is invalid")
            declarations = []
        selected_roles = row.get("selected_reduction_roles")
        if not isinstance(selected_roles, Mapping):
            errors.append(f"{label}: selected_reduction_roles is missing")
            selected_roles = {}
        selected_counts = selected_roles.get("counts")
        selected_role_declarations = selected_roles.get("declarations")
        route_atom_count = selected_roles.get("route_atom_count")
        if not isinstance(selected_counts, Mapping):
            errors.append(f"{label}: selected role counts are missing")
            selected_counts = {}
        if not isinstance(selected_role_declarations, Mapping):
            errors.append(f"{label}: selected role declarations are missing")
        if not _integer_metric(route_atom_count):
            errors.append(f"{label}: selected route_atom_count is invalid")
        elif route_atom_count != len(declarations):
            errors.append(f"{label}: route_atom_count disagrees with declarations")
        expected_selected = {
            "ingress": row.get("selected_ingress_count"),
            "sharedGadget": row.get("selected_shared_gadget_count"),
            "finalComposition": row.get("selected_final_facade_count"),
        }
        for role, expected in expected_selected.items():
            actual = selected_counts.get(role, 0)
            if actual != expected:
                errors.append(f"{label}: selected {role} metric disagrees with role data")
        if row.get("independent_lean_adapter_count") != row.get(
            "selected_ingress_count"
        ):
            errors.append(f"{label}: independent Lean adapter metric is inconsistent")
        if row.get("specialized_lean_interface_count") != (
            row.get("selected_ingress_count", -1)
            + row.get("selected_final_facade_count", -1)
        ):
            errors.append(f"{label}: specialized Lean interface metric is inconsistent")

        usage = row.get("usage")
        if not isinstance(usage, Mapping):
            errors.append(f"{label}: aggregate usage is missing")
            usage = {}
        for field in STAGE_F_REQUIRED_USAGE_METRICS:
            positive = field in {"prompt_tokens", "completion_tokens", "total_tokens"}
            if not _integer_metric(usage.get(field), positive=positive):
                errors.append(f"{label}: aggregate usage.{field} is missing or invalid")

        rounds = row.get("model_rounds")
        if not isinstance(rounds, list) or not rounds:
            errors.append(f"{label}: model_rounds is missing")
            rounds = []
        round_usages: list[Mapping[str, Any]] = []
        for round_index, round_row in enumerate(rounds, start=1):
            if not isinstance(round_row, Mapping):
                errors.append(f"{label}: model round {round_index} is invalid")
                continue
            if round_row.get("called") is not True or round_row.get("http_ok") is not True:
                errors.append(f"{label}: model round {round_index} was not a fresh successful call")
            if round_row.get("replayed") is not False:
                errors.append(f"{label}: model round {round_index} was replayed")
            round_usage = round_row.get("usage")
            if not isinstance(round_usage, Mapping):
                errors.append(f"{label}: model round {round_index} usage is missing")
                continue
            round_usages.append(round_usage)
            for field in STAGE_F_REQUIRED_USAGE_METRICS:
                positive = field in {"prompt_tokens", "completion_tokens", "total_tokens"}
                if not _integer_metric(round_usage.get(field), positive=positive):
                    errors.append(
                        f"{label}: model round {round_index} usage.{field} is missing or invalid"
                    )
        if round_usages and aggregate_usage(round_usages) != dict(sorted(usage.items())):
            errors.append(f"{label}: round usage does not equal case aggregate usage")
        if row.get("model_turn_count") != len(rounds):
            errors.append(f"{label}: model_turn_count disagrees with model_rounds")
        if row.get("external_api_calls_this_run") != len(rounds):
            errors.append(f"{label}: API turn count disagrees with model_rounds")
        if row.get("http_ok_count_this_run") != len(rounds):
            errors.append(f"{label}: successful API turn count disagrees with model_rounds")
        if row.get("called_this_run") is not True:
            errors.append(f"{label}: called_this_run is not true")
        if row.get("replayed_from_resume") is not False:
            errors.append(f"{label}: replayed_from_resume is not false")

    if len(grouped) != 18:
        errors.append("report does not contain exactly 18 comparison groups")
    for group_id, pair in sorted(grouped.items()):
        if len(pair) != 2 or {row.get("catalog_mode") for row in pair} != set(
            REPRESENTATION_COMPARISON_CATALOG_MODES
        ):
            errors.append(f"{group_id}: report pair does not contain both treatments")
    if comparison_metrics.get("matched_comparison_count") != 18:
        errors.append("aggregate matched_comparison_count is not 18")
    if comparison_metrics.get("both_lean_verified_count") != 18:
        errors.append("aggregate both_lean_verified_count is not 18")
    if set(comparison_metrics.get("selected_declaration_reuse_by_mode", {})) != set(
        REPRESENTATION_COMPARISON_CATALOG_MODES
    ):
        errors.append("aggregate declaration reuse modes are incomplete")
    family_rows = comparison_metrics.get("families")
    if not isinstance(family_rows, list) or {
        row.get("study_family") for row in family_rows if isinstance(row, Mapping)
    } != set(REPRESENTATION_COMPARISON_STUDY_FAMILIES):
        errors.append("aggregate family metrics are incomplete")
    audit_families = python_rule_audit.get("families")
    if not isinstance(audit_families, list) or {
        row.get("study_family") for row in audit_families if isinstance(row, Mapping)
    } != set(REPRESENTATION_COMPARISON_STUDY_FAMILIES):
        errors.append("Python family-rule audit families are incomplete")
    if python_rule_audit.get("python_family_specific_rule_count") != 0:
        errors.append("production Python routing contains family-specific rule literals")
    if catalog_scope.get("baseline_is_subset_of_component") is not True:
        errors.append("component catalog does not preserve every flat_api reduction")
    return tuple(errors)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description=(
            "Run a fixed-target observed-input suite with real DeepSeek, then "
            "run Lean exactly once"
        )
    )
    command.add_argument(
        "--suite",
        type=Path,
        default=(
            ROOT
            / "Benchmark"
            / "Hardness"
            / "Suites"
            / "input_grounding_fixed_target.json"
        ),
    )
    command.add_argument(
        "--problem-catalog",
        type=Path,
        default=ROOT / ".reduction-agent" / "problem-catalog.json",
    )
    command.add_argument(
        "--connection-catalog",
        type=Path,
        default=ROOT / ".reduction-agent" / "connection-catalog.json",
    )
    command.add_argument(
        "--observation-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "input-grounding" / "observations",
    )
    command.add_argument("--env-file", type=Path, default=ROOT / ".env")
    command.add_argument(
        "--resume-report",
        type=Path,
        help=(
            "replay and revalidate protocol-accepted model answers from an earlier "
            "same-fingerprint report; the new output directory must still be empty"
        ),
    )
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "deepseek-input-grounding-full",
    )
    command.add_argument(
        "--canonical-report",
        type=Path,
        default=None,
        help=(
            "canonical report destination; defaults to the fixed-target report or "
            "the dedicated representation-comparison report based on --suite"
        ),
    )
    command.add_argument("--run-label", default="initial-full-run")
    command.add_argument("--lean-timeout", type=int, default=600)
    command.add_argument("--model-timeout", type=int, default=None)
    command.add_argument("--model-max-tokens", type=int, default=4096)
    command.add_argument(
        "--query-rounds",
        type=int,
        default=MAX_INPUT_QUERY_ROUNDS,
        help="maximum bounded catalog queries per case",
    )
    return command


def prepare_fresh_output_root(path: Path) -> None:
    if path.exists():
        if not path.is_dir():
            raise ValueError(f"output root is not a directory: {path}")
        if any(path.iterdir()):
            raise ValueError(
                "output root is not empty; choose a fresh directory so model answers "
                "cannot be reused implicitly"
            )
    path.mkdir(parents=True, exist_ok=True)


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


def completed_action_counts(result: ObservedInputPlannerResult) -> Counter[str]:
    return Counter(
        str(row.get("action"))
        for row in result.query_trace
        if row.get("status") != "started" and isinstance(row.get("action"), str)
    )


def candidate_counts(result: ObservedInputPlannerResult) -> dict[str, int]:
    totals = {
        "problem_results": 0,
        "connection_results": 0,
        "reduction_results": 0,
        "architecture_results": 0,
    }
    keys = {
        "search_problems": "problem_results",
        "search_connections": "connection_results",
        "search_reductions": "reduction_results",
        "inspect_architecture": "architecture_results",
    }
    for row in result.query_trace:
        key = keys.get(str(row.get("action")))
        results = row.get("results")
        if key is not None and isinstance(results, list):
            totals[key] += len(results)
    return totals


def validate_observed_input_suite(suite: Any) -> tuple[BenchmarkCase, ...]:
    """Select the strict ABI for one supported observed-input study."""

    if suite.id == REPRESENTATION_COMPARISON_SUITE_ID:
        return validate_representation_comparison_suite(suite)
    return validate_input_grounding_suite(suite)


def retrieved_reduction_role_metrics(
    result: ObservedInputPlannerResult,
) -> dict[str, Any]:
    """Count unique retrieved declarations by Lean-exported component role."""

    declarations_by_role: dict[str, set[str]] = defaultdict(set)
    for row in result.query_trace:
        if row.get("action") != "search_reductions":
            continue
        results = row.get("results")
        if not isinstance(results, list):
            continue
        for item in results:
            if not isinstance(item, Mapping):
                continue
            declaration = item.get("declaration")
            role = item.get("role")
            if isinstance(declaration, str) and isinstance(role, str):
                declarations_by_role[role].add(declaration)
    return {
        "counts": {
            role: len(declarations)
            for role, declarations in sorted(declarations_by_role.items())
        },
        "declarations": {
            role: sorted(declarations)
            for role, declarations in sorted(declarations_by_role.items())
        },
    }


def selected_reduction_role_metrics(
    result: ObservedInputPlannerResult,
    reduction_catalog: TypedCatalog,
) -> dict[str, Any]:
    """Describe the exact catalog roles selected in the submitted path."""

    entries = {entry.declaration: entry for entry in reduction_catalog.entries}
    declarations_by_role: dict[str, list[str]] = defaultdict(list)
    for declaration in result.reduction_declarations:
        entry = entries.get(declaration)
        if entry is not None:
            declarations_by_role[entry.component_role].append(declaration)
    return {
        "counts": {
            role: len(declarations)
            for role, declarations in sorted(declarations_by_role.items())
        },
        "declarations": {
            role: list(declarations)
            for role, declarations in sorted(declarations_by_role.items())
        },
        "route_atom_count": len(result.reduction_declarations),
    }


def query_round_count(result: ObservedInputPlannerResult) -> int:
    return sum(
        1
        for row in result.query_trace
        if row.get("status") == "started"
        and row.get("action")
        in {
            "inspect_architecture",
            "search_problems",
            "search_connections",
            "search_reductions",
        }
    )


def normalize_action(payload: dict[str, Any]) -> dict[str, Any]:
    if isinstance(payload.get("action"), str):
        return payload
    candidates: list[dict[str, Any]] = []
    for action in (
        "inspect_architecture",
        "search_problems",
        "search_connections",
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
    for response in reversed(tuple(responses)):
        payload = extract_json_object(response.content)
        if payload is None:
            continue
        payload = normalize_action(payload)
        if payload.get("action") == "finish" and isinstance(
            payload.get("lean_term"), str
        ):
            return str(payload["lean_term"])
    return None


def protocol_matches_expected(
    case: BenchmarkCase, result: ObservedInputPlannerResult
) -> bool:
    if case.is_positive:
        return result.protocol_accepted and result.lean_term is not None
    return (
        result.failure_code == case.expected.final_failure_code
        and result.lean_term is None
    )


def prompt_leaks(prompts: Iterable[str]) -> tuple[tuple[str, ...], ...]:
    leaks: list[tuple[str, ...]] = []
    for prompt in prompts:
        value = json.loads(prompt)
        if not isinstance(value, dict):
            raise ValueError("model prompt is not a JSON object")
        leaked = find_prompt_forbidden_keys(value)
        if leaked:
            leaks.append(leaked)
    return tuple(leaks)


class ReplayModelClient:
    """Replay prior raw responses only when every regenerated prompt hash matches."""

    def __init__(self, rounds: list[dict[str, Any]]):
        self.rounds = rounds
        self.index = 0
        self.error: str | None = None

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        if self.index >= len(self.rounds):
            self.error = "resume response sequence ended before the protocol completed"
            return ModelResponse(
                called=False,
                ok=False,
                content="",
                error=self.error,
                status_code=None,
                duration_seconds=0.0,
                usage=None,
                attempts=0,
            )
        row = self.rounds[self.index]
        self.index += 1
        expected_prompt_hash = row.get("prompt_sha256")
        expected_system_hash = row.get("system_sha256")
        content = row.get("response_content")
        expected_response_hash = row.get("response_sha256")
        if expected_system_hash != sha256_text(system):
            self.error = "resume system prompt hash differs from the current protocol"
        elif expected_prompt_hash != sha256_text(prompt):
            self.error = "resume prompt hash differs from the current protocol"
        elif not isinstance(content, str):
            self.error = "resume round has no raw response content"
        elif expected_response_hash != sha256_text(content):
            self.error = "resume response hash does not match its raw content"
        if self.error is not None:
            return ModelResponse(
                called=False,
                ok=False,
                content="",
                error=self.error,
                status_code=None,
                duration_seconds=0.0,
                usage=None,
                attempts=0,
            )
        usage = row.get("usage")
        return ModelResponse(
            called=False,
            ok=True,
            content=content,
            error=None,
            status_code=row.get("status_code") if isinstance(row.get("status_code"), int) else 200,
            duration_seconds=0.0,
            usage=dict(usage) if isinstance(usage, dict) else None,
            attempts=0,
            finish_reason=(
                row.get("finish_reason")
                if isinstance(row.get("finish_reason"), str)
                else None
            ),
        )


def reusable_resume_rows(
    path: Path | None,
    *,
    registry_fingerprint: str,
    problem_catalog_id: str,
    connection_catalog_id: str,
    reduction_catalog_ids: Mapping[str, str],
) -> tuple[dict[str, dict[str, Any]], dict[str, Any] | None]:
    if path is None:
        return {}, None
    previous = json.loads(path.read_text(encoding="utf-8"))
    if previous.get("schema_version") != SCHEMA_VERSION:
        raise ValueError("resume report uses a different schema")
    catalogs = previous.get("catalogs")
    if not isinstance(catalogs, dict):
        raise ValueError("resume report has no catalog fingerprints")
    previous_ids = catalogs.get("reduction_catalog_ids_by_mode")
    if not isinstance(previous_ids, dict):
        legacy_id = catalogs.get("reduction_catalog_id")
        previous_ids = {"full": legacy_id} if isinstance(legacy_id, str) else {}
    if (
        catalogs.get("registry_fingerprint") != registry_fingerprint
        or catalogs.get("problem_catalog_id") != problem_catalog_id
        or catalogs.get("connection_catalog_id") != connection_catalog_id
        or previous_ids != dict(reduction_catalog_ids)
    ):
        raise ValueError("resume report catalogs do not match the current snapshots")
    raw_cases = previous.get("cases")
    if not isinstance(raw_cases, list):
        raise ValueError("resume report has no case records")
    rows = {
        str(row["id"]): row
        for row in raw_cases
        if isinstance(row, dict)
        and isinstance(row.get("id"), str)
        and row.get("protocol_matches_expected") is True
    }
    return rows, previous


def build_round_records(
    *,
    case_id: str,
    prompts: tuple[str, ...],
    responses: tuple[ModelResponse, ...],
    output_root: Path,
    config: DeepSeekConfig,
    replayed: bool,
) -> list[dict[str, Any]]:
    if len(prompts) != len(responses):
        raise ValueError("model prompt and response counts differ")
    call_dir = output_root / "calls" / case_id
    records: list[dict[str, Any]] = []
    for number, (prompt, response) in enumerate(
        zip(prompts, responses, strict=True), start=1
    ):
        prompt_path = call_dir / f"round-{number:02d}-prompt.json"
        response_path = call_dir / f"round-{number:02d}-response.json"
        prompt_payload = json.loads(prompt)
        write_json(
            prompt_path,
            {
                "system": OBSERVED_INPUT_SYSTEM_PROMPT,
                "system_sha256": sha256_text(OBSERVED_INPUT_SYSTEM_PROMPT),
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
            "error": config.redact(response.error or "") or None,
            "content": response.content,
            "content_sha256": sha256_text(response.content),
            "replayed": replayed,
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
                "error": config.redact(response.error or "") or None,
                "prompt_characters": len(prompt),
                "system_sha256": sha256_text(OBSERVED_INPUT_SYSTEM_PROMPT),
                "prompt_sha256": sha256_text(prompt),
                "response_sha256": sha256_text(response.content),
                "response_content": response.content,
                "prompt_file": str(prompt_path),
                "response_file": str(response_path),
                "replayed": replayed,
            }
        )
    return records


def result_row(
    *,
    case: BenchmarkCase,
    observation: LeanInputObservation,
    target_observation: LeanInputObservation,
    result: ObservedInputPlannerResult,
    round_records: list[dict[str, Any]],
    model_term: str | None,
    replayed: bool,
    resume_error: str | None,
    problem_catalog_id: str,
    connection_catalog_id: str,
    reduction_catalog: TypedCatalog,
) -> dict[str, Any]:
    leaks = prompt_leaks(result.model_prompts)
    usage = aggregate_usage(response.usage for response in result.model_responses)
    actions = completed_action_counts(result)
    retrieved_roles = retrieved_reduction_role_metrics(result)
    selected_roles = selected_reduction_role_metrics(result, reduction_catalog)
    return {
        "id": case.id,
        "module": case.module,
        "catalog_mode": case.catalog_mode,
        "comparison_group_id": getattr(case, "comparison_group_id", None),
        "matched_pair_id": case.matched_pair_id,
        "family_id": case.family_id or case.coverage.get("logical_source"),
        "study_family": case.coverage.get("study_family")
        or case.module.rsplit(".", 1)[-1].lower(),
        "source_form_id": case.source_form_id or case.coverage.get("input_form"),
        "target_form_id": case.target_form_id,
        "input_declaration": case.effective_input_declaration,
        "target_declaration": case.target,
        "input_kind": case.input_kind,
        "expected_status": case.expected.final_status,
        "expected_failure_code": case.expected.final_failure_code,
        "coverage": dict(case.coverage),
        "input_observation_id": observation.observation_id,
        "target_observation_id": target_observation.observation_id,
        "input_node_id": observation.normalized_problem_node_id,
        "target_node_id": target_observation.normalized_problem_node_id,
        "registry_fingerprint": observation.registry_fingerprint,
        "problem_catalog_id": problem_catalog_id,
        "connection_catalog_id": connection_catalog_id,
        "reduction_catalog_id": reduction_catalog.catalog_id,
        "reduction_catalog_entry_count": len(reduction_catalog.entries),
        "protocol_accepted": result.protocol_accepted,
        "protocol_matches_expected": protocol_matches_expected(case, result),
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
        "selected_reduction_declarations": list(result.reduction_declarations),
        "retrieved_reduction_roles": retrieved_roles,
        "selected_reduction_roles": selected_roles,
        "retrieved_ingress_count": retrieved_roles["counts"].get("ingress", 0),
        "selected_ingress_count": selected_roles["counts"].get("ingress", 0),
        "selected_shared_gadget_count": selected_roles["counts"].get(
            "sharedGadget", 0
        ),
        "selected_final_facade_count": selected_roles["counts"].get(
            "finalComposition", 0
        ),
        "independent_lean_adapter_count": selected_roles["counts"].get(
            "ingress", 0
        ),
        "specialized_lean_interface_count": (
            selected_roles["counts"].get("ingress", 0)
            + selected_roles["counts"].get("finalComposition", 0)
        ),
        "model_raw_lean_term": model_term,
        "lean_term": result.lean_term,
        "model_term_changed_by_agent": bool(
            result.lean_term is not None
            and (model_term is None or model_term.strip() != result.lean_term)
        ),
        "plan": result.plan.to_dict() if result.plan is not None else None,
        "query_trace": list(result.query_trace),
        "query_action_counts": dict(sorted(actions.items())),
        "candidate_counts": candidate_counts(result),
        "protocol_feedback_count": actions.get("protocol_feedback", 0),
        "query_round_count": query_round_count(result),
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
        "prompt_characters": sum(len(prompt) for prompt in result.model_prompts),
        "prompt_key_leaks": [list(leak) for leak in leaks],
        "model_rounds": round_records,
        "called_this_run": not replayed and any(
            response.called for response in result.model_responses
        ),
        "replayed_from_resume": replayed,
        "resume_validation_error": resume_error,
        "final_status": None,
        "final_failure_code": None,
        "final_explanation": None,
    }


def build_representation_comparison_metrics(
    rows: Iterable[Mapping[str, Any]],
    *,
    python_rule_counts_by_family: Mapping[str, int],
) -> dict[str, Any]:
    """Aggregate the phase-F matched and adapter-reuse measurements."""

    materialized = list(rows)
    grouped: dict[str, list[Mapping[str, Any]]] = defaultdict(list)
    for row in materialized:
        group_id = row.get("comparison_group_id") or row.get("matched_pair_id")
        if isinstance(group_id, str) and group_id:
            grouped[group_id].append(row)

    pair_rows: list[dict[str, Any]] = []
    for group_id, members in sorted(grouped.items()):
        by_mode = {
            str(member.get("catalog_mode")): member
            for member in members
            if isinstance(member.get("catalog_mode"), str)
        }
        pair_rows.append(
            {
                "comparison_group_id": group_id,
                "family_id": members[0].get("family_id") if members else None,
                "source_form_id": members[0].get("source_form_id") if members else None,
                "modes_present": sorted(by_mode),
                "both_lean_verified": set(by_mode)
                == set(REPRESENTATION_COMPARISON_CATALOG_MODES)
                and all(
                    by_mode[mode].get("final_status") == "VERIFIED"
                    for mode in (
                        STAGE_F_BASELINE_CATALOG_MODE,
                        STAGE_F_COMPONENT_CATALOG_MODE,
                    )
                ),
                STAGE_F_BASELINE_CATALOG_MODE: (
                    {
                        "case_id": by_mode[STAGE_F_BASELINE_CATALOG_MODE].get("id"),
                        "retrieved_ingress_count": by_mode[
                            STAGE_F_BASELINE_CATALOG_MODE
                        ].get(
                            "retrieved_ingress_count", 0
                        ),
                        "selected_ingress_count": by_mode[
                            STAGE_F_BASELINE_CATALOG_MODE
                        ].get(
                            "selected_ingress_count", 0
                        ),
                        "selected_shared_gadget_count": by_mode[
                            STAGE_F_BASELINE_CATALOG_MODE
                        ].get(
                            "selected_shared_gadget_count", 0
                        ),
                        "selected_final_facade_count": by_mode[
                            STAGE_F_BASELINE_CATALOG_MODE
                        ].get(
                            "selected_final_facade_count", 0
                        ),
                        "independent_lean_adapter_count": by_mode[
                            STAGE_F_BASELINE_CATALOG_MODE
                        ].get(
                            "independent_lean_adapter_count", 0
                        ),
                        "route_atom_count": by_mode[STAGE_F_BASELINE_CATALOG_MODE]
                        .get("selected_reduction_roles", {})
                        .get("route_atom_count", 0),
                        "query_round_count": by_mode[
                            STAGE_F_BASELINE_CATALOG_MODE
                        ].get(
                            "query_round_count", 0
                        ),
                        "prompt_characters": by_mode[
                            STAGE_F_BASELINE_CATALOG_MODE
                        ].get(
                            "prompt_characters", 0
                        ),
                        "usage": by_mode[STAGE_F_BASELINE_CATALOG_MODE].get(
                            "usage", {}
                        ),
                    }
                    if STAGE_F_BASELINE_CATALOG_MODE in by_mode
                    else None
                ),
                STAGE_F_COMPONENT_CATALOG_MODE: (
                    {
                        "case_id": by_mode[STAGE_F_COMPONENT_CATALOG_MODE].get("id"),
                        "retrieved_ingress_count": by_mode[
                            STAGE_F_COMPONENT_CATALOG_MODE
                        ].get(
                            "retrieved_ingress_count", 0
                        ),
                        "selected_ingress_count": by_mode[
                            STAGE_F_COMPONENT_CATALOG_MODE
                        ].get(
                            "selected_ingress_count", 0
                        ),
                        "selected_shared_gadget_count": by_mode[
                            STAGE_F_COMPONENT_CATALOG_MODE
                        ].get("selected_shared_gadget_count", 0),
                        "selected_final_facade_count": by_mode[
                            STAGE_F_COMPONENT_CATALOG_MODE
                        ].get(
                            "selected_final_facade_count", 0
                        ),
                        "independent_lean_adapter_count": by_mode[
                            STAGE_F_COMPONENT_CATALOG_MODE
                        ].get("independent_lean_adapter_count", 0),
                        "route_atom_count": by_mode[STAGE_F_COMPONENT_CATALOG_MODE]
                        .get("selected_reduction_roles", {})
                        .get("route_atom_count", 0),
                        "query_round_count": by_mode[
                            STAGE_F_COMPONENT_CATALOG_MODE
                        ].get(
                            "query_round_count", 0
                        ),
                        "prompt_characters": by_mode[
                            STAGE_F_COMPONENT_CATALOG_MODE
                        ].get(
                            "prompt_characters", 0
                        ),
                        "usage": by_mode[STAGE_F_COMPONENT_CATALOG_MODE].get(
                            "usage", {}
                        ),
                    }
                    if STAGE_F_COMPONENT_CATALOG_MODE in by_mode
                    else None
                ),
            }
        )

    mode_declaration_counts: dict[str, Counter[str]] = defaultdict(Counter)
    family_mode_ingress: dict[tuple[str, str], set[str]] = defaultdict(set)
    family_mode_facades: dict[tuple[str, str], set[str]] = defaultdict(set)
    family_input_forms: dict[str, set[str]] = defaultdict(set)
    family_comparison_groups: dict[str, set[str]] = defaultdict(set)
    for row in materialized:
        mode = row.get("catalog_mode")
        family = row.get("study_family")
        input_form = row.get("source_form_id")
        if not isinstance(mode, str):
            continue
        declarations = row.get("selected_reduction_declarations")
        if isinstance(declarations, list):
            mode_declaration_counts[mode].update(
                item for item in declarations if isinstance(item, str)
            )
        roles = row.get("selected_reduction_roles")
        role_declarations = roles.get("declarations", {}) if isinstance(roles, Mapping) else {}
        if isinstance(family, str):
            if isinstance(input_form, str):
                family_input_forms[family].add(input_form)
            comparison_group = row.get("comparison_group_id") or row.get(
                "matched_pair_id"
            )
            if isinstance(comparison_group, str):
                family_comparison_groups[family].add(comparison_group)
            ingress = role_declarations.get("ingress", [])
            facades = role_declarations.get("finalComposition", [])
            if isinstance(ingress, list):
                family_mode_ingress[(family, mode)].update(
                    item for item in ingress if isinstance(item, str)
                )
            if isinstance(facades, list):
                family_mode_facades[(family, mode)].update(
                    item for item in facades if isinstance(item, str)
                )

    family_rows: list[dict[str, Any]] = []
    for family in sorted(family_input_forms):
        family_rows.append(
            {
                "study_family": family,
                "input_form_kind_count": len(family_input_forms[family]),
                "input_form_count": len(family_comparison_groups[family]),
                "python_family_specific_rule_count": python_rule_counts_by_family[
                    family
                ],
                "flat_api_unique_ingress_adapter_count": len(
                    family_mode_ingress[(family, "flat_api")]
                ),
                "component_catalog_unique_ingress_adapter_count": len(
                    family_mode_ingress[(family, STAGE_F_COMPONENT_CATALOG_MODE)]
                ),
                "flat_api_unique_final_facade_count": len(
                    family_mode_facades[(family, "flat_api")]
                ),
                "component_catalog_unique_final_facade_count": len(
                    family_mode_facades[(family, STAGE_F_COMPONENT_CATALOG_MODE)]
                ),
                "flat_api_unique_specialized_interface_count": len(
                    family_mode_ingress[(family, "flat_api")]
                    | family_mode_facades[(family, "flat_api")]
                ),
                "component_catalog_unique_specialized_interface_count": len(
                    family_mode_ingress[(family, STAGE_F_COMPONENT_CATALOG_MODE)]
                    | family_mode_facades[(family, STAGE_F_COMPONENT_CATALOG_MODE)]
                ),
                "flat_api_ingress_declarations": sorted(
                    family_mode_ingress[(family, "flat_api")]
                ),
                "component_catalog_ingress_declarations": sorted(
                    family_mode_ingress[(family, STAGE_F_COMPONENT_CATALOG_MODE)]
                ),
            }
        )

    reuse_by_mode: dict[str, Any] = {}
    for mode, counts in sorted(mode_declaration_counts.items()):
        reused = {declaration: count for declaration, count in counts.items() if count > 1}
        reuse_by_mode[mode] = {
            "selected_declaration_occurrences": sum(counts.values()),
            "unique_selected_declarations": len(counts),
            "shared_declaration_count": len(reused),
            "shared_reuse_occurrences_beyond_first": sum(
                count - 1 for count in reused.values()
            ),
            "shared_declarations": dict(sorted(reused.items())),
        }

    return {
        "matched_comparisons": pair_rows,
        "matched_comparison_count": len(pair_rows),
        "both_lean_verified_count": sum(
            bool(row["both_lean_verified"]) for row in pair_rows
        ),
        "families": family_rows,
        "selected_declaration_reuse_by_mode": reuse_by_mode,
        "selected_ingress_total_by_mode": {
            mode: sum(
                int(row.get("selected_ingress_count", 0))
                for row in materialized
                if row.get("catalog_mode") == mode
            )
            for mode in (
                STAGE_F_BASELINE_CATALOG_MODE,
                STAGE_F_COMPONENT_CATALOG_MODE,
            )
        },
        "selected_shared_gadget_total_by_mode": {
            mode: sum(
                int(row.get("selected_shared_gadget_count", 0))
                for row in materialized
                if row.get("catalog_mode") == mode
            )
            for mode in (
                STAGE_F_BASELINE_CATALOG_MODE,
                STAGE_F_COMPONENT_CATALOG_MODE,
            )
        },
        "selected_final_facade_total_by_mode": {
            mode: sum(
                int(row.get("selected_final_facade_count", 0))
                for row in materialized
                if row.get("catalog_mode") == mode
            )
            for mode in (
                STAGE_F_BASELINE_CATALOG_MODE,
                STAGE_F_COMPONENT_CATALOG_MODE,
            )
        },
        "specialized_lean_interface_total_by_mode": {
            mode: sum(
                int(row.get("specialized_lean_interface_count", 0))
                for row in materialized
                if row.get("catalog_mode") == mode
            )
            for mode in (
                STAGE_F_BASELINE_CATALOG_MODE,
                STAGE_F_COMPONENT_CATALOG_MODE,
            )
        },
        "metric_definitions": {
            "independent_lean_adapter_count": (
                "selected Lean-exported reductions whose component role is ingress"
            ),
            "specialized_lean_interface_count": (
                "selected ingress adapters plus selected finalComposition facades; this "
                "keeps flat facades visible instead of misclassifying them as zero adapter cost"
            ),
            "shared_reuse_occurrences_beyond_first": (
                "for each selected declaration, occurrences after its first use across input forms"
            ),
        },
    }


def main() -> int:
    arguments = parser().parse_args()
    canonical_report: Path | None = (
        arguments.canonical_report.resolve()
        if arguments.canonical_report is not None
        else None
    )
    if arguments.lean_timeout <= 0:
        parser().error("--lean-timeout must be positive")
    if arguments.model_timeout is not None and arguments.model_timeout <= 0:
        parser().error("--model-timeout must be positive")
    if arguments.model_max_tokens <= 0:
        parser().error("--model-max-tokens must be positive")
    if not 1 <= arguments.query_rounds <= MAX_INPUT_QUERY_ROUNDS:
        parser().error(f"--query-rounds must be in 1..{MAX_INPUT_QUERY_ROUNDS}")
    if not arguments.run_label.strip():
        parser().error("--run-label must be non-empty")

    output_root = arguments.output_root.resolve()
    try:
        prepare_fresh_output_root(output_root)
    except (OSError, ValueError) as error:
        print(json.dumps({"status": "FAILED", "error": str(error)}), flush=True)
        return 1

    report_path = output_root / "report.json"
    transcript_root = output_root / "transcripts"
    plan_root = output_root / "plans"
    artifact_path = output_root / "InputGroundingDeepSeekBatch.lean"
    lean_root = ROOT / "Lean"
    report: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "started_at": utc_now(),
        "status": "RUNNING",
        "run_label": arguments.run_label.strip(),
        "scope": {
            "suite_file": str(arguments.suite.resolve()),
            "real_deepseek": True,
            "existing_library_declarations_only": True,
            "llm_selects_problem_connection_route_and_lean_term": True,
            "full_catalogs_sent_to_model": False,
            "family_specific_agent_rules": None,
            "hidden_route_fixtures": False,
            "lean_during_model_tasks": False,
            "final_lean_processes_expected": 1,
            "standard_axiom_gate": True,
            "maximum_query_rounds_per_case": arguments.query_rounds,
        },
        "output_root": str(output_root),
        "cases": [],
    }

    def finish(status: str, *, exit_code: int, error: str | None = None) -> int:
        report["status"] = status
        report["finished_at"] = utc_now()
        if error is not None:
            report["error"] = error
        write_json(report_path, report)
        canonical_published = status == "VERIFIED" and canonical_report is not None
        if canonical_published:
            write_json(canonical_report, report)
        print(
            json.dumps(
                {
                    "status": status,
                    "run_label": report["run_label"],
                    "report": str(report_path),
                    "canonical_report": (
                        str(canonical_report) if canonical_report is not None else None
                    ),
                    "canonical_report_published": canonical_published,
                    "summary": report.get("summary"),
                    "error": error,
                },
                ensure_ascii=False,
                sort_keys=True,
            ),
            flush=True,
        )
        return exit_code

    try:
        suite = load_benchmark_suite(arguments.suite)
        cases = validate_observed_input_suite(suite)
        execution_cases = (
            counterbalanced_representation_cases(cases)
            if suite.id == REPRESENTATION_COMPARISON_SUITE_ID
            else tuple(cases)
        )
        toolchain = (lean_root / "lean-toolchain").read_text(encoding="utf-8").strip()
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
        reduction_catalogs = {
            mode: build_reduction_catalog(connection_catalog, mode=mode)
            for mode in sorted({case.catalog_mode for case in cases})
        }
        python_rule_audit = (
            audit_python_family_specific_rules(
                cases,
                routing_source_paths=STAGE_F_RULE_AUDIT_PATHS,
                benchmark_validation_paths=STAGE_F_BENCHMARK_VALIDATION_PATHS,
                display_root=ROOT,
            )
            if suite.id == REPRESENTATION_COMPARISON_SUITE_ID
            else None
        )
        catalog_scope = (
            representation_catalog_scope(reduction_catalogs)
            if suite.id == REPRESENTATION_COMPARISON_SUITE_ID
            else None
        )
    except (
        BenchmarkManifestError,
        ProblemCatalogError,
        ConnectionCatalogError,
        OSError,
        UnicodeError,
        ValueError,
        json.JSONDecodeError,
    ) as error:
        return finish(
            "FAILED",
            exit_code=1,
            error=f"真实模型运行前的离线快照检查失败：{error}",
        )

    report["scope"]["suite"] = suite.id
    report["scope"]["family_specific_agent_rules"] = (
        python_rule_audit["python_family_specific_rule_count"]
        if python_rule_audit is not None
        else 0
    )
    if python_rule_audit is not None:
        report["python_family_rule_audit"] = python_rule_audit
    if catalog_scope is not None:
        report["representation_catalog_scope"] = catalog_scope

    if canonical_report is None:
        canonical_report = (
            ROOT
            / "Benchmark"
            / "Hardness"
            / (
                "INPUT_GROUNDING_REPRESENTATION_COMPARISON_REPORT.json"
                if suite.id == REPRESENTATION_COMPARISON_SUITE_ID
                else "INPUT_GROUNDING_REPORT.json"
            )
        ).resolve()
    if suite.id == REPRESENTATION_COMPARISON_SUITE_ID and arguments.resume_report:
        return finish(
            "FAILED",
            exit_code=1,
            error=(
                "阶段 F 的正式全量验收禁止 --resume-report；36 个 case 必须全部发生"
                "本次真实 DeepSeek HTTP 调用。"
            ),
        )
    if (
        suite.id == REPRESENTATION_COMPARISON_SUITE_ID
        and catalog_scope is not None
        and catalog_scope["baseline_is_subset_of_component"] is not True
    ):
        return finish(
            "FAILED",
            exit_code=1,
            error=(
                "阶段 F component catalog 没有保留 flat_api 的全部可查询归约；"
                "为避免通过缩小定理范围制造结果，真实 API 调用已取消。"
            ),
        )
    if (
        suite.id == REPRESENTATION_COMPARISON_SUITE_ID
        and python_rule_audit is not None
        and python_rule_audit["python_family_specific_rule_count"] != 0
    ):
        return finish(
            "FAILED",
            exit_code=1,
            error=(
                "阶段 F 的静态审计发现生产规划路径含 family/case 特殊规则；"
                "真实 API 调用已取消。"
            ),
        )

    report["benchmark"] = {
        "suite_id": suite.id,
        "case_count": len(cases),
        "positive_count": sum(case.is_positive for case in cases),
        "negative_count": sum(not case.is_positive for case in cases),
        "case_ids": [case.id for case in cases],
        "execution_case_ids": [case.id for case in execution_cases],
        "execution_order_policy": (
            "matched-pair treatment order alternates flat-first/component-first"
            if suite.id == REPRESENTATION_COMPARISON_SUITE_ID
            else "suite order"
        ),
        "suite_file": str(arguments.suite.resolve()),
        "suite_sha256": sha256_file(arguments.suite.resolve()),
        "comparison_group_count": len(
            {
                getattr(case, "comparison_group_id", None)
                or case.matched_pair_id
                for case in cases
                if getattr(case, "comparison_group_id", None)
                or case.matched_pair_id
            }
        ),
    }
    report["catalogs"] = {
        "registry_fingerprint": problem_catalog.registry_fingerprint,
        "problem_catalog_id": problem_catalog.catalog_id,
        "problem_count": len(problem_catalog.entries),
        "connection_catalog_id": connection_catalog.catalog_id,
        "connection_count": len(connection_catalog.entries),
        "reduction_catalog_ids_by_mode": {
            mode: catalog.catalog_id
            for mode, catalog in sorted(reduction_catalogs.items())
        },
        "reduction_counts_by_mode": {
            mode: len(catalog.entries)
            for mode, catalog in sorted(reduction_catalogs.items())
        },
        "toolchain": toolchain,
        "lake_manifest_sha256": manifest_sha256,
    }
    if set(reduction_catalogs) == {"full"}:
        report["catalogs"]["reduction_catalog_id"] = reduction_catalogs[
            "full"
        ].catalog_id
        report["catalogs"]["reduction_count"] = len(
            reduction_catalogs["full"].entries
        )

    observation_cache: dict[tuple[str, str], LeanInputObservation] = {}

    def load_observation(module: str, declaration: str) -> LeanInputObservation:
        key = (module, declaration)
        cached = observation_cache.get(key)
        if cached is not None:
            return cached
        source_path = module_file(lean_root, module)
        snapshot_path = observation_snapshot_path(
            arguments.observation_root,
            module=module,
            declaration=declaration,
        )
        observation = load_input_observation_snapshot(
            snapshot_path,
            expected_input_module=module,
            expected_input_declaration=declaration,
            expected_input_module_sha256=sha256_file(source_path),
            expected_toolchain=toolchain,
            expected_lake_manifest_sha256=manifest_sha256,
            expected_registry_fingerprint=problem_catalog.registry_fingerprint,
        )
        observation_cache[key] = observation
        return observation

    prepared_cases: list[
        tuple[BenchmarkCase, LeanInputObservation, LeanInputObservation]
    ] = []
    try:
        for case in execution_cases:
            assert case.target is not None
            prepared_cases.append(
                (
                    case,
                    load_observation(case.module, case.effective_input_declaration),
                    load_observation(case.module, case.target),
                )
            )
    except (InputObservationError, OSError, UnicodeError, ValueError) as error:
        return finish(
            "FAILED",
            exit_code=1,
            error=f"输入观察快照无法在调用 DeepSeek 前通过校验：{error}",
        )

    try:
        reusable_rows, previous_report = reusable_resume_rows(
            arguments.resume_report,
            registry_fingerprint=problem_catalog.registry_fingerprint,
            problem_catalog_id=problem_catalog.catalog_id,
            connection_catalog_id=connection_catalog.catalog_id,
            reduction_catalog_ids={
                mode: catalog.catalog_id
                for mode, catalog in sorted(reduction_catalogs.items())
            },
        )
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as error:
        return finish("FAILED", exit_code=1, error=f"resume 报告校验失败：{error}")
    if arguments.resume_report is not None:
        report["resume"] = {
            "report": str(arguments.resume_report.resolve()),
            "candidate_case_count": len(reusable_rows),
            "previous_status": previous_report.get("status") if previous_report else None,
            "replay_requires_current_prompt_hash_match": True,
        }

    config = DeepSeekConfig.from_environment(env_file=arguments.env_file)
    config = replace(config, max_tokens=arguments.model_max_tokens)
    if arguments.model_timeout is not None:
        config = replace(config, timeout_seconds=arguments.model_timeout)
    report["model"] = config.to_public_dict()
    report["model"]["system_prompt_sha256"] = sha256_text(
        OBSERVED_INPUT_SYSTEM_PROMPT
    )
    if not config.api_key:
        return finish(
            "FAILED",
            exit_code=1,
            error="没有配置 DEEPSEEK_API_KEY，因此尚未发生真实 DeepSeek 调用。",
        )
    write_json(report_path, report)

    client = DeepSeekClient(config)
    rows: list[dict[str, Any]] = []
    artifacts: list[CertifiedPathArtifactCase] = []
    all_usages: list[Mapping[str, Any] | None] = []
    for index, (case, observation, target_observation) in enumerate(
        prepared_cases, start=1
    ):
        reduction_catalog = reduction_catalogs[case.catalog_mode]
        print(
            json.dumps(
                {
                    "phase": "deepseek_input_grounding",
                    "case": case.id,
                    "index": index,
                    "total": len(prepared_cases),
                },
                ensure_ascii=False,
                sort_keys=True,
            ),
            flush=True,
        )
        result: ObservedInputPlannerResult | None = None
        replayed = False
        resume_error: str | None = None
        previous_row = reusable_rows.get(case.id)
        if previous_row is not None:
            identity_matches = (
                previous_row.get("module") == case.module
                and previous_row.get("input_declaration")
                == case.effective_input_declaration
                and previous_row.get("target_declaration") == case.target
                and previous_row.get("catalog_mode", "full") == case.catalog_mode
                and previous_row.get("reduction_catalog_id")
                == reduction_catalog.catalog_id
                and previous_row.get("input_observation_id")
                == observation.observation_id
                and previous_row.get("target_observation_id")
                == target_observation.observation_id
                and previous_row.get("expected_status") == case.expected.final_status
                and previous_row.get("expected_failure_code")
                == case.expected.final_failure_code
            )
            prior_rounds = previous_row.get("model_rounds")
            if identity_matches and isinstance(prior_rounds, list):
                replay_client = ReplayModelClient(prior_rounds)
                replay_result = generate_lean_path_from_observed_input(
                    observation=observation,
                    target_observation=target_observation,
                    problem_catalog=problem_catalog,
                    connection_catalog=connection_catalog,
                    reduction_catalog=reduction_catalog,
                    client=replay_client,  # type: ignore[arg-type]
                    maximum_query_rounds=arguments.query_rounds,
                )
                if (
                    replay_client.error is None
                    and replay_client.index == len(prior_rounds)
                    and protocol_matches_expected(case, replay_result)
                ):
                    result = replay_result
                    replayed = True
                else:
                    resume_error = (
                        replay_client.error
                        or "replayed responses no longer satisfy the current protocol"
                    )
            else:
                resume_error = "resume case identity or observation fingerprint changed"

        if result is None:
            result = generate_lean_path_from_observed_input(
                observation=observation,
                target_observation=target_observation,
                problem_catalog=problem_catalog,
                connection_catalog=connection_catalog,
                reduction_catalog=reduction_catalog,
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
            replayed=replayed,
        )
        row = result_row(
            case=case,
            observation=observation,
            target_observation=target_observation,
            result=result,
            round_records=round_records,
            model_term=model_term,
            replayed=replayed,
            resume_error=resume_error,
            problem_catalog_id=problem_catalog.catalog_id,
            connection_catalog_id=connection_catalog.catalog_id,
            reduction_catalog=reduction_catalog,
        )
        row["execution_position"] = index
        if suite.id == REPRESENTATION_COMPARISON_SUITE_ID:
            row["matched_pair_execution_position"] = 1 if index % 2 == 1 else 2
        rows.append(row)
        for response in result.model_responses:
            all_usages.append(response.usage)
        if result.plan is not None:
            write_json(plan_root / f"{case.id}.json", result.plan.to_dict())
        if case.is_positive and result.protocol_accepted and result.lean_term is not None:
            artifacts.append(
                CertifiedPathArtifactCase(
                    case_id=case.id,
                    input_module=case.module,
                    source_declaration=case.effective_input_declaration,
                    target_declaration=case.target or "",
                    lean_term=result.lean_term,
                )
            )
        write_json(transcript_root / f"{case.id}.json", row)
        report["cases"] = rows
        report["progress"] = {
            "completed_cases": len(rows),
            "model_api_turns_this_run": sum(
                item["external_api_calls_this_run"] for item in rows
            ),
            "real_http_request_count_this_run": sum(
                item["http_request_attempts_this_run"] for item in rows
            ),
            "usage": aggregate_usage(all_usages),
        }
        write_json(report_path, report)

    final_command: Any | None = None
    artifact_source: str | None = None
    artifact_error: str | None = None
    if artifacts:
        try:
            artifact_source = build_certified_path_batch_artifact_source(artifacts)
            assert_generated_source_is_safe(artifact_source)
            artifact_path.write_text(artifact_source, encoding="utf-8")
        except (OSError, UnicodeError, ValueError) as error:
            artifact_error = str(error)
        else:
            print(
                json.dumps(
                    {
                        "phase": "final_lean_validation",
                        "status": "started",
                        "lean_process": 1,
                        "accepted_positive_terms": len(artifacts),
                    },
                    ensure_ascii=False,
                    sort_keys=True,
                ),
                flush=True,
            )
            final_command = run_command(
                ["lake", "env", "lean", str(artifact_path.resolve())],
                cwd=lean_root,
                timeout_seconds=arguments.lean_timeout,
                output_limit=128 * 1024,
            )

    report["artifact"] = {
        "path": str(artifact_path),
        "generated": artifact_source is not None,
        "generation_error": artifact_error,
        "sha256": sha256_text(artifact_source) if artifact_source is not None else None,
        "accepted_positive_case_count": len(artifacts),
        "assert_standard_axioms_count": (
            artifact_source.count("assert_standard_axioms")
            if artifact_source is not None
            else 0
        ),
    }
    report["lean"] = {
        "process_count": 1 if final_command is not None else 0,
        "started_after_all_model_tasks": final_command is not None,
        "command": command_record(final_command) if final_command is not None else None,
        "not_started_reason": (
            None
            if final_command is not None
            else artifact_error
            or "没有任何通过协议的正例 Lean term 可供统一验证"
        ),
    }

    lean_ok = bool(final_command is not None and final_command.ok)
    for case, row in zip(cases, rows, strict=True):
        if case.is_positive:
            if row["protocol_accepted"] and lean_ok:
                row["final_status"] = "VERIFIED"
                row["final_failure_code"] = None
                row["final_explanation"] = (
                    "模型提交的路径已与其他正例一起通过唯一一次最终 Lean elaboration "
                    "和标准公理检查。"
                )
            elif row["protocol_accepted"]:
                row["final_status"] = "FAILED"
                row["final_failure_code"] = "final_lean_artifact_failed"
                row["final_explanation"] = (
                    "模型回答通过了非 Lean 协议检查，但合并后的最终 Lean artifact "
                    "没有通过 elaboration 或标准公理检查。"
                )
            else:
                row["final_status"] = "FAILED"
                row["final_failure_code"] = row["failure_code"] or "model_protocol_failed"
                row["final_explanation"] = (
                    "模型没有在有限查询会话中提交一条通过问题匹配、方向、检索来源和 "
                    "Lean term 静态检查的完整路径。具体原因：" + row["explanation"]
                )
        elif row["protocol_matches_expected"]:
            row["final_status"] = "BLOCKED"
            row["final_failure_code"] = row["failure_code"]
            row["final_explanation"] = row["explanation"]
        elif row["protocol_accepted"]:
            row["final_status"] = "FAILED"
            row["final_failure_code"] = "negative_case_unexpectedly_accepted"
            row["final_explanation"] = (
                "该负例本应因缺少合法输入表示或已有有向路线而拒绝，但模型提交被协议 "
                "接受；因此本次结果不符合 benchmark。"
            )
        else:
            row["final_status"] = "FAILED"
            row["final_failure_code"] = row["failure_code"] or "wrong_negative_failure"
            row["final_explanation"] = (
                "该负例确实没有生成证明，但失败原因与 Lean 观察和目录事实规定的预期 "
                "原因不同。具体原因：" + row["explanation"]
            )
        write_json(transcript_root / f"{case.id}.json", row)

    action_totals: Counter[str] = Counter()
    candidate_totals: Counter[str] = Counter()
    for row in rows:
        action_totals.update(row["query_action_counts"])
        candidate_totals.update(row["candidate_counts"])
    usage = aggregate_usage(all_usages)
    positive_protocol = sum(
        row["protocol_accepted"]
        for row in rows
        if row["expected_status"] == "VERIFIED"
    )
    positive_verified = sum(row["final_status"] == "VERIFIED" for row in rows)
    negative_correct = sum(
        row["expected_status"] == "BLOCKED"
        and row["final_status"] == "BLOCKED"
        and row["final_failure_code"] == row["expected_failure_code"]
        for row in rows
    )
    wrong_problem_matches = sum(
        bool(row["protocol_accepted"] and row["problem_match"] is None)
        for row in rows
        if row["expected_status"] == "VERIFIED"
    )
    unretrieved_uses = sum(
        row["failure_code"] in UNRETRIEVED_FAILURE_CODES for row in rows
    )
    prompt_leak_count = sum(len(row["prompt_key_leaks"]) for row in rows)
    term_changes = sum(row["model_term_changed_by_agent"] for row in rows)
    http_calls = sum(row["external_api_calls_this_run"] for row in rows)
    http_ok = sum(row["http_ok_count_this_run"] for row in rows)
    expected_positive = sum(case.is_positive for case in cases)
    expected_negative = len(cases) - expected_positive
    base_thresholds_met = (
        len(rows) == len(cases)
        and positive_protocol == expected_positive
        and positive_verified == expected_positive
        and negative_correct == expected_negative
        and wrong_problem_matches == 0
        and unretrieved_uses == 0
        and prompt_leak_count == 0
        and term_changes == 0
        and report["lean"]["process_count"] == 1
        and http_calls == http_ok
    )
    python_rule_counts_by_family: dict[str, int] = {}
    if python_rule_audit is not None:
        python_rule_counts_by_family = {
            str(row["study_family"]): int(
                row["python_family_specific_rule_count"]
            )
            for row in python_rule_audit["families"]
        }
    comparison_metrics = (
        build_representation_comparison_metrics(
            rows,
            python_rule_counts_by_family=python_rule_counts_by_family,
        )
        if suite.id == REPRESENTATION_COMPARISON_SUITE_ID
        else None
    )
    catalog_mode_summaries: dict[str, Any] = {}
    for mode in sorted({str(row["catalog_mode"]) for row in rows}):
        mode_rows = [row for row in rows if row["catalog_mode"] == mode]
        mode_usage = aggregate_usage(row.get("usage") for row in mode_rows)
        verified_count = sum(row["final_status"] == "VERIFIED" for row in mode_rows)
        catalog_mode_summaries[mode] = {
            "case_count": len(mode_rows),
            "lean_verified_count": verified_count,
            "lean_verified_rate": (
                verified_count / len(mode_rows) if mode_rows else None
            ),
            "query_round_count": sum(row["query_round_count"] for row in mode_rows),
            "average_query_round_count": (
                sum(row["query_round_count"] for row in mode_rows) / len(mode_rows)
                if mode_rows
                else None
            ),
            "model_turn_count": sum(row["model_turn_count"] for row in mode_rows),
            "prompt_characters": sum(row["prompt_characters"] for row in mode_rows),
            "usage": mode_usage,
        }
    fresh_real_case_count = sum(
        bool(row["called_this_run"] and not row["replayed_from_resume"])
        for row in rows
    )
    missing_usage_case_count = sum(
        not (
            isinstance(row.get("usage"), Mapping)
            and all(
                _integer_metric(
                    row["usage"].get(field),
                    positive=field
                    in {"prompt_tokens", "completion_tokens", "total_tokens"},
                )
                for field in STAGE_F_REQUIRED_USAGE_METRICS
            )
        )
        for row in rows
        if row["external_api_calls_this_run"] > 0
    )
    missing_usage_round_count = sum(
        not (
            isinstance(round_row.get("usage"), Mapping)
            and all(
                _integer_metric(
                    round_row["usage"].get(field),
                    positive=field
                    in {"prompt_tokens", "completion_tokens", "total_tokens"},
                )
                for field in STAGE_F_REQUIRED_USAGE_METRICS
            )
        )
        for row in rows
        for round_row in row.get("model_rounds", [])
        if isinstance(round_row, Mapping) and round_row.get("called") is True
    )
    stage_f_contract_errors: tuple[str, ...] = ()
    first_treatment_counts: Counter[str] = Counter()
    if comparison_metrics is not None:
        assert python_rule_audit is not None
        assert catalog_scope is not None
        stage_f_contract_errors = validate_representation_comparison_report_contract(
            rows,
            comparison_metrics=comparison_metrics,
            python_rule_audit=python_rule_audit,
            catalog_scope=catalog_scope,
        )
        first_treatment_counts.update(
            str(row["catalog_mode"])
            for row in rows
            if row.get("matched_pair_execution_position") == 1
        )
    if comparison_metrics is not None:
        stage_thresholds_met = (
            base_thresholds_met
            and len(rows) == 36
            and expected_positive == 36
            and expected_negative == 0
            and comparison_metrics["matched_comparison_count"] == 18
            and comparison_metrics["both_lean_verified_count"] == 18
            and fresh_real_case_count == 36
            and sum(row["replayed_from_resume"] for row in rows) == 0
            and len(comparison_metrics["families"]) == 3
            and all(
                family["python_family_specific_rule_count"] == 0
                for family in comparison_metrics["families"]
            )
            and all(row["prompt_characters"] > 0 for row in rows)
            and all(row["query_round_count"] > 0 for row in rows)
            and missing_usage_case_count == 0
            and missing_usage_round_count == 0
            and not stage_f_contract_errors
            and dict(first_treatment_counts)
            == {
                STAGE_F_BASELINE_CATALOG_MODE: 9,
                STAGE_F_COMPONENT_CATALOG_MODE: 9,
            }
            and set(catalog_mode_summaries)
            == set(REPRESENTATION_COMPARISON_CATALOG_MODES)
            and set(comparison_metrics["selected_declaration_reuse_by_mode"])
            == set(REPRESENTATION_COMPARISON_CATALOG_MODES)
        )
    else:
        stage_thresholds_met = base_thresholds_met
    report["cases"] = rows
    if comparison_metrics is not None:
        report["representation_comparison"] = comparison_metrics
        report["representation_comparison_contract"] = {
            "schema_version": "hardness_representation_comparison_report_contract_v1",
            "ok": not stage_f_contract_errors,
            "error_count": len(stage_f_contract_errors),
            "errors": list(stage_f_contract_errors),
            "first_treatment_counts": dict(sorted(first_treatment_counts.items())),
        }
    report["catalog_mode_summaries"] = catalog_mode_summaries
    report["summary"] = {
        "case_count": len(rows),
        "positive_protocol_accepted": positive_protocol,
        "positive_lean_verified": positive_verified,
        "negative_correctly_rejected": negative_correct,
        "wrong_problem_matches": wrong_problem_matches,
        "unretrieved_declaration_use_failures": unretrieved_uses,
        "model_term_normalization_count": term_changes,
        "family_specific_agent_rules": (
            python_rule_audit["python_family_specific_rule_count"]
            if python_rule_audit is not None
            else 0
        ),
        "family_specific_prompt_rules": (
            python_rule_audit["python_family_specific_rule_count"]
            if python_rule_audit is not None
            else 0
        ),
        "hidden_route_fixture_count": 0,
        "prompt_key_leak_count": prompt_leak_count,
        "model_turn_count": sum(row["model_turn_count"] for row in rows),
        "model_api_turn_count_this_run": http_calls,
        "successful_model_api_turn_count_this_run": http_ok,
        "real_http_request_count_this_run": sum(
            row["http_request_attempts_this_run"] for row in rows
        ),
        "fresh_real_api_case_count": fresh_real_case_count,
        "missing_usage_case_count": missing_usage_case_count,
        "missing_usage_round_count": missing_usage_round_count,
        "stage_f_contract_error_count": len(stage_f_contract_errors),
        "replayed_case_count": sum(row["replayed_from_resume"] for row in rows),
        "protocol_feedback_count": sum(row["protocol_feedback_count"] for row in rows),
        "query_action_counts": dict(sorted(action_totals.items())),
        "candidate_counts": dict(sorted(candidate_totals.items())),
        "prompt_characters": sum(row["prompt_characters"] for row in rows),
        "usage": usage,
        "prompt_cache_hit_tokens": usage.get("prompt_cache_hit_tokens", 0),
        "prompt_cache_miss_tokens": usage.get("prompt_cache_miss_tokens", 0),
        "lean_process_count": report["lean"]["process_count"],
        "artifact_sha256": report["artifact"]["sha256"],
        "all_stage_e_thresholds_met": (
            stage_thresholds_met
            if suite.id != REPRESENTATION_COMPARISON_SUITE_ID
            else None
        ),
        "all_stage_f_thresholds_met": (
            stage_thresholds_met
            if suite.id == REPRESENTATION_COMPARISON_SUITE_ID
            else None
        ),
    }
    if stage_thresholds_met:
        return finish("VERIFIED", exit_code=0)

    stage_name = "阶段 F" if comparison_metrics is not None else "阶段 E"
    pair_detail = (
        f"，matched comparison 双边通过 "
        f"{comparison_metrics['both_lean_verified_count']}/18"
        if comparison_metrics is not None
        else ""
    )
    failure = (
        f"{stage_name} 本次全量运行未达到验收门槛："
        f"正例协议接受 {positive_protocol}/{expected_positive}，最终 Lean 通过 "
        f"{positive_verified}/{expected_positive}，负例正确拒绝 "
        f"{negative_correct}/{expected_negative}，模型 API turn 成功 {http_ok}/{http_calls}"
        f"{pair_detail}，最终 Lean 进程数 {report['lean']['process_count']}。"
    )
    return finish("FAILED", exit_code=1, error=failure)


if __name__ == "__main__":
    raise SystemExit(main())
