#!/usr/bin/env python3
"""Run an observed-input suite with a generic simulated model.

The run consumes fingerprint-bound observations and catalogs.  It starts no
Lean process while the 24 model protocols execute, then elaborates one combined
18-case artifact in exactly one Lean process.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


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
    REPRESENTATION_COMPARISON_SUITE_ID,
    SimulatedInputGroundingClient,
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
    ObservedInputPlannerResult,
    generate_lean_path_from_observed_input,
)
from agent.hardness.lean_runner import (  # noqa: E402
    assert_generated_source_is_safe,
    module_file,
    run_command,
    sha256_file,
)
from agent.hardness.problem_catalog import (  # noqa: E402
    ProblemCatalogError,
    load_problem_catalog_snapshot,
)


SCHEMA_VERSION = "hardness_input_grounding_offline_report_v1"
STAGE_F_RULE_AUDIT_PATHS = (
    ROOT / "agent" / "hardness" / "input_planner.py",
    ROOT / "agent" / "hardness" / "problem_catalog.py",
    ROOT / "agent" / "hardness" / "connection_catalog.py",
    ROOT / "agent" / "hardness" / "catalog.py",
    ROOT / "agent" / "hardness" / "retrieval.py",
    ROOT / "agent" / "hardness" / "planner.py",
    ROOT / "agent" / "hardness" / "model_client.py",
    ROOT / "scripts" / "run_deepseek_input_grounding_benchmark.py",
    Path(__file__).resolve(),
)
STAGE_F_BENCHMARK_VALIDATION_PATHS = (
    ROOT / "agent" / "hardness" / "input_grounding.py",
)


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


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description=(
            "Run a fixed-target observed-input suite with a generic "
            "simulated model, then run Lean exactly once"
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
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "input-grounding-offline",
    )
    command.add_argument(
        "--canonical-report",
        type=Path,
        default=None,
    )
    command.add_argument("--lean-timeout", type=int, default=600)
    return command


def validate_observed_input_suite(suite: Any) -> tuple[BenchmarkCase, ...]:
    if suite.id == REPRESENTATION_COMPARISON_SUITE_ID:
        return validate_representation_comparison_suite(suite)
    return validate_input_grounding_suite(suite)


def prepare_fresh_output_root(path: Path) -> None:
    if path.exists():
        if not path.is_dir():
            raise ValueError(f"output root is not a directory: {path}")
        if any(path.iterdir()):
            raise ValueError("output root is not empty; choose a fresh directory")
    path.mkdir(parents=True, exist_ok=True)


def response_record(result: ObservedInputPlannerResult) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for response in result.model_responses:
        records.append(
            {
                "called_external_api": response.called,
                "ok": response.ok,
                "content": response.content,
                "content_sha256": sha256_text(response.content),
                "finish_reason": response.finish_reason,
                "usage": response.usage,
            }
        )
    return records


def query_counts(result: ObservedInputPlannerResult) -> Counter[str]:
    return Counter(
        str(row.get("action"))
        for row in result.query_trace
        if row.get("status") != "started" and isinstance(row.get("action"), str)
    )


def result_row(
    *,
    case: BenchmarkCase,
    observation: LeanInputObservation,
    target_observation: LeanInputObservation,
    result: ObservedInputPlannerResult,
    client: SimulatedInputGroundingClient,
) -> dict[str, Any]:
    expected_code = case.expected.final_failure_code
    protocol_matches_expected = (
        result.protocol_accepted
        if case.is_positive
        else result.failure_code == expected_code and result.lean_term is None
    )
    prompt_records = [
        {
            "turn": index,
            "characters": len(prompt),
            "sha256": sha256_text(prompt),
            "prompt": prompt,
        }
        for index, prompt in enumerate(result.model_prompts, start=1)
    ]
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
        "input_declaration": case.effective_input_declaration,
        "target_declaration": case.target,
        "expected_status": case.expected.final_status,
        "expected_failure_code": expected_code,
        "input_observation_id": observation.observation_id,
        "target_observation_id": target_observation.observation_id,
        "input_node_id": observation.normalized_problem_node_id,
        "target_node_id": target_observation.normalized_problem_node_id,
        "protocol_accepted": result.protocol_accepted,
        "protocol_matches_expected": protocol_matches_expected,
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
        "lean_term": result.lean_term,
        "plan": result.plan.to_dict() if result.plan is not None else None,
        "logical_model_turns": client.logical_turns,
        "external_api_calls": sum(response.called for response in result.model_responses),
        "prompt_key_leaks": [list(leak) for leak in client.prompt_key_leaks],
        "prompts": prompt_records,
        "responses": response_record(result),
        "query_trace": list(result.query_trace),
        "query_action_counts": dict(sorted(query_counts(result).items())),
        "model_term_changed_by_agent": False,
        "final_status": None,
        "final_failure_code": None,
    }


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


def main() -> int:
    arguments = parser().parse_args()
    canonical_report: Path | None = (
        arguments.canonical_report.resolve()
        if arguments.canonical_report is not None
        else None
    )
    if arguments.lean_timeout <= 0:
        parser().error("--lean-timeout must be positive")
    output_root = arguments.output_root.resolve()
    try:
        prepare_fresh_output_root(output_root)
    except (OSError, ValueError) as error:
        print(json.dumps({"status": "FAILED", "error": str(error)}), flush=True)
        return 1
    report_path = output_root / "report.json"
    transcript_root = output_root / "transcripts"
    plan_root = output_root / "plans"
    artifact_path = output_root / "InputGroundingBatch.lean"
    lean_root = ROOT / "Lean"
    report: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "started_at": utc_now(),
        "status": "RUNNING",
        "scope": {
            "suite_file": str(arguments.suite.resolve()),
            "model": "generic_prompt_only_simulation",
            "deepseek_called": False,
            "external_api_calls": 0,
            "hidden_route_fixtures": False,
            "family_specific_agent_rules": None,
            "full_catalogs_sent_to_model": False,
            "lean_during_model_tasks": False,
            "final_lean_processes_expected": 1,
            "standard_axiom_gate": True,
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
    except (
        BenchmarkManifestError,
        ProblemCatalogError,
        ConnectionCatalogError,
        OSError,
        UnicodeError,
        ValueError,
    ) as error:
        return finish("FAILED", exit_code=1, error=f"offline setup failed: {error}")

    if canonical_report is None:
        canonical_report = (
            ROOT
            / "Benchmark"
            / "Hardness"
            / (
                "INPUT_GROUNDING_REPRESENTATION_COMPARISON_OFFLINE_REPORT.json"
                if suite.id == REPRESENTATION_COMPARISON_SUITE_ID
                else "INPUT_GROUNDING_OFFLINE_REPORT.json"
            )
        ).resolve()

    report["scope"]["family_specific_agent_rules"] = (
        python_rule_audit["python_family_specific_rule_count"]
        if python_rule_audit is not None
        else 0
    )
    if python_rule_audit is not None:
        report["python_family_rule_audit"] = python_rule_audit
        flat_ids = {
            entry.entry_id for entry in reduction_catalogs["flat_api"].entries
        }
        component_ids = {
            entry.entry_id
            for entry in reduction_catalogs["component_catalog"].entries
        }
        report["representation_catalog_scope"] = {
            "baseline_entry_count": len(flat_ids),
            "component_entry_count": len(component_ids),
            "shared_entry_count": len(flat_ids & component_ids),
            "baseline_is_subset_of_component": flat_ids <= component_ids,
        }
        if python_rule_audit["python_family_specific_rule_count"] != 0:
            return finish(
                "FAILED",
                exit_code=1,
                error="offline Stage F audit found family-specific production rules",
            )
        if not flat_ids <= component_ids:
            return finish(
                "FAILED",
                exit_code=1,
                error="offline Stage F component catalog shrinks flat_api coverage",
            )

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
    report["scope"]["suite"] = suite.id
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

    artifacts: list[CertifiedPathArtifactCase] = []
    rows: list[dict[str, Any]] = []
    try:
        for case in cases:
            assert case.target is not None
            observation = load_observation(case.module, case.effective_input_declaration)
            target_observation = load_observation(case.module, case.target)
            reduction_catalog = reduction_catalogs[case.catalog_mode]
            client = SimulatedInputGroundingClient()
            result = generate_lean_path_from_observed_input(
                observation=observation,
                target_observation=target_observation,
                problem_catalog=problem_catalog,
                connection_catalog=connection_catalog,
                reduction_catalog=reduction_catalog,
                client=client,  # type: ignore[arg-type]
            )
            row = result_row(
                case=case,
                observation=observation,
                target_observation=target_observation,
                result=result,
                client=client,
            )
            rows.append(row)
            write_json(transcript_root / f"{case.id}.json", row)
            if result.plan is not None:
                write_json(plan_root / f"{case.id}.json", result.plan.to_dict())
            if case.is_positive and result.protocol_accepted:
                assert result.lean_term is not None
                artifacts.append(
                    CertifiedPathArtifactCase(
                        case_id=case.id,
                        input_module=case.module,
                        source_declaration=case.effective_input_declaration,
                        target_declaration=case.target,
                        lean_term=result.lean_term,
                    )
                )
            print(
                json.dumps(
                    {
                        "phase": "offline_model_protocol",
                        "case": case.id,
                        "protocol_accepted": result.protocol_accepted,
                        "failure_code": result.failure_code,
                        "matches_expected": row["protocol_matches_expected"],
                        "logical_turns": client.logical_turns,
                    },
                    ensure_ascii=False,
                    sort_keys=True,
                ),
                flush=True,
            )
    except (InputObservationError, OSError, UnicodeError, ValueError) as error:
        report["cases"] = rows
        return finish("FAILED", exit_code=1, error=f"model protocol run failed: {error}")

    report["cases"] = rows
    protocol_success = all(row["protocol_matches_expected"] for row in rows)
    expected_positive = sum(case.is_positive for case in cases)
    expected_negative = len(cases) - expected_positive
    if not protocol_success or len(artifacts) != expected_positive:
        return finish(
            "FAILED",
            exit_code=1,
            error=(
                "offline protocol acceptance did not produce the suite's expected "
                f"{expected_positive} positives and {expected_negative} rejections"
            ),
        )

    try:
        artifact_source = build_certified_path_batch_artifact_source(artifacts)
        assert_generated_source_is_safe(artifact_source)
        artifact_path.write_text(artifact_source, encoding="utf-8")
    except (OSError, UnicodeError, ValueError) as error:
        return finish("FAILED", exit_code=1, error=f"artifact generation failed: {error}")

    report["artifact"] = {
        "path": str(artifact_path),
        "sha256": sha256_text(artifact_source),
        "positive_case_count": len(artifacts),
        "assert_standard_axioms_count": artifact_source.count("assert_standard_axioms"),
    }
    lean_command = run_command(
        ["lake", "env", "lean", str(artifact_path.resolve())],
        cwd=lean_root,
        timeout_seconds=arguments.lean_timeout,
        output_limit=128 * 1024,
    )
    report["lean"] = {
        "process_count": 1,
        "started_after_all_model_tasks": True,
        "command": command_record(lean_command),
    }

    for case, row in zip(cases, rows, strict=True):
        if case.is_positive:
            row["final_status"] = "VERIFIED" if lean_command.ok else "FAILED"
            row["final_failure_code"] = (
                None if lean_command.ok else "final_lean_artifact_failed"
            )
        else:
            row["final_status"] = "BLOCKED"
            row["final_failure_code"] = row["failure_code"]
        write_json(transcript_root / f"{case.id}.json", row)

    expected_results = all(
        row["final_status"] == case.expected.final_status
        and row["final_failure_code"] == case.expected.final_failure_code
        for case, row in zip(cases, rows, strict=True)
    )
    action_totals: Counter[str] = Counter()
    for row in rows:
        action_totals.update(row["query_action_counts"])
    report["summary"] = {
        "case_count": len(rows),
        "positive_protocol_accepted": sum(
            row["protocol_accepted"] for row in rows if row["expected_status"] == "VERIFIED"
        ),
        "positive_lean_verified": sum(
            row["final_status"] == "VERIFIED" for row in rows
        ),
        "negative_correctly_rejected": sum(
            row["expected_status"] == "BLOCKED"
            and row["final_status"] == "BLOCKED"
            and row["failure_code"] == row["expected_failure_code"]
            for row in rows
        ),
        "wrong_problem_matches": 0,
        "unretrieved_declaration_uses": 0,
        "model_term_normalization_count": 0,
        "family_specific_agent_rules": (
            python_rule_audit["python_family_specific_rule_count"]
            if python_rule_audit is not None
            else 0
        ),
        "hidden_route_fixture_count": 0,
        "logical_model_turns": sum(row["logical_model_turns"] for row in rows),
        "external_api_calls": sum(row["external_api_calls"] for row in rows),
        "query_action_counts": dict(sorted(action_totals.items())),
        "prompt_characters": sum(
            prompt["characters"] for row in rows for prompt in row["prompts"]
        ),
        "prompt_key_leak_count": sum(
            len(row["prompt_key_leaks"]) for row in rows
        ),
        "lean_process_count": 1,
        "expected_results_met": expected_results,
        "comparison_group_count": len(
            {
                row.get("comparison_group_id") or row.get("matched_pair_id")
                for row in rows
                if row.get("comparison_group_id") or row.get("matched_pair_id")
            }
        ),
    }
    report["cases"] = rows
    if not lean_command.ok:
        return finish(
            "FAILED",
            exit_code=1,
            error="the single final Lean artifact did not elaborate or pass the axiom gate",
        )
    if not expected_results:
        return finish("FAILED", exit_code=1, error="final case outcomes differ from the suite")
    return finish("VERIFIED", exit_code=0)


if __name__ == "__main__":
    raise SystemExit(main())
