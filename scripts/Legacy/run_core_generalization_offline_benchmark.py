#!/usr/bin/env python3
"""Run the complete Stage-L suite with the prompt-only model double."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import time
from collections import Counter
from collections.abc import Mapping, Sequence
from datetime import datetime, timezone
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
    core_generalization_report_skeleton,
    validate_core_generalization_suite,
)
from agent.hardness.core_generalization_planner import (  # noqa: E402
    CoreGeneralizationRequest,
    audit_core_generalization_prompt,
    generate_core_generalization_evidence,
)
from agent.hardness.core_generalization_simulation import (  # noqa: E402
    SimulatedCoreGeneralizationClient,
)
from agent.hardness.hardness_target_catalog import (  # noqa: E402
    load_hardness_target_catalog_snapshot,
)
from agent.hardness.input_grounding import observation_snapshot_path  # noqa: E402
from agent.hardness.input_observation import (  # noqa: E402
    LeanInputObservation,
    load_input_observation_snapshot,
)
from agent.hardness.lean_runner import (  # noqa: E402
    assert_generated_source_is_safe,
    module_file,
    run_command,
    sha256_file,
)
from agent.hardness.problem_catalog import load_problem_catalog_snapshot  # noqa: E402
from scripts.run_deepseek_open_target_benchmark import (  # noqa: E402
    completed_action_counts,
)


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description="Run all 16 Stage-L cases without external API calls"
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
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "core-generalization-offline",
    )
    command.add_argument(
        "--report",
        type=Path,
        default=ROOT / "Reports" / "CORE_GENERALIZATION_OFFLINE_REPORT.json",
    )
    command.add_argument("--lean-timeout", type=int, default=1200)
    return command


def request_for_case(case: BenchmarkCase) -> CoreGeneralizationRequest:
    if case.maximum_route_atoms is None or case.maximum_dependencies is None:
        raise ValueError(f"case {case.id} has no frozen Stage-L route bounds")
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


def expected_protocol(case: BenchmarkCase, result: Any) -> bool:
    if case.is_positive:
        return bool(result.protocol_accepted and result.plan and result.lean_term)
    return bool(
        result.plan is None
        and result.lean_term is None
        and result.failure_code == case.expected.final_failure_code
    )


def submitted_objective_term(
    responses: Sequence[Any], objective: str
) -> str | None:
    field = {
        "prove_in_np": "membership_lean_term",
        "prove_np_complete": "completeness_lean_term",
    }.get(objective, "lean_term")
    for response in reversed(responses):
        try:
            payload = json.loads(response.content)
        except (AttributeError, json.JSONDecodeError):
            continue
        if isinstance(payload, Mapping) and payload.get("action") == "finish":
            value = payload.get(field)
            return value if isinstance(value, str) else None
    return None


def reduction_entry_ids(result: Any) -> tuple[str, ...]:
    if result.plan is None or not result.plan.outputs:
        return ()
    raw = result.plan.outputs[0].metadata.get("reduction_entry_ids", [])
    if not isinstance(raw, list):
        return ()
    return tuple(item for item in raw if isinstance(item, str))


def artifact_case(
    case: BenchmarkCase,
    observation: LeanInputObservation,
    result: Any,
) -> CoreGeneralizationArtifactCase:
    if result.plan is None or result.lean_term is None:
        raise ValueError(f"case {case.id} has no accepted objective evidence")
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


def grouped_metrics(
    rows: Sequence[Mapping[str, Any]], cases: Sequence[BenchmarkCase]
) -> dict[str, Any]:
    case_by_id = {case.id: case for case in cases}
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
            case = case_by_id[str(row["id"])]
            buckets.setdefault(selector(case), []).append(row)
        grouped[dimension] = {
            key: {
                "case_count": len(bucket),
                "protocol_expected_count": sum(
                    row.get("protocol_matches_expected") is True for row in bucket
                ),
                "verified_or_correctly_blocked_count": sum(
                    row.get("final_status") in {"VERIFIED", "BLOCKED"}
                    for row in bucket
                ),
                "model_turn_count": sum(
                    int(row.get("model_turn_count") or 0) for row in bucket
                ),
            }
            for key, bucket in sorted(buckets.items())
        }
    return grouped


def main() -> int:
    args = parser().parse_args()
    started = time.monotonic()
    if args.output_root.exists():
        print(f"refusing to reuse existing output root: {args.output_root}", file=sys.stderr)
        return 2
    args.output_root.mkdir(parents=True)
    plans_root = args.output_root / "plans"
    transcripts_root = args.output_root / "transcripts"
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

    input_path = module_file(lean_root, cases[0].module)
    input_sha256 = sha256_file(input_path)
    observation_cache: dict[str, LeanInputObservation] = {}

    def load_observation(declaration: str) -> LeanInputObservation:
        cached = observation_cache.get(declaration)
        if cached is not None:
            return cached
        snapshot = observation_snapshot_path(
            args.snapshots_root / "observations",
            module=cases[0].module,
            declaration=declaration,
        )
        loaded = load_input_observation_snapshot(
            snapshot,
            expected_input_module=cases[0].module,
            expected_input_declaration=declaration,
            expected_input_module_sha256=input_sha256,
            expected_toolchain=toolchain,
            expected_lake_manifest_sha256=manifest_sha256,
            expected_registry_fingerprint=fingerprint,
        )
        observation_cache[declaration] = loaded
        return loaded

    rows: list[dict[str, Any]] = []
    artifacts: list[CoreGeneralizationArtifactCase] = []
    prompt_errors: list[dict[str, Any]] = []
    for index, case in enumerate(cases, start=1):
        observation = load_observation(case.effective_input_declaration)
        target_observation = load_observation(case.target) if case.target else None
        result = generate_core_generalization_evidence(
            observation=observation,
            target_observation=target_observation,
            problem_catalog=problem_catalog,
            connection_catalog=connection_catalog,
            reduction_catalog=reduction_catalog,
            native_evidence_catalog=native_evidence_catalog,
            hardness_target_catalog=hardness_target_catalog,
            request=request_for_case(case),
            client=SimulatedCoreGeneralizationClient(),  # type: ignore[arg-type]
            maximum_model_turns=int(case.resources.get("max_model_calls", 14)),
        )
        for turn, prompt in enumerate(result.model_prompts, start=1):
            try:
                payload = json.loads(prompt)
                if not isinstance(payload, dict):
                    raise ValueError("prompt is not one JSON object")
                audit_core_generalization_prompt(payload)
            except (json.JSONDecodeError, ValueError) as error:
                prompt_errors.append(
                    {"case_id": case.id, "turn": turn, "error": str(error)}
                )
        protocol_ok = expected_protocol(case, result)
        entry_ids = reduction_entry_ids(result)
        atom_count = len(entry_ids) + int(result.selected_connection is not None)
        model_term = submitted_objective_term(result.model_responses, case.objective)
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
            "protocol_accepted": result.protocol_accepted,
            "protocol_matches_expected": protocol_ok,
            "failure_code": result.failure_code,
            "explanation": result.explanation,
            "problem_match": result.problem_match.to_dict() if result.problem_match else None,
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
            "submitted_model_term": model_term,
            "model_term_changed_by_agent": (
                model_term != result.lean_term
                if model_term is not None and result.lean_term is not None
                else None
            ),
            "model_turn_count": len(result.model_responses),
            "query_action_counts": completed_action_counts(result.query_trace),
            "prompt_oracle_errors": [],
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
        rows.append(row)
        write_json(
            transcripts_root / f"{case.id}.json",
            {
                **row,
                "prompts": list(result.model_prompts),
                "responses": [response.content for response in result.model_responses],
                "query_trace": list(result.query_trace),
            },
        )
        if result.plan is not None:
            write_json(plans_root / f"{case.id}.json", result.plan.to_dict())
        if case.is_positive and result.protocol_accepted:
            artifacts.append(artifact_case(case, observation, result))

    artifact_source = build_core_generalization_batch_artifact_source(artifacts)
    assert_generated_source_is_safe(artifact_source)
    artifact_path = args.output_root / "CoreGeneralizationBatch.lean"
    artifact_path.write_text(artifact_source, encoding="utf-8")
    lean = run_command(
        ["lake", "env", "lean", str(artifact_path.resolve())],
        cwd=lean_root,
        timeout_seconds=args.lean_timeout,
        output_limit=256 * 1024,
    )
    accepted_ids = {artifact.case_id for artifact in artifacts}
    for row in rows:
        if row["id"] in accepted_ids:
            row["final_status"] = "VERIFIED" if lean.ok else "FAILED"

    positives = [row for row in rows if row["expected_status"] == "VERIFIED"]
    negatives = [row for row in rows if row["expected_status"] == "BLOCKED"]
    repeated_searches = sum(
        int(row["query_action_counts"].get("repeated_reduction_search", 0))
        for row in rows
    )
    thresholds = bool(
        len(rows) == 16
        and len(positives) == 8
        and len(negatives) == 8
        and len(artifacts) == 8
        and all(row["protocol_matches_expected"] for row in rows)
        and all(row["final_status"] == "VERIFIED" for row in positives)
        and all(row["final_status"] == "BLOCKED" for row in negatives)
        and all(row["model_term_changed_by_agent"] is False for row in positives)
        and lean.ok
        and not prompt_errors
        and repeated_searches == 0
        and artifact_source.count("assert_standard_axioms") == 1
        and artifact_source.count("noncomputable def nativeMembership") == 1
        and artifact_source.count("noncomputable def nativeCompleteness") == 1
    )

    report = core_generalization_report_skeleton(offline=True)
    report.update(
        {
            "generated_at": utc_now(),
            "status": "VERIFIED" if thresholds else "FAILED",
            "mode": "offline_prompt_only_simulation",
            "benchmark": {
                "suite_id": suite.id,
                "suite_file": str(args.suite.resolve()),
                "suite_sha256": sha256_file(args.suite.resolve()),
                "case_count": len(rows),
                "positive_count": len(positives),
                "negative_count": len(negatives),
            },
            "model": {
                "provider": "prompt_only_simulator",
                "external_api_calls": 0,
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
            },
            "observations": {
                "count": len(observation_cache),
                "all_loaded_from_same_fingerprint": True,
            },
            "parallel_execution": {
                "execution_model": "sequential_offline_simulation",
                "configured_jobs": 1,
                "maximum_concurrent_case_tasks": 1,
                "active_case_task_count": 0,
            },
            "execution_layers": {
                "core_reuse": {
                    "case_count": 16,
                    "model_calls": sum(row["model_turn_count"] for row in rows),
                    "lean_process_count": 1,
                },
                "optional_authoring": {
                    "attempt_count": 0,
                    "candidate_file_count": 0,
                    "lean_precheck_count": 0,
                },
            },
            "cases": rows,
            "artifact": {
                "path": str(artifact_path),
                "sha256": hashlib.sha256(artifact_source.encode("utf-8")).hexdigest(),
                "accepted_positive_case_count": len(artifacts),
                "assert_standard_axioms_count": artifact_source.count(
                    "assert_standard_axioms"
                ),
                "objective_counts": dict(Counter(case.objective for case in artifacts)),
            },
            "lean": {
                "process_count": 1,
                "ok": lean.ok,
                "exit_code": lean.exit_code,
                "duration_seconds": lean.duration_seconds,
                "stdout": lean.stdout,
                "stderr": lean.stderr,
            },
            "grouped_metrics": grouped_metrics(rows, cases),
            "prompt_errors": prompt_errors,
            "summary": {
                "protocol_expected_count": sum(
                    row["protocol_matches_expected"] for row in rows
                ),
                "positive_lean_verified_count": sum(
                    row["final_status"] == "VERIFIED" for row in positives
                ),
                "negative_correctly_blocked_count": sum(
                    row["final_status"] == "BLOCKED" for row in negatives
                ),
                "model_turn_count": sum(row["model_turn_count"] for row in rows),
                "reduction_search_action_count": sum(
                    row["query_action_counts"].get("search_reductions", 0)
                    for row in rows
                ),
                "repeated_reduction_search_count": repeated_searches,
                "model_term_rewrite_count": sum(
                    row["model_term_changed_by_agent"] is True for row in rows
                ),
                "authoring_attempt_count": 0,
                "authoring_candidate_file_count": 0,
                "authoring_lean_precheck_count": 0,
                "lean_process_count": 1,
                "wall_duration_seconds": round(time.monotonic() - started, 3),
                "all_core_generalization_offline_thresholds_met": thresholds,
            },
        }
    )
    write_json(args.output_root / "report.json", report)
    if thresholds:
        write_json(args.report, report)
    print(json.dumps(report["summary"], ensure_ascii=False, sort_keys=True))
    return 0 if thresholds else 1


if __name__ == "__main__":
    raise SystemExit(main())
