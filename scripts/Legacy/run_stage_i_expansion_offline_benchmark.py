#!/usr/bin/env python3
"""Run the Stage-I expansion suite with the prompt-only model double."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.artifact import (  # noqa: E402
    OpenTargetArtifactCase,
    build_open_target_batch_artifact_source,
)
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
from agent.hardness.input_observation import load_input_observation_snapshot  # noqa: E402
from agent.hardness.lean_runner import (  # noqa: E402
    assert_generated_source_is_safe,
    module_file,
    run_command,
    sha256_file,
)
from agent.hardness.open_target import audit_open_target_prompt  # noqa: E402
from agent.hardness.open_target_planner import (  # noqa: E402
    OpenTargetRequestPolicy,
    generate_lean_path_to_open_target,
)
from agent.hardness.open_target_simulation import SimulatedOpenTargetClient  # noqa: E402
from agent.hardness.predicate_input import audit_predicate_input_prompt  # noqa: E402
from agent.hardness.problem_catalog import load_problem_catalog_snapshot  # noqa: E402
from agent.hardness.stage_i_expansion import (  # noqa: E402
    STAGE_I_SUITE_ID,
    validate_stage_i_expansion_suite,
)
from scripts.run_deepseek_open_target_benchmark import (  # noqa: E402
    completed_action_counts,
    open_target_candidate_metrics,
)


SCHEMA_VERSION = "hardness_stage_i_expansion_offline_report_v1"
FRONTIER_SCHEMA_VERSION = "hardness_frontier_efficiency_offline_report_v1"


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
        description="Run Stage-I expansion without external API calls"
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
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "stage-i-expansion-offline",
    )
    command.add_argument(
        "--report",
        type=Path,
        default=ROOT / "Reports" / "STAGE_I_EXPANSION_OFFLINE_REPORT.json",
    )
    command.add_argument("--lean-timeout", type=int, default=1200)
    return command


def request_policy(case: BenchmarkCase) -> OpenTargetRequestPolicy:
    assert case.required_hardness is not None
    assert case.maximum_route_atoms is not None
    assert case.maximum_dependencies is not None
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


def expected_protocol(case: BenchmarkCase, result: Any) -> bool:
    if case.is_positive:
        return bool(result.protocol_accepted and result.plan and result.lean_term)
    return bool(
        result.plan is None
        and result.lean_term is None
        and result.failure_code == case.expected.final_failure_code
    )


def _route_metrics(case: BenchmarkCase, result: Any, reduction_catalog: Any) -> dict[str, Any]:
    by_declaration = {entry.declaration: entry for entry in reduction_catalog.entries}
    roles = Counter(
        by_declaration[declaration].component_role
        for declaration in result.reduction_declarations
        if declaration in by_declaration
    )
    if result.selected_connection is not None:
        roles[result.selected_connection.component_role] += 1
    atom_count = len(result.reduction_declarations) + (
        1 if result.selected_connection is not None else 0
    )
    return {
        "selected_route_atom_count": atom_count,
        "selected_route_within_public_range": (
            case.minimum_route_atoms
            <= atom_count
            <= int(case.maximum_route_atoms or 0)
        ),
        "selected_path_required_simple": case.require_simple_path,
        "selected_component_role_counts": dict(sorted(roles.items())),
        "selected_shared_gadget_count": roles.get("sharedGadget", 0),
    }


def main() -> int:
    args = parser().parse_args()
    if args.output_root.exists():
        print(f"refusing to reuse existing output root: {args.output_root}", file=sys.stderr)
        return 2
    args.output_root.mkdir(parents=True)
    plans_root = args.output_root / "plans"
    transcripts_root = args.output_root / "transcripts"
    plans_root.mkdir()
    transcripts_root.mkdir()

    suite = load_benchmark_suite(args.suite)
    cases = validate_suite(suite)
    frontier_mode = suite.id == FRONTIER_EFFICIENCY_SUITE_ID
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

    rows: list[dict[str, Any]] = []
    artifacts: list[OpenTargetArtifactCase] = []
    prompt_errors: list[dict[str, Any]] = []
    for case in cases:
        input_path = module_file(lean_root, case.module)
        snapshot = observation_snapshot_path(
            args.snapshots_root / "observations",
            module=case.module,
            declaration=case.effective_input_declaration,
        )
        observation = load_input_observation_snapshot(
            snapshot,
            expected_input_module=case.module,
            expected_input_declaration=case.effective_input_declaration,
            expected_input_module_sha256=sha256_file(input_path),
            expected_toolchain=toolchain,
            expected_lake_manifest_sha256=manifest_sha256,
            expected_registry_fingerprint=problem_catalog.registry_fingerprint,
        )
        result = generate_lean_path_to_open_target(
            observation=observation,
            problem_catalog=problem_catalog,
            connection_catalog=connection_catalog,
            reduction_catalog=reduction_catalog,
            target_catalog=target_catalog,
            request_policy=request_policy(case),
            client=SimulatedOpenTargetClient(),  # type: ignore[arg-type]
            maximum_model_turns=int(case.resources.get("max_model_calls", 14)),
        )
        for turn, prompt in enumerate(result.model_prompts, start=1):
            try:
                payload = json.loads(prompt)
                if not isinstance(payload, dict):
                    raise ValueError("prompt is not a JSON object")
                audit_open_target_prompt(payload)
                if observation.input_kind == "predicate":
                    audit_predicate_input_prompt(payload)
            except (json.JSONDecodeError, ValueError) as error:
                prompt_errors.append(
                    {"case_id": case.id, "turn": turn, "error": str(error)}
                )
        protocol_ok = expected_protocol(case, result)
        route_metrics = _route_metrics(case, result, reduction_catalog)
        row = {
            "id": case.id,
            "input_kind": observation.input_kind,
            "input_declaration": observation.input_declaration,
            "expected_status": case.expected.final_status,
            "expected_failure_code": case.expected.final_failure_code,
            "protocol_accepted": result.protocol_accepted,
            "protocol_matches_expected": protocol_ok,
            "failure_code": result.failure_code,
            "explanation": result.explanation,
            "problem_match": result.problem_match.to_dict() if result.problem_match else None,
            "selected_target_declaration": result.plan.target_declaration if result.plan else None,
            "selected_target_evidence_kind": (
                result.plan.target_evidence.get("evidence_kind") if result.plan else None
            ),
            "selected_reduction_declarations": list(result.reduction_declarations),
            "lean_term": result.lean_term,
            "model_turn_count": len(result.model_responses),
            "query_action_counts": completed_action_counts(result.query_trace),
            "candidate_metrics": open_target_candidate_metrics(result.query_trace),
            "frontier_interactions": analyze_frontier_interactions(
                prompts=result.model_prompts,
                responses=result.model_responses,
            ),
            **route_metrics,
            "final_status": "PENDING" if case.is_positive else (
                "BLOCKED" if protocol_ok else "FAILED"
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
        if case.is_positive and result.protocol_accepted and result.plan is not None:
            evidence = result.plan.target_evidence
            artifacts.append(
                OpenTargetArtifactCase(
                    case_id=case.id,
                    input_module=case.module,
                    source_declaration=result.plan.source_declaration,
                    predicate_declaration=(
                        case.effective_input_declaration
                        if observation.input_kind == "predicate"
                        else None
                    ),
                    target_declaration=result.plan.target_declaration or "",
                    lean_term=result.lean_term or "",
                    required_hardness=case.required_hardness or "",
                    target_evidence_kind=str(evidence.get("evidence_kind") or ""),
                    target_evidence_lean_term=str(
                        evidence.get("evidence_lean_term") or ""
                    ),
                )
            )

    artifact_source = build_open_target_batch_artifact_source(artifacts)
    assert_generated_source_is_safe(artifact_source)
    artifact_path = args.output_root / "StageIExpansionBatch.lean"
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
    all_thresholds = bool(
        len(rows) == 8
        and len(positives) == 4
        and len(negatives) == 4
        and len(artifacts) == 4
        and all(row["protocol_matches_expected"] for row in rows)
        and all(row["final_status"] == "VERIFIED" for row in positives)
        and all(row["final_status"] == "BLOCKED" for row in negatives)
        and all(
            row["selected_target_evidence_kind"] == "transported_native_hardness"
            and row["selected_route_within_public_range"] is True
            and row["selected_shared_gadget_count"] >= 1
            and int(row["candidate_metrics"].get("unique_policy_route_allowed_targets", 0))
            >= int(
                next(
                    case.coverage.get("minimum_policy_allowed_target_count", 0)
                    for case in cases
                    if case.id == row["id"]
                )
            )
            for row in positives
        )
        and lean.ok
        and not prompt_errors
        and artifact_source.count("assert_standard_axioms") == 1
        and artifact_source.count("theorem inputPredicateGrounding") == 2
        and artifact_source.count("noncomputable def targetHardness") == 4
        and (
            not frontier_mode
            or (
                all(
                    row["frontier_interactions"]["frontier_guidance_error_count"]
                    == 0
                    for row in rows
                )
                and all(
                    row["frontier_interactions"][
                        "frontier_suggestion_followed_round_count"
                    ]
                    >= 1
                    and row["frontier_interactions"]["terminal_guidance_counts"].get(
                        "finish_now", 0
                    )
                    >= 1
                    for row in positives
                )
                and all(
                    row["frontier_interactions"]["terminal_guidance_counts"].get(
                        "stop_now", 0
                    )
                    >= 1
                    for row in negatives
                )
            )
        )
    )
    report = {
        "schema_version": (
            FRONTIER_SCHEMA_VERSION if frontier_mode else SCHEMA_VERSION
        ),
        "generated_at": utc_now(),
        "mode": "offline_prompt_only_simulation",
        "suite_id": suite.id,
        "suite_file": str(args.suite.resolve()),
        "case_count": len(rows),
        "positive_count": len(positives),
        "negative_count": len(negatives),
        "registry_fingerprint": problem_catalog.registry_fingerprint,
        "problem_catalog_id": problem_catalog.catalog_id,
        "connection_catalog_id": connection_catalog.catalog_id,
        "reduction_catalog_id": reduction_catalog.catalog_id,
        "hardness_target_catalog_id": target_catalog.catalog_id,
        "artifact": {
            "path": str(artifact_path),
            "sha256": hashlib.sha256(artifact_source.encode("utf-8")).hexdigest(),
            "accepted_positive_case_count": len(artifacts),
            "assert_standard_axioms_count": artifact_source.count(
                "assert_standard_axioms"
            ),
            "predicate_grounding_count": artifact_source.count(
                "theorem inputPredicateGrounding"
            ),
            "target_hardness_count": artifact_source.count(
                "noncomputable def targetHardness"
            ),
        },
        "lean": {
            "process_count": 1,
            "ok": lean.ok,
            "exit_code": lean.exit_code,
            "duration_seconds": lean.duration_seconds,
            "stdout": lean.stdout,
            "stderr": lean.stderr,
        },
        "prompt_errors": prompt_errors,
        "results": rows,
        "summary": {
            "protocol_expected_count": sum(
                bool(row["protocol_matches_expected"]) for row in rows
            ),
            "positive_lean_verified_count": sum(
                row["final_status"] == "VERIFIED" for row in positives
            ),
            "negative_correctly_blocked_count": sum(
                row["final_status"] == "BLOCKED" for row in negatives
            ),
            "all_stage_i_offline_thresholds_met": all_thresholds,
            "all_frontier_efficiency_offline_thresholds_met": (
                all_thresholds if frontier_mode else None
            ),
            "model_turn_count": sum(row["model_turn_count"] for row in rows),
            "reduction_search_action_count": sum(
                row["query_action_counts"].get("search_reductions", 0)
                for row in rows
            ),
            "protocol_feedback_count": sum(
                row["query_action_counts"].get("protocol_feedback", 0)
                for row in rows
            ),
        },
    }
    write_json(args.output_root / "report.json", report)
    write_json(args.report, report)
    print(json.dumps(report["summary"], ensure_ascii=False, sort_keys=True))
    return 0 if all_thresholds else 1


if __name__ == "__main__":
    raise SystemExit(main())
