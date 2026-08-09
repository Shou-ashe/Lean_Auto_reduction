#!/usr/bin/env python3
"""Run the Stage H predicate-input suite with the prompt-only model double."""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
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
from agent.hardness.predicate_input import (  # noqa: E402
    audit_predicate_input_prompt,
    validate_predicate_input_suite,
)
from agent.hardness.problem_catalog import load_problem_catalog_snapshot  # noqa: E402


SCHEMA_VERSION = "hardness_predicate_input_offline_report_v1"


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
        description="Run all Stage H predicate-input cases without external API calls"
    )
    command.add_argument(
        "--suite",
        type=Path,
        default=ROOT / "Benchmark" / "Hardness" / "Suites" / "predicate_input.json",
    )
    command.add_argument(
        "--snapshots-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "stage-h-snapshots",
    )
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "predicate-input-offline",
    )
    command.add_argument(
        "--report",
        type=Path,
        default=ROOT / "Benchmark" / "Hardness" / "PREDICATE_INPUT_OFFLINE_REPORT.json",
    )
    command.add_argument("--lean-timeout", type=int, default=900)
    return command


def request_policy(case: BenchmarkCase) -> OpenTargetRequestPolicy:
    if (
        case.required_hardness is None
        or case.maximum_route_atoms is None
        or case.maximum_dependencies is None
    ):
        raise ValueError(f"case {case.id} has incomplete open-target policy")
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


def expected_protocol(case: BenchmarkCase, result: Any) -> bool:
    if case.is_positive:
        return bool(result.protocol_accepted and result.plan and result.lean_term)
    return bool(
        result.plan is None
        and result.lean_term is None
        and result.failure_code == case.expected.final_failure_code
    )


def action_counts(trace: tuple[Mapping[str, Any], ...]) -> dict[str, int]:
    counts = Counter(
        str(row.get("action"))
        for row in trace
        if row.get("status") != "started" and isinstance(row.get("action"), str)
    )
    return dict(sorted(counts.items()))


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
        )
        for turn, prompt in enumerate(result.model_prompts, start=1):
            try:
                payload = json.loads(prompt)
                if not isinstance(payload, dict):
                    raise ValueError("prompt is not a JSON object")
                audit_open_target_prompt(payload)
                audit_predicate_input_prompt(payload)
            except (json.JSONDecodeError, ValueError) as error:
                prompt_errors.append(
                    {"case_id": case.id, "turn": turn, "error": str(error)}
                )
        protocol_ok = expected_protocol(case, result)
        row = {
            "id": case.id,
            "input_kind": observation.input_kind,
            "input_declaration": observation.input_declaration,
            "predicate_node_id": observation.predicate_node_id,
            "predicate_domain_node_id": observation.predicate_domain_node_id,
            "lean_confirmed_predicate_match_count": len(
                observation.predicate_presentation_matches
            ),
            "expected_status": case.expected.final_status,
            "expected_failure_code": case.expected.final_failure_code,
            "protocol_accepted": result.protocol_accepted,
            "protocol_matches_expected": protocol_ok,
            "failure_code": result.failure_code,
            "explanation": result.explanation,
            "problem_match": (
                result.problem_match.to_dict() if result.problem_match else None
            ),
            "path_source_declaration": (
                result.plan.source_declaration if result.plan else None
            ),
            "selected_target_declaration": (
                result.plan.target_declaration if result.plan else None
            ),
            "selected_reduction_declarations": list(result.reduction_declarations),
            "lean_term": result.lean_term,
            "model_turn_count": len(result.model_responses),
            "query_action_counts": action_counts(result.query_trace),
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
                    predicate_declaration=case.effective_input_declaration,
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
    artifact_path = args.output_root / "PredicateInputBatch.lean"
    artifact_path.write_text(artifact_source, encoding="utf-8")
    lean = run_command(
        ["lake", "env", "lean", str(artifact_path.resolve())],
        cwd=lean_root,
        timeout_seconds=args.lean_timeout,
        output_limit=128 * 1024,
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
        and lean.ok
        and not prompt_errors
        and artifact_source.count("assert_standard_axioms") == 1
        and artifact_source.count("theorem inputPredicateGrounding") == 4
        and artifact_source.count(".inputPredicateGrounding") == 4
    )
    report = {
        "schema_version": SCHEMA_VERSION,
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
            "sha256": sha256_text(artifact_source),
            "accepted_positive_case_count": len(artifacts),
            "assert_standard_axioms_count": artifact_source.count(
                "assert_standard_axioms"
            ),
            "predicate_grounding_count": artifact_source.count(
                "theorem inputPredicateGrounding"
            ),
            "predicate_grounding_audit_reference_count": artifact_source.count(
                ".inputPredicateGrounding"
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
            "all_stage_h_offline_thresholds_met": all_thresholds,
        },
    }
    write_json(args.output_root / "report.json", report)
    write_json(args.report, report)
    print(json.dumps(report["summary"], ensure_ascii=False, sort_keys=True))
    return 0 if all_thresholds else 1


if __name__ == "__main__":
    raise SystemExit(main())
