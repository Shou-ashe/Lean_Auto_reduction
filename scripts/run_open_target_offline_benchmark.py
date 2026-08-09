#!/usr/bin/env python3
"""Run the Stage G open-target suite with a prompt-only simulated model.

All observations and catalogs are fingerprint-bound snapshots.  No Lean process
runs during model planning.  Accepted positive cases are merged into one final
artifact and checked by exactly one Lean process.
"""

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
from agent.hardness.benchmark import (  # noqa: E402
    BenchmarkCase,
    load_benchmark_suite,
)
from agent.hardness.connection_catalog import (  # noqa: E402
    build_reduction_catalog,
    load_connection_catalog_snapshot,
)
from agent.hardness.hardness_target_catalog import (  # noqa: E402
    load_hardness_target_catalog_snapshot,
)
from agent.hardness.input_grounding import observation_snapshot_path  # noqa: E402
from agent.hardness.input_observation import (  # noqa: E402
    load_input_observation_snapshot,
)
from agent.hardness.lean_runner import (  # noqa: E402
    assert_generated_source_is_safe,
    module_file,
    run_command,
    sha256_file,
)
from agent.hardness.open_target import (  # noqa: E402
    audit_open_target_prompt,
    validate_open_target_suite,
)
from agent.hardness.open_target_planner import (  # noqa: E402
    OpenTargetRequestPolicy,
    generate_lean_path_to_open_target,
)
from agent.hardness.open_target_simulation import (  # noqa: E402
    SimulatedOpenTargetClient,
)
from agent.hardness.model_client import extract_json_object  # noqa: E402
from agent.hardness.problem_catalog import (  # noqa: E402
    load_problem_catalog_snapshot,
)


SCHEMA_VERSION = "hardness_open_target_offline_report_v1"


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
        description="Run the Stage G open-target suite with a prompt-only model double"
    )
    command.add_argument(
        "--suite",
        type=Path,
        default=ROOT / "Benchmark" / "Hardness" / "Suites" / "open_target.json",
    )
    command.add_argument(
        "--observations-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "stage-g-snapshots" / "observations",
    )
    command.add_argument(
        "--problem-catalog",
        type=Path,
        default=ROOT / ".reduction-agent" / "stage-g-snapshots" / "problem-catalog.json",
    )
    command.add_argument(
        "--connection-catalog",
        type=Path,
        default=ROOT
        / ".reduction-agent"
        / "stage-g-snapshots"
        / "connection-catalog.json",
    )
    command.add_argument(
        "--target-catalog",
        type=Path,
        default=ROOT
        / ".reduction-agent"
        / "stage-g-snapshots"
        / "hardness-target-catalog.json",
    )
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "open-target-offline",
    )
    command.add_argument(
        "--report",
        type=Path,
        default=ROOT / "Benchmark" / "Hardness" / "OPEN_TARGET_OFFLINE_REPORT.json",
    )
    command.add_argument("--lean-timeout", type=int, default=900)
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


def expected_protocol(case: BenchmarkCase, result: Any) -> bool:
    if case.is_positive:
        return bool(result.protocol_accepted)
    return (
        result.failure_code == case.expected.final_failure_code
        and result.plan is None
        and result.lean_term is None
    )


def action_counts(trace: tuple[Mapping[str, Any], ...]) -> dict[str, int]:
    counts = Counter(
        str(row.get("action"))
        for row in trace
        if row.get("status") != "started"
    )
    return dict(sorted(counts.items()))


def submitted_model_term(responses: tuple[Any, ...]) -> str | None:
    """Recover the exact final ``lean_term`` string before planner normalization."""

    for response in reversed(responses):
        payload = extract_json_object(response.content)
        if payload is None:
            continue
        if not isinstance(payload.get("action"), str):
            nested = payload.get("finish")
            if isinstance(nested, dict):
                payload = dict(nested)
                payload.setdefault("action", "finish")
        if payload.get("action") == "finish" and isinstance(
            payload.get("lean_term"), str
        ):
            return str(payload["lean_term"])
    return None


def transcript_payload(case: BenchmarkCase, result: Any) -> dict[str, Any]:
    return {
        "case_id": case.id,
        "prompts": list(result.model_prompts),
        "responses": [
            {
                "called": response.called,
                "ok": response.ok,
                "content": response.content,
                "error": response.error,
                "finish_reason": response.finish_reason,
            }
            for response in result.model_responses
        ],
        "query_trace": list(result.query_trace),
        "failure_code": result.failure_code,
        "explanation": result.explanation,
    }


def main() -> int:
    args = parser().parse_args()
    if args.output_root.exists():
        print(
            f"refusing to reuse existing output root: {args.output_root}",
            file=sys.stderr,
        )
        return 2
    args.output_root.mkdir(parents=True)
    plans_dir = args.output_root / "plans"
    transcripts_dir = args.output_root / "transcripts"
    plans_dir.mkdir()
    transcripts_dir.mkdir()

    suite = load_benchmark_suite(args.suite)
    cases = validate_open_target_suite(suite)
    lean_root = ROOT / "Lean"
    toolchain = (lean_root / "lean-toolchain").read_text(encoding="utf-8").strip()
    manifest_hash = sha256_file(lean_root / "lake-manifest.json")
    problem_catalog = load_problem_catalog_snapshot(
        args.problem_catalog,
        expected_toolchain=toolchain,
        expected_lake_manifest_sha256=manifest_hash,
    )
    connection_catalog = load_connection_catalog_snapshot(
        args.connection_catalog,
        expected_registry_fingerprint=problem_catalog.registry_fingerprint,
        expected_toolchain=toolchain,
        expected_lake_manifest_sha256=manifest_hash,
    )
    target_catalog = load_hardness_target_catalog_snapshot(
        args.target_catalog,
        expected_registry_fingerprint=problem_catalog.registry_fingerprint,
        expected_toolchain=toolchain,
        expected_lake_manifest_sha256=manifest_hash,
    )
    reduction_catalog = build_reduction_catalog(connection_catalog, mode="full")

    rows: list[dict[str, Any]] = []
    accepted_cases: list[OpenTargetArtifactCase] = []
    results: dict[str, Any] = {}
    prompt_leaks: list[dict[str, Any]] = []
    for case in cases:
        input_path = module_file(lean_root, case.module)
        observation = load_input_observation_snapshot(
            observation_snapshot_path(
                args.observations_root,
                module=case.module,
                declaration=case.effective_input_declaration,
            ),
            expected_input_module=case.module,
            expected_input_declaration=case.effective_input_declaration,
            expected_input_module_sha256=sha256_file(input_path),
            expected_toolchain=toolchain,
            expected_lake_manifest_sha256=manifest_hash,
            expected_registry_fingerprint=problem_catalog.registry_fingerprint,
        )
        client = SimulatedOpenTargetClient()
        result = generate_lean_path_to_open_target(
            observation=observation,
            problem_catalog=problem_catalog,
            connection_catalog=connection_catalog,
            reduction_catalog=reduction_catalog,
            target_catalog=target_catalog,
            request_policy=request_policy(case),
            client=client,  # type: ignore[arg-type]
        )
        results[case.id] = result
        for turn, prompt in enumerate(result.model_prompts, start=1):
            try:
                parsed = json.loads(prompt)
                if not isinstance(parsed, dict):
                    raise ValueError("prompt is not an object")
                audit_open_target_prompt(parsed)
            except (json.JSONDecodeError, ValueError) as error:
                prompt_leaks.append(
                    {"case_id": case.id, "turn": turn, "error": str(error)}
                )
        protocol_ok = expected_protocol(case, result)
        raw_model_term = submitted_model_term(result.model_responses)
        selected_target = result.plan.target_declaration if result.plan else None
        selected_evidence = dict(result.plan.target_evidence) if result.plan else {}
        row = {
            "id": case.id,
            "module": case.module,
            "source": case.source,
            "required_hardness": case.required_hardness,
            "allowed_target_evidence": list(case.allowed_target_evidence),
            "maximum_route_atoms": case.maximum_route_atoms,
            "maximum_dependencies": case.maximum_dependencies,
            "allow_reflexive_target": case.allow_reflexive_target,
            "expected_status": case.expected.final_status,
            "expected_failure_code": case.expected.final_failure_code,
            "protocol_accepted": result.protocol_accepted,
            "protocol_matches_expected": protocol_ok,
            "failure_code": result.failure_code,
            "explanation": result.explanation,
            "selected_target_declaration": selected_target,
            "selected_target_entry_id": selected_evidence.get("target_entry_id"),
            "selected_target_evidence_id": selected_evidence.get("evidence_id"),
            "selected_target_evidence_kind": selected_evidence.get("evidence_kind"),
            "selected_target_evidence_declaration": selected_evidence.get(
                "evidence_declaration"
            ),
            "target_policy_satisfied": selected_evidence.get("policy_satisfied"),
            "reduction_declarations": list(result.reduction_declarations),
            "model_raw_lean_term": raw_model_term,
            "lean_term": result.lean_term,
            "model_term_rewritten": bool(
                result.lean_term is not None and raw_model_term != result.lean_term
            ),
            "model_turn_count": len(result.model_responses),
            "query_round_count": sum(
                1
                for trace_row in result.query_trace
                if trace_row.get("status") == "started"
            ),
            "action_counts": action_counts(result.query_trace),
            "plan_id": result.plan.plan_id if result.plan else None,
            "final_status": "PENDING" if case.is_positive else (
                "BLOCKED" if protocol_ok else "FAILED"
            ),
        }
        rows.append(row)
        if result.plan is not None:
            write_json(plans_dir / f"{case.id}.json", result.plan.to_dict())
        write_json(transcripts_dir / f"{case.id}.json", transcript_payload(case, result))
        if case.is_positive and result.protocol_accepted and result.plan is not None:
            evidence = result.plan.target_evidence
            accepted_cases.append(
                OpenTargetArtifactCase(
                    case_id=case.id,
                    input_module=case.module,
                    source_declaration=case.source,
                    target_declaration=result.plan.target_declaration or "",
                    lean_term=result.lean_term or "",
                    required_hardness=case.required_hardness or "",
                    target_evidence_kind=str(evidence["evidence_kind"]),
                    target_evidence_lean_term=str(evidence["evidence_lean_term"]),
                )
            )

    lean_process_count = 0
    lean_record: dict[str, Any] | None = None
    artifact_path: Path | None = None
    artifact_sha256: str | None = None
    if accepted_cases:
        artifact_source = build_open_target_batch_artifact_source(accepted_cases)
        assert_generated_source_is_safe(artifact_source)
        artifact_path = args.output_root / "OpenTargetBatch.lean"
        artifact_path.write_text(artifact_source, encoding="utf-8")
        artifact_sha256 = sha256_text(artifact_source)
        command = run_command(
            ["lake", "env", "lean", str(artifact_path.resolve())],
            cwd=lean_root,
            timeout_seconds=args.lean_timeout,
            output_limit=128000,
        )
        lean_process_count = 1
        lean_record = {
            "command": list(command.command),
            "exit_code": command.exit_code,
            "duration_seconds": command.duration_seconds,
            "timed_out": command.timed_out,
            "stdout": command.stdout,
            "stderr": command.stderr,
            "ok": command.ok,
        }
        accepted_ids = {case.case_id for case in accepted_cases}
        for row in rows:
            if row["id"] in accepted_ids:
                row["final_status"] = "VERIFIED" if command.ok else "FAILED"

    positive_rows = [row for row in rows if row["expected_status"] == "VERIFIED"]
    negative_rows = [row for row in rows if row["expected_status"] == "BLOCKED"]
    all_thresholds = (
        len(rows) == len(cases)
        and all(row["protocol_matches_expected"] for row in rows)
        and len(positive_rows) == 3
        and all(row["final_status"] == "VERIFIED" for row in positive_rows)
        and len(negative_rows) == 4
        and all(row["final_status"] == "BLOCKED" for row in negative_rows)
        and lean_process_count == 1
        and not prompt_leaks
        and all(row["model_term_rewritten"] is False for row in positive_rows)
    )
    report = {
        "schema_version": SCHEMA_VERSION,
        "generated_at": utc_now(),
        "suite_id": suite.id,
        "suite_file": str(args.suite),
        "mode": "offline_prompt_only_simulation",
        "case_count": len(rows),
        "positive_count": len(positive_rows),
        "negative_count": len(negative_rows),
        "registry_fingerprint": problem_catalog.registry_fingerprint,
        "problem_catalog_id": problem_catalog.catalog_id,
        "connection_catalog_id": connection_catalog.catalog_id,
        "reduction_catalog_id": reduction_catalog.catalog_id,
        "hardness_target_catalog_id": target_catalog.catalog_id,
        "hardness_target_count": len(target_catalog.entries),
        "hardness_target_evidence_count": target_catalog.evidence_count,
        "toolchain": toolchain,
        "lake_manifest_sha256": manifest_hash,
        "artifact_path": str(artifact_path) if artifact_path else None,
        "artifact_sha256": artifact_sha256,
        "final_lean_process_count": lean_process_count,
        "final_lean": lean_record,
        "prompt_leaks": prompt_leaks,
        "results": rows,
        "summary": {
            "protocol_expected_count": sum(
                bool(row["protocol_matches_expected"]) for row in rows
            ),
            "positive_lean_verified_count": sum(
                row["final_status"] == "VERIFIED" for row in positive_rows
            ),
            "negative_correctly_blocked_count": sum(
                row["final_status"] == "BLOCKED" for row in negative_rows
            ),
            "all_stage_g_offline_thresholds_met": all_thresholds,
        },
    }
    write_json(args.output_root / "report.json", report)
    write_json(args.report, report)
    print(json.dumps(report["summary"], ensure_ascii=False, sort_keys=True))
    return 0 if all_thresholds else 1


if __name__ == "__main__":
    raise SystemExit(main())
