#!/usr/bin/env python3
"""Run P-B's fixed-model 24-case offline and 72-case mutation qualification."""

from __future__ import annotations

import argparse
import json
import shutil
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.benchmark import load_benchmark_suite  # noqa: E402
from agent.hardness.lean_runner import run_command, sha256_file  # noqa: E402
from agent.hardness.models import sha256_id  # noqa: E402
from agent.hardness.stage_p_benchmark import (  # noqa: E402
    build_stage_p_offline_aggregate_source,
    run_stage_p_offline_canonical,
    stage_p_offline_summary,
)
from agent.hardness.stage_p_contract import (  # noqa: E402
    load_and_validate_stage_p_mutations,
    validate_stage_p_suites,
)
from agent.hardness.stage_p_mutations import run_stage_p_mutation_suite  # noqa: E402


POSITIVE_SUITE = ROOT / "Benchmark/Hardness/Suites/stage_p_open_world.json"
NEGATIVE_SUITE = ROOT / "Benchmark/Hardness/Suites/stage_p_adversarial.json"
MUTATION_SUITE = ROOT / "Benchmark/Hardness/Suites/stage_p_mutations.json"
WORKER_REPORT = ROOT / "Benchmark/Hardness/STAGE_P_LEAN_WORKER_REPORT.json"
CANONICAL_REPORT = ROOT / "Benchmark/Hardness/STAGE_P_OPEN_WORLD_OFFLINE_REPORT.json"
INPUT_SOURCE = ROOT / "Lean/Reference/Benchmark/Hardness/Inputs/StageP/Inputs.lean"


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def prepare_fresh_output_root(path: Path) -> None:
    if path.exists() and any(path.iterdir()):
        raise ValueError(f"Stage P offline output root must be fresh and empty: {path}")
    path.mkdir(parents=True, exist_ok=True)


def _load_worker_report(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if payload.get("status") != "VERIFIED":
        raise ValueError("Stage P offline qualification requires a VERIFIED worker report")
    gates = payload.get("gates")
    if not isinstance(gates, dict) or not gates or not all(gates.values()):
        raise ValueError("Stage P worker report has an incomplete gate set")
    return payload


def _implementation_shortcut_audit() -> dict[str, Any]:
    files = (
        ROOT / "agent/hardness/stage_p_runtime.py",
        ROOT / "agent/hardness/stage_p_model_authoring.py",
        ROOT / "agent/hardness/stage_p_candidate_validation.py",
        ROOT / "agent/hardness/stage_p_publication.py",
        ROOT / "agent/hardness/lean_worker_pool.py",
        ROOT / "agent/hardness/stage_p_benchmark.py",
        ROOT / "agent/hardness/stage_p_mutations.py",
    )
    case_branch_hits: list[dict[str, Any]] = []
    family_branch_hits: list[dict[str, Any]] = []
    family_tokens = ("graph", "numeric", "set_system", "clause_csp")
    for path in files:
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            stripped = line.strip().lower()
            if not stripped.startswith(("if ", "elif ", "case ")):
                continue
            if "p-" in stripped:
                case_branch_hits.append(
                    {"file": str(path.relative_to(ROOT)), "line": number}
                )
            if any(token in stripped for token in family_tokens):
                family_branch_hits.append(
                    {"file": str(path.relative_to(ROOT)), "line": number}
                )
    return {
        "files": [str(path.relative_to(ROOT)) for path in files],
        "case_specific_branch_hits": case_branch_hits,
        "family_specific_branch_hits": family_branch_hits,
        "case_specific_branch_count": len(case_branch_hits),
        "family_specific_branch_count": len(family_branch_hits),
    }


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    command.add_argument("--positive-suite", type=Path, default=POSITIVE_SUITE)
    command.add_argument("--negative-suite", type=Path, default=NEGATIVE_SUITE)
    command.add_argument("--mutations", type=Path, default=MUTATION_SUITE)
    command.add_argument("--worker-report", type=Path, default=WORKER_REPORT)
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent/stage-p-open-world-offline",
    )
    command.add_argument("--canonical-report", type=Path, default=CANONICAL_REPORT)
    command.add_argument("--lean-timeout", type=int, default=1200)
    return command


def main() -> int:
    args = parser().parse_args()
    prepare_fresh_output_root(args.output_root)
    if args.canonical_report.exists():
        raise ValueError(
            f"canonical Stage P offline report already exists: {args.canonical_report}"
        )
    positive = load_benchmark_suite(args.positive_suite)
    negative = load_benchmark_suite(args.negative_suite)
    cases = validate_stage_p_suites(positive, negative)
    mutation_rows = load_and_validate_stage_p_mutations(args.mutations)
    worker_report = _load_worker_report(args.worker_report)
    lean_root = ROOT / "Lean"
    toolchain = (lean_root / "lean-toolchain").read_text(encoding="utf-8").strip()
    lake_manifest_sha256 = sha256_id(
        (lean_root / "lake-manifest.json").read_text(encoding="utf-8")
    )
    input_source_sha256 = sha256_id(INPUT_SOURCE.read_text(encoding="utf-8"))
    run_id = "stage-p-offline-" + sha256_id(
        {
            "positive_suite": sha256_file(args.positive_suite),
            "negative_suite": sha256_file(args.negative_suite),
            "mutations": sha256_file(args.mutations),
            "worker_report": sha256_file(args.worker_report),
        }
    ).removeprefix("sha256:")[:16]
    report_path = args.output_root / "report.json"
    report: dict[str, Any] = {
        "schema_version": "hardness_stage_p_open_world_offline_report_v1",
        "stage": "P-B",
        "qualification_scope": (
            "fixed simulated model with real aggregate Lean/axiom/replay; "
            "model-generated capability credit remains zero"
        ),
        "status": "FAILED",
        "started_at": utc_now(),
        "run_id": run_id,
        "output_root": str(args.output_root.resolve()),
        "resume_used": False,
        "replay_used": False,
        "old_response_used": False,
        "benchmark": {
            "positive_suite_sha256": sha256_file(args.positive_suite),
            "negative_suite_sha256": sha256_file(args.negative_suite),
            "mutation_suite_sha256": sha256_file(args.mutations),
            "worker_report_sha256": sha256_file(args.worker_report),
            "input_source_sha256": input_source_sha256,
            "lake_manifest_sha256": lake_manifest_sha256,
            "toolchain": toolchain,
        },
    }
    write_json(report_path, report)

    try:
        outcomes = run_stage_p_offline_canonical(
            cases,
            output_root=args.output_root,
            run_id=run_id,
            toolchain=toolchain,
            lake_manifest_sha256=lake_manifest_sha256,
            input_source_sha256=input_source_sha256,
        )
        for outcome in outcomes:
            write_json(
                args.output_root / "cases" / outcome.case.id / "outcome.json",
                outcome.row,
            )
        mutation_results = run_stage_p_mutation_suite(
            mutation_rows, workspace_root=args.output_root / "mutations"
        )
        write_json(
            args.output_root / "mutation-results.json",
            [result.to_dict() for result in mutation_results],
        )
        aggregate_source = build_stage_p_offline_aggregate_source(outcomes)
        final_source = args.output_root / "final" / "StagePOfflineAggregate.lean"
        final_source.parent.mkdir(parents=True, exist_ok=False)
        final_source.write_text(aggregate_source, encoding="utf-8")
        final_command = run_command(
            ["lake", "env", "lean", str(final_source.resolve())],
            cwd=lean_root,
            timeout_seconds=args.lean_timeout,
            output_limit=128 * 1024,
        )
        replay_source = args.output_root / "release-replay" / "StagePOfflineReplay.lean"
        replay_source.parent.mkdir(parents=True, exist_ok=False)
        replay_source.write_text(aggregate_source, encoding="utf-8")
        replay_command = run_command(
            ["lake", "env", "lean", str(replay_source.resolve())],
            cwd=lean_root,
            timeout_seconds=args.lean_timeout,
            output_limit=128 * 1024,
        )
        rows = [outcome.row for outcome in outcomes]
        for row in rows[:12]:
            row["final_combined_lean"] = {
                "offline_simulated": False,
                "verified": final_command.ok,
                "aggregate_source_sha256": sha256_id(aggregate_source),
            }
            row["standard_axiom_audit"] = {
                "offline_simulated": False,
                "verified": final_command.ok,
                "aggregate_source_sha256": sha256_id(aggregate_source),
            }
            row["release_replay"] = {
                "offline_simulated": False,
                "verified": replay_command.ok,
                "aggregate_source_sha256": sha256_id(aggregate_source),
            }
        summary = stage_p_offline_summary(outcomes)
        summary["mutation_expected_count"] = sum(
            result.passed for result in mutation_results
        )
        summary["aggregate_candidate_declaration_count"] = sum(
            len(outcome.candidate_declarations) for outcome in outcomes
        )
        shortcut_audit = _implementation_shortcut_audit()
        report.update(
            {
                "cases": rows,
                "summary": summary,
                "mutations": {
                    "case_count": len(mutation_results),
                    "expected_count": sum(result.passed for result in mutation_results),
                    "failure_count": sum(not result.passed for result in mutation_results),
                },
                "worker_qualification": {
                    "report": str(args.worker_report.resolve()),
                    "status": worker_report["status"],
                    "gates": worker_report["gates"],
                    "performance": worker_report.get("performance"),
                    "isolation": worker_report.get("isolation"),
                },
                "final_combined_lean": {
                    "source": str(final_source.resolve()),
                    "source_sha256": sha256_id(aggregate_source),
                    "command": final_command.to_dict(),
                },
                "release_replay": {
                    "source": str(replay_source.resolve()),
                    "source_sha256": sha256_id(aggregate_source),
                    "command": replay_command.to_dict(),
                    "independent_process": True,
                },
                "implementation_shortcut_audit": shortcut_audit,
            }
        )
        gates = {
            "offline_canonical_24_of_24": summary["protocol_expected_count"] == 24,
            "offline_positive_12_of_12": summary["positive_expected_count"] == 12,
            "offline_negative_12_of_12": summary["negative_expected_count"] == 12,
            "mutation_72_of_72": summary["mutation_expected_count"] == 72,
            "eleven_simulated_authoring_cases": summary[
                "simulated_model_case_count"
            ]
            == 11,
            "provenance_credit_separated": summary["model_generated_case_count"] == 0
            and summary["deterministic_fixture_case_count"] == 23
            and summary["existing_reuse_case_count"] == 1,
            "three_full_bundle_fixtures": summary[
                "full_reduction_bundle_authored_count"
            ]
            == 3,
            "twenty_four_gap_publications": summary["published_capability_count"]
            == 24,
            "all_simulated_model_bodies_required": summary[
                "all_model_bodies_required"
            ],
            "consumer_zero_authoring": summary["consumer_zero_authoring"],
            "compiler_inserted_math_zero": summary[
                "compiler_inserted_math_token_count"
            ]
            == 0,
            "aggregate_final_lean": final_command.ok,
            "aggregate_standard_axiom_audit": final_command.ok,
            "independent_release_replay": replay_command.ok,
            "persistent_worker_qualification_verified": worker_report["status"]
            == "VERIFIED"
            and all(worker_report["gates"].values()),
            "no_case_or_family_specific_solution_branch": shortcut_audit[
                "case_specific_branch_count"
            ]
            == 0
            and shortcut_audit["family_specific_branch_count"] == 0,
            "no_resume_replay_or_old_response": all(
                row.get("resume_used") is False
                and row.get("replay_used") is False
                and row.get("old_response_used") is False
                for row in rows
            ),
        }
        report["gates"] = gates
        report["status"] = "VERIFIED" if all(gates.values()) else "FAILED"
    except Exception as error:
        report["runner_error"] = f"{type(error).__name__}: {error}"
        report.setdefault("gates", {})["runner_completed"] = False
    report["finished_at"] = utc_now()
    write_json(report_path, report)
    if report["status"] == "VERIFIED":
        args.canonical_report.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(report_path, args.canonical_report)
    print(
        json.dumps(
            {
                "status": report["status"],
                "report": str(report_path.resolve()),
                "canonical_expected": report.get("summary", {}).get(
                    "protocol_expected_count"
                ),
                "mutation_expected": report.get("summary", {}).get(
                    "mutation_expected_count"
                ),
            },
            sort_keys=True,
        )
    )
    return 0 if report["status"] == "VERIFIED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
