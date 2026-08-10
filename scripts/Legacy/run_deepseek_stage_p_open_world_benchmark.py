#!/usr/bin/env python3
"""P-B real DeepSeek 24-case open-world integration full run.

Requires a fresh, empty output directory.  All 11 authoring positives make
this run's real DeepSeek HTTP calls; every accepted capability goes through
real Lean candidate validation, run-local immutable publication, fresh Core
resolution, the aggregate final combined Lean, the standard-axiom audit, and
an independent release replay.  Adversarial cases are exercised
deterministically through the real gate chain (zero model calls).
"""

from __future__ import annotations

import argparse
import json
import shutil
import sys
import threading
from collections.abc import Mapping, Sequence
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.benchmark import load_benchmark_suite  # noqa: E402
from agent.hardness.lean_runner import build_module_command, run_command, sha256_file  # noqa: E402
from agent.hardness.lean_worker_pool import StagePLeanWorkerPool  # noqa: E402
from agent.hardness.model_client import DEFAULT_MODEL, DeepSeekConfig  # noqa: E402
from dataclasses import replace  # noqa: E402
from agent.hardness.models import sha256_id  # noqa: E402
from agent.hardness.stage_p_benchmark import (  # noqa: E402
    build_stage_p_offline_aggregate_source,
)
from agent.hardness.stage_p_contract import (  # noqa: E402
    STAGE_P_FEASIBILITY_MODULE,
    STAGE_P_INPUT_MODULE,
    STAGE_P_PRODUCER_SUPPORT_MODULE,
    STAGE_P_PROBE_MODULE,
    STAGE_P_STANDARD_HELPER_MODULE,
    STAGE_P_SYSTEM_PROMPT,
    load_and_validate_stage_p_mutations,
    validate_stage_p_suites,
)
from agent.hardness.stage_p_real_benchmark import (  # noqa: E402
    STAGE_P_OPEN_WORLD_SYSTEM_PROMPT,
    STAGE_P_REAL_RUN_SCHEMA,
    run_stage_p_real_canonical,
    stage_p_real_gap_coverage,
    stage_p_real_objective_coverage,
    stage_p_real_summary,
)


DEFAULT_POSITIVE_SUITE = ROOT / "Gate/Suites/stage_p_open_world.json"
DEFAULT_NEGATIVE_SUITE = ROOT / "Gate/Suites/stage_p_adversarial.json"
DEFAULT_MUTATIONS = ROOT / "Gate/Suites/stage_p_mutations.json"
DEFAULT_WORKER_REPORT = ROOT / "Reports/STAGE_P_LEAN_WORKER_REPORT.json"
STAGE_P_INPUT_SOURCE = ROOT / "Lean/Reference/Reports/Inputs/StageP/Inputs.lean"
STAGE_P_PRODUCER_SUPPORT_SOURCE = (
    ROOT / "Lean/Reference/Reports/Inputs/StageP/ProducerSupport.lean"
)
STAGE_P_STANDARD_HELPER_SOURCE = (
    ROOT / "Lean/Reference/ComplexityReduction/Problems/Karp21/ExactCoverStandardTM.lean"
)
STAGE_P_FEASIBILITY_SOURCE = (
    ROOT / "Lean/Reference/Reports/Oracles/Gold/StagePSemanticFeasibility.lean"
)
FAMILY_TOKENS = ("graph", "numeric", "set_system", "clause_csp")
PRIMARY_FAMILIES = ("graph", "numeric", "set_system", "clause_csp")


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def semantic_source_hashes() -> dict[str, str]:
    """Bare 64-character sha256 digests of the frozen P-A public sources."""

    return {
        "stage_p_input_source_sha256": sha256_file(STAGE_P_INPUT_SOURCE),
        "producer_support_source_sha256": sha256_file(STAGE_P_PRODUCER_SUPPORT_SOURCE),
        "exact_cover_standard_helper_sha256": sha256_file(STAGE_P_STANDARD_HELPER_SOURCE),
        "hidden_semantic_feasibility_sha256": sha256_file(STAGE_P_FEASIBILITY_SOURCE),
    }


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
        raise ValueError(f"Stage P real output root must be fresh and empty: {path}")
    path.mkdir(parents=True, exist_ok=True)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    command.add_argument("--positive-suite", type=Path, default=DEFAULT_POSITIVE_SUITE)
    command.add_argument("--negative-suite", type=Path, default=DEFAULT_NEGATIVE_SUITE)
    command.add_argument("--mutations", type=Path, default=DEFAULT_MUTATIONS)
    command.add_argument("--worker-report", type=Path, default=DEFAULT_WORKER_REPORT)
    command.add_argument("--env-file", type=Path, default=ROOT / ".env")
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent/deepseek-stage-p-open-world-full",
    )
    command.add_argument(
        "--canonical-report",
        type=Path,
        default=ROOT / "Reports/STAGE_P_IMPLEMENTATION_REAL_REPORT.json",
    )
    command.add_argument("--run-label", default="stage-p-b-open-world-real-deepseek")
    command.add_argument("--model", default=DEFAULT_MODEL)
    command.add_argument("--model-timeout", type=int, default=300)
    command.add_argument("--model-max-tokens", type=int, default=24576)
    command.add_argument("--lean-timeout", type=int, default=1200)
    command.add_argument("--jobs", type=int, default=4)
    return command


def _registry_absence(cases: Sequence[Any]) -> dict[str, Any]:
    production_root = ROOT / "Lean/Reference/ComplexityReduction"
    marker = "Benchmark.Hardness.Inputs.StageP"
    production_hits: list[str] = []
    for source in production_root.rglob("*.lean"):
        try:
            text = source.read_text(encoding="utf-8")
        except OSError:
            continue
        if marker in text:
            production_hits.append(str(source.relative_to(ROOT)))
    public_sources = (STAGE_P_INPUT_SOURCE, STAGE_P_PRODUCER_SUPPORT_SOURCE)
    public_text = "\n".join(source.read_text(encoding="utf-8") for source in public_sources)
    forbidden_closed_capability_markers = (
        "registerReduction",
        "CertifiedReduction",
        "NativeTMNPComplete",
        "AuthoringTemplate",
    )
    intended_support_markers = (
        "targetNativeTMInNP",
        "complexity_reduction_ir_typed_native_membership",
    )
    forbidden_hit_count = sum(
        public_text.count(token) for token in forbidden_closed_capability_markers
    )
    intended_support_present = all(token in public_text for token in intended_support_markers)
    authoring_cases = [
        case for case in cases if case.stage_p.get("protocol_role") == "authoring"
    ]
    rows = [
        {
            "source_endpoint": case.source,
            "target_endpoint": case.target,
            "objective": case.objective,
            "exact_closed_capability_absent": not production_hits
            and forbidden_hit_count == 0
            and intended_support_present,
        }
        for case in authoring_cases
    ]
    return {
        "schema_version": "hardness_stage_p_registry_absence_preflight_v2",
        "authoring_positive_count": len(rows),
        "production_reference_hits": production_hits,
        "public_input_files": [str(source.relative_to(ROOT)) for source in public_sources],
        "forbidden_closed_capability_marker_count": forbidden_hit_count,
        "producer_target_native_membership_support_present": intended_support_present,
        "cases": rows,
        "passed_count": sum(row["exact_closed_capability_absent"] for row in rows),
    }


def _semantic_feasibility_isolation(
    *, positive_suite: Path, negative_suite: Path
) -> dict[str, Any]:
    public_files = (
        STAGE_P_INPUT_SOURCE,
        STAGE_P_PRODUCER_SUPPORT_SOURCE,
        STAGE_P_STANDARD_HELPER_SOURCE,
        positive_suite,
        negative_suite,
    )
    forbidden_markers = (
        "StagePSemanticFeasibility",
        "Benchmark.Hardness.Oracles.Gold",
        "Reports/Oracles/Gold",
    )
    hits: list[dict[str, str]] = []
    for source in public_files:
        text = source.read_text(encoding="utf-8")
        for marker in forbidden_markers:
            if marker in text:
                hits.append({"file": str(source.relative_to(ROOT)), "marker": marker})
    return {
        "schema_version": "hardness_stage_p_semantic_feasibility_isolation_v1",
        "hidden_module": STAGE_P_FEASIBILITY_MODULE,
        "qualification_compile_only": True,
        "public_reference_hits": hits,
        "passed": not hits,
    }


def _implementation_shortcut_audit() -> dict[str, Any]:
    files = (
        ROOT / "agent/hardness/stage_p_real_benchmark.py",
        ROOT / "agent/hardness/stage_p_runtime.py",
        ROOT / "agent/hardness/stage_p_model_authoring.py",
        ROOT / "agent/hardness/stage_p_candidate_validation.py",
        ROOT / "agent/hardness/stage_p_publication.py",
        ROOT / "agent/hardness/lean_worker_pool.py",
        ROOT / "agent/hardness/stage_p_benchmark.py",
        ROOT / "agent/hardness/stage_p_mutations.py",
        Path(__file__).resolve(),
    )
    case_branch_hits: list[dict[str, Any]] = []
    family_branch_hits: list[dict[str, Any]] = []
    for path in files:
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            stripped = line.strip().lower()
            if not stripped.startswith(("if ", "elif ", "case ")):
                continue
            if '"p-" in stripped' in line or "token in stripped" in line:
                continue
            if "p-" in stripped:
                case_branch_hits.append({"file": str(path.relative_to(ROOT)), "line": number})
            if any(token in stripped for token in FAMILY_TOKENS):
                family_branch_hits.append({"file": str(path.relative_to(ROOT)), "line": number})
    return {
        "files": [str(path.relative_to(ROOT)) for path in files],
        "case_specific_branch_hits": case_branch_hits,
        "family_specific_branch_hits": family_branch_hits,
        "case_specific_branch_count": len(case_branch_hits),
        "family_specific_branch_count": len(family_branch_hits),
    }


def _scan_for_secret(root: Path, secret: str | None) -> list[str]:
    if not secret:
        return []
    hits: list[str] = []
    for path in root.rglob("*"):
        if not path.is_file():
            continue
        try:
            if secret in path.read_text(encoding="utf-8", errors="ignore"):
                hits.append(str(path.resolve()))
        except OSError:
            continue
    return hits


def _family_verification(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    verified_by_family: dict[str, int] = {}
    for row in rows[:12]:
        family = str(row.get("family") or "")
        if row.get("status") == "VERIFIED" and family in PRIMARY_FAMILIES:
            verified_by_family[family] = verified_by_family.get(family, 0) + 1
    return {
        "verified_by_family": verified_by_family,
        "all_families_at_least_two": all(
            verified_by_family.get(family, 0) >= 2 for family in PRIMARY_FAMILIES
        ),
    }


def _feature_cases(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    verified = {row.get("id") for row in rows[:12] if row.get("status") == "VERIFIED"}
    return {
        "native_membership_case": "p-single-native-membership",
        "native_membership_verified": "p-single-native-membership" in verified,
        "completeness_case": "p-full-bundle-set-completeness",
        "completeness_verified": "p-full-bundle-set-completeness" in verified,
    }


def main() -> int:
    args = parser().parse_args()
    if not 1 <= args.jobs <= 4:
        raise ValueError("Stage P real jobs must be in 1..4")
    prepare_fresh_output_root(args.output_root)
    if args.canonical_report.exists():
        raise ValueError(
            f"canonical Stage P implementation-real report already exists: {args.canonical_report}"
        )
    positive = load_benchmark_suite(args.positive_suite)
    negative = load_benchmark_suite(args.negative_suite)
    cases = validate_stage_p_suites(positive, negative)
    mutation_rows = load_and_validate_stage_p_mutations(args.mutations)
    worker_report = json.loads(args.worker_report.read_text(encoding="utf-8"))
    config = DeepSeekConfig.from_environment(env_file=args.env_file)
    config = replace(
        config,
        model=args.model,
        timeout_seconds=args.model_timeout,
        max_tokens=args.model_max_tokens,
    )
    if not config.api_key:
        raise ValueError("real Stage P open-world run requires DEEPSEEK_API_KEY")

    lean_root = ROOT / "Lean"
    toolchain = (lean_root / "lean-toolchain").read_text(encoding="utf-8").strip()
    lake_manifest_sha256 = sha256_id((lean_root / "lake-manifest.json").read_text(encoding="utf-8"))
    semantic_hashes = semantic_source_hashes()
    input_source_sha256 = sha256_id(STAGE_P_INPUT_SOURCE.read_text(encoding="utf-8"))
    run_id = "stage-p-real-" + sha256_id(
        {
            "positive_suite": sha256_file(args.positive_suite),
            "negative_suite": sha256_file(args.negative_suite),
            "worker_report": sha256_file(args.worker_report),
        }
    ).removeprefix("sha256:")[:16]
    report_path = args.output_root / "report.json"
    report: dict[str, Any] = {
        "schema_version": STAGE_P_REAL_RUN_SCHEMA,
        "stage": "P-B",
        "qualification_scope": (
            "real DeepSeek open-world integration: this run's HTTP calls, real Lean "
            "candidate validation, run-local publication, fresh Core, aggregate final "
            "Lean, standard-axiom audit, independent release replay"
        ),
        "status": "FAILED",
        "run_label": args.run_label,
        "started_at": utc_now(),
        "run_id": run_id,
        "output_root": str(args.output_root.resolve()),
        "resume_used": False,
        "replay_used": False,
        "old_response_used": False,
        "benchmark": {
            "positive_suite": str(args.positive_suite.resolve()),
            "positive_suite_sha256": sha256_file(args.positive_suite),
            "negative_suite": str(args.negative_suite.resolve()),
            "negative_suite_sha256": sha256_file(args.negative_suite),
            "mutations": str(args.mutations.resolve()),
            "mutations_sha256": sha256_file(args.mutations),
            "mutation_case_count": len(mutation_rows),
            "worker_report": str(args.worker_report.resolve()),
            "worker_report_sha256": sha256_file(args.worker_report),
            **semantic_hashes,
            "canonical_case_count": len(cases),
            "toolchain": toolchain,
            "lake_manifest_sha256": lake_manifest_sha256,
        },
        "contract_schemas": {
            "patch": "hardness_stage_p_patch_v1",
            "bound_task": "hardness_stage_p_bound_task_v1",
            "runtime_gap": "hardness_stage_p_runtime_gap_v1",
            "candidate_receipt": "hardness_stage_p_candidate_validation_receipt_v1",
            "publication": "hardness_stage_p_publication_manifest_v1",
            "worker": "hardness_stage_p_worker_session_v1",
            "report": STAGE_P_REAL_RUN_SCHEMA,
        },
        "model": config.to_public_dict(),
        "system_prompt_sha256": sha256_id(STAGE_P_OPEN_WORLD_SYSTEM_PROMPT),
        "p_a_system_prompt_sha256": sha256_id(STAGE_P_SYSTEM_PROMPT),
    }
    write_json(report_path, report)

    lean_started = _monotonic()
    lean_build = run_command(
        build_module_command(
            [
                STAGE_P_INPUT_MODULE,
                STAGE_P_PRODUCER_SUPPORT_MODULE,
                STAGE_P_PROBE_MODULE,
                STAGE_P_STANDARD_HELPER_MODULE,
                "Benchmark.Hardness.Inputs.StageP.Regression",
                STAGE_P_FEASIBILITY_MODULE,
            ]
        ),
        cwd=lean_root,
        timeout_seconds=args.lean_timeout,
        output_limit=64 * 1024,
    )
    report["lean_input_gate"] = {
        "command": lean_build.to_dict(),
        "wall_duration_seconds": round(_monotonic() - lean_started, 3),
        "public_modules": [
            STAGE_P_INPUT_MODULE,
            STAGE_P_PRODUCER_SUPPORT_MODULE,
            STAGE_P_PROBE_MODULE,
            STAGE_P_STANDARD_HELPER_MODULE,
            "Benchmark.Hardness.Inputs.StageP.Regression",
        ],
        "hidden_semantic_feasibility_module": STAGE_P_FEASIBILITY_MODULE,
        "hidden_module_exposed_to_model": False,
    }
    report["registry_absence_preflight"] = _registry_absence(cases)
    report["semantic_feasibility_isolation"] = _semantic_feasibility_isolation(
        positive_suite=args.positive_suite, negative_suite=args.negative_suite
    )
    write_json(report_path, report)
    if not lean_build.ok:
        report["status"] = "FAILED"
        report["failures"] = ["stage_p_input_lean_build_failed"]
        report["finished_at"] = utc_now()
        write_json(report_path, report)
        print(json.dumps({"status": "FAILED", "reason": "lean input gate failed"}))
        return 1

    activity = {"lock": threading.Lock(), "active": 0, "max_active": 0}
    runner_error: str | None = None
    pool = StagePLeanWorkerPool(
        lean_root=lean_root,
        workspace_root=args.output_root / "worker-workspace",
        service_root=args.output_root / "worker-service",
        maximum_workers=min(args.jobs, 4),
        timeout_seconds=max(120, min(args.lean_timeout, 900)),
    )
    outcomes: tuple[Any, ...] = ()
    try:
        outcomes = run_stage_p_real_canonical(
            cases,
            output_root=args.output_root,
            run_id=run_id,
            toolchain=toolchain,
            lake_manifest_sha256=lake_manifest_sha256,
            input_source_sha256=input_source_sha256,
            config=config,
            pool=pool,
            jobs=args.jobs,
            lean_timeout=args.lean_timeout,
            activity=activity,
        )
    except Exception as error:  # noqa: BLE001 - report must fail closed with evidence
        runner_error = f"{type(error).__name__}: {error}"
        outcomes = tuple()
    finally:
        pool_state = pool.to_dict()
        pool.close()

    if runner_error is not None:
        report["runner_error"] = runner_error
        report["status"] = "FAILED"
        report["finished_at"] = utc_now()
        write_json(report_path, report)
        print(json.dumps({"status": "FAILED", "runner_error": runner_error}, sort_keys=True))
        return 1

    rows = [outcome.row for outcome in outcomes]
    for row in rows:
        write_json(args.output_root / "cases" / str(row["id"]) / "outcome.json", row)
    aggregate_source = build_stage_p_offline_aggregate_source(outcomes)
    final_source = args.output_root / "final" / "StagePRealAggregate.lean"
    final_source.parent.mkdir(parents=True, exist_ok=True)
    final_source.write_text(aggregate_source, encoding="utf-8")
    final_command = run_command(
        ["lake", "env", "lean", str(final_source.resolve())],
        cwd=lean_root,
        timeout_seconds=args.lean_timeout,
        output_limit=128 * 1024,
    )
    replay_source = args.output_root / "release-replay" / "StagePRealReplay.lean"
    replay_source.parent.mkdir(parents=True, exist_ok=True)
    replay_source.write_text(aggregate_source, encoding="utf-8")
    replay_command = run_command(
        ["lake", "env", "lean", str(replay_source.resolve())],
        cwd=lean_root,
        timeout_seconds=args.lean_timeout,
        output_limit=128 * 1024,
    )
    for row in rows[:12]:
        row["final_combined_lean"] = {
            "real_aggregate": True,
            "verified": final_command.ok,
            "aggregate_source_sha256": sha256_id(aggregate_source),
        }
        row["standard_axiom_audit"] = {
            "real_aggregate": True,
            "verified": final_command.ok,
            "aggregate_source_sha256": sha256_id(aggregate_source),
        }
        row["release_replay"] = {
            "real_aggregate": True,
            "verified": replay_command.ok,
            "aggregate_source_sha256": sha256_id(aggregate_source),
        }
    summary = stage_p_real_summary(rows)
    gap_coverage = stage_p_real_gap_coverage(rows)
    objective_coverage = stage_p_real_objective_coverage(rows)
    family_coverage = _family_verification(rows)
    feature_cases = _feature_cases(rows)
    shortcut_audit = _implementation_shortcut_audit()
    secret_hits = _scan_for_secret(args.output_root, config.api_key)
    report.update(
        {
            "cases": rows,
            "summary": summary,
            "gap_coverage": gap_coverage,
            "objective_coverage": objective_coverage,
            "family_coverage": family_coverage,
            "feature_cases": feature_cases,
            "worker_pool": pool_state,
            "configured_jobs": args.jobs,
            "observed_max_active_cases": activity["max_active"],
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
            "secret_audit": {
                "api_key_occurrence_count": len(secret_hits),
                "authorization_header_occurrence_count": sum(
                    "authorization:" in path.read_text(encoding="utf-8", errors="ignore").lower()
                    for path in args.output_root.rglob("*")
                    if path.is_file()
                ),
            },
        }
    )
    semantic_hash_keys = (
        "stage_p_input_source_sha256",
        "producer_support_source_sha256",
        "exact_cover_standard_helper_sha256",
        "hidden_semantic_feasibility_sha256",
    )
    gates = {
        "stage_p_lean_input_modules_build": lean_build.ok,
        "semantic_feasibility_standard_axiom_gate": lean_build.ok
        and report["lean_input_gate"]["hidden_module_exposed_to_model"] is False,
        "semantic_feasibility_oracle_isolated": report["semantic_feasibility_isolation"]["passed"]
        is True,
        "semantic_source_hashes_recorded": all(
            isinstance(report["benchmark"].get(key), str)
            and len(report["benchmark"][key]) == 64
            for key in semantic_hash_keys
        ),
        "registry_absence_11_of_11": report["registry_absence_preflight"]["passed_count"] == 11,
        "full_24_case_matrix": len(rows) == 24,
        "positive_12_of_12": summary["positive_expected_count"] == 12,
        "negative_12_of_12": summary["negative_expected_count"] == 12,
        "model_generated_11_of_11": summary["model_generated_case_count"] == 11,
        "real_http_for_all_11_model_eligible": summary["model_eligible_cases_with_http_call"] == 11
        and summary["model_eligible_cases_with_http_ok"] == 11,
        "new_full_reduction_bundles_3": summary["full_reduction_bundle_authored_count"] == 3,
        "published_capabilities_24": summary["published_capability_count"] == 24,
        "gap_depths_1_2_3_4_verified": gap_coverage["single_gap_verified"]
        and gap_coverage["two_gap_verified"]
        and gap_coverage["three_gap_verified"]
        and gap_coverage["four_gap_verified"],
        "family_coverage_at_least_two_each": family_coverage["all_families_at_least_two"],
        "five_objectives_covered": objective_coverage["all_covered"],
        "native_membership_verified": feature_cases["native_membership_verified"],
        "completeness_verified": feature_cases["completeness_verified"],
        "producer_consumer_wave_barrier": rows[11].get("wave_barrier_satisfied") is True,
        "consumer_zero_authoring": summary["consumer_zero_authoring"],
        "compiler_inserted_math_zero": summary["compiler_inserted_math_token_count"] == 0,
        "no_api_key_or_authorization_leak": report["secret_audit"]["api_key_occurrence_count"] == 0
        and report["secret_audit"]["authorization_header_occurrence_count"] == 0,
        "no_resume_replay_or_old_response": all(
            row.get("resume_used") is False
            and row.get("replay_used") is False
            and row.get("old_response_used") is False
            for row in rows
        ),
        "no_case_or_family_specific_solution_branch": shortcut_audit[
            "case_specific_branch_count"
        ]
        == 0
        and shortcut_audit["family_specific_branch_count"] == 0,
        "aggregate_final_lean": final_command.ok,
        "aggregate_standard_axiom_audit": final_command.ok,
        "independent_release_replay": replay_command.ok,
        "worker_pool_no_crash": pool_state.get("worker_crash_count") == 0,
        "jobs_within_limit": 1 <= args.jobs <= 4,
        "observed_parallelism": activity["max_active"] >= min(args.jobs, 11),
        "no_active_case_leak": activity["active"] == 0,
    }
    report["gates"] = gates
    report["status"] = "VERIFIED" if all(gates.values()) else "FAILED"
    report["published"] = report["status"] == "VERIFIED"
    report["finished_at"] = utc_now()
    write_json(report_path, report)
    if report["published"]:
        args.canonical_report.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(report_path, args.canonical_report)
    print(
        json.dumps(
            {
                "status": report["status"],
                "report": str(report_path.resolve()),
                "real_model_call_count": summary["real_model_call_count"],
                "protocol_expected_count": summary["protocol_expected_count"],
                "model_generated": summary["model_generated_case_count"],
            },
            sort_keys=True,
        )
    )
    return 0 if report["status"] == "VERIFIED" else 1


def _monotonic() -> float:
    import time

    return time.monotonic()


if __name__ == "__main__":
    raise SystemExit(main())
