#!/usr/bin/env python3
"""Run the frozen Stage P 20x cold/persistent Lean worker qualification."""

from __future__ import annotations

import argparse
import json
import os
import shutil
import sys
from dataclasses import replace
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.lean_worker_pool import (  # noqa: E402
    StagePLeanWorkerKey,
    StagePLeanWorkerPool,
)
from agent.hardness.models import sha256_id  # noqa: E402
from agent.hardness.stage_p_contract import (  # noqa: E402
    StagePContractError,
    load_and_validate_stage_p_worker_microbenchmark,
)


DEFAULT_CONTRACT = ROOT / "Gate/Suites/stage_p_lean_worker_microbenchmark.json"
DEFAULT_CANONICAL_REPORT = ROOT / "Reports/STAGE_P_LEAN_WORKER_REPORT.json"
PROBE_SOURCE = ROOT / "Lean/Reference/Reports/Inputs/StageP/ContractProbes.lean"
NAMESPACE = "StagePWorkerQualification.Session"


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
        raise ValueError(f"Stage P worker output root must be fresh and empty: {path}")
    path.mkdir(parents=True, exist_ok=True)


def build_benchmark_source() -> str:
    return (
        "import Benchmark.Hardness.Inputs.StageP.ContractProbes\n\n"
        f"namespace {NAMESPACE}\n\n"
        "def candidate : "
        "Benchmark.Hardness.Inputs.StageP.ContractProbes.proofProbe := by\n"
        "  intro value\n"
        "  rfl\n\n"
        f"end {NAMESPACE}\n"
    )


def build_worker_key(
    *, lean_root: Path, source: str, session_id: str
) -> StagePLeanWorkerKey:
    return StagePLeanWorkerKey(
        toolchain=(lean_root / "lean-toolchain").read_text(encoding="utf-8").strip(),
        lake_manifest_sha256=sha256_id(
            (lean_root / "lake-manifest.json").read_text(encoding="utf-8")
        ),
        base_registry_fingerprint=sha256_id("stage-p-worker-qualification-base-registry-v1"),
        complete_source_sha256=sha256_id(source),
        dependency_sha256=(
            sha256_id(PROBE_SOURCE.read_text(encoding="utf-8")),
        ),
        namespace=NAMESPACE,
        session_id=session_id,
        editable_allowlist=("candidate_body",),
    )


def _expect_code(operation: Callable[[], object], code: str) -> bool:
    try:
        operation()
    except StagePContractError as error:
        return error.code == code
    return False


def _mem_total_bytes() -> int | None:
    try:
        for line in Path("/proc/meminfo").read_text(encoding="utf-8").splitlines():
            if line.startswith("MemTotal:"):
                return int(line.split()[1]) * 1024
    except (OSError, ValueError, IndexError):
        return None
    return None


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    command.add_argument("--contract", type=Path, default=DEFAULT_CONTRACT)
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent/stage-p-lean-worker-benchmark",
    )
    command.add_argument(
        "--canonical-report", type=Path, default=DEFAULT_CANONICAL_REPORT
    )
    command.add_argument("--lean-timeout", type=int, default=300)
    command.add_argument("--cold-parallelism", type=int, default=2)
    return command


def main() -> int:
    args = parser().parse_args()
    contract = load_and_validate_stage_p_worker_microbenchmark(args.contract)
    maximum_workers = int(contract["maximum_workers"])
    repeat_count = int(contract["repeat_count"])
    if not 1 <= args.cold_parallelism <= maximum_workers:
        raise ValueError("cold parallelism must be within the frozen worker bound")
    prepare_fresh_output_root(args.output_root)
    if args.canonical_report.exists():
        raise ValueError(
            f"canonical Stage P worker report already exists: {args.canonical_report}"
        )

    report_path = args.output_root / "report.json"
    source_path = args.output_root / "candidate" / "Validation.lean"
    source_path.parent.mkdir(parents=True, exist_ok=False)
    source = build_benchmark_source()
    source_path.write_text(source, encoding="utf-8")
    lean_root = ROOT / "Lean"
    report: dict[str, Any] = {
        "schema_version": "hardness_stage_p_lean_worker_report_v1",
        "status": "FAILED",
        "started_at": utc_now(),
        "output_root": str(args.output_root.resolve()),
        "contract": contract,
        "environment": {
            "cpu_count": os.cpu_count(),
            "memory_total_bytes": _mem_total_bytes(),
            "cold_parallelism": args.cold_parallelism,
        },
        "source": {
            "path": str(source_path.resolve()),
            "source_sha256": sha256_id(source),
            "dependency_source_sha256": sha256_id(
                PROBE_SOURCE.read_text(encoding="utf-8")
            ),
        },
    }
    write_json(report_path, report)

    pool = StagePLeanWorkerPool(
        lean_root=lean_root,
        workspace_root=ROOT,
        service_root=args.output_root / "worker-service",
        maximum_workers=maximum_workers,
        timeout_seconds=args.lean_timeout,
    )
    try:
        session_id = pool.start_session(owner="worker-qualification", namespace=NAMESPACE)
        key = build_worker_key(
            lean_root=lean_root, source=source, session_id=session_id
        )
        performance = pool.microbenchmark(
            session_id=session_id,
            owner="worker-qualification",
            key=key,
            source_path=source_path,
            dependency_sha256=key.dependency_sha256,
            repeat_count=repeat_count,
            cold_parallelism=args.cold_parallelism,
        )

        first_cached = pool.validate(
            session_id=session_id,
            owner="worker-qualification",
            key=key,
            source_path=source_path,
            dependency_sha256=key.dependency_sha256,
            use_cache=True,
            allow_cold_fallback=False,
        )
        exact_hit = pool.validate(
            session_id=session_id,
            owner="worker-qualification",
            key=key,
            source_path=source_path,
            dependency_sha256=key.dependency_sha256,
            use_cache=True,
            allow_cold_fallback=False,
        )
        foreign_owner_rejected = _expect_code(
            lambda: pool.validate(
                session_id=session_id,
                owner="foreign-owner",
                key=key,
                source_path=source_path,
                dependency_sha256=key.dependency_sha256,
            ),
            "lean_worker_session_leak",
        )
        foreign_namespace_rejected = _expect_code(
            lambda: pool.validate(
                session_id=session_id,
                owner="worker-qualification",
                key=replace(key, namespace="StagePWorkerQualification.Foreign"),
                source_path=source_path,
                dependency_sha256=key.dependency_sha256,
            ),
            "lean_worker_session_leak",
        )
        dependency_mismatch_rejected = _expect_code(
            lambda: pool.validate(
                session_id=session_id,
                owner="worker-qualification",
                key=key,
                source_path=source_path,
                dependency_sha256=(sha256_id("mutated-dependency"),),
            ),
            "lean_worker_stale_result",
        )

        backup_path = source_path.with_suffix(".lean.saved")
        source_path.replace(backup_path)
        try:
            deletion_after_cache_rejected = _expect_code(
                lambda: pool.validate(
                    session_id=session_id,
                    owner="worker-qualification",
                    key=key,
                    source_path=source_path,
                    dependency_sha256=key.dependency_sha256,
                ),
                "lean_worker_stale_result",
            )
        finally:
            backup_path.replace(source_path)

        changed_source = source.replace("  rfl\n", "  exact Eq.refl value\n")
        source_path.write_text(changed_source, encoding="utf-8")
        try:
            stale_source_rejected = _expect_code(
                lambda: pool.validate(
                    session_id=session_id,
                    owner="worker-qualification",
                    key=key,
                    source_path=source_path,
                    dependency_sha256=key.dependency_sha256,
                ),
                "lean_worker_stale_result",
            )
        finally:
            source_path.write_text(source, encoding="utf-8")

        distinct_keys = {
            "registry": replace(
                key, base_registry_fingerprint=sha256_id("changed-registry")
            ).cache_key
            != key.cache_key,
            "toolchain": replace(key, toolchain=key.toolchain + "-changed").cache_key
            != key.cache_key,
            "dependency": replace(
                key, dependency_sha256=(sha256_id("changed-dependency"),)
            ).cache_key
            != key.cache_key,
            "source": replace(
                key, complete_source_sha256=sha256_id(changed_source)
            ).cache_key
            != key.cache_key,
        }
        entries_before_restart = pool.to_dict()["cache_entry_count"]
        pool.restart_all()
        restart_invalidated_cache = (
            entries_before_restart >= 1 and pool.to_dict()["cache_entry_count"] == 0
        )
        isolation = {
            "exact_cache_hit": first_cached.verified and exact_hit.cache_hit,
            "session_ownership_rejected": foreign_owner_rejected,
            "namespace_isolation_rejected": foreign_namespace_rejected,
            "dependency_mismatch_rejected": dependency_mismatch_rejected,
            "deletion_after_cache_rejected": deletion_after_cache_rejected,
            "stale_source_rejected": stale_source_rejected,
            "complete_key_changes_on_all_content_dimensions": all(
                distinct_keys.values()
            ),
            "restart_invalidated_cache": restart_invalidated_cache,
        }
        report["performance"] = performance
        report["isolation"] = {
            **isolation,
            "content_dimension_key_checks": distinct_keys,
            "pass_rate": sum(isolation.values()) / len(isolation),
        }
        report["pool"] = pool.to_dict()
        gates = {
            "frozen_20_repeat_4_worker_contract": repeat_count == 20
            and maximum_workers == 4,
            "warm_p50_over_cold_p50": performance["gates"][
                "warm_p50_over_cold_p50"
            ],
            "wall_time_reduction": performance["gates"]["wall_time_reduction"],
            "worker_count_within_limit": performance["gates"][
                "worker_count_within_limit"
            ],
            "isolation_and_stale_rejection_100_percent": all(isolation.values()),
            "no_performance_fallback": performance["pool"]["cold_fallback_count"]
            == 0,
            "no_worker_crash_during_performance": performance["pool"][
                "worker_crash_count"
            ]
            == 0,
        }
        report["gates"] = gates
        report["status"] = "VERIFIED" if all(gates.values()) else "FAILED"
    except Exception as error:
        report["runner_error"] = f"{type(error).__name__}: {error}"
        report.setdefault("gates", {})["runner_completed"] = False
    finally:
        pool.close()
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
                "cold_p50_seconds": report.get("performance", {}).get(
                    "cold_p50_seconds"
                ),
                "warm_p50_seconds": report.get("performance", {}).get(
                    "warm_p50_seconds"
                ),
            },
            sort_keys=True,
        )
    )
    return 0 if report["status"] == "VERIFIED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
