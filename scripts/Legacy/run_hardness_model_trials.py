#!/usr/bin/env python3
"""Run the Phase-7 model-authoring case repeatedly under isolated policies."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
POLICIES = ("model-auto", "model-required")
SCHEMA = "hardness_model_trials_v1"


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description=(
            "Repeat the hidden-gold Phase-7 model-authoring benchmark under "
            "model-auto and model-required without mixing deterministic lanes"
        )
    )
    command.add_argument(
        "--manifest",
        type=Path,
        default=ROOT / "Gate" / "MANIFEST.json",
    )
    command.add_argument(
        "--case", default="model-semantic-proof-authoring"
    )
    command.add_argument(
        "--policy", action="append", choices=POLICIES, default=[]
    )
    command.add_argument("--repetitions", type=int, default=3)
    command.add_argument("--env-file", type=Path, default=ROOT / ".env")
    command.add_argument("--lean-timeout", type=int, default=600)
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "model-trials",
    )
    return command


def _load_report(path: Path) -> dict[str, Any] | None:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return value if isinstance(value, dict) else None


def _compact_report(report: dict[str, Any] | None) -> dict[str, Any] | None:
    if report is None:
        return None
    return {
        "schema_version": report.get("schema_version"),
        "runner_version": report.get("runner_version"),
        "benchmark_id": report.get("benchmark_id"),
        "total": report.get("total"),
        "passed": report.get("passed"),
        "failed": report.get("failed"),
        "metrics": report.get("metrics"),
        "evaluation_lanes": report.get("evaluation_lanes"),
        "results": [
            {
                "id": result.get("id"),
                "actual_status": result.get("actual_status"),
                "passed": result.get("passed"),
                "model_call_count": result.get("model_call_count"),
                "model_usage": result.get("model_usage"),
                "authoring_attempt_count": result.get("authoring_attempt_count"),
                "authored_source_origin": result.get("authored_source_origin"),
                "report": result.get("report"),
            }
            for result in report.get("results", [])
            if isinstance(result, dict)
        ],
    }


def _policy_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    completed = [row for row in rows if isinstance(row.get("report"), dict)]
    passed = [row for row in completed if row["report"].get("failed") == 0]
    model_lane_rates = [
        row["report"]
        .get("evaluation_lanes", {})
        .get("model_synthesis", {})
        .get("outcome_accuracy")
        for row in completed
    ]
    return {
        "runs": len(rows),
        "reports_completed": len(completed),
        "all_cases_passed_runs": len(passed),
        "stable_all_passed": len(passed) == len(rows),
        "model_synthesis_outcome_accuracy": model_lane_rates,
    }


def main() -> int:
    arguments = parser().parse_args()
    if arguments.repetitions <= 0:
        parser().error("--repetitions must be positive")
    if arguments.lean_timeout <= 0:
        parser().error("--lean-timeout must be positive")
    policies = tuple(dict.fromkeys(arguments.policy or POLICIES))
    arguments.output_root.mkdir(parents=True, exist_ok=True)
    rows: list[dict[str, Any]] = []
    for policy in policies:
        for repetition in range(1, arguments.repetitions + 1):
            trial_root = arguments.output_root / policy / f"run-{repetition:02d}"
            command = [
                sys.executable,
                str(ROOT / "scripts" / "run_hardness_benchmark.py"),
                "--manifest",
                str(arguments.manifest),
                "--case",
                arguments.case,
                "--agent-phase",
                "7",
                "--planner",
                "deterministic",
                "--authoring",
                policy,
                "--env-file",
                str(arguments.env_file),
                "--lean-timeout",
                str(arguments.lean_timeout),
                "--output-root",
                str(trial_root),
            ]
            started = time.monotonic()
            completed = subprocess.run(
                command,
                cwd=ROOT,
                capture_output=True,
                text=True,
                check=False,
            )
            report_path = trial_root / "report.json"
            compact_report = _compact_report(_load_report(report_path))
            rows.append(
                {
                    "policy": policy,
                    "repetition": repetition,
                    "return_code": completed.returncode,
                    "duration_seconds": round(time.monotonic() - started, 3),
                    "report_file": str(report_path.resolve()),
                    "report": compact_report,
                    "stdout_sha256": hashlib.sha256(
                        completed.stdout.encode("utf-8")
                    ).hexdigest(),
                    "stderr_sha256": hashlib.sha256(
                        completed.stderr.encode("utf-8")
                    ).hexdigest(),
                }
            )
    summary = {
        policy: _policy_summary([row for row in rows if row["policy"] == policy])
        for policy in policies
    }
    report = {
        "schema_version": SCHEMA,
        "case": arguments.case,
        "repetitions": arguments.repetitions,
        "policies": list(policies),
        "summary": summary,
        "runs": rows,
    }
    report_path = arguments.output_root / "report.json"
    report_path.write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(report, ensure_ascii=False, sort_keys=True))
    return 0 if all(value["stable_all_passed"] for value in summary.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
