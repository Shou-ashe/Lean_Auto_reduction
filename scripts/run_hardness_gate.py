#!/usr/bin/env python3
"""Unified gate entry: rerun every non-benchmark lane and check stability.

Gate lanes (from GATE_REGISTRY.json) never merge into benchmark credit:
  - fixture_protocol: v1 protocol/fixture suites through the manifest lane driver
  - capability_safety: C0-safety negatives via the capability driver
  - unified_registry:  de-duplicated logical cases via the unified driver
  - archived_drivers:  legacy suites kept runnable via their original drivers

All lanes are consolidated under one gate root.  Each gate run writes a
single <output-root>/trial-<n>/ directory per trial (with gate_report.json
per trial); --stability-trials N reruns the selected lanes N times and
compares per-case status across trials; any drift fails the gate.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.benchmark import load_benchmark_manifest  # noqa: E402
from agent.hardness.np_hard_capability import (  # noqa: E402
    load_capability_bundle,
)

HARDNESS = ROOT / "Benchmark" / "Hardness"
GATE = ROOT / "Gate"
SCRIPTS = ROOT / "scripts"
LEGACY = SCRIPTS / "Legacy"
GATE_REGISTRY = GATE / "GATE_REGISTRY.json"
GATE_MANIFEST = GATE / "GATE_MANIFEST.json"
CAPABILITY_MANIFEST = HARDNESS / "CAPABILITY_MANIFEST_V2.json"
UNIFIED_REGISTRY = ROOT / "Gate/NP_HARD_UNIFIED_BENCHMARK_REGISTRY.json"
UNIFIED_TAXONOMY = ROOT / "Gate/BENCHMARK_TAXONOMY.json"
CAPABILITY_SPLITS = ("dev", "validation", "heldout")

ARCHIVED_DRIVERS = {
    "run_np_hard_h_e_heldout.py": ("--output-root", "--env-file"),
    "run_np_hard_h_f_qualification.py": ("--output-root", "--jobs", "--timeout"),
    "run_np_hard_h_h_existing_routes.py": ("--output-root", "--jobs"),
    "run_np_hard_hub_selection_benchmark.py": ("--output-root",),
    "run_np_hard_mvp_offline.py": ("--output-root",),
    "run_quals_offline_benchmark.py": ("--output-root", "--jobs"),
}

GATE_LANES = ("fixture_protocol", "capability_safety", "unified_registry", "archived_drivers")


def _read_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def _load_registry(arguments: argparse.Namespace) -> dict[str, Any]:
    path = (
        arguments.registry.resolve()
        if arguments.registry is not None
        else GATE_REGISTRY
    )
    registry = _read_json(path)
    if registry.get("schema_version") != "hardness_gate_registry_v1":
        raise ValueError(f"unsupported gate registry schema: {registry.get('schema_version')!r}")
    if registry.get("benchmark_id") != "np-hard-gate-v1":
        raise ValueError(f"unexpected gate registry benchmark_id: {registry.get('benchmark_id')!r}")
    return registry


def _validate_registry(registry: dict[str, Any]) -> None:
    manifest = load_benchmark_manifest(GATE_MANIFEST.resolve())
    lane = registry["lanes"]["fixture_protocol"]
    registry_suite_counts = lane["suite_case_counts"]
    by_name = {Path(suite.source_file).name: suite for suite in manifest.suites}
    for suite_file, count in registry_suite_counts.items():
        name = Path(suite_file).name
        if name not in by_name:
            raise ValueError(f"gate registry suite {suite_file!r} is outside GATE_MANIFEST.json")
        if len(by_name[name].cases) != count:
            raise ValueError(
                f"gate registry suite {suite_file!r} case count drifted ({by_name[name]!r})"
            )
    manifest_ids = {case.id for suite in manifest.suites for case in suite.cases}
    for case_row in registry["cases"]:
        if case_row["lane"] == "fixture_protocol" and case_row["case_id"] not in manifest_ids:
            raise ValueError(
                f"gate case {case_row['case_id']!r} is outside GATE_MANIFEST.json"
            )
    safety_ids = _safety_case_ids(registry)
    bundle = load_capability_bundle(CAPABILITY_MANIFEST.resolve(), root=ROOT, verify_oracle=False)
    public_ids = {
        case.case_id
        for split in CAPABILITY_SPLITS
        for case in bundle.suites[split].cases
    }
    for case_id in safety_ids:
        if case_id not in public_ids or "-sf-" not in case_id:
            raise ValueError(
                f"capability_safety case {case_id!r} is not a C0-safety negative in dev/validation/heldout"
            )
    for entry in registry["lanes"]["archived_drivers"]["drivers"]:
        driver = entry.get("driver")
        if driver is None:
            continue
        if driver not in ARCHIVED_DRIVERS:
            raise ValueError(f"archived driver {driver!r} is not supported by the gate runner")
        suite_file = GATE / "Suites" / entry["suite_file"]
        if not suite_file.is_file():
            raise ValueError(f"archived driver suite {entry['suite_file']!r} is missing")
        if not (SCRIPTS / driver).is_file():
            raise ValueError(f"archived driver script {driver!r} is missing")


def _safety_case_ids(registry: Mapping[str, Any]) -> tuple[str, ...]:
    return tuple(
        case["case_id"]
        for case in registry["cases"]
        if case["lane"] == "capability_safety"
    )


def _archived_entries(registry: Mapping[str, Any]) -> list[dict[str, Any]]:
    return list(registry["lanes"]["archived_drivers"]["drivers"])


def _run_process(command: list[str], *, cwd: Path) -> tuple[int, str]:
    completed = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        capture_output=True,
        timeout=None,
    )
    return completed.returncode, (completed.stdout or "") + (completed.stderr or "")


def _lane_command(
    *,
    lane: str,
    trial_dir: Path,
    arguments: argparse.Namespace,
    registry: Mapping[str, Any],
) -> list[list[str]]:
    if lane == "fixture_protocol":
        return [
            [
                sys.executable,
                str(LEGACY / "run_hardness_benchmark_manifest.py"),
                "--manifest",
                str(GATE_MANIFEST),
                "--output-root",
                str(trial_dir / lane),
                "--jobs",
                str(arguments.jobs),
                "--env-file",
                str(arguments.env_file),
            ]
        ]
    if lane == "capability_safety":
        command = [
            sys.executable,
            str(SCRIPTS / "run_np_hard_capability_benchmark.py"),
            "--manifest",
            str(CAPABILITY_MANIFEST),
            "--output-root",
            str(trial_dir / lane),
            "--env-file",
            str(arguments.env_file),
            "--jobs",
            str(arguments.jobs),
        ]
        for split in CAPABILITY_SPLITS:
            command.extend(("--split", split))
        command.extend(("--case-ids", *_safety_case_ids(registry)))
        return [command]
    if lane == "unified_registry":
        return [
            [
                sys.executable,
                str(SCRIPTS / "run_np_hard_unified_benchmark.py"),
                "--registry",
                str(UNIFIED_REGISTRY),
                "--taxonomy",
                str(UNIFIED_TAXONOMY),
                "--selector",
                "all",
                "--output-root",
                str(trial_dir / lane),
                "--report",
                str(trial_dir / lane / "report.json"),
                "--env-file",
                str(arguments.env_file),
                "--jobs",
                str(arguments.jobs),
            ]
        ]
    if lane == "archived_drivers":
        commands: list[list[str]] = []
        for entry in _archived_entries(registry):
            driver = entry.get("driver")
            if driver is None:
                continue
            command = [sys.executable, str(SCRIPTS / driver)]
            for flag in ARCHIVED_DRIVERS[driver]:
                if flag == "--output-root":
                    command.extend(
                        (flag, str(trial_dir / lane / entry["driver"].rsplit(".", 1)[0]))
                    )
                elif flag == "--jobs":
                    command.extend((flag, str(arguments.jobs)))
                elif flag == "--timeout":
                    command.extend((flag, "1200"))
                elif flag == "--env-file":
                    command.extend((flag, str(arguments.env_file)))
            commands.append(command)
        return commands
    raise ValueError(f"unknown gate lane {lane!r}")


def _per_case_status(lane: str, trial_dir: Path) -> dict[str, str]:
    if lane == "fixture_protocol":
        report = _read_json(trial_dir / lane / "report.json")
        return {
            str(row["id"]): str(row["actual_status"])
            for row in report.get("results", [])
        }
    if lane == "capability_safety":
        report = _read_json(trial_dir / lane / "report.json")
        return {
            str(row["case_id"]): str(row["public_status"])
            for row in report.get("cases", [])
        }
    if lane == "unified_registry":
        report = _read_json(trial_dir / lane / "report.json")
        return {
            str(row["source_case_id"]): str(row["status"])
            for row in report.get("cases", [])
        }
    raise ValueError(f"per-case status not defined for lane {lane!r}")


def _stability_compare(
    *, lane: str, trial_dir: Path, trials: int,
) -> dict[str, Any]:
    fingerprints: list[Mapping[str, str]] = []
    for trial in range(1, trials + 1):
        fingerprint = _per_case_status(lane, trial_dir / f"trial-{trial}")
        fingerprints.append(fingerprint)
    first = fingerprints[0]
    drift: list[dict[str, Any]] = []
    for case_id in sorted(first):
        statuses = [fingerprint.get(case_id) for fingerprint in fingerprints]
        if len(set(statuses)) > 1:
            drift.append({"case_id": case_id, "statuses": statuses})
    return {
        "lane": lane,
        "trials": trials,
        "case_count": len(first),
        "stable": len(drift) == 0,
        "drifted_cases": drift,
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Unified gate entry: rerun every non-benchmark lane and check stability"
    )
    parser.add_argument(
        "--registry",
        type=Path,
        default=None,
        help="defaults to Gate/GATE_REGISTRY.json",
    )
    parser.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "gate",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=4,
        help="case parallelism; must be in 1..4 where a lane supports it",
    )
    parser.add_argument(
        "--lane",
        action="append",
        choices=GATE_LANES,
        default=None,
        help="restrict to a lane (repeatable); defaults to all four",
    )
    parser.add_argument(
        "--stability-trials",
        type=int,
        default=1,
        help="number of full reruns to compare for per-case drift; defaults to 1",
    )
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument(
        "--list",
        action="store_true",
        help="validate the gate registry and list lane cases without executing anything",
    )
    return parser


def _write_trial_report(
    *,
    trial_dir: Path,
    registry: Mapping[str, Any],
    lanes: tuple[str, ...],
) -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for lane in lanes:
        if lane == "archived_drivers":
            continue
        for case_id, status in _per_case_status(lane, trial_dir).items():
            rows.append({"case_id": case_id, "lane": lane, "status": status})
    report = {
        "schema_version": "hardness_gate_trial_report_v1",
        "benchmark_id": registry["benchmark_id"],
        "trial_dir": str(trial_dir.resolve()),
        "case_count": len(rows),
        "cases": rows,
    }
    (trial_dir / "gate_report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    return report


def main() -> int:
    arguments = build_parser().parse_args()
    if arguments.jobs <= 0 or arguments.jobs > 4:
        print(json.dumps({"run_valid": False, "failure_code": "gate_jobs_invalid"}, ensure_ascii=False))
        return 2
    if arguments.stability_trials <= 0:
        print(json.dumps({"run_valid": False, "failure_code": "gate_trials_invalid"}, ensure_ascii=False))
        return 2
    try:
        registry = _load_registry(arguments)
        _validate_registry(registry)
        if arguments.list:
            by_kind: dict[str, list[str]] = {}
            for case_row in registry["cases"]:
                by_kind.setdefault(str(case_row["lane"]), []).append(str(case_row["case_id"]))
            print(
                json.dumps(
                    {
                        "benchmark_id": registry["benchmark_id"],
                        "case_count": registry["lane_case_counts"],
                        "unique_case_count": len(registry["cases"]),
                        "lanes": by_kind,
                    },
                    ensure_ascii=False,
                    indent=2,
                    sort_keys=True,
                )
            )
            return 0
        arguments.output_root.mkdir(parents=True, exist_ok=True)
        lanes = arguments.lane or list(GATE_LANES)
        stability: list[dict[str, Any]] = []
        for lane in lanes:
            if arguments.stability_trials == 1:
                trial_dir = arguments.output_root / "trial-1"
                trial_dir.mkdir(parents=True, exist_ok=True)
                commands = _lane_command(
                    lane=lane, trial_dir=trial_dir, arguments=arguments, registry=registry
                )
                failures: list[str] = []
                for command in commands:
                    code, output = _run_process(command, cwd=ROOT)
                    if code != 0:
                        failures.append(f"{command[1]}: {output[-800:]}")
                if failures:
                    print(
                        json.dumps(
                            {"run_valid": False, "lane": lane, "failures": failures},
                            ensure_ascii=False,
                            indent=2,
                        )
                    )
                    return 3
            else:
                drifted: list[dict[str, Any]] = []
                for trial in range(1, arguments.stability_trials + 1):
                    trial_dir = arguments.output_root / f"trial-{trial}"
                    trial_dir.mkdir(parents=True, exist_ok=True)
                    commands = _lane_command(
                        lane=lane, trial_dir=trial_dir, arguments=arguments, registry=registry
                    )
                    for command in commands:
                        code, output = _run_process(command, cwd=ROOT)
                        if code != 0:
                            drifted.append(
                                {
                                    "trial": trial,
                                    "command": command[1],
                                    "failure": output[-800:],
                                }
                            )
                stability.append(
                    _stability_compare(
                        lane=lane,
                        trial_dir=arguments.output_root,
                        trials=arguments.stability_trials,
                    )
                )
                if drifted:
                    print(
                        json.dumps(
                            {
                                "run_valid": False,
                                "lane": lane,
                                "trial_failures": drifted,
                            },
                            ensure_ascii=False,
                            indent=2,
                        )
                    )
                    return 4
        # consolidate the running trials into one gate directory: each trial
        # dir holds its own gate_report.json; stability lives in summary.json
        if arguments.lane is None:
            for trial_dir in sorted(
                arguments.output_root.glob("trial-*"),
                key=lambda p: int(p.name.split("-")[1]),
            ):
                _write_trial_report(
                    trial_dir=trial_dir, registry=registry, lanes=tuple(lanes)
                )
        stability_summary = {
            "schema_version": "hardness_gate_summary_v1",
            "benchmark_id": registry["benchmark_id"],
            "stability_trials": arguments.stability_trials,
            "lanes": stability or None,
            "drifted_cases": [
                {"lane": item["lane"], "cases": item["drifted_cases"]}
                for item in stability
                if item.get("drifted_cases")
            ],
        }
        (arguments.output_root / "summary.json").write_text(
            json.dumps(stability_summary, indent=2, sort_keys=True, ensure_ascii=False) + "\n",
            encoding="utf-8",
        )
        print(json.dumps(stability_summary, ensure_ascii=False, indent=2, sort_keys=True))
        drifted_total = sum(len(item.get("drifted_cases", [])) for item in stability)
        return 1 if drifted_total else 0
    except (OSError, UnicodeError, ValueError, json.JSONDecodeError) as error:
        print(
            json.dumps(
                {
                    "run_valid": False,
                    "failure_code": getattr(error, "code", "gate_runner_failed"),
                    "error": str(error),
                },
                ensure_ascii=False,
            )
        )
        return 2


if __name__ == "__main__":
    raise SystemExit(main())