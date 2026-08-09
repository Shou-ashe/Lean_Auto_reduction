#!/usr/bin/env python3
"""Build the Stage O three-run real-DeepSeek stability aggregate."""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.stage_o_contract import stability_aggregate_skeleton  # noqa: E402


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    command.add_argument("reports", nargs=3, type=Path)
    command.add_argument(
        "--output",
        type=Path,
        default=ROOT / "Benchmark/Hardness/STAGE_O_MULTI_GAP_STABILITY_AGGREGATE.json",
    )
    return command


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"stability report is not an object: {path}")
    return value


def main() -> int:
    args = parser().parse_args()
    reports = [load(path.resolve()) for path in args.reports]
    aggregate = stability_aggregate_skeleton()
    aggregate["run_reports"] = [str(path.resolve()) for path in args.reports]
    run_ids = [report.get("run_id") for report in reports]
    output_roots = [report.get("output_root") for report in reports]
    case_ids = sorted(
        {
            row.get("case_id")
            for report in reports
            for row in report.get("cases", [])
            if isinstance(row.get("case_id"), str)
        }
    )
    outcome_matrix: dict[str, list[dict[str, Any]]] = {case_id: [] for case_id in case_ids}
    gap_sequences: dict[str, list[dict[str, Any]]] = defaultdict(list)
    choice_distribution: dict[str, Counter[str]] = defaultdict(Counter)
    artifact_hashes: Counter[str] = Counter()
    for index, report in enumerate(reports, start=1):
        for row in report.get("cases", []):
            case_id = row["case_id"]
            outcome_matrix[case_id].append(
                {
                    "run": index,
                    "status": row.get("status"),
                    "failure_code": row.get("final_failure_code"),
                    "expected": row.get("expected_scoring", {}).get("matches"),
                }
            )
            trace = row.get("sequential_trace")
            if isinstance(trace, dict):
                gap_sequences[case_id].append(
                    {
                        "run": index,
                        "states": trace.get("states", []),
                        "gap_ids": trace.get("gap_ids", []),
                        "fresh_core_resolve_count": trace.get("fresh_core_resolve_count"),
                        "complete": trace.get("complete"),
                    }
                )
            for selection in row.get("selections", []):
                packet_id = selection.get("selected_packet_id") or "BLOCKED"
                choice_distribution[case_id][packet_id] += 1
        for artifact in report.get("artifacts", []):
            value = artifact.get("final_source_sha256")
            if isinstance(value, str):
                artifact_hashes[value] += 1

    outcome_ok = all(
        len(entries) == 3 and all(entry["expected"] is True for entry in entries)
        for entries in outcome_matrix.values()
    ) and len(outcome_matrix) == 16
    gap_ok = len(gap_sequences) == 2 and all(
        len(entries) == 3
        and all(
            entry["complete"] is True
            and entry["fresh_core_resolve_count"] == 2
            and len(entry["gap_ids"]) == 2
            and len(set(entry["gap_ids"])) == 2
            for entry in entries
        )
        for entries in gap_sequences.values()
    )
    reuse_ok = all(
        report.get("metrics", {}).get("published_capability_reuse_rate") == 1.0
        and report.get("metrics", {}).get("consumer_zero_authoring_rate") == 1.0
        for report in reports
    )
    ablation_ok = all(
        len(report.get("ablation_replays", [])) == 2
        and all(row.get("success") is True for row in report["ablation_replays"])
        for report in reports
    )
    lean_ok = all(
        report.get("gates", {}).get("final_combined_lean") is True
        and report.get("gates", {}).get("independent_release_replay") is True
        for report in reports
    )
    independent = len(set(run_ids)) == 3 and len(set(output_roots)) == 3
    reports_verified = all(
        report.get("status") == "VERIFIED"
        and report.get("qualification") == "stability"
        and report.get("published") is True
        for report in reports
    )
    aggregate["outcome_matrix"] = outcome_matrix
    aggregate["typed_gap_sequences"] = dict(gap_sequences)
    aggregate["reuse"] = {"all_runs_pass": reuse_ok}
    aggregate["ablations"] = {"all_runs_pass": ablation_ok}
    aggregate["route_packet_choice_distribution"] = {
        case_id: dict(counter) for case_id, counter in choice_distribution.items()
    }
    aggregate["artifact_hash_distribution"] = dict(artifact_hashes)
    aggregate["lean_release_replay"] = {"all_runs_pass": lean_ok}
    aggregate["summary"] = {
        "run_count": len(reports),
        "independent_run_ids": len(set(run_ids)),
        "independent_output_roots": len(set(output_roots)),
        "case_count": len(outcome_matrix),
        "all_reports_verified": reports_verified,
        "outcomes_stable": outcome_ok,
        "typed_gap_sequences_stable": gap_ok,
        "reuse_stable": reuse_ok,
        "ablations_stable": ablation_ok,
        "lean_release_replay_stable": lean_ok,
    }
    aggregate["status"] = (
        "VERIFIED"
        if all((independent, reports_verified, outcome_ok, gap_ok, reuse_ok, ablation_ok, lean_ok))
        else "FAILED"
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(aggregate, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({"status": aggregate["status"], "report": str(args.output.resolve())}))
    return 0 if aggregate["status"] == "VERIFIED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
