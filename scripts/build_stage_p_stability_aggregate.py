#!/usr/bin/env python3
"""Build the Stage P three-run real-DeepSeek stability aggregate (P-C).

The three input reports must be fully independent real DeepSeek 24-case runs
recorded by scripts/run_deepseek_stage_p_open_world_benchmark.py.  Stability is
judged on outcome, gap sequence, source provenance, repair trajectory,
publication/reuse, artifact Lean/replay and security gates; artifact hash
diversity between runs is allowed because every artifact is independently
validated by its own final combined Lean and release replay.
"""

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


STAGE_P_REAL_RUN_SCHEMA = "hardness_stage_p_implementation_real_report_v1"
POSITIVE_IDS = {
    "p-single-semantic-proof",
    "p-single-program-definition",
    "p-single-direct-tm",
    "p-single-native-membership",
    "p-two-gap-presentation-reduction",
    "p-three-gap-program-semantics-direct-tm",
    "p-four-gap-presentation-program-semantics-direct-tm",
    "p-full-bundle-graph-to-csp",
    "p-full-bundle-numeric-to-graph",
    "p-full-bundle-set-completeness",
    "p-capability-producer",
}
NEGATIVE_IDS = {
    "p-authoring-budget-exhausted",
    "p-fabricated-declaration-handle",
    "p-gap-cycle-or-repeat",
    "p-gold-or-oracle-import",
    "p-impossible-semantic-goal",
    "p-local-pass-final-resolution-fail",
    "p-prompt-injection-request-mutation",
    "p-sorry-axiom-unsafe-candidate",
    "p-stale-gap-dependency",
    "p-unauthorized-file-edit",
    "p-wrong-direction-candidate",
    "p-wrong-endpoint-candidate",
}
CONSUMER_ID = "p-capability-consumer"


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    command.add_argument("reports", nargs=3, type=Path)
    command.add_argument(
        "--output",
        type=Path,
        default=ROOT / "Benchmark/Hardness/STAGE_P_OPEN_WORLD_STABILITY_AGGREGATE.json",
    )
    return command


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"stability report is not an object: {path}")
    return value


def rows_by_id(report: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {row.get("id"): row for row in report.get("cases", []) if isinstance(row, dict)}


def main() -> int:
    args = parser().parse_args()
    reports = [load(path.resolve()) for path in args.reports]
    run_ids = [report.get("run_id") for report in reports]
    output_roots = [report.get("output_root") for report in reports]
    started_ats = [report.get("started_at") for report in reports]
    schemas = [report.get("schema_version") for report in reports]
    all_rows = [rows_by_id(report) for report in reports]
    case_ids = sorted({case_id for rows in all_rows for case_id in rows})

    outcome_matrix: dict[str, list[dict[str, Any]]] = {case_id: [] for case_id in case_ids}
    gap_sequences: dict[str, list[dict[str, Any]]] = defaultdict(list)
    repair_trajectories: dict[str, list[dict[str, Any]]] = defaultdict(list)
    provenance: dict[str, list[dict[str, Any]]] = defaultdict(list)
    publication_counts: dict[str, list[int]] = defaultdict(list)
    artifact_hashes: Counter[str] = Counter()
    per_run = []
    for index, (report, rows) in enumerate(zip(reports, all_rows), start=1):
        summary = report.get("summary") or {}
        gates = report.get("gates") or {}
        for case_id in case_ids:
            row = rows.get(case_id)
            if row is None:
                outcome_matrix[case_id].append({"run": index, "status": None})
                continue
            expected = row.get("expected_status")
            outcome_matrix[case_id].append(
                {
                    "run": index,
                    "status": row.get("status"),
                    "failure_code": row.get("failure_code"),
                    "expected_failure_code": row.get("expected_failure_code"),
                    "expected_status": expected,
                    "protocol_matches_expected": row.get("protocol_matches_expected"),
                }
            )
            gap_sequences[case_id].append(
                {
                    "run": index,
                    "gap_count": row.get("gap_count"),
                    "gap_depth": row.get("gap_depth"),
                    "fresh_core_resolve_count": row.get("fresh_core_resolve_count"),
                    "publication_count": len(row.get("publications") or []),
                    "resolver": row.get("resolver"),
                    "complete": row.get("status") == row.get("expected_status"),
                }
            )
            repair_trajectories[case_id].append(
                {
                    "run": index,
                    "semantic_turns": len(row.get("calls") or []),
                    "model_generated": row.get("model_generated"),
                    "model_generated_body_count": row.get("model_generated_body_count"),
                    "wall_duration_seconds": row.get("wall_duration_seconds"),
                }
            )
            provenance[case_id].append(
                {
                    "run": index,
                    "provenance_kind": row.get("provenance_kind"),
                    "model_generated_body_count": row.get("model_generated_body_count"),
                    "capability_heads": sorted(
                        {
                            pub.get("capability_head")
                            for pub in (row.get("publications") or [])
                            if pub.get("capability_head")
                        }
                    ),
                    "deletion_of_model_body_restores_blocker": row.get(
                        "deletion_of_model_body_restores_blocker"
                    ),
                }
            )
            publication_counts[case_id].append(len(row.get("publications") or []))
            for pub in row.get("publications") or []:
                if isinstance(pub.get("capability_hash"), str):
                    artifact_hashes[pub["capability_hash"]] += 1
        per_run.append(
            {
                "run": index,
                "run_id": report.get("run_id"),
                "status": report.get("status"),
                "published": report.get("published"),
                "schema_version": report.get("schema_version"),
                "model_generated_case_count": summary.get("model_generated_case_count"),
                "protocol_expected_count": summary.get("protocol_expected_count"),
                "published_capability_count": summary.get("published_capability_count"),
                "full_reduction_bundle_authored_count": summary.get(
                    "full_reduction_bundle_authored_count"
                ),
                "compiler_inserted_math_token_count": summary.get(
                    "compiler_inserted_math_token_count"
                ),
                "http_request_attempt_count": summary.get("http_request_attempt_count"),
                "real_model_call_count": summary.get("real_model_call_count"),
                "usage": summary.get("usage"),
                "gates": gates,
            }
        )

    outcomes_ok = (
        len(outcome_matrix) == 24
        and all(
            case_id in POSITIVE_IDS
            and len(entries) == 3
            and all(
                entry["status"] == "VERIFIED"
                and entry["expected_status"] == "VERIFIED"
                and entry["protocol_matches_expected"] is True
                for entry in entries
            )
            for case_id, entries in outcome_matrix.items()
            if case_id in POSITIVE_IDS
        )
        and all(
            case_id in NEGATIVE_IDS
            and len(entries) == 3
            and all(
                entry["status"] == "BLOCKED"
                and entry["expected_status"] == "BLOCKED"
                and entry["failure_code"] == entry["expected_failure_code"]
                and entry["protocol_matches_expected"] is True
                for entry in entries
            )
            for case_id, entries in outcome_matrix.items()
            if case_id in NEGATIVE_IDS
        )
        and all(
            len(entries) == 3
            and all(entry["status"] == "VERIFIED" for entry in entries)
            for case_id, entries in outcome_matrix.items()
            if case_id == CONSUMER_ID
        )
    )
    gap_sequences_ok = (
        len(gap_sequences) == 24
        and all(
            len(entries) == 3
            and all(
                entry["complete"] is True
                and entry["fresh_core_resolve_count"] == entry["gap_count"]
                and entry["publication_count"] == entry["gap_count"]
                and isinstance(entry["resolver"], dict)
                and entry["resolver"].get("resolve_count") == entry["gap_count"] + 1
                and len(entry["resolver"].get("revealed_gap_ids") or []) == entry["gap_count"]
                and len(set(entry["resolver"].get("revealed_gap_ids") or []))
                == entry["gap_count"]
                for entry in entries
            )
            for case_id, entries in gap_sequences.items()
            if case_id in POSITIVE_IDS
        )
    )
    provenance_ok = all(
        len(entries) == 3
        and all(
            entry["provenance_kind"] == "model_generated"
            and entry["model_generated_body_count"] >= 1
            and entry["deletion_of_model_body_restores_blocker"] is True
            for entry in entries
        )
        for case_id, entries in provenance.items()
        if case_id in POSITIVE_IDS
    )
    repair_ok = all(
        len(entries) == 3
        and all(
            entry["model_generated"] is True
            and entry["semantic_turns"] >= 1
            and entry["semantic_turns"] <= 16
            for entry in entries
        )
        for case_id, entries in repair_trajectories.items()
        if case_id in POSITIVE_IDS
    )
    publication_ok = all(
        len(entries) == 3
        and all(1 <= entry <= 4 for entry in entries)
        for case_id, entries in publication_counts.items()
        if case_id in POSITIVE_IDS
    )
    per_run_ok = all(
        run["status"] == "VERIFIED"
        and run["published"] is True
        and run["schema_version"] == STAGE_P_REAL_RUN_SCHEMA
        and run["model_generated_case_count"] == 11
        and run["protocol_expected_count"] == 24
        and run["published_capability_count"] == 24
        and run["full_reduction_bundle_authored_count"] == 3
        and run["compiler_inserted_math_token_count"] == 0
        and run["gates"].get("aggregate_final_lean") is True
        and run["gates"].get("aggregate_standard_axiom_audit") is True
        and run["gates"].get("independent_release_replay") is True
        and run["gates"].get("no_api_key_or_authorization_leak") is True
        and run["gates"].get("no_resume_replay_or_old_response") is True
        and run["gates"].get("consumer_zero_authoring") is True
        and run["gates"].get("producer_consumer_wave_barrier") is True
        for run in per_run
    )
    independent = (
        len(set(output_roots)) == 3
        and len(set(started_ats)) == 3
        and all(isinstance(value, str) and value for value in started_ats)
        and len(set(schemas)) == 1
    )
    aggregate = {
        "schema_version": "hardness_stage_p_stability_aggregate_v1",
        "stage": "P-C",
        "run_reports": [str(path.resolve()) for path in args.reports],
        "run_ids": run_ids,
        "output_roots": output_roots,
        "outcome_matrix": outcome_matrix,
        "gap_sequences": dict(gap_sequences),
        "repair_trajectories": dict(repair_trajectories),
        "source_provenance": dict(provenance),
        "publication_counts": dict(publication_counts),
        "artifact_hash_distribution": dict(artifact_hashes),
        "per_run": per_run,
        "summary": {
            "run_count": len(reports),
            "independent_run_ids": len(set(run_ids)),
            "independent_started_at": len(set(started_ats)),
            "independent_output_roots": len(set(output_roots)),
            "case_count": len(outcome_matrix),
            "outcomes_stable": outcomes_ok,
            "gap_sequences_stable": gap_sequences_ok,
            "source_provenance_stable": provenance_ok,
            "repair_trajectories_stable": repair_ok,
            "publication_reuse_stable": publication_ok,
            "per_run_lean_replay_security_stable": per_run_ok,
            "artifact_hash_diversity": (
                len(artifact_hashes) >= 24 and len(artifact_hashes) <= 72
            ),
        },
        "status": (
            "VERIFIED"
            if all(
                (
                    len(set(started_ats)) == 3,
                    independent,
                    outcomes_ok,
                    gap_sequences_ok,
                    provenance_ok,
                    repair_ok,
                    publication_ok,
                    per_run_ok,
                )
            )
            else "FAILED"
        ),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(aggregate, ensure_ascii=True, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({"status": aggregate["status"], "report": str(args.output.resolve())}))
    return 0 if aggregate["status"] == "VERIFIED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
