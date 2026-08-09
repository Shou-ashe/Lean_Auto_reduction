#!/usr/bin/env python3
"""Validate three fresh N-C Quals runs and publish their stability aggregate."""

from __future__ import annotations

import argparse
import hashlib
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
HARDNESS = ROOT / "Benchmark" / "Hardness"
SCHEMA = "hardness_quals_completeness_stability_aggregate_v1"
DEFAULT_REPORTS = (
    HARDNESS / "QUALS_COMPLETENESS_N_C_STABILITY_1_REPORT.json",
    HARDNESS / "QUALS_COMPLETENESS_N_C_STABILITY_2_REPORT.json",
    HARDNESS / "QUALS_COMPLETENESS_N_C_STABILITY_3_REPORT.json",
)
DEFAULT_OFFICIAL_REPORT = HARDNESS / "QUALS_COMPLETENESS_N_C_REPORT.json"
DEFAULT_OUTPUT = HARDNESS / "QUALS_COMPLETENESS_N_C_STABILITY_AGGREGATE.json"
USAGE_FIELDS = (
    "prompt_tokens",
    "completion_tokens",
    "total_tokens",
    "prompt_cache_hit_tokens",
    "prompt_cache_miss_tokens",
)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    command.add_argument(
        "--report",
        action="append",
        type=Path,
        default=[],
        help="A verified stability report; provide exactly three or use defaults.",
    )
    command.add_argument(
        "--official-report",
        type=Path,
        default=DEFAULT_OFFICIAL_REPORT,
    )
    command.add_argument(
        "--excluded-report",
        action="append",
        type=Path,
        default=[],
        help="An incomplete/non-verified attempt retained for audit but not counted.",
    )
    command.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    return command


def _load_object(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"{path}: expected a JSON object")
    return value


def _sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _display_path(path: Path) -> str:
    resolved = path.resolve()
    try:
        return str(resolved.relative_to(ROOT))
    except ValueError:
        return str(resolved)


def _resolved_artifact_path(value: object) -> Path | None:
    if not isinstance(value, str) or not value:
        return None
    path = Path(value)
    return path if path.is_absolute() else ROOT / path


def _expect(errors: list[str], condition: bool, message: str) -> None:
    if not condition:
        errors.append(message)


def _counter(values: Iterable[object]) -> dict[str, int]:
    return dict(sorted(Counter(str(value) for value in values if value).items()))


def _sum_usage(rows: Sequence[Mapping[str, Any]]) -> dict[str, int]:
    return {
        field: sum(int(row.get(field, 0)) for row in rows)
        for field in USAGE_FIELDS
    }


def _selection_evidence(
    *, report: Mapping[str, Any], role: str, errors: list[str]
) -> list[dict[str, Any]]:
    evidence: list[dict[str, Any]] = []
    for case in report.get("cases", []):
        if not isinstance(case, Mapping) or not case.get("positive"):
            continue
        case_id = str(case.get("id"))
        calls = case.get("selection_calls", [])
        _expect(errors, len(calls) == 1, f"{role}/{case_id}: expected one selection call")
        for call in calls:
            if not isinstance(call, Mapping):
                errors.append(f"{role}/{case_id}: malformed selection call")
                continue
            response_file = _resolved_artifact_path(call.get("response_file"))
            response: Mapping[str, Any] = {}
            if response_file is None or not response_file.is_file():
                errors.append(f"{role}/{case_id}: response evidence is missing")
            else:
                response = _load_object(response_file)
            called = call.get("called") is True and response.get("called") is True
            ok = call.get("ok") is True and response.get("ok") is True
            status_code = call.get("status_code")
            replayed = response.get("replayed")
            _expect(errors, called, f"{role}/{case_id}: call was not real")
            _expect(errors, ok, f"{role}/{case_id}: HTTP call was not successful")
            _expect(errors, status_code == 200, f"{role}/{case_id}: HTTP status is not 200")
            _expect(errors, replayed is False, f"{role}/{case_id}: response was replayed")
            evidence.append(
                {
                    "case_id": case_id,
                    "called": called,
                    "ok": ok,
                    "status_code": status_code,
                    "replayed": replayed,
                    "attempts": call.get("attempts"),
                    "prompt_sha256": call.get("prompt_sha256"),
                    "response_sha256": call.get("response_sha256"),
                    "response_file": (
                        _display_path(response_file) if response_file is not None else None
                    ),
                    "usage": call.get("usage", {}),
                }
            )
    return evidence


def _compact_verified_report(path: Path, role: str) -> tuple[dict[str, Any], list[str]]:
    report = _load_object(path)
    errors: list[str] = []
    cases = [case for case in report.get("cases", []) if isinstance(case, Mapping)]
    primary = [case for case in cases if case.get("positive")]
    adversarial = [case for case in cases if not case.get("positive")]
    gates = report.get("gates", {})
    model = report.get("model_configuration", {})
    selection = _selection_evidence(report=report, role=role, errors=errors)

    _expect(errors, report.get("status") == "VERIFIED", f"{role}: status is not VERIFIED")
    _expect(errors, report.get("stage") == "N", f"{role}: stage is not N")
    _expect(errors, report.get("milestone") == "N-C", f"{role}: milestone is not N-C")
    _expect(errors, report.get("real_deepseek") is True, f"{role}: real_deepseek is not true")
    _expect(errors, report.get("published") is True, f"{role}: report is not published")
    _expect(errors, report.get("primary_case_count") == 5, f"{role}: primary count is not 5")
    _expect(errors, report.get("primary_verified_count") == 5, f"{role}: primary verified is not 5")
    _expect(errors, report.get("adversarial_case_count") == 7, f"{role}: adversarial count is not 7")
    _expect(errors, report.get("adversarial_correct_count") == 7, f"{role}: adversarial correct is not 7")
    _expect(errors, report.get("protocol_expected_count") == 12, f"{role}: protocol count is not 12")
    _expect(errors, report.get("real_http_call_count") == 5, f"{role}: real HTTP call count is not 5")
    _expect(errors, len(primary) == 5, f"{role}: report does not contain 5 primary rows")
    _expect(errors, len(adversarial) == 7, f"{role}: report does not contain 7 adversarial rows")
    _expect(errors, len(selection) == 5, f"{role}: selection evidence count is not 5")
    _expect(errors, isinstance(gates, Mapping) and len(gates) == 18, f"{role}: gate count is not 18")
    _expect(errors, bool(gates) and all(value is True for value in gates.values()), f"{role}: not all gates passed")
    _expect(errors, report.get("final_active_case_count") == 0, f"{role}: active case leak")
    for field in ("request_mutation_count", "endpoint_mutation_count", "objective_mutation_count"):
        _expect(errors, report.get(field) == 0, f"{role}: {field} is not zero")
    _expect(errors, report.get("final_combined_lean", {}).get("exit_code") == 0, f"{role}: final Lean failed")
    _expect(errors, report.get("release_replay", {}).get("exit_code") == 0, f"{role}: release replay failed")
    _expect(errors, all(case.get("final_status") == "VERIFIED" for case in primary), f"{role}: a primary is not VERIFIED")
    _expect(errors, all(case.get("protocol_matches_expected") is True for case in cases), f"{role}: protocol mismatch")
    _expect(errors, all(case.get("model_call_count") == 0 for case in adversarial), f"{role}: adversarial model call detected")
    _expect(errors, all(case.get("pre_model_blocked") is True for case in adversarial), f"{role}: adversarial was not pre-model blocked")

    candidate_hashes = {
        str(case.get("id")): case.get("candidate_sha256") for case in primary
    }
    candidate_stage_hashes = {
        str(case.get("id")): case.get("candidate_stage_sha256") for case in primary
    }
    usage = report.get("usage", {}).get("combined", {})
    compact = {
        "role": role,
        "report": _display_path(path),
        "report_sha256": _sha256(path),
        "run_label": report.get("run_label"),
        "output_root": report.get("output_root"),
        "status": report.get("status"),
        "started_at": report.get("started_at"),
        "finished_at": report.get("finished_at"),
        "model": model.get("model"),
        "base_url": model.get("base_url"),
        "primary_verified": report.get("primary_verified_count"),
        "adversarial_correct": report.get("adversarial_correct_count"),
        "protocol_expected": report.get("protocol_expected_count"),
        "gates_passed": sum(value is True for value in gates.values()),
        "gate_count": len(gates),
        "real_http_calls": report.get("real_http_call_count"),
        "http_ok": sum(item["ok"] and item["status_code"] == 200 for item in selection),
        "replayed_response_count": sum(item["replayed"] is True for item in selection),
        "selection_evidence": selection,
        "usage": {field: int(usage.get(field, 0)) for field in USAGE_FIELDS},
        "wall_duration_seconds": report.get("wall_duration_seconds"),
        "final_lean": report.get("final_combined_lean"),
        "release_replay": report.get("release_replay"),
        "process_counts": report.get("process_counts"),
        "suite_hashes": report.get("suite_hashes"),
        "final_artifact_sha256": report.get("final_artifact_sha256"),
        "candidate_sha256": candidate_hashes,
        "candidate_stage_sha256": candidate_stage_hashes,
        "failure_reason_distribution": _counter(
            case.get("final_failure_code") for case in adversarial
        ),
        "positive_failure_reason_distribution": _counter(
            case.get("final_failure_code") for case in primary
        ),
    }
    return compact, errors


def _hash_analysis(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    candidate_hashes: dict[str, list[str]] = defaultdict(list)
    response_hashes: dict[str, list[str]] = defaultdict(list)
    for row in rows:
        for case_id, value in row["candidate_sha256"].items():
            if isinstance(value, str):
                candidate_hashes[case_id].append(value)
        for call in row["selection_evidence"]:
            value = call.get("response_sha256")
            if isinstance(value, str):
                response_hashes[str(call["case_id"])].append(value)
    artifacts = [str(row["final_artifact_sha256"]) for row in rows]
    reports = [str(row["report_sha256"]) for row in rows]
    return {
        "report_sha256": reports,
        "unique_report_sha256_count": len(set(reports)),
        "final_artifact_sha256": artifacts,
        "unique_final_artifact_sha256_count": len(set(artifacts)),
        "final_artifact_identical_across_runs": len(set(artifacts)) == 1,
        "candidate_sha256_by_case": {
            case_id: {
                "values": values,
                "unique_count": len(set(values)),
                "identical_across_runs": len(set(values)) == 1,
            }
            for case_id, values in sorted(candidate_hashes.items())
        },
        "response_sha256_by_case": {
            case_id: {"values": values, "unique_count": len(set(values))}
            for case_id, values in sorted(response_hashes.items())
        },
    }


def build_aggregate(
    report_paths: Sequence[Path],
    *,
    official_report: Path,
    excluded_reports: Sequence[Path] = (),
) -> dict[str, Any]:
    errors: list[str] = []
    if len(report_paths) != 3:
        errors.append("exactly three stability reports are required")
    rows: list[dict[str, Any]] = []
    for index, path in enumerate(report_paths, start=1):
        row, row_errors = _compact_verified_report(path, f"stability_{index}")
        rows.append(row)
        errors.extend(row_errors)
    official, official_errors = _compact_verified_report(official_report, "official")
    errors.extend(official_errors)

    labels = [row.get("run_label") for row in rows]
    roots = [row.get("output_root") for row in rows]
    response_files = [
        call.get("response_file") for row in rows for call in row["selection_evidence"]
    ]
    _expect(errors, len(set(labels)) == 3, "stability run labels are not unique")
    _expect(errors, len(set(roots)) == 3, "stability output roots are not unique")
    _expect(errors, len(response_files) == len(set(response_files)) == 15, "response evidence paths are not unique")
    _expect(errors, len({row.get("model") for row in rows}) == 1, "model changed across stability runs")
    _expect(errors, len({row.get("base_url") for row in rows}) == 1, "base URL changed across stability runs")
    _expect(errors, len({json.dumps(row.get("suite_hashes"), sort_keys=True) for row in rows}) == 1, "suite hashes changed across stability runs")

    usages = [row["usage"] for row in rows]
    failure_reasons = Counter()
    process_counts = Counter()
    for row in rows:
        failure_reasons.update(row["failure_reason_distribution"])
        process_counts.update(row.get("process_counts") or {})
    hash_analysis = _hash_analysis(rows)
    _expect(errors, hash_analysis["unique_report_sha256_count"] == 3, "stability reports are not independently hashed")
    _expect(errors, hash_analysis["unique_final_artifact_sha256_count"] == 1, "final Lean artifact is not stable")

    excluded = []
    for path in excluded_reports:
        report = _load_object(path)
        excluded.append(
            {
                "report": _display_path(path),
                "report_sha256": _sha256(path),
                "run_label": report.get("run_label"),
                "output_root": report.get("output_root"),
                "status": report.get("status"),
                "started_at": report.get("started_at"),
                "finished_at": report.get("finished_at"),
                "counted": False,
                "reason": "non_verified_or_incomplete_run_excluded_from_stability_count",
            }
        )

    return {
        "schema_version": SCHEMA,
        "status": "VERIFIED" if not errors else "FAILED",
        "stage": "N",
        "milestone": "N-C",
        "model": rows[0].get("model") if rows else None,
        "base_url": rows[0].get("base_url") if rows else None,
        "requirements": {
            "independent_full_runs": 3,
            "fresh_output_directory_per_run": True,
            "resume_used": False,
            "replayed_model_answers": False,
            "primary_verified_per_run": 5,
            "adversarial_correct_per_run": 7,
            "protocol_expected_per_run": 12,
            "real_http_calls_per_run": 5,
            "gates_passed_per_run": 18,
            "final_lean_processes_per_run": 1,
            "release_replays_per_run": 1,
        },
        "official_run": official,
        "runs": rows,
        "aggregate": {
            "run_count": len(rows),
            "case_executions": len(rows) * 12,
            "primary_verified": sum(int(row["primary_verified"]) for row in rows),
            "adversarial_correct": sum(int(row["adversarial_correct"]) for row in rows),
            "protocol_expected": sum(int(row["protocol_expected"]) for row in rows),
            "gates_passed": sum(int(row["gates_passed"]) for row in rows),
            "real_http_calls": sum(int(row["real_http_calls"]) for row in rows),
            "http_ok": sum(int(row["http_ok"]) for row in rows),
            "replayed_response_count": sum(int(row["replayed_response_count"]) for row in rows),
            "usage": _sum_usage(usages),
            "wall_duration_seconds": round(sum(float(row["wall_duration_seconds"]) for row in rows), 3),
            "process_counts": dict(sorted(process_counts.items())),
            "failure_reason_distribution": dict(sorted(failure_reasons.items())),
            "positive_failure_reason_distribution": {},
        },
        "independence_evidence": {
            "unique_run_label_count": len(set(labels)),
            "unique_output_root_count": len(set(roots)),
            "unique_report_sha256_count": hash_analysis["unique_report_sha256_count"],
            "unique_response_file_count": len(set(response_files)),
            "called_response_count": sum(
                call["called"] is True for row in rows for call in row["selection_evidence"]
            ),
            "replayed_response_count": sum(
                call["replayed"] is True for row in rows for call in row["selection_evidence"]
            ),
        },
        "artifact_hash_analysis": hash_analysis,
        "excluded_attempts": excluded,
        "validation_errors": errors,
    }


def main() -> int:
    arguments = parser().parse_args()
    reports = tuple(arguments.report) if arguments.report else DEFAULT_REPORTS
    aggregate = build_aggregate(
        reports,
        official_report=arguments.official_report,
        excluded_reports=arguments.excluded_report,
    )
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_text(
        json.dumps(aggregate, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    print(json.dumps({"status": aggregate["status"], "report": str(arguments.output)}))
    return 0 if aggregate["status"] == "VERIFIED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
