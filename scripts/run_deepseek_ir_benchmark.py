#!/usr/bin/env python3
"""Run all IR-feasibility cases with DeepSeek-authored Lean path terms.

Normal runs consume an offline snapshot of the already compiled library.  No
Lean process is started for preflight, theorem retrieval, path selection, or
reference checking.  After all model turns for the 12 cases, one combined
artifact is elaborated once and checked by the standard axiom gate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import defaultdict
from dataclasses import replace
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.benchmark import (  # noqa: E402
    BenchmarkCase,
    BenchmarkManifestError,
    load_benchmark_manifest,
    select_benchmark_cases,
)
from agent.hardness.catalog import build_all_catalogs  # noqa: E402
from agent.hardness.deepseek_ir import build_batch_codegen_artifact_source  # noqa: E402
from agent.hardness.lean_runner import (  # noqa: E402
    assert_generated_source_is_safe,
    run_command,
)
from agent.hardness.model_client import DeepSeekClient, DeepSeekConfig  # noqa: E402
from agent.hardness.models import CommandResult, TypedCatalog, TypedInventoryEntry  # noqa: E402
from agent.hardness.planner import (  # noqa: E402
    MAX_MODEL_RETRIEVAL_ROUNDS,
    generate_lean_path_with_deepseek,
)


SCHEMA_VERSION = "hardness_deepseek_retrieval_codegen_full_v2"
SNAPSHOT_SCHEMA = "hardness_ir_catalog_snapshot_v2"
SUITE_ID = "ir-feasibility"
EXPECTED_EXECUTIONS = 12
EXPECTED_MATCHED_PAIRS = 6
ENTRY_FIELDS = (
    "declaration",
    "capability_kind",
    "component_role",
    "source_fingerprint",
    "target_fingerprint",
    "is_final_facade",
    "discovery",
    "registry_fingerprint",
    "source_display",
    "target_display",
    "source_node_id",
    "target_node_id",
)


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


def aggregate_usage(usages: Iterable[dict[str, Any] | None]) -> dict[str, int]:
    totals: dict[str, int] = defaultdict(int)
    for usage in usages:
        if not isinstance(usage, dict):
            continue
        for key, value in usage.items():
            if isinstance(value, int) and not isinstance(value, bool):
                totals[key] += value
    return dict(sorted(totals.items()))


def row_api_call_count(row: dict[str, Any]) -> int:
    """Return logical model turns, with a fallback for older reports."""

    value = row.get("api_call_count")
    if isinstance(value, int) and not isinstance(value, bool) and value >= 0:
        return value
    return 1 if row.get("model_called") is True else 0


def row_http_ok_count(row: dict[str, Any]) -> int:
    """Return successful model turns, with a fallback for older reports."""

    value = row.get("http_ok_count")
    if isinstance(value, int) and not isinstance(value, bool) and value >= 0:
        return value
    return 1 if row.get("http_ok") is True else 0


def api_calls_this_run(rows: Iterable[dict[str, Any]]) -> int:
    return sum(
        row_api_call_count(row)
        for row in rows
        if row.get("called_this_run") is True
    )


def command_summary(result: CommandResult) -> dict[str, Any]:
    return {
        "command": list(result.command),
        "exit_code": result.exit_code,
        "ok": result.ok,
        "timed_out": result.timed_out,
        "duration_seconds": result.duration_seconds,
        "stdout_sha256": sha256_text(result.stdout),
        "stderr_sha256": sha256_text(result.stderr),
        "stdout_tail": result.stdout[-4000:],
        "stderr_tail": result.stderr[-8000:],
    }


def validate_suite(cases: tuple[BenchmarkCase, ...]) -> None:
    if len(cases) != EXPECTED_EXECUTIONS:
        raise ValueError(
            f"{SUITE_ID} must contain exactly {EXPECTED_EXECUTIONS} runnable executions"
        )
    pairs: dict[str, set[str]] = defaultdict(set)
    for case in cases:
        if (
            case.objective != "reduce_to"
            or case.target_policy != "fixed"
            or not case.target
            or case.membership is not None
            or case.catalog_mode not in {"flat_api", "ir_components"}
            or not case.matched_pair_id
        ):
            raise ValueError(f"case {case.id} is outside the fixed-target IR study ABI")
        pairs[case.matched_pair_id].add(case.catalog_mode)
    if len(pairs) != EXPECTED_MATCHED_PAIRS or any(
        modes != {"flat_api", "ir_components"} for modes in pairs.values()
    ):
        raise ValueError("IR study must contain six complete flat/IR matched pairs")


def load_snapshot(
    path: Path, cases: tuple[BenchmarkCase, ...]
) -> tuple[dict[str, TypedCatalog], dict[str, dict[str, Any]], dict[str, Any]]:
    snapshot = json.loads(path.read_text(encoding="utf-8"))
    if snapshot.get("schema_version") != SNAPSHOT_SCHEMA:
        raise ValueError("unsupported IR catalog snapshot schema")
    fingerprint = snapshot.get("registry_fingerprint")
    raw_entries = snapshot.get("inventory_entries")
    topology = snapshot.get("endpoint_topology")
    if not isinstance(fingerprint, str) or not fingerprint:
        raise ValueError("IR catalog snapshot has no registry fingerprint")
    if not isinstance(raw_entries, list) or not raw_entries:
        raise ValueError("IR catalog snapshot has no typed inventory entries")
    if (
        not isinstance(topology, dict)
        or topology.get("schema_version") != "hardness_endpoint_topology_v1"
        or topology.get("producer") != "lean_whnf_endpoint_hash"
        or topology.get("registry_fingerprint") != fingerprint
    ):
        raise ValueError("IR catalog snapshot has no matching endpoint topology")
    entries: list[TypedInventoryEntry] = []
    for raw in raw_entries:
        if not isinstance(raw, dict) or any(field not in raw for field in ENTRY_FIELDS):
            raise ValueError("IR catalog snapshot contains an invalid inventory entry")
        if not raw.get("source_node_id") or not raw.get("target_node_id"):
            raise ValueError("IR catalog snapshot contains an entry without endpoint nodes")
        entries.append(TypedInventoryEntry(**{field: raw[field] for field in ENTRY_FIELDS}))
    if snapshot.get("inventory_entry_count") != len(entries):
        raise ValueError("IR catalog snapshot inventory count does not match its payload")
    catalogs = build_all_catalogs(entries, registry_fingerprint=fingerprint)
    recorded_catalogs = snapshot.get("catalogs")
    if not isinstance(recorded_catalogs, dict):
        raise ValueError("IR catalog snapshot has no catalog records")
    for mode in ("flat_api", "ir_components"):
        recorded = recorded_catalogs.get(mode)
        if not isinstance(recorded, dict) or recorded.get("catalog_id") != catalogs[mode].catalog_id:
            raise ValueError(f"IR catalog snapshot {mode} catalog ID is stale")
    raw_case_rows = snapshot.get("cases")
    if not isinstance(raw_case_rows, list):
        raise ValueError("IR catalog snapshot has no case display records")
    case_rows = {
        row.get("id"): row for row in raw_case_rows if isinstance(row, dict)
    }
    for case in cases:
        row = case_rows.get(case.id)
        if (
            not isinstance(row, dict)
            or row.get("catalog_mode") != case.catalog_mode
            or row.get("source_declaration") != case.source
            or row.get("target_declaration") != case.target
            or not isinstance(row.get("source_display"), str)
            or not isinstance(row.get("target_display"), str)
            or not isinstance(row.get("source_node_id"), str)
            or not row.get("source_node_id")
            or not isinstance(row.get("target_node_id"), str)
            or not row.get("target_node_id")
        ):
            raise ValueError(f"IR catalog snapshot does not match case {case.id}")
    return catalogs, case_rows, snapshot


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(
        description=(
            "Call DeepSeek for all 12 IR cases, let it write Lean path terms, "
            "then run Lean exactly once"
        )
    )
    command.add_argument(
        "--manifest",
        type=Path,
        default=ROOT / "Benchmark" / "Hardness" / "MANIFEST.json",
    )
    command.add_argument(
        "--catalog-snapshot",
        type=Path,
        default=ROOT / "Benchmark" / "Hardness" / "IR_CATALOG_SNAPSHOT.json",
    )
    command.add_argument("--env-file", type=Path, default=ROOT / ".env")
    command.add_argument(
        "--resume-report",
        type=Path,
        help=(
            "reuse protocol-accepted model terms from an earlier report and call "
            "DeepSeek only for missing/failed cases"
        ),
    )
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "deepseek-ir-codegen-full",
    )
    command.add_argument(
        "--canonical-report",
        type=Path,
        default=ROOT / "Benchmark" / "Hardness" / "IR_DEEPSEEK_FULL_REPORT.json",
    )
    command.add_argument("--lean-timeout", type=int, default=600)
    command.add_argument("--model-timeout", type=int, default=None)
    command.add_argument("--model-max-tokens", type=int, default=8192)
    command.add_argument(
        "--retrieval-rounds",
        type=int,
        default=MAX_MODEL_RETRIEVAL_ROUNDS,
        help="maximum DeepSeek search/codegen turns per benchmark case",
    )
    return command


def main() -> int:
    arguments = parser().parse_args()
    if arguments.lean_timeout <= 0:
        parser().error("--lean-timeout must be positive")
    if arguments.model_timeout is not None and arguments.model_timeout <= 0:
        parser().error("--model-timeout must be positive")
    if arguments.model_max_tokens <= 0:
        parser().error("--model-max-tokens must be positive")
    if not 1 <= arguments.retrieval_rounds <= 8:
        parser().error("--retrieval-rounds must be in 1..8")

    output_root = arguments.output_root.resolve()
    output_root.mkdir(parents=True, exist_ok=True)
    report_path = output_root / "report.json"
    report: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "started_at": utc_now(),
        "status": "RUNNING",
        "scope": {
            "suite_id": SUITE_ID,
            "existing_library_declarations_only": True,
            "deepseek_writes_lean_path_terms": True,
            "deepseek_may_add_new_library_reductions": False,
            "offline_compiled_library_catalog": True,
            "model_driven_theorem_retrieval": True,
            "full_theorem_catalog_sent_to_model": False,
            "compiled_endpoint_topology": True,
            "maximum_retrieval_rounds_per_case": arguments.retrieval_rounds,
            "lean_validation_timing": "once_after_all_model_calls",
            "expected_lean_process_count": 1,
            "standard_axiom_gate": True,
        },
        "output_root": str(output_root),
        "cases": [],
    }

    def finish(status: str, *, exit_code: int, error: str | None = None) -> int:
        report["status"] = status
        report["finished_at"] = utc_now()
        if error is not None:
            report["error"] = error
        write_json(report_path, report)
        write_json(arguments.canonical_report.resolve(), report)
        print(
            json.dumps(
                {
                    "status": status,
                    "report": str(report_path),
                    "canonical_report": str(arguments.canonical_report.resolve()),
                    "summary": report.get("summary"),
                    "error": error,
                },
                ensure_ascii=False,
                sort_keys=True,
            ),
            flush=True,
        )
        return exit_code

    try:
        manifest = load_benchmark_manifest(arguments.manifest)
        selection = select_benchmark_cases(
            manifest, suite_ids=(SUITE_ID,), agent_phase=1
        )
        if selection.skipped:
            raise ValueError("IR feasibility suite contains skipped cases")
        cases = selection.runnable
        validate_suite(cases)
        catalogs, case_metadata, snapshot = load_snapshot(
            arguments.catalog_snapshot, cases
        )
    except (BenchmarkManifestError, OSError, UnicodeError, ValueError, json.JSONDecodeError) as error:
        return finish("FAILED", exit_code=1, error=f"offline setup failed: {error}")

    config = DeepSeekConfig.from_environment(env_file=arguments.env_file)
    config = replace(config, max_tokens=arguments.model_max_tokens)
    if arguments.model_timeout is not None:
        config = replace(config, timeout_seconds=arguments.model_timeout)
    report["benchmark"] = {
        "benchmark_id": manifest.benchmark_id,
        "execution_count": len(cases),
        "matched_pair_count": len({case.matched_pair_id for case in cases}),
        "case_ids": [case.id for case in cases],
    }
    report["catalog_snapshot"] = {
        "path": str(arguments.catalog_snapshot.resolve()),
        "schema_version": snapshot["schema_version"],
        "registry_fingerprint": snapshot["registry_fingerprint"],
        "endpoint_topology": snapshot["endpoint_topology"],
        "inventory_entry_count": snapshot["inventory_entry_count"],
        "source": snapshot.get("source"),
        "catalogs": {
            mode: {
                "catalog_id": catalogs[mode].catalog_id,
                "agent_interface_count": catalogs[mode].agent_interface_count,
                "semantic_atomic_interface_count": (
                    catalogs[mode].semantic_atomic_interface_count
                ),
            }
            for mode in ("flat_api", "ir_components")
        },
    }
    report["model"] = config.to_public_dict()
    reusable_rows: dict[str, dict[str, Any]] = {}
    if arguments.resume_report is not None:
        try:
            previous = json.loads(arguments.resume_report.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, json.JSONDecodeError) as error:
            return finish("FAILED", exit_code=1, error=f"resume report failed: {error}")
        previous_cases = previous.get("cases")
        if not isinstance(previous_cases, list):
            return finish("FAILED", exit_code=1, error="resume report has no cases")
        for previous_row in previous_cases:
            if (
                isinstance(previous_row, dict)
                and previous_row.get("protocol_accepted") is True
                and isinstance(previous_row.get("id"), str)
            ):
                reusable_rows[previous_row["id"]] = previous_row
        report["resume"] = {
            "report": str(arguments.resume_report.resolve()),
            "reusable_case_count": len(reusable_rows),
        }
    write_json(report_path, report)

    client = DeepSeekClient(config)
    selections: list[tuple[BenchmarkCase, str]] = []
    rows: list[dict[str, Any]] = []
    usages: list[dict[str, Any] | None] = []
    for index, case in enumerate(cases, start=1):
        metadata = case_metadata[case.id]
        catalog = catalogs[case.catalog_mode]
        reusable = reusable_rows.get(case.id)
        if reusable is not None:
            declarations = reusable.get("selected_declarations")
            lean_term = reusable.get("lean_term")
            allowed = {entry.declaration for entry in catalog.entries}
            if (
                reusable.get("catalog_id") == catalog.catalog_id
                and isinstance(declarations, list)
                and declarations
                and all(
                    isinstance(declaration, str) and declaration in allowed
                    for declaration in declarations
                )
                and isinstance(lean_term, str)
                and lean_term.strip()
                and all(declaration in lean_term for declaration in declarations)
            ):
                print(
                    json.dumps(
                        {
                            "phase": "deepseek_codegen",
                            "case": case.id,
                            "status": "reused",
                        }
                    ),
                    flush=True,
                )
                selections.append((case, lean_term))
                usages.append(
                    reusable.get("usage")
                    if isinstance(reusable.get("usage"), dict)
                    else None
                )
                row = dict(reusable)
                row["lean_verified"] = False
                row["called_this_run"] = False
                row["reused_from_report"] = str(arguments.resume_report.resolve())
                rows.append(row)
                report["cases"] = rows
                report["calls"] = {
                    "expected": len(cases),
                    "completed": len(rows),
                    "api_calls_this_run": api_calls_this_run(rows),
                    "usage": aggregate_usage(usages),
                }
                write_json(report_path, report)
                continue
        print(
            json.dumps(
                {
                    "phase": "deepseek_codegen",
                    "call": index,
                    "total": len(cases),
                    "case": case.id,
                    "catalog_mode": case.catalog_mode,
                }
            ),
            flush=True,
        )
        generated = generate_lean_path_with_deepseek(
            catalog=catalog,
            source_declaration=case.source,
            source_display=metadata["source_display"],
            source_node_id=metadata["source_node_id"],
            target_declaration=case.target or "",
            target_display=metadata["target_display"],
            target_node_id=metadata["target_node_id"],
            client=client,
            maximum_retrieval_rounds=arguments.retrieval_rounds,
            benchmark_context={
                "matched_pair_id": case.matched_pair_id,
                "family_id": case.family_id,
                "source_form_id": case.source_form_id,
                "target_form_id": case.target_form_id,
                "hub_ids": list(case.hub_ids),
            },
        )
        response = generated.model_response
        round_prompts = generated.model_prompts or (generated.model_prompt,)
        round_responses = generated.model_responses or (response,)
        case_usage = aggregate_usage(item.usage for item in round_responses)
        usages.append(case_usage)
        call_dir = output_root / "calls" / case.id
        call_dir.mkdir(parents=True, exist_ok=True)
        prompt_path = call_dir / "prompt.json"
        response_path = call_dir / "response.json"
        write_json(prompt_path, json.loads(generated.model_prompt))
        write_json(
            response_path,
            {
                "called": response.called,
                "ok": response.ok,
                "status_code": response.status_code,
                "duration_seconds": response.duration_seconds,
                "attempts": response.attempts,
                "finish_reason": response.finish_reason,
                "usage": response.usage,
                "error": config.redact(response.error or "") or None,
                "content": response.content,
            },
        )
        model_rounds: list[dict[str, Any]] = []
        for round_number, (round_prompt, round_response) in enumerate(
            zip(round_prompts, round_responses, strict=True), start=1
        ):
            round_prompt_path = call_dir / f"round-{round_number:02d}-prompt.json"
            round_response_path = call_dir / f"round-{round_number:02d}-response.json"
            write_json(round_prompt_path, json.loads(round_prompt))
            write_json(
                round_response_path,
                {
                    "called": round_response.called,
                    "ok": round_response.ok,
                    "status_code": round_response.status_code,
                    "duration_seconds": round_response.duration_seconds,
                    "attempts": round_response.attempts,
                    "finish_reason": round_response.finish_reason,
                    "usage": round_response.usage,
                    "error": config.redact(round_response.error or "") or None,
                    "content": round_response.content,
                },
            )
            model_rounds.append(
                {
                    "round": round_number,
                    "called": round_response.called,
                    "http_ok": round_response.ok,
                    "status_code": round_response.status_code,
                    "duration_seconds": round_response.duration_seconds,
                    "attempts": round_response.attempts,
                    "finish_reason": round_response.finish_reason,
                    "usage": round_response.usage,
                    "prompt_sha256": sha256_text(round_prompt),
                    "response_sha256": sha256_text(round_response.content),
                    "prompt_file": str(round_prompt_path),
                    "response_file": str(round_response_path),
                }
            )
        if generated.protocol_accepted and generated.lean_term is not None:
            selections.append((case, generated.lean_term))
        api_call_count = sum(1 for item in round_responses if item.called)
        http_ok_count = sum(1 for item in round_responses if item.ok)
        case_duration = round(sum(item.duration_seconds for item in round_responses), 3)
        row = {
            "id": case.id,
            "matched_pair_id": case.matched_pair_id,
            "family_id": case.family_id,
            "catalog_mode": case.catalog_mode,
            "catalog_id": catalog.catalog_id,
            "agent_interface_count": catalog.agent_interface_count,
            "source_node_id": metadata["source_node_id"],
            "target_node_id": metadata["target_node_id"],
            "model_called": any(item.called for item in round_responses),
            "api_call_count": api_call_count,
            "http_ok": all(item.ok for item in round_responses),
            "http_ok_count": http_ok_count,
            "status_code": response.status_code,
            "attempts": sum(item.attempts for item in round_responses),
            "duration_seconds": case_duration,
            "finish_reason": response.finish_reason,
            "usage": case_usage,
            "protocol_accepted": generated.protocol_accepted,
            "model_error": config.redact(generated.decision.model_error or "") or None,
            "plan": generated.plan.to_dict() if generated.plan is not None else None,
            "retrieval_trace": list(generated.retrieval_trace),
            "retrieved_declarations": list(generated.retrieved_declarations),
            "model_rounds": model_rounds,
            "selected_declarations": list(generated.declarations),
            "lean_term": generated.lean_term,
            "model_lean_term": generated.model_lean_term,
            "lean_term_normalized": generated.lean_term_normalized,
            "lean_term_sha256": (
                sha256_text(generated.lean_term) if generated.lean_term else None
            ),
            "prompt_sha256": sha256_text(generated.model_prompt),
            "response_sha256": sha256_text(response.content),
            "prompt_file": str(prompt_path),
            "response_file": str(response_path),
            "lean_verified": False,
            "called_this_run": True,
        }
        rows.append(row)
        report["cases"] = rows
        report["calls"] = {
            "expected": len(cases),
            "completed": len(rows),
            "api_calls_this_run": api_calls_this_run(rows),
            "usage": aggregate_usage(usages),
        }
        write_json(report_path, report)

    all_protocol_accepted = len(selections) == len(cases)
    final_command: CommandResult | None = None
    if all_protocol_accepted:
        try:
            artifact_source = build_batch_codegen_artifact_source(selections)
            assert_generated_source_is_safe(artifact_source)
        except ValueError as error:
            report["final_validation"] = {
                "started": False,
                "ok": False,
                "lean_process_count": 0,
                "error": str(error),
            }
        else:
            artifact_path = output_root / "DeepSeekArtifact.lean"
            artifact_path.write_text(artifact_source, encoding="utf-8")
            print(
                json.dumps(
                    {
                        "phase": "final_lean_validation",
                        "status": "started",
                        "lean_process": 1,
                    }
                ),
                flush=True,
            )
            final_command = run_command(
                ["lake", "env", "lean", str(artifact_path)],
                cwd=ROOT / "Lean",
                timeout_seconds=arguments.lean_timeout,
            )
            write_json(
                output_root / "commands" / "final-lean.json", final_command.to_dict()
            )
            report["final_validation"] = {
                **command_summary(final_command),
                "started": True,
                "lean_process_count": 1,
                "artifact": str(artifact_path),
                "artifact_sha256": sha256_text(artifact_source),
            }
    else:
        report["final_validation"] = {
            "started": False,
            "ok": False,
            "lean_process_count": 0,
            "reason": "not every DeepSeek response passed the non-Lean protocol fences",
        }

    final_ok = bool(final_command and final_command.ok)
    if final_ok:
        for row in rows:
            row["lean_verified"] = True
    pair_rows: list[dict[str, Any]] = []
    for pair_id in sorted({case.matched_pair_id for case in cases if case.matched_pair_id}):
        members = [row for row in rows if row["matched_pair_id"] == pair_id]
        pair_rows.append(
            {
                "matched_pair_id": pair_id,
                "case_ids": [row["id"] for row in members],
                "both_protocol_accepted": all(row["protocol_accepted"] for row in members),
                "both_lean_verified": all(row["lean_verified"] for row in members),
            }
        )
    report["cases"] = rows
    report["matched_pairs"] = pair_rows
    report["calls"] = {
        "expected": len(cases),
        "completed": len(rows),
        "called": sum(row_api_call_count(row) for row in rows),
        "model_case_count": sum(1 for row in rows if row["model_called"]),
        "api_calls_this_run": api_calls_this_run(rows),
        "http_ok": sum(row_http_ok_count(row) for row in rows),
        "protocol_accepted": sum(1 for row in rows if row["protocol_accepted"]),
        "usage": aggregate_usage(usages),
        "duration_seconds": round(sum(row["duration_seconds"] for row in rows), 3),
    }
    verified_count = sum(1 for row in rows if row["lean_verified"])
    report["summary"] = {
        "execution_count": len(cases),
        "model_case_count": sum(1 for row in rows if row["model_called"]),
        "model_call_count": sum(row_api_call_count(row) for row in rows),
        "api_calls_this_run": api_calls_this_run(rows),
        "protocol_accepted_count": sum(1 for row in rows if row["protocol_accepted"]),
        "lean_process_count": (
            report.get("final_validation", {}).get("lean_process_count", 0)
        ),
        "lean_verified_count": verified_count,
        "matched_pair_both_verified_count": sum(
            1 for pair in pair_rows if pair["both_lean_verified"]
        ),
        "all_12_verified": verified_count == EXPECTED_EXECUTIONS,
    }
    return finish(
        "VERIFIED" if verified_count == EXPECTED_EXECUTIONS else "FAILED",
        exit_code=0 if verified_count == EXPECTED_EXECUTIONS else 1,
        error=None
        if verified_count == EXPECTED_EXECUTIONS
        else "DeepSeek codegen protocol or the one final Lean validation failed",
    )


if __name__ == "__main__":
    raise SystemExit(main())
