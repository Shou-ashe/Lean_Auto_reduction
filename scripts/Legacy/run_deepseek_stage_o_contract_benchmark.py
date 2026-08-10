#!/usr/bin/env python3
"""Run the frozen 16-case O-A contract against fresh real DeepSeek calls."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import sys
import threading
import time
from collections.abc import Mapping, Sequence
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, replace
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.benchmark import BenchmarkCase, load_benchmark_suite  # noqa: E402
from agent.hardness.lean_runner import (  # noqa: E402
    build_module_command,
    run_command,
    sha256_file,
)
from agent.hardness.model_client import (  # noqa: E402
    DEFAULT_MODEL,
    DeepSeekClient,
    DeepSeekConfig,
    ModelResponse,
)
from agent.hardness.stage_o_contract import (  # noqa: E402
    STAGE_O_ACTION_SCHEMA,
    STAGE_O_INPUT_MODULE,
    STAGE_O_MAX_JOBS,
    STAGE_O_SYSTEM_PROMPT,
    StageOAction,
    StageOContractError,
    audit_stage_o_prompt,
    build_contract_candidate_set,
    build_stage_o_contract_prompt,
    globally_valid_candidate,
    locally_valid_candidate,
    parse_stage_o_action,
    stage_o_report_skeleton,
    validate_stage_o_suites,
    validate_stage_o_terminal_action,
)


DEFAULT_POSITIVE_SUITE = (
    ROOT / "Gate" / "Suites" / "stage_o_multi_gap.json"
)
DEFAULT_NEGATIVE_SUITE = (
    ROOT / "Gate" / "Suites" / "stage_o_adversarial.json"
)
DEFAULT_MICROBENCHMARK = (
    ROOT
    / "Benchmark"
    / "Hardness"
    / "Suites"
    / "stage_o_lean_service_microbenchmark.json"
)


@dataclass(frozen=True)
class CaseOutcome:
    index: int
    row: dict[str, Any]


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def aggregate_usage(rows: Sequence[Mapping[str, Any] | None]) -> dict[str, int]:
    totals: dict[str, int] = {}
    for row in rows:
        if not isinstance(row, Mapping):
            continue
        for key, value in row.items():
            if isinstance(value, int) and not isinstance(value, bool):
                totals[key] = totals.get(key, 0) + value
    return totals


def prepare_fresh_output_root(path: Path) -> None:
    if path.exists() and any(path.iterdir()):
        raise ValueError(f"Stage O contract output root must be fresh and empty: {path}")
    path.mkdir(parents=True, exist_ok=True)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    command.add_argument("--positive-suite", type=Path, default=DEFAULT_POSITIVE_SUITE)
    command.add_argument("--negative-suite", type=Path, default=DEFAULT_NEGATIVE_SUITE)
    command.add_argument("--microbenchmark", type=Path, default=DEFAULT_MICROBENCHMARK)
    command.add_argument("--env-file", type=Path, default=ROOT / ".env")
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "deepseek-stage-o-contract-full",
    )
    command.add_argument(
        "--canonical-report",
        type=Path,
        default=ROOT / "Reports" / "STAGE_O_CONTRACT_REPORT.json",
    )
    command.add_argument("--run-label", default="stage-o-a-contract-full-real-deepseek")
    command.add_argument("--model", default=DEFAULT_MODEL)
    command.add_argument("--model-timeout", type=int, default=300)
    command.add_argument("--model-max-tokens", type=int, default=4096)
    command.add_argument("--max-contract-turns", type=int, default=4)
    command.add_argument("--lean-timeout", type=int, default=1200)
    command.add_argument("--jobs", type=int, default=4)
    return command


def _response_record(
    *,
    case_root: Path,
    turn: int,
    prompt: str,
    response: ModelResponse,
    config: DeepSeekConfig,
) -> dict[str, Any]:
    prompt_path = case_root / "calls" / f"turn-{turn:02d}-prompt.json"
    response_path = case_root / "calls" / f"turn-{turn:02d}-response.json"
    write_json(
        prompt_path,
        {
            "system": STAGE_O_SYSTEM_PROMPT,
            "system_sha256": sha256_text(STAGE_O_SYSTEM_PROMPT),
            "prompt": prompt,
            "prompt_sha256": sha256_text(prompt),
        },
    )
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
            "error": config.redact(response.error or ""),
            "content": response.content,
            "content_sha256": sha256_text(response.content),
            "replayed": False,
        },
    )
    return {
        "turn": turn,
        "called": response.called,
        "ok": response.ok,
        "status_code": response.status_code,
        "duration_seconds": response.duration_seconds,
        "attempts": response.attempts,
        "finish_reason": response.finish_reason,
        "usage": response.usage,
        "error": config.redact(response.error or ""),
        "prompt_sha256": sha256_text(prompt),
        "response_sha256": sha256_text(response.content),
        "prompt_file": str(prompt_path.resolve()),
        "response_file": str(response_path.resolve()),
    }


def _prompt_with_feedback(base_prompt: str, feedback: str | None) -> str:
    if not feedback:
        return base_prompt
    payload = json.loads(base_prompt)
    payload["last_protocol_error"] = feedback
    audit_stage_o_prompt(payload)
    return json.dumps(payload, ensure_ascii=True, sort_keys=True)


def _initial_inspections(case: BenchmarkCase) -> tuple[str, ...]:
    candidate_set = build_contract_candidate_set(case)
    locally_valid = [
        candidate.packet_id
        for candidate in candidate_set.candidates
        if locally_valid_candidate(candidate, candidate_set)
    ]
    remaining = [
        candidate.packet_id
        for candidate in candidate_set.candidates
        if candidate.packet_id not in locally_valid
    ]
    return tuple((*locally_valid, *remaining)[:3])


def run_case(
    *,
    index: int,
    case: BenchmarkCase,
    output_root: Path,
    config: DeepSeekConfig,
    max_contract_turns: int,
) -> CaseOutcome:
    started = time.monotonic()
    case_root = output_root / "cases" / case.id
    case_root.mkdir(parents=True, exist_ok=True)
    candidate_set = build_contract_candidate_set(case)
    inspected = list(_initial_inspections(case))
    calls: list[dict[str, Any]] = []
    responses: list[ModelResponse] = []
    prompt_errors: list[str] = []
    protocol_errors: list[dict[str, str]] = []
    feedback: str | None = None
    accepted_action: StageOAction | None = None
    client = DeepSeekClient(config)

    for turn in range(1, max_contract_turns + 1):
        base_prompt = build_stage_o_contract_prompt(
            candidate_set=candidate_set,
            inspected_packet_ids=inspected,
        )
        prompt = _prompt_with_feedback(base_prompt, feedback)
        try:
            audit_stage_o_prompt(json.loads(prompt), forbidden_values=(case.id,))
        except (json.JSONDecodeError, StageOContractError) as error:
            prompt_errors.append(str(error))
            break
        response = client.complete_json(system=STAGE_O_SYSTEM_PROMPT, prompt=prompt)
        responses.append(response)
        calls.append(
            _response_record(
                case_root=case_root,
                turn=turn,
                prompt=prompt,
                response=response,
                config=config,
            )
        )
        if not response.ok:
            feedback = response.error or "DeepSeek HTTP call failed"
            continue
        try:
            action = parse_stage_o_action(response.content, candidate_set=candidate_set)
            if action.action == "inspect_packet":
                if action.packet_id not in inspected:
                    if len(inspected) >= 3:
                        raise StageOContractError(
                            "inspect_budget_exhausted", "model requested a fourth inspection"
                        )
                    inspected.append(action.packet_id or "")
                feedback = "The requested packet is now present in inspected_packets; return one terminal action."
                continue
            validate_stage_o_terminal_action(action, candidate_set=candidate_set)
            accepted_action = action
            break
        except StageOContractError as error:
            protocol_errors.append({"code": error.code, "message": error.message})
            feedback = f"{error.code}: {error.message}"

    expected_action = "select_packet" if case.is_positive else "stop_authoring"
    protocol_accepted = accepted_action is not None
    protocol_matches_expected = bool(
        protocol_accepted and accepted_action and accepted_action.action == expected_action
    )
    selected_packet_id = accepted_action.packet_id if accepted_action else None
    model_choice_preserved = bool(
        accepted_action is not None
        and (
            accepted_action.action != "select_packet"
            or selected_packet_id
            in {candidate.packet_id for candidate in candidate_set.candidates}
        )
    )
    row = {
        "id": case.id,
        "execution_position": index,
        "objective": case.objective,
        "input_kind": case.input_kind,
        "positive": case.is_positive,
        "expected_action": expected_action,
        "candidate_set_id": candidate_set.candidate_set_id,
        "candidate_count": len(candidate_set.candidates),
        "locally_valid_candidate_count": sum(
            locally_valid_candidate(candidate, candidate_set)
            for candidate in candidate_set.candidates
        ),
        "globally_valid_candidate_count": sum(
            globally_valid_candidate(candidate, candidate_set)
            for candidate in candidate_set.candidates
        ),
        "inspected_packet_ids": inspected,
        "model_calls": calls,
        "external_api_calls_this_run": sum(response.called for response in responses),
        "http_ok_count_this_run": sum(response.called and response.ok for response in responses),
        "http_request_attempts_this_run": sum(response.attempts for response in responses),
        "usage": aggregate_usage(
            [response.usage for response in responses if isinstance(response.usage, Mapping)]
        ),
        "raw_terminal_action": accepted_action.to_dict() if accepted_action else None,
        "selected_packet_id": selected_packet_id,
        "model_choice_preserved": model_choice_preserved,
        "protocol_accepted": protocol_accepted,
        "protocol_matches_expected": protocol_matches_expected,
        "prompt_oracle_errors": prompt_errors,
        "protocol_errors": protocol_errors,
        "replayed_from_resume": False,
        "case_task_wall_duration_seconds": round(time.monotonic() - started, 3),
        "status": "VERIFIED" if protocol_matches_expected and not prompt_errors else "FAILED",
    }
    write_json(case_root / "case.json", row)
    return CaseOutcome(index=index, row=row)


def main() -> int:
    args = parser().parse_args()
    if args.jobs < 1 or args.jobs > STAGE_O_MAX_JOBS:
        raise ValueError(f"Stage O contract jobs must be in 1..{STAGE_O_MAX_JOBS}")
    if args.max_contract_turns < 1:
        raise ValueError("max-contract-turns must be positive")
    prepare_fresh_output_root(args.output_root)
    if args.canonical_report.exists():
        raise ValueError(f"canonical Stage O contract report already exists: {args.canonical_report}")

    positive_suite = load_benchmark_suite(args.positive_suite)
    negative_suite = load_benchmark_suite(args.negative_suite)
    cases = validate_stage_o_suites(positive_suite, negative_suite)
    config = DeepSeekConfig.from_environment(env_file=args.env_file)
    config = replace(
        config,
        model=args.model,
        timeout_seconds=args.model_timeout,
        max_tokens=args.model_max_tokens,
    )
    if not config.api_key:
        raise ValueError("real Stage O contract run requires DEEPSEEK_API_KEY")

    report = stage_o_report_skeleton(offline=False, contract_only=True)
    report.update(
        {
            "run_label": args.run_label,
            "started_at": utc_now(),
            "output_root": str(args.output_root.resolve()),
            "benchmark": {
                "positive_suite": str(args.positive_suite.resolve()),
                "positive_suite_sha256": sha256_file(args.positive_suite),
                "negative_suite": str(args.negative_suite.resolve()),
                "negative_suite_sha256": sha256_file(args.negative_suite),
                "microbenchmark": str(args.microbenchmark.resolve()),
                "microbenchmark_sha256": sha256_file(args.microbenchmark),
                "case_count": len(cases),
            },
            "model": config.to_public_dict(),
            "parallel_execution": {
                "configured_jobs": args.jobs,
                "observed_max_case_concurrency": 0,
                "active_case_task_count": 0,
            },
        }
    )
    report_path = args.output_root / "report.json"
    write_json(report_path, report)

    lean_started = time.monotonic()
    lean_build = run_command(
        build_module_command([STAGE_O_INPUT_MODULE]),
        cwd=ROOT / "Lean",
        timeout_seconds=args.lean_timeout,
        output_limit=64 * 1024,
    )
    report["execution_layers"]["input_gate"] = {
        "module": STAGE_O_INPUT_MODULE,
        "command": lean_build.to_dict(),
        "wall_duration_seconds": round(time.monotonic() - lean_started, 3),
    }
    if not lean_build.ok:
        report["status"] = "FAILED"
        report["failures"] = ["stage_o_input_module_build_failed"]
        report["finished_at"] = utc_now()
        write_json(report_path, report)
        return 1

    active = 0
    max_active = 0
    lock = threading.Lock()

    def guarded(item: tuple[int, BenchmarkCase]) -> CaseOutcome:
        nonlocal active, max_active
        index, case = item
        with lock:
            active += 1
            max_active = max(max_active, active)
        try:
            return run_case(
                index=index,
                case=case,
                output_root=args.output_root,
                config=config,
                max_contract_turns=args.max_contract_turns,
            )
        finally:
            with lock:
                active -= 1

    outcomes: list[CaseOutcome] = []
    suite_started = time.monotonic()
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = {
            executor.submit(guarded, item): item[0]
            for item in enumerate(cases, start=1)
        }
        for future in as_completed(futures):
            index = futures[future]
            try:
                outcomes.append(future.result())
            except Exception as error:
                case = cases[index - 1]
                outcomes.append(
                    CaseOutcome(
                        index=index,
                        row={
                            "id": case.id,
                            "execution_position": index,
                            "status": "FAILED",
                            "protocol_accepted": False,
                            "protocol_matches_expected": False,
                            "runner_error": config.redact(f"{type(error).__name__}: {error}"),
                            "external_api_calls_this_run": 0,
                            "http_ok_count_this_run": 0,
                            "http_request_attempts_this_run": 0,
                            "usage": {},
                            "prompt_oracle_errors": [],
                            "protocol_errors": [],
                            "model_choice_preserved": False,
                        },
                    )
                )
    outcomes.sort(key=lambda outcome: outcome.index)
    rows = [outcome.row for outcome in outcomes]
    report["cases"] = rows
    report["parallel_execution"] = {
        "configured_jobs": args.jobs,
        "observed_max_case_concurrency": max_active,
        "active_case_task_count": active,
        "case_suite_wall_duration_seconds": round(time.monotonic() - suite_started, 3),
    }

    total_calls = sum(int(row.get("external_api_calls_this_run", 0)) for row in rows)
    http_ok = sum(int(row.get("http_ok_count_this_run", 0)) for row in rows)
    report["metrics"].update(
        {
            "competitive_choice_case_count": sum(
                int(row.get("locally_valid_candidate_count", 0)) >= 2 for row in rows
            ),
            "locally_valid_candidate_count": sum(
                int(row.get("locally_valid_candidate_count", 0)) for row in rows
            ),
            "unique_candidate_before_model_rate": sum(
                int(row.get("globally_valid_candidate_count", 0)) == 1 for row in rows
            )
            / len(rows),
            "model_choice_preserved_rate": sum(
                row.get("model_choice_preserved") is True for row in rows
            )
            / len(rows),
        }
    )
    report["summary"] = {
        "protocol_expected_count": sum(
            row.get("protocol_matches_expected") is True for row in rows
        ),
        "real_model_call_count": total_calls,
        "http_ok_count": http_ok,
        "http_request_attempt_count": sum(
            int(row.get("http_request_attempts_this_run", 0)) for row in rows
        ),
        "usage": aggregate_usage(
            [row.get("usage") for row in rows if isinstance(row.get("usage"), Mapping)]
        ),
        "prompt_oracle_error_count": sum(
            len(row.get("prompt_oracle_errors", [])) for row in rows
        ),
        "model_choice_preserved_count": sum(
            row.get("model_choice_preserved") is True for row in rows
        ),
    }
    gates = {
        "stage_o_input_module_builds": lean_build.ok,
        "full_16_case_matrix": len(rows) == 16,
        "protocol_16_of_16": report["summary"]["protocol_expected_count"] == 16,
        "real_http_used_for_all_cases": total_calls >= 16 and http_ok >= 16,
        "zero_prompt_oracle_leaks": report["summary"]["prompt_oracle_error_count"] == 0,
        "model_choice_preserved_16_of_16": report["summary"]["model_choice_preserved_count"] == 16,
        "jobs_within_limit": 1 <= args.jobs <= STAGE_O_MAX_JOBS,
        "observed_parallelism": max_active >= min(args.jobs, len(cases)),
        "no_active_case_leak": active == 0,
        "no_resume_or_replay": all(row.get("replayed_from_resume") is False for row in rows),
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
                "real_model_call_count": total_calls,
            }
        )
    )
    return 0 if report["status"] == "VERIFIED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
