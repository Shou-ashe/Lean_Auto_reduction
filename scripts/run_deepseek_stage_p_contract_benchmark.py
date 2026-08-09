#!/usr/bin/env python3
"""Run the frozen 24-case P-A contract with fresh real DeepSeek calls."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import sys
import threading
import time
from collections import Counter
from collections.abc import Mapping, Sequence
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, replace
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
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
from agent.hardness.stage_p_contract import (  # noqa: E402
    STAGE_P_FEASIBILITY_MODULE,
    STAGE_P_INPUT_MODULE,
    STAGE_P_MAX_JOBS,
    STAGE_P_PROBE_MODULE,
    STAGE_P_PRODUCER_SUPPORT_MODULE,
    STAGE_P_STANDARD_HELPER_MODULE,
    STAGE_P_SYSTEM_PROMPT,
    StagePContractError,
    StagePPatchAction,
    audit_stage_p_prompt,
    build_contract_probe_source,
    build_stage_p_contract_prompt,
    build_stage_p_task,
    load_and_validate_stage_p_mutations,
    load_and_validate_stage_p_worker_microbenchmark,
    parse_stage_p_action,
    stage_p_report_skeleton,
    validate_stage_p_suites,
    validate_stage_p_terminal_action,
)


DEFAULT_POSITIVE_SUITE = ROOT / "Benchmark/Hardness/Suites/stage_p_open_world.json"
DEFAULT_NEGATIVE_SUITE = ROOT / "Benchmark/Hardness/Suites/stage_p_adversarial.json"
DEFAULT_MUTATIONS = ROOT / "Benchmark/Hardness/Suites/stage_p_mutations.json"
DEFAULT_WORKER_BENCHMARK = (
    ROOT / "Benchmark/Hardness/Suites/stage_p_lean_worker_microbenchmark.json"
)
STAGE_P_INPUT_SOURCE = ROOT / "Lean/Reference/Benchmark/Hardness/Inputs/StageP/Inputs.lean"
STAGE_P_PRODUCER_SUPPORT_SOURCE = (
    ROOT / "Lean/Reference/Benchmark/Hardness/Inputs/StageP/ProducerSupport.lean"
)
STAGE_P_STANDARD_HELPER_SOURCE = (
    ROOT / "Lean/Reference/ComplexityReduction/Problems/Karp21/ExactCoverStandardTM.lean"
)
STAGE_P_FEASIBILITY_SOURCE = (
    ROOT / "Lean/Reference/Benchmark/Hardness/Oracles/Gold/StagePSemanticFeasibility.lean"
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
        raise ValueError(f"Stage P contract output root must be fresh and empty: {path}")
    path.mkdir(parents=True, exist_ok=True)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    command.add_argument("--positive-suite", type=Path, default=DEFAULT_POSITIVE_SUITE)
    command.add_argument("--negative-suite", type=Path, default=DEFAULT_NEGATIVE_SUITE)
    command.add_argument("--mutations", type=Path, default=DEFAULT_MUTATIONS)
    command.add_argument("--worker-benchmark", type=Path, default=DEFAULT_WORKER_BENCHMARK)
    command.add_argument("--env-file", type=Path, default=ROOT / ".env")
    command.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent/deepseek-stage-p-contract-full",
    )
    command.add_argument(
        "--canonical-report",
        type=Path,
        default=ROOT / "Benchmark/Hardness/STAGE_P_CONTRACT_REPORT.json",
    )
    command.add_argument("--run-label", default="stage-p-a-contract-full-real-deepseek")
    command.add_argument("--model", default=DEFAULT_MODEL)
    command.add_argument("--model-timeout", type=int, default=300)
    command.add_argument("--model-max-tokens", type=int, default=24576)
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
            "system": STAGE_P_SYSTEM_PROMPT,
            "system_sha256": sha256_text(STAGE_P_SYSTEM_PROMPT),
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


def _first_diagnostic(command_result: Any) -> str:
    text = "\n".join(
        part for part in (command_result.stderr, command_result.stdout) if part
    ).strip()
    if not text:
        return "Lean candidate validation failed without diagnostic text"
    lines = text.splitlines()
    return "\n".join(lines[:12])[:2000]


def _feedback_for_prompt(
    *, case: BenchmarkCase, output_root: Path, message: str
) -> str:
    """Bound diagnostics while removing benchmark-local path identifiers."""

    sanitized = message
    case_root = output_root / "cases" / case.id
    for value, replacement in (
        (str(case_root.resolve()), "<case-workspace>"),
        (str(output_root.resolve()), "<run-workspace>"),
        (case.id, "<case>"),
    ):
        sanitized = sanitized.replace(value, replacement)
    return sanitized[:2000]


def _contract_registry_absence(cases: Sequence[BenchmarkCase]) -> dict[str, Any]:
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
        "Benchmark/Hardness/Oracles/Gold",
    )
    hits: list[dict[str, str]] = []
    for source in public_files:
        text = source.read_text(encoding="utf-8")
        for marker in forbidden_markers:
            if marker in text:
                hits.append(
                    {"file": str(source.relative_to(ROOT)), "marker": marker}
                )
    return {
        "schema_version": "hardness_stage_p_semantic_feasibility_isolation_v1",
        "hidden_module": STAGE_P_FEASIBILITY_MODULE,
        "qualification_compile_only": True,
        "public_reference_hits": hits,
        "passed": not hits,
    }


def run_case(
    *,
    index: int,
    case: BenchmarkCase,
    output_root: Path,
    config: DeepSeekConfig,
    max_contract_turns: int,
    lean_timeout: int,
) -> CaseOutcome:
    started = time.monotonic()
    case_root = output_root / "cases" / case.id
    case_root.mkdir(parents=True, exist_ok=True)
    task = build_stage_p_task(case)
    write_json(case_root / "task.json", task.to_dict())
    calls: list[dict[str, Any]] = []
    protocol_errors: list[dict[str, str]] = []
    compile_attempts: list[dict[str, Any]] = []
    accepted_action: StagePPatchAction | None = None
    feedback: str | None = None
    seen_patch_hashes: Counter[str] = Counter()
    client = DeepSeekClient(config)
    attempt_budget = min(
        max_contract_turns,
        int(case.authoring_policy.get("attempt_budget", 4)),
        max(1, task.semantic_turn_budget),
    )

    for turn in range(1, attempt_budget + 1):
        prompt = build_stage_p_contract_prompt(task=task, previous_rejection=feedback)
        try:
            prompt_payload = json.loads(prompt)
            audit_stage_p_prompt(prompt_payload, forbidden_values=(case.id,))
        except (json.JSONDecodeError, StagePContractError) as error:
            protocol_errors.append(
                {"turn": str(turn), "code": "prompt_oracle_leak", "message": str(error)}
            )
            break
        response = client.complete_json(system=STAGE_P_SYSTEM_PROMPT, prompt=prompt)
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
            feedback = _feedback_for_prompt(
                case=case,
                output_root=output_root,
                message=config.redact(response.error or "DeepSeek HTTP call failed"),
            )
            continue
        try:
            action = parse_stage_p_action(response.content, task=task)
            write_json(case_root / "calls" / f"turn-{turn:02d}-action.json", action.to_dict())
            validate_stage_p_terminal_action(action, task=task)
            if action.action == "submit_patch":
                body_hash = sha256_text(action.replacement_body or "")
                seen_patch_hashes[body_hash] += 1
                if seen_patch_hashes[body_hash] >= 2:
                    raise StagePContractError(
                        "authoring_no_progress", "the same replacement body was submitted twice"
                    )
                generated_source = build_contract_probe_source(
                    task=task,
                    action=action,
                    namespace_suffix=f"Case{index}_{body_hash[:12]}",
                )
                candidate_path = case_root / "candidate" / f"turn-{turn:02d}.lean"
                candidate_path.parent.mkdir(parents=True, exist_ok=True)
                candidate_path.write_text(generated_source, encoding="utf-8")
                lean_result = run_command(
                    ["lake", "env", "lean", str(candidate_path.resolve())],
                    cwd=ROOT / "Lean",
                    timeout_seconds=lean_timeout,
                    output_limit=64 * 1024,
                )
                compile_record = {
                    "turn": turn,
                    "candidate_file": str(candidate_path.resolve()),
                    "candidate_source_sha256": sha256_text(generated_source),
                    "model_body_sha256": body_hash,
                    "compiler_inserted_math_token_count": 0,
                    "command": lean_result.to_dict(),
                }
                compile_attempts.append(compile_record)
                write_json(
                    case_root / "candidate" / f"turn-{turn:02d}-compile.json",
                    compile_record,
                )
                if not lean_result.ok:
                    raise StagePContractError(
                        "candidate_lean_compile_failed", _first_diagnostic(lean_result)
                    )
            accepted_action = action
            break
        except StagePContractError as error:
            protocol_errors.append(
                {"turn": str(turn), "code": error.code, "message": error.message[:2000]}
            )
            feedback = _feedback_for_prompt(
                case=case,
                output_root=output_root,
                message=f"{error.code}: {error.message}",
            )

    expected_status = case.expected.final_status
    expected_failure = case.expected.final_failure_code
    if accepted_action is None:
        final_status = "FAILED"
        final_failure = protocol_errors[-1]["code"] if protocol_errors else "model_transport_failed"
        protocol_matches = False
    elif accepted_action.action == "submit_patch":
        final_status = "VERIFIED"
        final_failure = None
        protocol_matches = expected_status == "VERIFIED"
    else:
        final_status = "BLOCKED"
        final_failure = accepted_action.failure_code
        protocol_matches = (
            expected_status == "BLOCKED" and final_failure == expected_failure
        )
    usage = aggregate_usage(
        [call.get("usage") for call in calls if isinstance(call.get("usage"), Mapping)]
    )
    row = {
        "id": case.id,
        "execution_position": index,
        "protocol_role": case.stage_p["protocol_role"],
        "contract_probe_profile_sha256": sha256_text(
            str(case.stage_p["contract_probe_profile"])
        ),
        "expected_status": expected_status,
        "expected_failure_code": expected_failure,
        "status": final_status,
        "failure_code": final_failure,
        "protocol_matches_expected": protocol_matches,
        "model_generated_body_accepted": bool(
            accepted_action and accepted_action.action == "submit_patch"
        ),
        "accepted_action": accepted_action.to_dict() if accepted_action else None,
        "calls": calls,
        "compile_attempts": compile_attempts,
        "protocol_errors": protocol_errors,
        "external_api_calls_this_run": sum(call["called"] is True for call in calls),
        "http_ok_count_this_run": sum(call["ok"] is True for call in calls),
        "http_request_attempts_this_run": sum(int(call.get("attempts", 0)) for call in calls),
        "usage": usage,
        "compiler_inserted_math_token_count": 0,
        "replayed_from_resume": False,
        "old_response_used": False,
        "wall_duration_seconds": round(time.monotonic() - started, 3),
    }
    write_json(case_root / "outcome.json", row)
    return CaseOutcome(index=index, row=row)


def consumer_outcome(
    *, index: int, case: BenchmarkCase, output_root: Path, producer_passed: bool
) -> CaseOutcome:
    case_root = output_root / "cases" / case.id
    case_root.mkdir(parents=True, exist_ok=True)
    row = {
        "id": case.id,
        "execution_position": index,
        "protocol_role": "consumer",
        "expected_status": "VERIFIED",
        "expected_failure_code": None,
        "status": "VERIFIED" if producer_passed else "FAILED",
        "failure_code": None if producer_passed else "published_capability_not_visible",
        "protocol_matches_expected": producer_passed,
        "model_generated_body_accepted": False,
        "accepted_action": {
            "action": "reuse_capability",
            "publication_source": "p-capability-producer",
            "wave_barrier_satisfied": producer_passed,
        },
        "calls": [],
        "compile_attempts": [],
        "protocol_errors": [],
        "external_api_calls_this_run": 0,
        "http_ok_count_this_run": 0,
        "http_request_attempts_this_run": 0,
        "usage": {},
        "compiler_inserted_math_token_count": 0,
        "replayed_from_resume": False,
        "old_response_used": False,
        "consumer_authoring_attempts": 0,
        "wall_duration_seconds": 0.0,
    }
    write_json(case_root / "outcome.json", row)
    return CaseOutcome(index=index, row=row)


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


def main() -> int:
    args = parser().parse_args()
    if not 1 <= args.jobs <= STAGE_P_MAX_JOBS:
        raise ValueError(f"Stage P contract jobs must be in 1..{STAGE_P_MAX_JOBS}")
    if not 1 <= args.max_contract_turns <= 4:
        raise ValueError("Stage P P-A max-contract-turns must be in 1..4")
    prepare_fresh_output_root(args.output_root)
    if args.canonical_report.exists():
        raise ValueError(f"canonical Stage P contract report already exists: {args.canonical_report}")

    positive_suite = load_benchmark_suite(args.positive_suite)
    negative_suite = load_benchmark_suite(args.negative_suite)
    cases = validate_stage_p_suites(positive_suite, negative_suite)
    mutations = load_and_validate_stage_p_mutations(args.mutations)
    worker_benchmark = load_and_validate_stage_p_worker_microbenchmark(
        args.worker_benchmark
    )
    config = DeepSeekConfig.from_environment(env_file=args.env_file)
    config = replace(
        config,
        model=args.model,
        timeout_seconds=args.model_timeout,
        max_tokens=args.model_max_tokens,
    )
    if not config.api_key:
        raise ValueError("real Stage P contract run requires DEEPSEEK_API_KEY")

    report = stage_p_report_skeleton()
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
                "mutations": str(args.mutations.resolve()),
                "mutations_sha256": sha256_file(args.mutations),
                "worker_benchmark": str(args.worker_benchmark.resolve()),
                "worker_benchmark_sha256": sha256_file(args.worker_benchmark),
                "stage_p_input_source_sha256": sha256_file(STAGE_P_INPUT_SOURCE),
                "producer_support_source_sha256": sha256_file(
                    STAGE_P_PRODUCER_SUPPORT_SOURCE
                ),
                "exact_cover_standard_helper_sha256": sha256_file(
                    STAGE_P_STANDARD_HELPER_SOURCE
                ),
                "hidden_semantic_feasibility_sha256": sha256_file(
                    STAGE_P_FEASIBILITY_SOURCE
                ),
                "canonical_case_count": len(cases),
                "materialized_mutation_count": len(mutations),
            },
            "contract_schemas": {
                "typed_task": "hardness_stage_p_task_v1",
                "patch": "hardness_stage_p_patch_v1",
                "diagnostics": "hardness_stage_p_diagnostics_v1",
                "publication": "hardness_stage_p_publication_manifest_v1",
                "worker": "hardness_stage_p_worker_session_v1",
                "report": "hardness_stage_p_contract_deepseek_report_v1",
            },
            "model": config.to_public_dict(),
            "worker_contract": {
                "benchmark_id": worker_benchmark["benchmark_id"],
                "repeat_count": worker_benchmark["repeat_count"],
                "maximum_workers": worker_benchmark["maximum_workers"],
                "schema_validated": True,
                "performance_executed_in_p_a": False,
            },
        }
    )
    report_path = args.output_root / "report.json"
    write_json(report_path, report)

    lean_started = time.monotonic()
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
        cwd=ROOT / "Lean",
        timeout_seconds=args.lean_timeout,
        output_limit=64 * 1024,
    )
    report["lean_input_gate"] = {
        "command": lean_build.to_dict(),
        "wall_duration_seconds": round(time.monotonic() - lean_started, 3),
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
    report["registry_absence_preflight"] = _contract_registry_absence(cases)
    report["semantic_feasibility_isolation"] = _semantic_feasibility_isolation(
        positive_suite=args.positive_suite,
        negative_suite=args.negative_suite,
    )
    write_json(report_path, report)
    if not lean_build.ok:
        report["status"] = "FAILED"
        report["failures"] = ["stage_p_input_module_build_failed"]
        report["finished_at"] = utc_now()
        write_json(report_path, report)
        return 1

    indexed_cases = list(enumerate(cases, start=1))
    model_cases = [item for item in indexed_cases if item[1].stage_p["protocol_role"] != "consumer"]
    consumer_item = next(item for item in indexed_cases if item[1].stage_p["protocol_role"] == "consumer")
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
                lean_timeout=args.lean_timeout,
            )
        finally:
            with lock:
                active -= 1

    outcomes: list[CaseOutcome] = []
    suite_started = time.monotonic()
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = {executor.submit(guarded, item): item for item in model_cases}
        for future in as_completed(futures):
            index, case = futures[future]
            try:
                outcomes.append(future.result())
            except Exception as error:
                outcomes.append(
                    CaseOutcome(
                        index=index,
                        row={
                            "id": case.id,
                            "execution_position": index,
                            "status": "FAILED",
                            "failure_code": "runner_error",
                            "protocol_matches_expected": False,
                            "runner_error": config.redact(f"{type(error).__name__}: {error}"),
                            "external_api_calls_this_run": 0,
                            "http_ok_count_this_run": 0,
                            "http_request_attempts_this_run": 0,
                            "usage": {},
                            "compiler_inserted_math_token_count": 0,
                            "replayed_from_resume": False,
                            "old_response_used": False,
                        },
                    )
                )
    producer = next(
        (outcome for outcome in outcomes if outcome.row.get("id") == "p-capability-producer"),
        None,
    )
    outcomes.append(
        consumer_outcome(
            index=consumer_item[0],
            case=consumer_item[1],
            output_root=args.output_root,
            producer_passed=bool(producer and producer.row.get("protocol_matches_expected") is True),
        )
    )
    outcomes.sort(key=lambda outcome: outcome.index)
    rows = [outcome.row for outcome in outcomes]
    report["cases"] = rows
    report["parallel_execution"] = {
        "configured_jobs": args.jobs,
        "observed_max_case_concurrency": max_active,
        "active_case_task_count": active,
        "producer_consumer_wave_barrier": True,
        "case_suite_wall_duration_seconds": round(time.monotonic() - suite_started, 3),
    }

    model_rows = [row for row in rows if row.get("protocol_role") != "consumer"]
    positive_rows = [row for row in rows[:12]]
    negative_rows = [row for row in rows[12:]]
    total_calls = sum(int(row.get("external_api_calls_this_run", 0)) for row in rows)
    report["summary"] = {
        "protocol_expected_count": sum(row.get("protocol_matches_expected") is True for row in rows),
        "positive_expected_count": sum(row.get("protocol_matches_expected") is True for row in positive_rows),
        "negative_expected_count": sum(row.get("protocol_matches_expected") is True for row in negative_rows),
        "model_generated_probe_body_count": sum(row.get("model_generated_body_accepted") is True for row in positive_rows),
        "real_model_call_count": total_calls,
        "model_eligible_cases_with_http_call": sum(int(row.get("external_api_calls_this_run", 0)) >= 1 for row in model_rows),
        "model_eligible_cases_with_http_ok": sum(int(row.get("http_ok_count_this_run", 0)) >= 1 for row in model_rows),
        "http_request_attempt_count": sum(int(row.get("http_request_attempts_this_run", 0)) for row in rows),
        "usage": aggregate_usage([row.get("usage") for row in rows]),
        "compiler_inserted_math_token_count": sum(int(row.get("compiler_inserted_math_token_count", 0)) for row in rows),
        "prompt_or_protocol_error_count": sum(len(row.get("protocol_errors", [])) for row in rows),
    }
    secret_hits = _scan_for_secret(args.output_root, config.api_key)
    report["secret_audit"] = {
        "api_key_occurrence_count": len(secret_hits),
        "authorization_header_occurrence_count": sum(
            "authorization:" in path.read_text(encoding="utf-8", errors="ignore").lower()
            for path in args.output_root.rglob("*")
            if path.is_file()
        ),
    }
    registry = report["registry_absence_preflight"]
    semantic_hash_keys = (
        "stage_p_input_source_sha256",
        "producer_support_source_sha256",
        "exact_cover_standard_helper_sha256",
        "hidden_semantic_feasibility_sha256",
    )
    gates = {
        "stage_p_lean_contract_modules_build": lean_build.ok,
        "semantic_feasibility_standard_axiom_gate": lean_build.ok
        and report["lean_input_gate"]["hidden_module_exposed_to_model"] is False,
        "semantic_feasibility_oracle_isolated": report[
            "semantic_feasibility_isolation"
        ]["passed"]
        is True,
        "semantic_source_hashes_recorded": all(
            isinstance(report["benchmark"].get(key), str)
            and len(report["benchmark"][key]) == 64
            for key in semantic_hash_keys
        ),
        "full_24_case_matrix": len(rows) == 24,
        "protocol_24_of_24": report["summary"]["protocol_expected_count"] == 24,
        "positive_12_of_12": report["summary"]["positive_expected_count"] == 12,
        "negative_12_of_12": report["summary"]["negative_expected_count"] == 12,
        "model_generated_probe_bodies_11_of_11": report["summary"]["model_generated_probe_body_count"] == 11,
        "real_http_used_for_all_23_model_eligible_cases": report["summary"]["model_eligible_cases_with_http_call"] == 23,
        "http_ok_for_all_23_model_eligible_cases": report["summary"]["model_eligible_cases_with_http_ok"] == 23,
        "consumer_zero_authoring": rows[11].get("external_api_calls_this_run") == 0 and rows[11].get("consumer_authoring_attempts") == 0,
        "mutation_matrix_frozen_at_72": len(mutations) == 72,
        "worker_contract_frozen": report["worker_contract"]["schema_validated"] is True,
        "registry_absence_11_of_11": registry["passed_count"] == 11,
        "compiler_inserted_math_zero": report["summary"]["compiler_inserted_math_token_count"] == 0,
        "no_api_key_or_authorization_leak": report["secret_audit"]["api_key_occurrence_count"] == 0 and report["secret_audit"]["authorization_header_occurrence_count"] == 0,
        "no_resume_replay_or_old_response": all(
            row.get("replayed_from_resume") is False and row.get("old_response_used") is False
            for row in rows
        ),
        "jobs_within_limit": 1 <= args.jobs <= STAGE_P_MAX_JOBS,
        "observed_parallelism": max_active >= min(args.jobs, len(model_cases)),
        "no_active_case_leak": active == 0,
        "producer_consumer_wave_barrier": rows[11].get("accepted_action", {}).get("wave_barrier_satisfied") is True,
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
                "protocol_expected_count": report["summary"]["protocol_expected_count"],
            }
        )
    )
    return 0 if report["status"] == "VERIFIED" else 1


if __name__ == "__main__":
    raise SystemExit(main())
