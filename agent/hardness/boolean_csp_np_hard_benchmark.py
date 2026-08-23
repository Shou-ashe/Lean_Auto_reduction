"""Runner/scorer contracts for the thirty-case NP-hard Boolean CSP suite.

The production run path reads only the answer-free public suite.  Oracle loading
is exposed as a separate scoring operation and is never called by ``run_suite``.
"""

from __future__ import annotations

from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
from typing import Any, Mapping, Sequence

from agent.reduction import (
    PROFILE_NAMES,
    ReductionOrchestrator,
    ReductionOrchestratorConfig,
    SearchBudget,
    public_status,
)

# Compatibility names for callers that monkeypatch the historical adapter.
NPHardOrchestratorV2 = ReductionOrchestrator
NPHardOrchestratorConfigV2 = ReductionOrchestratorConfig

from .np_hard_input import NPHardInputError
from .np_hard_orchestrator import NPHardOrchestratorError
from .np_hard_production import (
    load_np_hard_production_model_config,
    public_np_hard_status,
)


SUITE_SCHEMA = "boolean_csp_np_hard_suite_v1"
ORACLE_SCHEMA = "boolean_csp_np_hard_oracle_v1"
RUN_SCHEMA = "boolean_csp_np_hard_run_v1"
SCORE_SCHEMA = "boolean_csp_np_hard_score_v1"
SUITE_ID = "boolean-csp-np-hard-v1"
CASE_COUNT = 30
SPLITS = frozenset({"dev", "validation", "heldout"})
CASE_ID_RE = re.compile(r"[a-z0-9][a-z0-9-]*")
DECL_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+")
PUBLIC_CASE_FIELDS = frozenset(
    {"case_id", "split", "module", "problem", "budget_profile"}
)
FORBIDDEN_PUBLIC_KEYS = frozenset(
    {
        "answer",
        "expected",
        "expected_public_status",
        "gold",
        "hint",
        "oracle",
        "route",
        "solution",
    }
)


class BooleanCSPBenchmarkError(ValueError):
    """Stable public-suite, run, or score contract failure."""


@dataclass(frozen=True)
class BooleanCSPCase:
    case_id: str
    split: str
    module: str
    problem: str
    budget_profile: str


@dataclass(frozen=True)
class BooleanCSPSuite:
    suite_id: str
    objective: str
    final_lean_type: str
    cases: tuple[BooleanCSPCase, ...]
    path: Path
    sha256: str


def _read_json(path: Path, *, label: str) -> dict[str, Any]:
    try:
        with path.open(encoding="utf-8") as handle:
            value = json.load(handle)
    except (OSError, json.JSONDecodeError) as error:
        raise BooleanCSPBenchmarkError(f"cannot read {label}: {path}") from error
    if not isinstance(value, dict):
        raise BooleanCSPBenchmarkError(f"{label} must be a JSON object")
    return value


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return "sha256:" + digest.hexdigest()


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _exact_keys(value: Mapping[str, Any], expected: set[str], *, label: str) -> None:
    actual = set(value)
    if actual != expected:
        raise BooleanCSPBenchmarkError(
            f"{label} fields differ: missing={sorted(expected - actual)!r}, "
            f"extra={sorted(actual - expected)!r}"
        )


def load_suite(path: Path) -> BooleanCSPSuite:
    """Load and strictly validate the answer-free thirty-case public suite."""

    resolved = path.resolve()
    value = _read_json(resolved, label="Boolean-CSP public suite")
    _exact_keys(
        value,
        {"schema_version", "suite_id", "objective", "final_lean_type", "cases"},
        label="Boolean-CSP public suite",
    )
    if value["schema_version"] != SUITE_SCHEMA or value["suite_id"] != SUITE_ID:
        raise BooleanCSPBenchmarkError("unsupported Boolean-CSP public suite identity")
    if value["objective"] != "prove_np_hard":
        raise BooleanCSPBenchmarkError("Boolean-CSP suite objective must be prove_np_hard")
    if value["final_lean_type"] != (
        "ComplexityReduction.Certificate.NativeTMNPHard input"
    ):
        raise BooleanCSPBenchmarkError("Boolean-CSP suite changed its final Lean type")
    raw_cases = value["cases"]
    if not isinstance(raw_cases, list) or len(raw_cases) != CASE_COUNT:
        raise BooleanCSPBenchmarkError(f"Boolean-CSP suite must contain exactly {CASE_COUNT} cases")

    cases: list[BooleanCSPCase] = []
    for index, raw in enumerate(raw_cases):
        if not isinstance(raw, dict):
            raise BooleanCSPBenchmarkError(f"case {index} must be an object")
        _exact_keys(raw, set(PUBLIC_CASE_FIELDS), label=f"case {index}")
        if FORBIDDEN_PUBLIC_KEYS.intersection(raw):
            raise BooleanCSPBenchmarkError(f"case {index} leaks oracle material")
        case_id = raw["case_id"]
        split = raw["split"]
        module = raw["module"]
        problem = raw["problem"]
        budget_profile = raw["budget_profile"]
        if not isinstance(case_id, str) or CASE_ID_RE.fullmatch(case_id) is None:
            raise BooleanCSPBenchmarkError(f"case {index} has an invalid case_id")
        if split not in SPLITS:
            raise BooleanCSPBenchmarkError(f"case {case_id} has an invalid split")
        if (
            not isinstance(module, str)
            or DECL_RE.fullmatch(module) is None
            or not module.startswith("Benchmark.Hardness.Inputs.BooleanCSPNPHard.")
        ):
            raise BooleanCSPBenchmarkError(f"case {case_id} has an invalid module")
        if not isinstance(problem, str) or DECL_RE.fullmatch(problem) is None:
            raise BooleanCSPBenchmarkError(f"case {case_id} has an invalid problem")
        if not problem.startswith(module + "."):
            raise BooleanCSPBenchmarkError(f"case {case_id} problem is outside its module")
        if budget_profile != "formal-default":
            raise BooleanCSPBenchmarkError(f"case {case_id} has an invalid budget profile")
        cases.append(BooleanCSPCase(case_id, split, module, problem, budget_profile))

    ids = [case.case_id for case in cases]
    problems = [case.problem for case in cases]
    modules = [case.module for case in cases]
    if len(set(ids)) != CASE_COUNT:
        raise BooleanCSPBenchmarkError("Boolean-CSP suite repeats a case_id")
    if len(set(problems)) != CASE_COUNT or len(set(modules)) != CASE_COUNT:
        raise BooleanCSPBenchmarkError("each Boolean-CSP case needs an isolated module/problem")
    split_counts = {split: sum(case.split == split for case in cases) for split in SPLITS}
    if split_counts != {"dev": 4, "validation": 6, "heldout": 20}:
        raise BooleanCSPBenchmarkError(f"Boolean-CSP split counts drifted: {split_counts!r}")
    return BooleanCSPSuite(
        suite_id=value["suite_id"],
        objective=value["objective"],
        final_lean_type=value["final_lean_type"],
        cases=tuple(cases),
        path=resolved,
        sha256=_sha256_file(resolved),
    )


def _selected_cases(
    suite: BooleanCSPSuite,
    *,
    case_ids: Sequence[str] = (),
    splits: Sequence[str] = (),
) -> tuple[BooleanCSPCase, ...]:
    requested_ids = set(case_ids)
    requested_splits = set(splits)
    unknown_ids = requested_ids - {case.case_id for case in suite.cases}
    unknown_splits = requested_splits - SPLITS
    if unknown_ids:
        raise BooleanCSPBenchmarkError(f"unknown Boolean-CSP case IDs: {sorted(unknown_ids)!r}")
    if unknown_splits:
        raise BooleanCSPBenchmarkError(f"unknown Boolean-CSP splits: {sorted(unknown_splits)!r}")
    if not requested_ids and not requested_splits:
        return suite.cases
    selected = tuple(
        case
        for case in suite.cases
        if case.case_id in requested_ids or case.split in requested_splits
    )
    if not selected:
        raise BooleanCSPBenchmarkError("Boolean-CSP selection is empty")
    return selected


def _run_one(
    *,
    root: Path,
    case: BooleanCSPCase,
    output_root: Path,
    authoring: str,
    lean_timeout: int,
    env_file: Path | None,
    model: str | None,
    model_timeout: int | None,
    model_max_tokens: int | None,
    model_max_retries: int | None,
    reasoning_effort: str | None,
    authoring_attempts: int | None,
    model_call_budget: int | None,
    profile: str,
) -> dict[str, Any]:
    case_dir = (output_root / case.case_id).resolve()
    case_dir.mkdir(parents=True, exist_ok=True)
    started = datetime.now(timezone.utc)
    deepseek = load_np_hard_production_model_config(
        env_file=env_file,
        model=model,
        timeout_seconds=model_timeout,
        max_tokens=model_max_tokens,
        max_retries=model_max_retries,
        reasoning_effort=reasoning_effort,
    )
    try:
        result = NPHardOrchestratorV2(
            NPHardOrchestratorConfigV2(
                root=root,
                input_module=case.module,
                problem_declaration=case.problem,
                output_dir=case_dir,
                profile=profile,
                lean_timeout_seconds=lean_timeout,
                budget=SearchBudget(
                    max_model_calls=(
                        model_call_budget if model_call_budget is not None else 2
                    )
                ),
                model_policy={
                    "disabled": "disabled",
                    "model-auto": "auto",
                    "model-required": "required",
                }[authoring],
                deepseek=deepseek,
            )
        ).run()
    except (NPHardInputError, NPHardOrchestratorError) as error:
        status = public_np_hard_status(
            internal_status="FAILED", failure_code=error.code
        )
        return {
            "case_id": case.case_id,
            "split": case.split,
            "module": case.module,
            "problem": case.problem,
            "status": status,
            "failure_code": error.code,
            "model_calls": 0,
            "model_http_ok": False,
            "model_strategy_accepted": False,
            "model_total_tokens": 0,
            "return_code": 1 if status.startswith("FAILED_") else 2,
            "timed_out": False,
            "elapsed_seconds": (datetime.now(timezone.utc) - started).total_seconds(),
            "report": None,
            "independent_replay_passed": False,
            "axiom_audit_passed": False,
            "endpoint_equality_audit_passed": False,
        }

    if hasattr(result, "model_call_count"):
        identity = result.input_identity or {}
        status = public_status(result)
        model_calls = result.model_call_count
        replay_passed = result.independent_replay_passed
        axiom_passed = result.axiom_audit_passed
        endpoint_passed = result.endpoint_equality_audit_passed
        records = result.model_calls
        model_http_ok = bool(records) and all(
            record.called and record.status_code == 200 for record in records
        )
        model_strategy_accepted = any(record.ok for record in records)
        model_total_tokens = sum(
            int((record.usage or {}).get("total_tokens", 0)) for record in records
        )
    else:
        payload = result.to_dict()
        identity = payload.get("input_identity") or {}
        artifact = payload.get("artifact") or {}
        replay_passed = (payload.get("independent_replay") or {}).get("passed") is True
        axiom_passed = (payload.get("axiom_audit") or {}).get("passed") is True
        endpoint_passed = artifact.get("endpoint") == identity.get("canonical_problem")
        raw_model_calls = result.model_calls
        model_calls = raw_model_calls if isinstance(raw_model_calls, int) else len(raw_model_calls)
        status = public_np_hard_status(
            internal_status=result.status,
            failure_code=result.failure_code,
            model_calls=model_calls,
        )
        model_http_ok = model_calls > 0
        model_strategy_accepted = model_calls > 0
        model_total_tokens = 0
    child_report_path = case_dir / "report.json"
    return {
        "case_id": case.case_id,
        "split": case.split,
        "module": case.module,
        "problem": case.problem,
        "status": status,
        "failure_code": result.failure_code,
        "model_calls": model_calls,
        "model_http_ok": model_http_ok,
        "model_strategy_accepted": model_strategy_accepted,
        "model_total_tokens": model_total_tokens,
        "return_code": (
            0 if status == "VERIFIED" else (1 if status.startswith("FAILED_") else 2)
        ),
        "timed_out": False,
        "elapsed_seconds": (datetime.now(timezone.utc) - started).total_seconds(),
        "report": str(child_report_path) if child_report_path.exists() else None,
        "independent_replay_passed": replay_passed,
        "axiom_audit_passed": axiom_passed,
        "endpoint_equality_audit_passed": (
            endpoint_passed
            and identity.get("requested_declaration") == case.problem
            and identity.get("normalization_certificate") == "lean-checked-artifact"
        ),
    }


def run_suite(
    *,
    root: Path,
    suite_path: Path,
    output_root: Path,
    authoring: str = "model-auto",
    case_ids: Sequence[str] = (),
    splits: Sequence[str] = (),
    jobs: int = 1,
    lean_timeout: int = 600,
    env_file: Path | None = None,
    model: str | None = None,
    model_timeout: int | None = None,
    model_max_tokens: int | None = None,
    model_max_retries: int | None = None,
    reasoning_effort: str | None = None,
    authoring_attempts: int | None = None,
    model_call_budget: int | None = None,
    profile: str = "benchmark",
) -> dict[str, Any]:
    """Run selected public cases without reading any scorer/oracle file."""

    if authoring not in {"disabled", "model-auto", "model-required"}:
        raise BooleanCSPBenchmarkError("unsupported authoring policy")
    if profile not in PROFILE_NAMES:
        raise BooleanCSPBenchmarkError("unsupported reduction profile")
    if jobs < 1 or lean_timeout < 1:
        raise BooleanCSPBenchmarkError("jobs and Lean timeout must be positive")
    root = root.resolve()
    suite = load_suite(suite_path)
    selected = _selected_cases(suite, case_ids=case_ids, splits=splits)
    output_root = output_root.resolve()
    output_root.mkdir(parents=True, exist_ok=True)

    arguments = {
        "root": root,
        "output_root": output_root,
        "authoring": authoring,
        "lean_timeout": lean_timeout,
        "env_file": env_file,
        "model": model,
        "model_timeout": model_timeout,
        "model_max_tokens": model_max_tokens,
        "model_max_retries": model_max_retries,
        "reasoning_effort": reasoning_effort,
        "authoring_attempts": authoring_attempts,
        "model_call_budget": model_call_budget,
        "profile": profile,
    }
    by_id: dict[str, dict[str, Any]] = {}
    with ThreadPoolExecutor(max_workers=min(jobs, len(selected))) as executor:
        futures = {
            executor.submit(_run_one, case=case, **arguments): case.case_id
            for case in selected
        }
        for future in as_completed(futures):
            by_id[futures[future]] = future.result()
    results = [by_id[case.case_id] for case in selected]
    report: dict[str, Any] = {
        "schema_version": RUN_SCHEMA,
        "suite_id": suite.suite_id,
        "suite_sha256": suite.sha256,
        "suite_file": str(suite.path),
        "authoring": authoring,
        "profile": profile,
        "external_model_payload": "opaque-candidate-metadata-only",
        "selected_case_ids": [case.case_id for case in selected],
        "started_case_count": len(selected),
        "completed_case_count": len(results),
        "total_model_calls": sum(result["model_calls"] for result in results),
        "model_called_case_count": sum(result["model_calls"] > 0 for result in results),
        "model_http_ok_case_count": sum(result["model_http_ok"] for result in results),
        "model_strategy_accepted_case_count": sum(
            result["model_strategy_accepted"] for result in results
        ),
        "model_total_tokens": sum(result["model_total_tokens"] for result in results),
        "required_model_call_coverage_passed": (
            authoring != "model-required"
            or all(result["model_calls"] > 0 for result in results)
        ),
        "required_model_http_coverage_passed": (
            authoring != "model-required"
            or all(result["model_http_ok"] for result in results)
        ),
        "cases": results,
        "oracle_accessed": False,
    }
    _write_json(output_root / "run_report.json", report)
    return report


def load_oracle(path: Path, *, suite: BooleanCSPSuite) -> dict[str, Any]:
    """Load the isolated mathematical/scoring oracle after production finishes."""

    value = _read_json(path.resolve(), label="Boolean-CSP oracle")
    _exact_keys(value, {"schema_version", "suite_id", "source_problem", "cases"}, label="oracle")
    if value["schema_version"] != ORACLE_SCHEMA or value["suite_id"] != suite.suite_id:
        raise BooleanCSPBenchmarkError("Boolean-CSP oracle identity mismatch")
    raw_cases = value["cases"]
    if not isinstance(raw_cases, list) or len(raw_cases) != CASE_COUNT:
        raise BooleanCSPBenchmarkError(
            f"Boolean-CSP oracle must contain exactly {CASE_COUNT} cases"
        )
    expected_fields = {
        "case_id",
        "expected_public_status",
        "mathematical_class",
        "embedding_kind",
        "requires_model",
    }
    for index, raw in enumerate(raw_cases):
        if not isinstance(raw, dict):
            raise BooleanCSPBenchmarkError(f"oracle case {index} must be an object")
        _exact_keys(raw, expected_fields, label=f"oracle case {index}")
        if raw["expected_public_status"] != "VERIFIED":
            raise BooleanCSPBenchmarkError("every hard Boolean-CSP oracle target must verify")
        if raw["mathematical_class"] != "NP-complete":
            raise BooleanCSPBenchmarkError("oracle mathematical class drifted")
    public_ids = {case.case_id for case in suite.cases}
    oracle_ids = {raw["case_id"] for raw in raw_cases}
    if oracle_ids != public_ids or len(oracle_ids) != CASE_COUNT:
        raise BooleanCSPBenchmarkError("Boolean-CSP oracle/public case sets differ")
    return value


def score_run(
    *,
    suite_path: Path,
    oracle_path: Path,
    run_report_path: Path,
    score_report_path: Path,
) -> dict[str, Any]:
    """Score kernel-verified exact-endpoint completions using the isolated oracle."""

    suite = load_suite(suite_path)
    run = _read_json(run_report_path.resolve(), label="Boolean-CSP run report")
    if run.get("schema_version") != RUN_SCHEMA or run.get("suite_id") != suite.suite_id:
        raise BooleanCSPBenchmarkError("Boolean-CSP run report identity mismatch")
    if run.get("suite_sha256") != suite.sha256 or run.get("oracle_accessed") is not False:
        raise BooleanCSPBenchmarkError("Boolean-CSP run was not bound to the isolated public suite")
    oracle = load_oracle(oracle_path, suite=suite)
    oracle_by_id = {case["case_id"]: case for case in oracle["cases"]}
    scored: list[dict[str, Any]] = []
    for result in run.get("cases", []):
        case_id = result.get("case_id")
        if case_id not in oracle_by_id:
            raise BooleanCSPBenchmarkError(f"run contains unknown case {case_id!r}")
        verified = (
            result.get("status") == "VERIFIED"
            and result.get("independent_replay_passed") is True
            and result.get("axiom_audit_passed") is True
            and result.get("endpoint_equality_audit_passed") is True
        )
        scored.append(
            {
                "case_id": case_id,
                "passed": verified,
                "actual_status": result.get("status"),
                "failure_code": result.get("failure_code"),
                "model_calls": result.get("model_calls", 0),
                "embedding_kind": oracle_by_id[case_id]["embedding_kind"],
            }
        )
    passed = sum(case["passed"] for case in scored)
    total = len(scored)
    score: dict[str, Any] = {
        "schema_version": SCORE_SCHEMA,
        "suite_id": suite.suite_id,
        "suite_sha256": suite.sha256,
        "oracle_sha256": _sha256_file(oracle_path.resolve()),
        "run_report": str(run_report_path.resolve()),
        "selected_case_count": total,
        "passed_case_count": passed,
        "completion_rate": 0.0 if total == 0 else passed / total,
        "cases": scored,
    }
    _write_json(score_report_path.resolve(), score)
    return score


__all__ = [
    "BooleanCSPBenchmarkError",
    "BooleanCSPCase",
    "BooleanCSPSuite",
    "load_oracle",
    "load_suite",
    "run_suite",
    "score_run",
]
