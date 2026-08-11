"""Case-level, source-hidden Archon comparison benchmark.

Unlike the legacy model-client adapter, this runner never exposes the
production agent's typed DAG, selected route, dependency bodies, diagnostics,
or benchmark-authored proof recommendation.  Every Archon call receives only
one public case statement, one formal Lean goal, and the requested proof kind.
The trusted repository verifies the returned body only after Archon exits.
"""

from __future__ import annotations

import hashlib
import json
import re
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

from .archon_runner import ArchonModelClient, _indent_two, _sanitize_component
from .lean_runner import run_command
from .model_client import DeepSeekConfig


SCHEMA_VERSION = "hardness_archon_blackbox_benchmark_v1"
CASE_SCHEMA_VERSION = "hardness_archon_blackbox_case_v1"
REGISTRY_SCHEMA_VERSION = "hardness_benchmark_registry_v1"
REGISTRY_BENCHMARK_ID = "np-hard-real-reduction-v1"
FORBIDDEN_BODY_RE = re.compile(r"\b(?:sorry|admit|sorryAx|axiom|unsafe)\b")
OBVIOUS_COMPOSITION_RE = re.compile(
    r"(?:\.comp\b|CertifiedPath|toCertifiedReduction|ofCompleteAlongPath)"
)


@dataclass(frozen=True)
class ArchonBenchmarkCase:
    ordinal: int
    case_id: str
    kind: str
    split: str
    module: str
    statement: str
    requirement: str
    exact_type: str
    problem: str | None = None
    source: str | None = None
    target: str | None = None

    @property
    def imports(self) -> tuple[str, ...]:
        abi = (
            "ComplexityReduction.Certificate.NativeCompleteness"
            if self.kind in {"capability", "frontier", "boolean_csp"}
            else "ComplexityReduction.Certificate.Reduction"
        )
        return (abi, self.module)

    def public_input(self) -> dict[str, Any]:
        return {
            "case_id": self.case_id,
            "kind": self.kind,
            "split": self.split,
            "statement": self.statement,
            "requirement": self.requirement,
            "formal_goal": {
                "imports": list(self.imports),
                "exact_type": self.exact_type,
            },
        }


def _read_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        value = json.load(handle)
    if not isinstance(value, dict):
        raise ValueError(f"expected one JSON object in {path}")
    return value


def _sha256_text(value: str) -> str:
    return "sha256:" + hashlib.sha256(value.encode("utf-8")).hexdigest()


def _sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return "sha256:" + digest.hexdigest()


def _write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def load_archon_benchmark_cases(
    *,
    root: Path,
    lanes: Sequence[str] | None = None,
    selected_case_ids: Sequence[str] | None = None,
) -> tuple[ArchonBenchmarkCase, ...]:
    """Load only the frozen public registry and public suite statements."""

    root = root.resolve()
    registry_path = root / "Benchmark" / "Hardness" / "BENCHMARK_REGISTRY.json"
    registry = _read_json(registry_path)
    if registry.get("schema_version") != REGISTRY_SCHEMA_VERSION:
        raise ValueError("unsupported benchmark registry schema")
    if registry.get("benchmark_id") != REGISTRY_BENCHMARK_ID:
        raise ValueError("unexpected benchmark registry identity")

    exact_by_id: dict[str, dict[str, Any]] = {}
    for name in (
        "exact_reduction_edge_dev_v1.json",
        "exact_reduction_edge_heldout_v1.json",
        "exact_reduction_edge_validation_v1.json",
    ):
        suite = _read_json(root / "Benchmark" / "Hardness" / "Suites" / name)
        for raw in suite.get("cases") or []:
            if not isinstance(raw, dict) or not isinstance(raw.get("case_id"), str):
                raise ValueError(f"invalid exact-edge public case in {name}")
            exact_by_id[raw["case_id"]] = raw

    lane_filter = set(lanes or ("capability", "frontier", "exact_edge", "boolean_csp"))
    id_filter = set(selected_case_ids or ())
    cases: list[ArchonBenchmarkCase] = []
    for ordinal, raw in enumerate(registry.get("cases") or []):
        if not isinstance(raw, dict):
            raise ValueError("benchmark registry contains a non-object case")
        case_id = str(raw.get("case_id") or "")
        kind = str(raw.get("kind") or "")
        if kind not in lane_filter or (id_filter and case_id not in id_filter):
            continue
        split = str(raw.get("split") or "")
        module = str(raw.get("module") or "")
        if kind in {"capability", "frontier", "boolean_csp"}:
            problem = str(raw.get("problem") or "")
            statement = f"Prove in Lean 4 that `{problem}` is NP-hard."
            cases.append(
                ArchonBenchmarkCase(
                    ordinal=ordinal,
                    case_id=case_id,
                    kind=kind,
                    split=split,
                    module=module,
                    statement=statement,
                    requirement="Produce a complete proof of NP-hardness.",
                    exact_type=(
                        "ComplexityReduction.Certificate.NativeTMNPHard " + problem
                    ),
                    problem=problem,
                )
            )
            continue
        if kind != "exact_edge":
            raise ValueError(f"unsupported benchmark lane: {kind!r}")
        public = exact_by_id.get(case_id)
        if public is None:
            raise ValueError(f"exact-edge case is missing from public suites: {case_id}")
        source = str(public.get("source") or "")
        target = str(public.get("target") or "")
        cases.append(
            ArchonBenchmarkCase(
                ordinal=ordinal,
                case_id=case_id,
                kind=kind,
                split=split,
                module=module,
                statement=str(public.get("statement") or ""),
                requirement=(
                    "Produce a complete certified reduction in the stated direction."
                ),
                exact_type=(
                    "ComplexityReduction.Certificate.CertifiedReduction\n"
                    f"      {source}\n"
                    f"      {target}"
                ),
                source=source,
                target=target,
            )
        )
    if id_filter and id_filter != {case.case_id for case in cases}:
        missing = sorted(id_filter - {case.case_id for case in cases})
        raise ValueError(f"requested case IDs are outside the selected lanes: {missing}")
    return tuple(cases)


def _verification_source(case: ArchonBenchmarkCase, body: str) -> tuple[str, str]:
    safe = _sanitize_component(case.case_id, fallback="Case")
    namespace = f"Generated.ArchonVerification.{safe}"
    source = "\n".join(
        [
            *(f"import {module}" for module in case.imports),
            "import ComplexityReduction.AxiomGate",
            "",
            f"namespace {namespace}",
            "",
            "noncomputable def result :",
            f"    {case.exact_type} :=",
            _indent_two(body.rstrip()),
            "",
            f"end {namespace}",
            "",
            f"assert_standard_axioms {namespace}.result",
            "",
        ]
    )
    return namespace, source


def _public_goal_preflight_source(case: ArchonBenchmarkCase) -> str:
    safe = _sanitize_component(case.case_id, fallback="Case")
    namespace = f"Generated.ArchonPublicGoal.{safe}"
    return "\n".join(
        [
            *(f"import {module}" for module in case.imports),
            "",
            f"namespace {namespace}",
            "",
            "noncomputable def result :",
            f"    {case.exact_type} :=",
            "  by",
            "    sorry",
            "",
            f"end {namespace}",
            "",
        ]
    )


def _command_evidence(command: Any) -> dict[str, Any]:
    return {
        "ok": bool(command.ok),
        "exit_code": command.exit_code,
        "timed_out": command.timed_out,
        "duration_seconds": command.duration_seconds,
        "stdout": command.stdout,
        "stderr": command.stderr,
    }


def _run_case(
    *,
    root: Path,
    output_root: Path,
    case: ArchonBenchmarkCase,
    client: ArchonModelClient,
    lean_timeout_seconds: int,
) -> dict[str, Any]:
    started = time.monotonic()
    case_dir = output_root / "cases" / case.case_id
    case_dir.mkdir(parents=True, exist_ok=True)
    public_input = case.public_input()
    _write_json(case_dir / "archon-input.json", public_input)

    public_goal_file = case_dir / "PublicGoalPreflight.lean"
    public_goal_file.write_text(
        _public_goal_preflight_source(case),
        encoding="utf-8",
    )
    public_goal_preflight = run_command(
        ["lake", "env", "lean", str(public_goal_file)],
        cwd=root / "Lean",
        timeout_seconds=lean_timeout_seconds,
    )
    if not public_goal_preflight.ok:
        row = {
            "schema_version": CASE_SCHEMA_VERSION,
            "ordinal": case.ordinal,
            "case_id": case.case_id,
            "kind": case.kind,
            "split": case.split,
            "statement_sha256": _sha256_text(case.statement),
            "public_input_file": str((case_dir / "archon-input.json").resolve()),
            "public_input_sha256": _sha256_file(case_dir / "archon-input.json"),
            "status": "BLOCKED_INPUT",
            "kernel_verified": False,
            "proof_sha256": None,
            "forbidden_token": None,
            "archon": {
                "called": False,
                "ok": False,
                "error": "public formal goal does not elaborate",
                "duration_seconds": 0.0,
                "usage": None,
                "worker_index": None,
                "call_index": None,
                "log_file": None,
                "exit_code": None,
            },
            "isolation": {
                "passed": True,
                "visible_lean_sources": [],
                "complexity_reduction_source_visible": False,
                "benchmark_recommendation_visible": False,
                "oracle_visible": False,
                "typed_dag_visible": False,
                "previous_diagnostics_visible": False,
                "web_and_search_tools_enabled": False,
                "compiled_dependencies": "not opened because the public goal failed",
            },
            "verification": {
                "public_goal_preflight": _command_evidence(public_goal_preflight),
            },
            "case_dir": str(case_dir.resolve()),
            "wall_duration_seconds": round(time.monotonic() - started, 3),
        }
        _write_json(case_dir / "result.json", row)
        return row

    attempt = client.prove_case(
        case_id=case.case_id,
        statement=case.statement,
        requirement=case.requirement,
        imports=case.imports,
        exact_type=case.exact_type,
    )
    (case_dir / "ArchonObjective.lean").write_text(
        attempt.objective_source,
        encoding="utf-8",
    )
    (case_dir / "USER_HINTS.md").write_text(attempt.user_hints, encoding="utf-8")

    forbidden_token = None
    verification: dict[str, Any] = {}
    proof_sha256 = None
    if attempt.body is not None:
        proof_sha256 = _sha256_text(attempt.body)
        match = FORBIDDEN_BODY_RE.search(attempt.body)
        forbidden_token = match.group(0) if match else None
        if forbidden_token is None:
            namespace, verify_source = _verification_source(case, attempt.body)
            verify_file = case_dir / "Verify.lean"
            replay_file = case_dir / "Replay.lean"
            verify_file.write_text(verify_source, encoding="utf-8")
            replay_file.write_text(verify_source, encoding="utf-8")
            kernel = run_command(
                ["lake", "env", "lean", str(verify_file)],
                cwd=root / "Lean",
                timeout_seconds=lean_timeout_seconds,
            )
            replay = run_command(
                ["lake", "env", "lean", str(replay_file)],
                cwd=root / "Lean",
                timeout_seconds=lean_timeout_seconds,
            )
            verification = {
                "namespace": namespace,
                "kernel_and_axiom": _command_evidence(kernel),
                "independent_replay": _command_evidence(replay),
                "source_sha256": _sha256_file(verify_file),
            }

    kernel_ok = bool(
        verification.get("kernel_and_axiom", {}).get("ok") is True
        and verification.get("independent_replay", {}).get("ok") is True
    )
    isolation_ok = (
        len(attempt.visible_lean_sources) == 1
        and all("ComplexityReduction" not in path or "ArchonWorker" in path
                for path in attempt.visible_lean_sources)
        and "recommended" not in attempt.user_hints.lower()
    )
    status = "VERIFIED" if kernel_ok and isolation_ok else (
        "FAILED_MODEL" if attempt.body is None else "FAILED_LEAN"
    )
    row: dict[str, Any] = {
        "schema_version": CASE_SCHEMA_VERSION,
        "ordinal": case.ordinal,
        "case_id": case.case_id,
        "kind": case.kind,
        "split": case.split,
        "statement_sha256": _sha256_text(case.statement),
        "public_input_file": str((case_dir / "archon-input.json").resolve()),
        "public_input_sha256": _sha256_file(case_dir / "archon-input.json"),
        "status": status,
        "kernel_verified": kernel_ok,
        "proof_sha256": proof_sha256,
        "forbidden_token": forbidden_token,
        "archon": {
            "called": True,
            "ok": attempt.ok,
            "error": attempt.error,
            "duration_seconds": attempt.duration_seconds,
            "usage": attempt.usage,
            "worker_index": attempt.worker_index,
            "call_index": attempt.call_index,
            "log_file": attempt.log_file,
            "exit_code": attempt.archon_exit_code,
        },
        "isolation": {
            "passed": isolation_ok,
            "visible_lean_sources": list(attempt.visible_lean_sources),
            "complexity_reduction_source_visible": False,
            "benchmark_recommendation_visible": False,
            "oracle_visible": False,
            "typed_dag_visible": False,
            "previous_diagnostics_visible": False,
            "web_and_search_tools_enabled": False,
            "compiled_dependencies": "Lean typechecking only",
        },
        "verification": {
            "public_goal_preflight": _command_evidence(public_goal_preflight),
            **verification,
        },
        "case_dir": str(case_dir.resolve()),
        "wall_duration_seconds": round(time.monotonic() - started, 3),
    }
    _write_json(case_dir / "result.json", row)
    return row


def _load_postrun_policy(
    root: Path,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    capability = _read_json(
        root / "Evaluation" / "np_hard_capability_oracle_v2.json"
    )
    exact = _read_json(root / "Evaluation" / "exact_reduction_edge_oracle_v1.json")
    boolean = _read_json(root / "Evaluation" / "boolean_csp_np_hard_oracle_v1.json")
    return (
        {
            str(row["case_id"]): row
            for row in capability.get("cases") or []
            if isinstance(row, dict) and isinstance(row.get("case_id"), str)
        },
        {
            str(row["case_id"]): row
            for row in exact.get("cases") or []
            if isinstance(row, dict) and isinstance(row.get("case_id"), str)
        },
        {
            str(row["case_id"]): row
            for row in boolean.get("cases") or []
            if isinstance(row, dict) and isinstance(row.get("case_id"), str)
        },
    )


def _apply_postrun_policy(
    rows: list[dict[str, Any]],
    *,
    capability_policy: Mapping[str, Any],
    exact_policy: Mapping[str, Any],
    boolean_policy: Mapping[str, Any],
) -> None:
    """Score after production without feeding any policy data to Archon."""

    for row in rows:
        body_path = Path(str(row["case_dir"])) / "ArchonObjective.lean"
        body_source = body_path.read_text(encoding="utf-8") if body_path.is_file() else ""
        if row["kind"] in {"capability", "frontier", "boolean_csp"}:
            is_boolean = row["kind"] == "boolean_csp"
            policy = (boolean_policy if is_boolean else capability_policy).get(
                row["case_id"]
            )
            scored = bool(
                isinstance(policy, Mapping)
                and (is_boolean or policy.get("scored") is True)
            )
            row["postrun_policy"] = {
                "scored": scored,
                "eligible": scored,
                "expected_public_status": (
                    policy.get("expected_public_status")
                    if isinstance(policy, Mapping)
                    else None
                ),
                "verified_at_budget": bool(row["kernel_verified"]) if scored else None,
                "opened_after_archon_completed": True,
            }
            _write_json(Path(str(row["case_dir"])) / "result.json", row)
            continue
        policy = exact_policy.get(row["case_id"])
        ready = bool(isinstance(policy, Mapping) and policy.get("status") == "ready")
        issues: list[str] = []
        if ready and not row["kernel_verified"]:
            issues.append("kernel_or_replay_failed")
        if ready and isinstance(policy, Mapping) and row["kernel_verified"]:
            existing_route = policy.get("existing_route")
            if isinstance(existing_route, str) and existing_route not in body_source:
                issues.append("expected_existing_route_not_observed")
            for prefix in policy.get("forbidden_route_imports") or []:
                if isinstance(prefix, str) and prefix in body_source:
                    issues.append("forbidden_route_reference")
            if policy.get("allow_composition") is False and OBVIOUS_COMPOSITION_RE.search(
                body_source
            ):
                issues.append("forbidden_composition")
        row["postrun_policy"] = {
            "scored": ready,
            "eligible": ready,
            "oracle_status": policy.get("status") if isinstance(policy, Mapping) else None,
            "verified_at_budget": (
                bool(row["kernel_verified"] and not issues) if ready else None
            ),
            "issues": sorted(set(issues)),
            "opened_after_archon_completed": True,
        }
        _write_json(Path(str(row["case_dir"])) / "result.json", row)


def _sum_usage(rows: Sequence[Mapping[str, Any]]) -> dict[str, Any]:
    totals: dict[str, int | float] = {}
    for row in rows:
        archon = row.get("archon")
        usage = archon.get("usage") if isinstance(archon, Mapping) else None
        if not isinstance(usage, Mapping):
            continue
        for key in (
            "prompt_tokens",
            "completion_tokens",
            "total_tokens",
            "archon_sessions",
        ):
            value = usage.get(key)
            if isinstance(value, int) and not isinstance(value, bool):
                totals[key] = int(totals.get(key, 0)) + value
        cost = usage.get("estimated_cost_usd")
        if isinstance(cost, (int, float)) and not isinstance(cost, bool):
            totals["estimated_cost_usd"] = round(
                float(totals.get("estimated_cost_usd", 0.0)) + float(cost), 9
            )
    return dict(totals)


def _lane_metrics(rows: Sequence[Mapping[str, Any]], lane: str) -> dict[str, Any]:
    selected = [row for row in rows if row.get("kind") == lane]
    eligible = [
        row
        for row in selected
        if isinstance(row.get("postrun_policy"), Mapping)
        and row["postrun_policy"].get("eligible") is True
    ]
    policy_verified = [
        row
        for row in eligible
        if row["postrun_policy"].get("verified_at_budget") is True
    ]
    return {
        "case_count": len(selected),
        "model_called_count": sum(
            isinstance(row.get("archon"), Mapping)
            and row["archon"].get("called") is True
            for row in selected
        ),
        "blocked_input_count": sum(row.get("status") == "BLOCKED_INPUT" for row in selected),
        "kernel_verified_count": sum(row.get("kernel_verified") is True for row in selected),
        "kernel_verified_rate": (
            sum(row.get("kernel_verified") is True for row in selected) / len(selected)
            if selected
            else None
        ),
        "eligible_count": len(eligible),
        "policy_verified_count": len(policy_verified),
        "policy_verified_rate": (
            len(policy_verified) / len(eligible) if eligible else None
        ),
        "usage": _sum_usage(selected),
    }


def _load_baseline_metrics(baseline_root: Path | None) -> dict[str, Any] | None:
    if baseline_root is None or not baseline_root.is_dir():
        return None
    result: dict[str, Any] = {"root": str(baseline_root.resolve())}
    for lane, filename in (
        ("capability", "report.json"),
        ("frontier", "report.json"),
        ("exact_edge", "score.json"),
    ):
        path = baseline_root / lane / filename
        if not path.is_file():
            continue
        report = _read_json(path)
        result[lane] = {
            "file": str(path.resolve()),
            "run_valid": report.get("run_valid"),
            "metrics": report.get("metrics"),
            "scorecard": report.get("scorecard"),
        }
    return result


def run_archon_blackbox_benchmark(
    *,
    root: Path,
    output_root: Path,
    archon_cli: Path,
    model_config: DeepSeekConfig,
    jobs: int = 4,
    max_iterations: int = 4,
    max_tool_rounds: int = 16,
    loop_timeout_seconds: int = 7200,
    lean_timeout_seconds: int = 600,
    lanes: Sequence[str] | None = None,
    selected_case_ids: Sequence[str] | None = None,
    baseline_root: Path | None = None,
    preflight: bool = True,
) -> dict[str, Any]:
    if not 1 <= jobs <= 4:
        raise ValueError("jobs must be in 1..4")
    root = root.resolve()
    output_root = output_root.resolve()
    if output_root.exists() and any(output_root.iterdir()):
        raise ValueError(f"output root must be new or empty: {output_root}")
    output_root.mkdir(parents=True, exist_ok=True)
    if not archon_cli.is_file():
        raise ValueError(f"Archon CLI does not exist: {archon_cli}")
    if not model_config.api_key:
        raise ValueError("real API run requires DEEPSEEK_API_KEY")

    cases = load_archon_benchmark_cases(
        root=root,
        lanes=lanes,
        selected_case_ids=selected_case_ids,
    )
    if not cases:
        raise ValueError("benchmark selection is empty")

    preflight_evidence: dict[str, Any] | None = None
    if preflight:
        command = run_command(
            ["lake", "build", "ComplexityReduction", "Benchmark"],
            cwd=root / "Lean",
            timeout_seconds=max(lean_timeout_seconds, 1800),
        )
        preflight_evidence = _command_evidence(command)
        _write_json(output_root / "preflight.json", preflight_evidence)
        if not command.ok:
            raise ValueError("Lean preflight failed; see preflight.json")

    client = ArchonModelClient(
        root=root,
        output_dir=output_root,
        archon_cli=archon_cli,
        max_iterations=max_iterations,
        loop_timeout_seconds=loop_timeout_seconds,
        report_config=model_config,
        worker_count=jobs,
        benchmark_tool_rounds=max_tool_rounds,
    )
    activity_lock = threading.Lock()
    active = 0
    peak = 0
    completed = 0
    started = time.monotonic()

    def execute(case: ArchonBenchmarkCase) -> dict[str, Any]:
        nonlocal active, peak, completed
        with activity_lock:
            active += 1
            peak = max(peak, active)
        try:
            return _run_case(
                root=root,
                output_root=output_root,
                case=case,
                client=client,
                lean_timeout_seconds=lean_timeout_seconds,
            )
        finally:
            with activity_lock:
                active -= 1
                completed += 1

    rows: list[dict[str, Any]] = []
    with ThreadPoolExecutor(max_workers=jobs) as pool:
        futures = {pool.submit(execute, case): case for case in cases}
        for future in as_completed(futures):
            rows.append(future.result())
    rows.sort(key=lambda row: int(row["ordinal"]))

    # This is the first point at which scorer-only material is opened.
    capability_policy, exact_policy, boolean_policy = _load_postrun_policy(root)
    _apply_postrun_policy(
        rows,
        capability_policy=capability_policy,
        exact_policy=exact_policy,
        boolean_policy=boolean_policy,
    )

    metrics = {
        lane: _lane_metrics(rows, lane)
        for lane in ("capability", "frontier", "exact_edge", "boolean_csp")
        if any(row["kind"] == lane for row in rows)
    }
    report: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "benchmark_id": REGISTRY_BENCHMARK_ID,
        "agent": "compare/Archon",
        "run_valid": all(row["isolation"]["passed"] is True for row in rows),
        "real_api_called": any(
            isinstance(row["archon"].get("usage"), Mapping)
            and int(row["archon"]["usage"].get("archon_sessions") or 0) > 0
            for row in rows
        ),
        "model_configuration": model_config.to_public_dict(),
        "input_contract": {
            "visible_to_archon": [
                "public problem statement",
                "formal Lean goal",
                "proof-kind requirement",
            ],
            "hidden_from_archon": [
                "ComplexityReduction source files",
                "benchmark recommended proof body",
                "oracle and gold material",
                "typed DAG and route selection",
                "dependency proof bodies",
                "previous Lean diagnostics",
                "previous cases and worker state",
            ],
            "compiled_dependencies": "available only to Lean typechecking",
        },
        "parallelism": {
            "configured_jobs": jobs,
            "observed_peak_active_cases": peak,
            "completed_cases": completed,
            "final_active_cases": active,
        },
        "archon": {
            "cli": str(archon_cli.resolve()),
            "max_iterations": max_iterations,
            "max_tool_rounds_per_role": max_tool_rounds,
            "loop_timeout_seconds": loop_timeout_seconds,
        },
        "preflight": preflight_evidence,
        "metrics": metrics,
        "usage": _sum_usage(rows),
        "baseline": _load_baseline_metrics(
            baseline_root.resolve() if baseline_root is not None else None
        ),
        "cases": rows,
        "output_root": str(output_root),
        "wall_duration_seconds": round(time.monotonic() - started, 3),
    }
    _write_json(output_root / "report.json", report)
    return report


__all__ = [
    "ArchonBenchmarkCase",
    "load_archon_benchmark_cases",
    "run_archon_blackbox_benchmark",
]
