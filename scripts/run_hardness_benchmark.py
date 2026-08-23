#!/usr/bin/env python3
"""The repository's only benchmark runner: execute and score all 88 cases.

Reads BENCHMARK_REGISTRY.json and executes exactly the frozen lanes:
  - capability: 32 C0 target-hardness cases (dev/validation/heldout)
  - frontier:   2 F0 unscored cases (frontier split)
  - exact_edge: 24 certified-reduction edge cases (dev/heldout/validation)
  - boolean_csp: 30 NP-hard Boolean-CSP cases (dev/validation/heldout)

The scorer-only oracles are opened only after every production case finishes.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import replace
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from agent.hardness.np_hard_capability import (  # noqa: E402
    NPHardCapabilityError,
    run_np_hard_capability_benchmark,
    score_np_hard_capability_benchmark,
)
from agent.hardness.boolean_csp_np_hard_benchmark import (  # noqa: E402
    BooleanCSPBenchmarkError,
    load_suite as load_boolean_csp_suite,
    run_suite as run_boolean_csp_suite,
    score_run as score_boolean_csp_run,
)
from agent.hardness.np_hard_exact_edge import (  # noqa: E402
    ExactEdgeContractError,
    combine_exact_edge_suites,
    load_exact_edge_manifest,
    load_exact_edge_oracle,
    run_exact_reduction_edge_benchmark,
    score_exact_reduction_edge_run,
    write_exact_edge_report,
)
from agent.hardness.np_hard_production import (  # noqa: E402
    load_np_hard_production_model_config,
)
from agent.hardness.models import sha256_id  # noqa: E402

CAPABILITY_MANIFEST = ROOT / "Benchmark" / "Hardness" / "CAPABILITY_MANIFEST_V2.json"
EXACT_EDGE_MANIFEST = (
    ROOT / "Benchmark" / "Hardness" / "EXACT_REDUCTION_EDGE_MANIFEST.json"
)
BOOLEAN_CSP_SUITE = (
    ROOT / "Benchmark" / "Hardness" / "Suites" / "boolean_csp_np_hard_public_v1.json"
)
BOOLEAN_CSP_ORACLE = ROOT / "Evaluation" / "boolean_csp_np_hard_oracle_v1.json"
EDGE_SPLITS = ("dev", "heldout", "validation")
LANES = ("capability", "frontier", "exact_edge", "boolean_csp")


def _read_json(path: Path) -> dict[str, Any]:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def _registry_path(arguments: argparse.Namespace) -> Path:
    if arguments.registry is not None:
        return arguments.registry.resolve()
    return ROOT / "Benchmark" / "Hardness" / "BENCHMARK_REGISTRY.json"


def _load_registry(arguments: argparse.Namespace) -> dict[str, Any]:
    path = _registry_path(arguments)
    registry = _read_json(path)
    if registry.get("schema_version") != "hardness_benchmark_registry_v1":
        raise ValueError(f"unsupported registry schema: {registry.get('schema_version')!r}")
    if registry.get("benchmark_id") != "np-hard-real-reduction-v1":
        raise ValueError(f"unexpected registry benchmark_id: {registry.get('benchmark_id')!r}")
    return registry


def _lane_case_ids(registry: dict[str, Any], lane: str) -> tuple[str, ...]:
    return tuple(
        case["case_id"]
        for case in registry["cases"]
        if case["kind"] == lane
    )


def _validate_registry(registry: dict[str, Any]) -> dict[str, Any]:
    bundle = _load_capability_bundle()
    suite_ids = {
        case.case_id: case.split
        for split in ("dev", "validation", "heldout", "frontier")
        for case in bundle.suites[split].cases
    }
    capability_ids = _lane_case_ids(registry, "capability")
    frontier_ids = _lane_case_ids(registry, "frontier")
    source_capability_ids = {
        case_id
        for case_id, split in suite_ids.items()
        if split in {"dev", "validation", "heldout"}
    }
    source_frontier_ids = {
        case_id
        for case_id, split in suite_ids.items()
        if split == "frontier"
    }
    if set(capability_ids) != source_capability_ids:
        raise ValueError("registry capability set drifted from CAPABILITY_MANIFEST_V2.json")
    for case_id in frontier_ids:
        if case_id not in source_frontier_ids:
            raise ValueError(f"frontier case {case_id!r} is outside the frontier split")
    if set(frontier_ids) != source_frontier_ids:
        raise ValueError("registry frontier set drifted from CAPABILITY_MANIFEST_V2.json")

    edge_manifest = load_exact_edge_manifest(EXACT_EDGE_MANIFEST.resolve())
    edge_ids = _lane_case_ids(registry, "exact_edge")
    source_edge_ids = {
        case.case_id
        for name in EDGE_SPLITS
        for case in edge_manifest.suites[name].cases
    }
    if set(edge_ids) != source_edge_ids:
        raise ValueError("registry exact_edge set drifted from EXACT_REDUCTION_EDGE_MANIFEST.json")
    boolean_suite = load_boolean_csp_suite(BOOLEAN_CSP_SUITE)
    boolean_ids = _lane_case_ids(registry, "boolean_csp")
    source_boolean_ids = {case.case_id for case in boolean_suite.cases}
    if set(boolean_ids) != source_boolean_ids:
        raise ValueError("registry Boolean-CSP set drifted from its public suite")
    all_ids = [str(case.get("case_id")) for case in registry.get("cases", ())]
    if len(all_ids) != 88 or len(set(all_ids)) != 88:
        raise ValueError("benchmark registry must contain exactly 88 unique cases")
    return {
        "benchmark_id": registry["benchmark_id"],
        "capability_case_count": len(capability_ids),
        "frontier_case_count": len(frontier_ids),
        "exact_edge_case_count": len(edge_ids),
        "boolean_csp_case_count": len(boolean_ids),
        "total_case_count": len(all_ids),
        "capability_manifest": str(CAPABILITY_MANIFEST),
        "exact_edge_manifest": str(EXACT_EDGE_MANIFEST),
        "boolean_csp_suite": str(BOOLEAN_CSP_SUITE),
    }


def _load_capability_bundle():
    from agent.hardness.np_hard_capability import load_capability_bundle

    return load_capability_bundle(CAPABILITY_MANIFEST.resolve(), root=ROOT, verify_oracle=False)


def _model_configuration(arguments: argparse.Namespace) -> Any:
    return load_np_hard_production_model_config(
        env_file=arguments.env_file,
        model=arguments.model,
        timeout_seconds=arguments.model_timeout,
        max_tokens=arguments.model_max_tokens,
        max_retries=arguments.model_max_retries,
        reasoning_effort=arguments.reasoning_effort,
    )


def _model_client(arguments: argparse.Namespace, deepseek: Any, *, subdir: str) -> Any | None:
    if arguments.agent != "archon":
        return None
    from agent.hardness.archon_runner import ArchonModelClient  # noqa: E402

    return ArchonModelClient(
        root=ROOT,
        output_dir=(arguments.output_root / subdir).resolve(),
        archon_cli=arguments.archon_cli,
        max_iterations=arguments.archon_iterations,
        report_config=deepseek,
        worker_count=arguments.jobs,
    )


def _run_capability_lane(
    *,
    registry: dict[str, Any],
    arguments: argparse.Namespace,
    deepseek: Any,
    lane: str,
) -> dict[str, Any]:
    ids = _lane_case_ids(registry, lane)
    requested_ids = set(arguments.capability_case_id or ())
    unknown_ids = sorted(requested_ids - set(ids))
    if unknown_ids:
        raise ValueError(f"case IDs are outside the {lane} lane: {unknown_ids!r}")
    if requested_ids:
        ids = tuple(case_id for case_id in ids if case_id in requested_ids)
    if lane == "frontier":
        splits = ("frontier",)
        output_root = (arguments.output_root / lane).resolve()
        report = run_np_hard_capability_benchmark(
            root=ROOT,
            manifest_path=CAPABILITY_MANIFEST,
            output_root=output_root,
            report_path=output_root / "report.json",
            deepseek=deepseek,
            selected_splits=splits,
            selected_case_ids=ids,
            jobs=arguments.jobs,
            model_client=_model_client(arguments, deepseek, subdir=lane),
        )
        return {
            "run_valid": bool(report.get("run_valid")),
            "run_id": report.get("run_id"),
            "report": str(output_root / "report.json"),
        }
    output_root = (arguments.output_root / lane).resolve()
    run_report = output_root / "report.json"
    report = run_np_hard_capability_benchmark(
        root=ROOT,
        manifest_path=CAPABILITY_MANIFEST,
        output_root=output_root,
        report_path=run_report,
        deepseek=deepseek,
        selected_splits=("dev", "validation", "heldout"),
        selected_case_ids=ids,
        jobs=arguments.jobs,
        model_client=_model_client(arguments, deepseek, subdir=lane),
    )
    return {
        "run_valid": bool(report.get("run_valid")),
        "run_id": report.get("run_id"),
        "capability_report": str(run_report),
    }


def _score_capability_lane(*, arguments: argparse.Namespace) -> dict[str, Any]:
    output_root = (arguments.output_root / "capability").resolve()
    score_report = output_root / "score.json"
    score = score_np_hard_capability_benchmark(
        root=ROOT,
        manifest_path=CAPABILITY_MANIFEST,
        run_report_path=output_root / "report.json",
        score_report_path=score_report,
    )
    return {
        "score_valid": bool(score.get("score_valid")),
        "score_report": str(score_report),
        "metrics": score.get("metrics"),
    }


def _run_edge_lane(
    *,
    registry: dict[str, Any],
    arguments: argparse.Namespace,
    deepseek: Any,
) -> tuple[dict[str, Any], dict[str, Any] | None]:
    manifest = load_exact_edge_manifest(EXACT_EDGE_MANIFEST.resolve())
    suites = tuple(manifest.suites[name] for name in EDGE_SPLITS)
    suite = (
        suites[0]
        if len(suites) == 1
        else combine_exact_edge_suites(suites)
    )
    requested_ids = set(arguments.exact_edge_case_id or ())
    available_ids = {case.case_id for case in suite.cases}
    unknown_ids = sorted(requested_ids - available_ids)
    if unknown_ids:
        raise ValueError(f"unknown exact-edge case IDs: {unknown_ids!r}")
    selected_splits = set(arguments.exact_edge_split or ())
    if selected_splits or requested_ids:
        selected_cases = tuple(
            case
            for case in suite.cases
            if case.split in selected_splits or case.case_id in requested_ids
        )
        if not selected_cases:
            raise ValueError("exact-edge selection is empty")
        suite = replace(
            suite,
            split="selected",
            cases=selected_cases,
            sha256=sha256_id(
                {
                    "parent_suite_sha256": suite.sha256,
                    "case_ids": [case.case_id for case in selected_cases],
                }
            ),
        )
    output_root = (arguments.output_root / "exact_edge").resolve()
    report = run_exact_reduction_edge_benchmark(
        root=ROOT,
        suite=suite,
        budget_profiles=manifest.budget_profiles,
        output_root=output_root,
        deepseek=deepseek,
        model_client=_model_client(arguments, deepseek, subdir="exact_edge"),
        jobs=arguments.jobs,
        isolate_workspace=manifest.isolate_workspace,
        runtime_prebuilt=manifest.runtime_prebuilt,
        manifest_sha256=manifest.sha256,
        expected_oracle_sha256=manifest.oracle_sha256,
        resume=arguments.resume,
    )
    write_exact_edge_report(output_root / "run_report.json", report)
    score = None
    if not arguments.no_score:
        oracle = load_exact_edge_oracle(
            ROOT / "Evaluation" / "exact_reduction_edge_oracle_v1.json"
        )
        score = score_exact_reduction_edge_run(
            manifest=manifest,
            suite=suite,
            oracle=oracle,
            run_report=report,
        )
        write_exact_edge_report(output_root / "score.json", score)
    payload = {
        "run_valid": bool(report.get("run_valid")),
        "run_id": report.get("run_id"),
        "run_report": str(output_root / "run_report.json"),
    }
    if score is not None:
        payload["score_valid"] = bool(score.get("run_valid"))
        payload["score_report"] = str(output_root / "score.json")
        payload["scorecard"] = score.get("scorecard")
    return payload, score


def _run_boolean_csp_lane(
    *,
    registry: dict[str, Any],
    arguments: argparse.Namespace,
    deepseek: Any,
) -> dict[str, Any]:
    output_root = (arguments.output_root / "boolean_csp").resolve()
    registered_ids = _lane_case_ids(registry, "boolean_csp")
    requested_ids = tuple(arguments.boolean_csp_case_id or ())
    unknown_ids = sorted(set(requested_ids) - set(registered_ids))
    if unknown_ids:
        raise ValueError(f"unknown Boolean-CSP case IDs: {unknown_ids!r}")
    report = run_boolean_csp_suite(
        root=ROOT,
        suite_path=BOOLEAN_CSP_SUITE,
        output_root=output_root,
        authoring=arguments.authoring,
        case_ids=requested_ids,
        splits=tuple(arguments.boolean_csp_split or ()),
        jobs=arguments.jobs,
        lean_timeout=arguments.lean_timeout,
        env_file=arguments.env_file,
        model=deepseek.model,
        model_timeout=deepseek.timeout_seconds,
        model_max_tokens=deepseek.max_tokens,
        model_max_retries=deepseek.max_retries,
        reasoning_effort=deepseek.reasoning_effort,
        authoring_attempts=arguments.authoring_attempts,
        model_call_budget=arguments.model_call_budget,
        profile=arguments.reduction_profile,
    )
    run_report = output_root / "run_report.json"
    payload: dict[str, Any] = {
        "run_valid": report.get("completed_case_count")
        == report.get("started_case_count"),
        "run_report": str(run_report),
        "selected_case_count": report.get("started_case_count"),
    }
    if not arguments.no_score:
        score_path = output_root / "score.json"
        score = score_boolean_csp_run(
            suite_path=BOOLEAN_CSP_SUITE,
            oracle_path=BOOLEAN_CSP_ORACLE,
            run_report_path=run_report,
            score_report_path=score_path,
        )
        payload.update(
            score_report=str(score_path),
            passed_case_count=score.get("passed_case_count"),
            completion_rate=score.get("completion_rate"),
        )
    return payload


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Unified benchmark entry for real complexity-reduction cases"
    )
    parser.add_argument(
        "--registry",
        type=Path,
        default=None,
        help="defaults to Benchmark/Hardness/BENCHMARK_REGISTRY.json",
    )
    parser.add_argument(
        "--output-root",
        type=Path,
        default=ROOT / ".reduction-agent" / "benchmark",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=4,
        help="capability/edge case jobs; must be in 1..4",
    )
    parser.add_argument(
        "--lane",
        action="append",
        choices=LANES,
        default=None,
        help="restrict to one lane (repeatable); defaults to all four",
    )
    parser.add_argument(
        "--exact-edge-split",
        action="append",
        choices=EDGE_SPLITS,
        default=None,
        help="restrict exact_edge to selected public splits (repeatable)",
    )
    parser.add_argument(
        "--capability-case-id",
        action="append",
        default=None,
        help="run selected capability/frontier cases (repeatable)",
    )
    parser.add_argument(
        "--exact-edge-case-id",
        action="append",
        default=None,
        help="include an exact-edge case explicitly; combines by union with split filters",
    )
    parser.add_argument(
        "--resume",
        action="store_true",
        help="resume an exact-edge output in place after hash-bound checkpoint replay",
    )
    parser.add_argument(
        "--boolean-csp-split",
        action="append",
        choices=("dev", "validation", "heldout"),
        default=None,
        help="restrict Boolean-CSP to selected public splits (repeatable)",
    )
    parser.add_argument(
        "--boolean-csp-case-id",
        action="append",
        default=None,
        help="run selected Boolean-CSP cases (repeatable)",
    )
    parser.add_argument(
        "--authoring",
        choices=("disabled", "model-auto", "model-required"),
        default="model-auto",
        help="Boolean-CSP authoring policy",
    )
    parser.add_argument(
        "--reduction-profile",
        choices=("research", "strict-release", "benchmark"),
        default="benchmark",
        help="verification profile for the NP-hard-first Boolean-CSP core",
    )
    parser.add_argument("--authoring-attempts", type=int, default=4)
    parser.add_argument("--model-call-budget", type=int, default=None)
    parser.add_argument("--lean-timeout", type=int, default=600)
    parser.add_argument("--env-file", type=Path, default=ROOT / ".env")
    parser.add_argument("--model", default=None)
    parser.add_argument("--model-timeout", type=int, default=None)
    parser.add_argument("--model-max-tokens", type=int, default=None)
    parser.add_argument("--model-max-retries", type=int, default=None)
    parser.add_argument("--reasoning-effort", default=None)
    parser.add_argument(
        "--agent",
        choices=("deepseek", "archon", "oneshot-llm"),
        default="deepseek",
        help="model provider for node/authoring calls: direct DeepSeek HTTP "
        "chat inside the production agent (default), an Archon "
        "autoformalization prove-loop, or one direct LLM request per whole case",
    )
    parser.add_argument(
        "--archon-cli",
        type=Path,
        default=None,
        help="Archon CLI executable; defaults to 'archon' on PATH. The "
        "bundled venv is compare/Archon/.venv/bin/archon",
    )
    parser.add_argument(
        "--archon-iterations",
        type=int,
        default=1,
        help="whole-case Archon iterations when --agent archon (default 1)",
    )
    parser.add_argument(
        "--archon-tool-rounds",
        type=int,
        default=16,
        help="maximum DeepSeek tool rounds per Archon role in black-box mode",
    )
    parser.add_argument(
        "--archon-report",
        type=Path,
        default=(
            ROOT
            / ".reduction-agent"
            / "benchmark-archon-blackbox-jobs4-20260810-v2"
            / "report.json"
        ),
        help="completed Archon report used to audit identical public inputs "
        "for --agent oneshot-llm",
    )
    parser.add_argument(
        "--no-score",
        action="store_true",
        help="development-only: run without opening the scorer-only oracles",
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="validate the registry against frozen manifests and list cases",
    )
    return parser


def main() -> int:
    arguments = build_parser().parse_args()
    if arguments.jobs <= 0 or arguments.jobs > 4:
        return _fail("benchmark_jobs_invalid", "jobs must be in 1..4")
    registry: dict[str, Any] | None = None
    try:
        registry = _load_registry(arguments)
        validated = _validate_registry(registry)
        if arguments.list:
            print(
                json.dumps(
                    {
                        "registry": validated["benchmark_id"],
                        "case_count": {
                            "capability": validated["capability_case_count"],
                            "frontier": validated["frontier_case_count"],
                            "exact_edge": validated["exact_edge_case_count"],
                            "boolean_csp": validated["boolean_csp_case_count"],
                            "total": validated["total_case_count"],
                        },
                        "lanes": {
                            lane: list(_lane_case_ids(registry, lane))
                            for lane in LANES
                        },
                    },
                    ensure_ascii=False,
                    indent=2,
                    sort_keys=True,
                )
            )
            return 0
        arguments.output_root.mkdir(parents=True, exist_ok=True)
        deepseek = _model_configuration(arguments)
        lanes = arguments.lane or LANES
        if arguments.agent == "archon":
            from agent.hardness.archon_blackbox_benchmark import (
                run_archon_blackbox_benchmark,
            )

            archon_cli = arguments.archon_cli or (
                ROOT / "compare" / "Archon" / ".venv" / "bin" / "archon"
            )
            report = run_archon_blackbox_benchmark(
                root=ROOT,
                output_root=arguments.output_root,
                archon_cli=archon_cli,
                model_config=deepseek,
                jobs=arguments.jobs,
                max_iterations=arguments.archon_iterations,
                max_tool_rounds=arguments.archon_tool_rounds,
                lanes=lanes,
                baseline_root=(
                    ROOT / ".reduction-agent" / "benchmark-real-20260810-092600"
                ),
            )
            print(
                json.dumps(
                    {
                        "benchmark_id": validated["benchmark_id"],
                        "agent": "compare/Archon",
                        "output_root": report["output_root"],
                        "run_valid": report["run_valid"],
                        "real_api_called": report["real_api_called"],
                        "parallelism": report["parallelism"],
                        "metrics": report["metrics"],
                        "usage": report["usage"],
                    },
                    ensure_ascii=False,
                    indent=2,
                    sort_keys=True,
                )
            )
            return 0
        if arguments.agent == "oneshot-llm":
            from compare.OneShotLLM.benchmark import run_oneshot_llm_benchmark

            report = run_oneshot_llm_benchmark(
                root=ROOT,
                output_root=arguments.output_root,
                model_config=deepseek,
                jobs=arguments.jobs,
                lanes=lanes,
                baseline_root=(
                    ROOT / ".reduction-agent" / "benchmark-real-20260810-092600"
                ),
                archon_report_path=arguments.archon_report,
            )
            print(
                json.dumps(
                    {
                        "benchmark_id": validated["benchmark_id"],
                        "agent": "compare/OneShotLLM",
                        "output_root": report["output_root"],
                        "run_valid": report["run_valid"],
                        "real_api_called": report["real_api_called"],
                        "parallelism": report["parallelism"],
                        "metrics": report["metrics"],
                        "usage": report["usage"],
                        "archon_comparison": report["archon_comparison"],
                    },
                    ensure_ascii=False,
                    indent=2,
                    sort_keys=True,
                )
            )
            return 0
        results: dict[str, Any] = {}
        for lane in lanes:
            if lane in ("capability", "frontier"):
                results[lane] = _run_capability_lane(
                    registry=registry, arguments=arguments, deepseek=deepseek, lane=lane
                )
            elif lane == "exact_edge":
                results["exact_edge"], _ = _run_edge_lane(
                    registry=registry, arguments=arguments, deepseek=deepseek
                )
            else:
                results["boolean_csp"] = _run_boolean_csp_lane(
                    registry=registry, arguments=arguments, deepseek=deepseek
                )
        if not arguments.no_score and "capability" in lanes:
            results["capability"]["score"] = _score_capability_lane(arguments=arguments)
        print(
            json.dumps(
                {
                    "benchmark_id": validated["benchmark_id"],
                    "output_root": str(arguments.output_root.resolve()),
                    "lanes": results,
                },
                ensure_ascii=False,
                indent=2,
                sort_keys=True,
            )
        )
        return 0
    except (
        NPHardCapabilityError,
        BooleanCSPBenchmarkError,
        ExactEdgeContractError,
        OSError,
        UnicodeError,
        ValueError,
        json.JSONDecodeError,
    ) as error:
        return _fail(
            getattr(error, "code", "benchmark_runner_failed"),
            str(error),
            registry=registry,
        )


def _fail(code: str, message: str, *, registry: dict[str, Any] | None = None) -> int:
    payload: dict[str, Any] = {"run_valid": False, "failure_code": code, "error": message}
    if registry is not None:
        payload["benchmark_id"] = registry.get("benchmark_id")
    print(json.dumps(payload, ensure_ascii=False))
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
