from __future__ import annotations

import json
from pathlib import Path

import pytest

from agent.hardness.model_client import DeepSeekConfig
from agent.hardness.np_hard_production import (
    FORMAL_BASE_URL,
    FORMAL_MAX_RETRIES,
    FORMAL_MAX_TOKENS,
    FORMAL_MODEL,
    FORMAL_REASONING_EFFORT,
    FORMAL_TIMEOUT_SECONDS,
)
from agent.hardness.np_hard_unified_benchmark import (
    UnifiedBenchmarkError,
    discover_suite_case_inventory,
    load_public_r1_coverage_suite,
    load_unified_registry,
    load_unified_taxonomy,
    registry_aliases,
    require_formal_profile,
    run_unified_benchmark,
    select_unified_cases,
)


ROOT = Path(__file__).resolve().parents[1]
HARDNESS = ROOT / "Benchmark/Hardness"
REGISTRY = ROOT / "Gate/NP_HARD_UNIFIED_BENCHMARK_REGISTRY.json"
TAXONOMY = ROOT / "Gate/BENCHMARK_TAXONOMY.json"
PUBLIC_R1_SUITE = ROOT / "Gate/Suites/np_hard_public_r1_coverage_v1.json"


def _formal_config(*, api_key: str | None = "test-key") -> DeepSeekConfig:
    return DeepSeekConfig(
        api_key=api_key,
        base_url=FORMAL_BASE_URL,
        model=FORMAL_MODEL,
        timeout_seconds=FORMAL_TIMEOUT_SECONDS,
        temperature=0.0,
        max_tokens=FORMAL_MAX_TOKENS,
        max_retries=FORMAL_MAX_RETRIES,
        reasoning_effort=FORMAL_REASONING_EFFORT,
    )


def test_registry_is_one_semantically_deduplicated_compatibility_source() -> None:
    registry = load_unified_registry(REGISTRY, root=ROOT)
    main_aliases = registry_aliases(registry.cases, view="legacy-regression-45")
    release_aliases = registry_aliases(
        registry.cases, view="legacy-release-reliability-12"
    )
    alias_logical_cases = [case for case in registry.cases if case.compatibility_aliases]

    assert len(main_aliases) == len(set(main_aliases)) == 45
    assert len(release_aliases) == len(set(release_aliases)) == 12
    assert len(alias_logical_cases) == 49 < 57
    assert len(registry.cases) == 59
    assert all(case.capability_weight == 0 for case in registry.cases)


def test_obvious_legacy_release_motifs_share_one_production_backend() -> None:
    registry = load_unified_registry(REGISTRY, root=ROOT)
    by_alias = {
        (alias.view, alias.case_id): case
        for case in registry.cases
        for alias in case.compatibility_aliases
    }
    merged = (
        ("three-sat-refl", "nphg-existing-canonical-three-sat"),
        ("three-sat-explicit-suffix", "nphg-existing-clique"),
        ("tagged-three-sat-normalization", "nphg-existing-membership-free"),
        ("model-semantic-proof-authoring", "nphg-author-sat-proof-only"),
        ("program-indexed-reduction-authoring", "nphg-author-set-system-composition"),
        ("completeness-wrong-direction", "nphg-negative-reverse-only"),
        ("wrong-membership-endpoint", "nphg-negative-endpoint-mutation"),
    )
    for main_id, release_id in merged:
        main = by_alias[("legacy-regression-45", main_id)]
        release = by_alias[("legacy-release-reliability-12", release_id)]
        assert main is release
        assert main.execution_backend == "release_real_round"
        assert main.selector == "production"

    candidate_absent = by_alias[
        ("legacy-regression-45", "program-indexed-candidate-absent")
    ]
    assert candidate_absent is by_alias[
        ("legacy-regression-45", "program-indexed-reduction-authoring")
    ]


def test_selectors_are_disjoint_and_all_executes_each_logical_case_once() -> None:
    registry = load_unified_registry(REGISTRY, root=ROOT)
    contract = select_unified_cases(registry, selector="contract")
    production = select_unified_cases(registry, selector="production")
    all_cases = select_unified_cases(registry, selector="all")

    assert len(contract) == 30
    assert len(production) == 29
    assert len(all_cases) == 59
    assert {case.logical_case_id for case in contract}.isdisjoint(
        {case.logical_case_id for case in production}
    )
    assert len({case.logical_case_id for case in all_cases}) == len(all_cases)
    assert sum(case.execution_backend == "release_real_round" for case in all_cases) == 12
    assert sum(case.execution_backend == "public_existing_route" for case in all_cases) == 10


def test_public_r1_suite_is_answer_free_and_registry_owned() -> None:
    cases = load_public_r1_coverage_suite(PUBLIC_R1_SUITE)
    registry = load_unified_registry(REGISTRY, root=ROOT)
    registered = {
        case.source_case_id: case
        for case in registry.cases
        if case.execution_backend == "public_existing_route"
    }

    assert len(cases) == len(registered) == 10
    assert len({case["problem"] for case in cases}) == 10
    assert all(set(case) == {"case_id", "module", "problem", "family"} for case in cases)
    assert all(case["problem"].startswith("ComplexityReduction.") for case in cases)
    assert all(registered[case["case_id"]].public_identity == case["problem"] for case in cases)
    assert all(not registered[case["case_id"]].fixture for case in cases)
    assert all(registered[case["case_id"]].model_requirement == "forbidden" for case in cases)


def test_taxonomy_exactly_covers_every_checked_in_suite_and_case() -> None:
    registry = load_unified_registry(REGISTRY, root=ROOT)
    taxonomy = load_unified_taxonomy(TAXONOMY, registry=registry, root=ROOT)
    expected = discover_suite_case_inventory(ROOT)
    actual = {
        suite["suite_file"]: tuple(case["case_id"] for case in suite["cases"])
        for suite in taxonomy["suite_inventory"]
    }

    assert actual == expected
    assert len(actual) == len(
        list((HARDNESS / "Suites").glob("*.json")) + list((ROOT / "Gate" / "Suites").glob("*.json"))
    )
    assert sum(len(case_ids) for case_ids in actual.values()) == sum(
        len(case_ids) for case_ids in expected.values()
    )
    assert all(
        not case["capability_scored"] or (
            case["tier"] == "C0"
            and case["public_problem"]
            and not case["fixture"]
            and case["capability_weight"] == 1
        )
        for suite in taxonomy["suite_inventory"]
        for case in suite["cases"]
    )


def test_taxonomy_freezes_32_c0_2_f0_10_r1_unique_public_identities() -> None:
    registry = load_unified_registry(REGISTRY, root=ROOT)
    taxonomy = load_unified_taxonomy(TAXONOMY, registry=registry, root=ROOT)
    ownership = taxonomy["public_identity_ownership"]

    assert len(ownership) == 44
    assert len({row["case_id"] for row in ownership}) == 44
    assert len({row["public_identity"] for row in ownership}) == 44
    assert sum(row["tier"] == "C0" for row in ownership) == 32
    assert sum(row["tier"] == "F0" for row in ownership) == 2
    assert sum(row["tier"] == "R1" for row in ownership) == 10


def test_public_suite_rejects_oracle_fields(tmp_path: Path) -> None:
    value = json.loads(PUBLIC_R1_SUITE.read_text(encoding="utf-8"))
    value["cases"][0]["expected_status"] = "VERIFIED"
    mutated = tmp_path / "mutated-public-r1.json"
    mutated.write_text(json.dumps(value), encoding="utf-8")

    with pytest.raises(UnifiedBenchmarkError) as raised:
        load_public_r1_coverage_suite(mutated)
    assert raised.value.code == "oracle_field_in_public_suite"


def test_formal_profile_and_required_api_key_fail_closed() -> None:
    require_formal_profile(_formal_config(api_key=None), require_api_key=False)
    with pytest.raises(UnifiedBenchmarkError) as missing_key:
        require_formal_profile(_formal_config(api_key=None), require_api_key=True)
    assert missing_key.value.code == "model_provider_unavailable"

    drifted = DeepSeekConfig(
        api_key="test-key",
        base_url=FORMAL_BASE_URL,
        model="deepseek-chat",
        timeout_seconds=FORMAL_TIMEOUT_SECONDS,
        temperature=0.0,
        max_tokens=FORMAL_MAX_TOKENS,
        max_retries=FORMAL_MAX_RETRIES,
        reasoning_effort=FORMAL_REASONING_EFFORT,
    )
    with pytest.raises(UnifiedBenchmarkError) as mismatch:
        require_formal_profile(drifted, require_api_key=True)
    assert mismatch.value.code == "qualification_model_profile_mismatch"


def test_unified_all_report_counts_one_execution_per_logical_case(tmp_path: Path) -> None:
    calls = {"legacy": 0, "release": 0, "public": 0}

    def legacy_executor(**kwargs):
        calls["legacy"] += 1
        return {
            "jobs": kwargs["jobs"],
            "results": [
                {
                    "id": case_id,
                    "actual_status": "VERIFIED",
                    "actual_failure_code": None,
                    "passed": True,
                    "model_call_count": 0,
                    "report": f"legacy/{case_id}/report.json",
                }
                for case_id in kwargs["case_ids"]
            ],
        }

    def release_executor(**kwargs):
        calls["release"] += 1
        suite = json.loads(kwargs["suite_path"].read_text(encoding="utf-8"))
        return {
            "stage": "fake-release-round",
            "parallel_execution": {
                "configured_jobs": kwargs["jobs"],
                "maximum_concurrent_case_tasks": kwargs["jobs"],
                "final_active_case_tasks": 0,
            },
            "cases": [
                {
                    "case_id": case["id"],
                    "status": "VERIFIED",
                    "failure_code": None,
                    "matched": True,
                    "model_calls": 0,
                }
                for case in suite["cases"]
            ],
        }

    def public_executor(**kwargs):
        calls["public"] += 1
        suite = json.loads(kwargs["suite_path"].read_text(encoding="utf-8"))
        return {
            "stage": "fake-public-r1",
            "parallel_execution": {
                "configured_jobs": kwargs["jobs"],
                "maximum_concurrent_case_tasks": kwargs["jobs"],
                "final_active_case_tasks": 0,
            },
            "cases": [
                {
                    "case_id": case["case_id"],
                    "status": "VERIFIED",
                    "failure_code": None,
                    "matched": True,
                    "model_calls": 0,
                }
                for case in suite["cases"]
            ],
        }

    output_root = tmp_path / "unified"
    report = run_unified_benchmark(
        root=ROOT,
        registry_path=REGISTRY,
        taxonomy_path=TAXONOMY,
        selector="all",
        output_root=output_root,
        report_path=output_root / "report.json",
        env_file=ROOT / ".env",
        deepseek=_formal_config(),
        jobs=4,
        legacy_executor=legacy_executor,
        production_executor=release_executor,
        public_coverage_executor=public_executor,
    )

    assert calls == {"legacy": 1, "release": 1, "public": 1}
    assert report["passed"] is True
    assert report["counts"]["logical_cases"] == 59
    assert report["counts"]["case_executions"] == 59
    assert report["counts"]["case_executions"] <= report["counts"]["logical_cases"]
    assert report["counts"]["model_calls"] == 0
    assert report["counts"]["capability_weight"] == 0
    assert report["compatibility_views"] == {
        "legacy-regression-45": 45,
        "legacy-release-reliability-12": 12,
    }
    legacy_inventory = report["regression_asset_inventory"]["legacy-regression-45"]
    assert legacy_inventory["fixture_case_count"] == 45
    assert legacy_inventory["public_capability_case_count"] == 0
    assert legacy_inventory["ir_feasibility_case_count"] == 12
    assert legacy_inventory["negative_lane_case_count"] == 15
    assert legacy_inventory["model_synthesis_case_count"] == 1
    assert report["trust_boundary"]["production_round_count"] == 1
    assert report["trust_boundary"]["public_r1_identity_count"] == 10
    assert report["parallel_execution"]["configured_jobs"] == 4
    assert report["parallel_execution"]["maximum_concurrent_case_tasks"] == 4
    assert report["parallel_execution"]["final_active_case_tasks"] == 0
    assert len({row["logical_case_id"] for row in report["results"]}) == 59
