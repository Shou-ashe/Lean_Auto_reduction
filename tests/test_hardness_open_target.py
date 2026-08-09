import json
from collections import Counter
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.benchmark import (
    BenchmarkManifestError,
    load_benchmark_suite,
)
from agent.hardness.open_target import (
    COVERAGE_FORBIDDEN_KEYS,
    EXPECTED_NEGATIVE_FAILURES,
    EXPECTED_SOURCE_COUNTS,
    OPEN_TARGET_CASE_COUNT,
    OPEN_TARGET_NEGATIVE_COUNT,
    OPEN_TARGET_POSITIVE_COUNT,
    audit_open_target_prompt,
    find_open_target_prompt_forbidden_keys,
    validate_open_target_suite,
)


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "Benchmark" / "Hardness" / "Suites" / "open_target.json"


def _all_keys(value: object) -> set[str]:
    if isinstance(value, dict):
        keys = set(value)
        for item in value.values():
            keys.update(_all_keys(item))
        return keys
    if isinstance(value, list):
        keys: set[str] = set()
        for item in value:
            keys.update(_all_keys(item))
        return keys
    return set()


def _all_strings(value: object) -> tuple[str, ...]:
    if isinstance(value, dict):
        return tuple(
            item
            for nested in value.values()
            for item in _all_strings(nested)
        )
    if isinstance(value, list):
        return tuple(item for nested in value for item in _all_strings(nested))
    return (value,) if isinstance(value, str) else ()


def test_open_target_suite_has_seven_target_free_cases() -> None:
    cases = validate_open_target_suite(load_benchmark_suite(SUITE))

    assert len(cases) == OPEN_TARGET_CASE_COUNT == 7
    assert sum(case.is_positive for case in cases) == OPEN_TARGET_POSITIVE_COUNT == 3
    assert sum(not case.is_positive for case in cases) == OPEN_TARGET_NEGATIVE_COUNT == 4
    assert Counter(case.source for case in cases) == EXPECTED_SOURCE_COUNTS
    assert len({case.source for case in cases}) == 6
    assert all(case.target is None for case in cases)
    assert all(case.membership is None for case in cases)
    assert all(case.resources["max_model_calls"] == 14 for case in cases)

    positives = [case for case in cases if case.is_positive]
    assert {case.required_hardness for case in positives} == {
        "native_np",
        "native_np_hard",
        "native_np_complete",
    }
    assert all(
        case.coverage.get("minimum_eligible_target_count", 0) >= 2
        or case.coverage.get("require_unreachable_distractor") is True
        for case in positives
    )

    negatives = {case.id: case for case in cases if not case.is_positive}
    assert {
        case.expected.final_failure_code for case in negatives.values()
    } == {
        "eligible_target_has_no_existing_route",
        "no_eligible_hardness_target",
    }
    assert all(
        case.expected.final_failure_code == EXPECTED_NEGATIVE_FAILURES[case_id]
        for case_id, case in negatives.items()
    )


def test_open_target_suite_expected_and_coverage_have_no_gold_target() -> None:
    raw = json.loads(SUITE.read_text(encoding="utf-8"))
    for case in raw["cases"]:
        assert case["target"] is None
        assert set(case["expected"]) <= {"final_status", "final_failure_code"}
        assert not (_all_keys(case["coverage"]) & COVERAGE_FORBIDDEN_KEYS)
        assert not any(
            value.startswith(("ComplexityReduction.", "Benchmark.Hardness."))
            for value in _all_strings(case["coverage"])
        )


def test_open_target_validator_rejects_policy_or_oracle_drift() -> None:
    suite = load_benchmark_suite(SUITE)
    cases = list(suite.cases)
    cases[0] = replace(cases[0], maximum_route_atoms=4)
    with pytest.raises(ValueError, match="changed its public target policy"):
        validate_open_target_suite(replace(suite, cases=tuple(cases)))

    cases = list(suite.cases)
    cases[0] = replace(
        cases[0],
        coverage={
            **cases[0].coverage,
            "acceptable_targets": ["ComplexityReduction.Hidden.Target"],
        },
    )
    with pytest.raises(ValueError, match="coverage contains target/route oracle data"):
        validate_open_target_suite(replace(suite, cases=tuple(cases)))


def test_open_target_prompt_audit_allows_retrieved_candidates_only() -> None:
    payload = {
        "request": {
            "input_declaration": "Benchmark.Hardness.Inputs.InputGrounding.Clause.twoCNFDirect",
            "objective_direction": "source_to_target",
            "required_hardness": "native_np_hard",
            "allowed_target_evidence": ["native_completeness"],
            "maximum_route_atoms": 3,
            "maximum_dependencies": 8,
            "allow_reflexive_target": False,
        },
        "retrieved": {
            "hardness_targets": [
                {
                    "target_declaration": "ComplexityReduction.Public.Target",
                    "target_node_id": "lean-whnf:target",
                    "evidence_kind": "native_completeness",
                }
            ],
            "reductions": [
                {
                    "source_node_id": "lean-whnf:source",
                    "target_node_id": "lean-whnf:target",
                }
            ],
        },
    }
    assert find_open_target_prompt_forbidden_keys(payload) == ()
    audit_open_target_prompt(payload)

    leaked = {
        **payload,
        "request": {**payload["request"], "target_declaration": "Gold.target"},
        "acceptable_targets": ["Gold.target"],
    }
    assert find_open_target_prompt_forbidden_keys(leaked) == (
        "acceptable_targets",
        "request.target_declaration",
    )
    with pytest.raises(ValueError, match="benchmark answer fields"):
        audit_open_target_prompt(leaked)


def _write_schema_suite(
    tmp_path: Path,
    *,
    updates: dict[str, object] | None = None,
    remove: str | None = None,
) -> Path:
    repository = tmp_path / "repo"
    hardness = repository / "Benchmark" / "Hardness"
    suites = hardness / "Suites"
    input_file = (
        repository
        / "Lean"
        / "Reference"
        / "Benchmark"
        / "Hardness"
        / "Inputs"
        / "Example"
        / "Source.lean"
    )
    suites.mkdir(parents=True)
    input_file.parent.mkdir(parents=True)
    input_file.write_text(
        "namespace Benchmark.Hardness.Inputs.Example.Source\n"
        "end Benchmark.Hardness.Inputs.Example.Source\n",
        encoding="utf-8",
    )
    case: dict[str, object] = {
        "id": "open-target-schema",
        "module": "Benchmark.Hardness.Inputs.Example.Source",
        "source": "Benchmark.Hardness.Inputs.Example.Source.source",
        "input_declaration": "Benchmark.Hardness.Inputs.Example.Source.source",
        "input_kind": "presented_problem",
        "membership": None,
        "target": None,
        "objective": "reduce_to_known_np",
        "objective_direction": "source_to_target",
        "target_policy": "open",
        "required_hardness": "native_np",
        "allowed_target_evidence": ["native_membership"],
        "maximum_route_atoms": 0,
        "maximum_dependencies": 0,
        "allow_reflexive_target": False,
        "catalog_mode": "full",
        "evaluation_lane": "open_target",
        "execution_layer": "core_reuse",
        "verification_profile": "core",
        "authoring_policy": {"enabled": False, "mode": "disabled"},
        "expected": {"final_status": "VERIFIED"},
        "coverage": {"require_target_from_search": True},
        "resources": {"max_model_calls": 14},
        "tags": ["test"],
    }
    if updates:
        case.update(updates)
    if remove is not None:
        case.pop(remove)
    suite = suites / "open_target.json"
    suite.write_text(
        json.dumps(
            {
                "schema_version": "hardness_benchmark_suite_v1",
                "suite_id": "schema-open-target",
                "description": "schema fixture",
                "cases": [case],
            }
        ),
        encoding="utf-8",
    )
    return suite


def test_open_target_schema_accepts_zero_resource_limits(tmp_path: Path) -> None:
    case = load_benchmark_suite(_write_schema_suite(tmp_path)).cases[0]
    assert case.maximum_route_atoms == 0
    assert case.maximum_dependencies == 0


@pytest.mark.parametrize(
    ("updates", "remove"),
    [
        ({"required_hardness": "backend_np"}, None),
        ({"allowed_target_evidence": ["backend_completeness"]}, None),
        ({"maximum_route_atoms": -1}, None),
        ({"maximum_dependencies": -1}, None),
        ({"allow_reflexive_target": "false"}, None),
        ({"input_kind": "predicate"}, None),
        ({"target_policy": "fixed"}, None),
        ({}, "maximum_dependencies"),
    ],
)
def test_open_target_schema_rejects_invalid_policy_or_lane_abi(
    tmp_path: Path,
    updates: dict[str, object],
    remove: str | None,
) -> None:
    with pytest.raises(BenchmarkManifestError) as error:
        load_benchmark_suite(
            _write_schema_suite(tmp_path, updates=updates, remove=remove)
        )
    assert error.value.code == "invalid_schema"


@pytest.mark.parametrize(
    "evidence_kind",
    (
        "native_completeness_projection",
        "transported_native_hardness",
        "transported_native_completeness",
    ),
)
def test_open_target_schema_rejects_unemittable_catalog_evidence_kind(
    tmp_path: Path,
    evidence_kind: str,
) -> None:
    with pytest.raises(BenchmarkManifestError) as error:
        load_benchmark_suite(
            _write_schema_suite(
                tmp_path,
                updates={"allowed_target_evidence": [evidence_kind]},
            )
        )
    assert error.value.code == "invalid_schema"
    assert "outside the open_target lane ABI" in error.value.message


def test_open_target_policy_fields_are_forbidden_in_other_lanes(tmp_path: Path) -> None:
    with pytest.raises(BenchmarkManifestError) as error:
        load_benchmark_suite(
            _write_schema_suite(tmp_path, updates={"evaluation_lane": "existing_route"})
        )
    assert error.value.code == "invalid_schema"
    assert "outside the open_target lane" in error.value.message
