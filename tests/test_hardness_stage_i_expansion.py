import json
import threading
from copy import deepcopy
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.benchmark import load_benchmark_suite
from agent.hardness.stage_i_expansion import validate_stage_i_expansion_suite
from scripts.run_deepseek_stage_i_expansion_benchmark import (
    DEFAULT_CASE_JOBS,
    DEFAULT_STAGE_I_MODEL_MAX_TOKENS,
    DEFAULT_STAGE_I_MODEL_TIMEOUT,
    MAX_CASE_JOBS,
    CaseExecutionOutcome,
    _contract_errors,
    parallel_execution_errors,
    parser,
    request_policy as deepseek_request_policy,
    run_case_tasks,
    validate_case_concurrency,
)
from scripts.run_stage_i_expansion_offline_benchmark import (
    request_policy as offline_request_policy,
)


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "Benchmark" / "Hardness" / "Suites" / "stage_i_expansion.json"


def cases():
    return validate_stage_i_expansion_suite(load_benchmark_suite(SUITE))


def test_stage_i_suite_has_eight_target_and_route_free_cases() -> None:
    selected = cases()

    assert len(selected) == 8
    assert sum(case.is_positive for case in selected) == 4
    assert sum(not case.is_positive for case in selected) == 4
    assert {case.input_kind for case in selected} == {
        "presented_problem",
        "predicate",
    }
    assert all(case.target is None and case.membership is None for case in selected)
    assert all(case.objective == "reduce_to_known_hardness" for case in selected)
    assert all(case.minimum_route_atoms > 0 for case in selected)
    assert all(case.require_simple_path for case in selected)
    assert all(
        case.allowed_target_evidence == ("transported_native_hardness",)
        for case in selected
    )


def test_stage_i_manifest_has_no_duplicate_json_keys() -> None:
    duplicates: list[str] = []

    def reject_duplicates(pairs):
        value = {}
        for key, item in pairs:
            if key in value:
                duplicates.append(str(key))
            value[key] = item
        return value

    json.loads(SUITE.read_text(encoding="utf-8"), object_pairs_hook=reject_duplicates)
    assert duplicates == []


def test_stage_i_validator_rejects_gold_route_or_abi_drift() -> None:
    suite = load_benchmark_suite(SUITE)
    first = suite.cases[0]

    with pytest.raises(ValueError, match="outside the Stage I expansion ABI"):
        validate_stage_i_expansion_suite(
            replace(
                suite,
                cases=(
                    replace(first, require_simple_path=False),
                    *suite.cases[1:],
                ),
            )
        )

    leaked_coverage = dict(first.coverage)
    leaked_coverage["gold_route"] = ["Fixture.Route.secret"]
    with pytest.raises(ValueError, match="oracle data"):
        validate_stage_i_expansion_suite(
            replace(
                suite,
                cases=(
                    replace(first, coverage=leaked_coverage),
                    *suite.cases[1:],
                ),
            )
        )


def test_stage_i_offline_and_deepseek_runners_share_the_public_request() -> None:
    for case in cases():
        offline = offline_request_policy(case)
        online = deepseek_request_policy(case)
        assert offline == online
        assert online.to_dict() == {
            "required_hardness": "native_np_hard",
            "allowed_target_evidence": ["transported_native_hardness"],
            "minimum_route_atoms": case.minimum_route_atoms,
            "maximum_route_atoms": case.maximum_route_atoms,
            "maximum_dependencies": case.maximum_dependencies,
            "allow_reflexive_target": False,
            "require_simple_path": True,
            "objective": "reduce_to_known_hardness",
        }


def _valid_contract_rows() -> list[dict]:
    usage = {
        "prompt_tokens": 10,
        "completion_tokens": 4,
        "total_tokens": 14,
        "prompt_cache_hit_tokens": 6,
        "prompt_cache_miss_tokens": 4,
    }
    rows = []
    for case in cases():
        row = {
            "id": case.id,
            "expected_status": case.expected.final_status,
            "expected_failure_code": case.expected.final_failure_code,
            "protocol_matches_expected": True,
            "replayed_from_resume": False,
            "prompt_oracle_errors": [],
            "compact_retrieved_view_all_rounds": True,
            "compact_retrieved_view_errors": [],
            "external_api_calls_this_run": 1,
            "http_ok_count_this_run": 1,
            "round_usage_complete": True,
            "usage": usage,
            "candidate_metrics": {},
        }
        if case.is_positive:
            row.update(
                {
                    "final_status": "VERIFIED",
                    "model_term_changed_by_agent": False,
                    "selected_target_evidence_kind": "transported_native_hardness",
                    "selected_route_within_public_range": True,
                    "selected_path_is_simple": True,
                    "selected_shared_gadget_count": 1,
                    "selected_target_from_search": True,
                    "selected_evidence_from_search": True,
                    "selected_evidence_policy_satisfied": True,
                    "matched_problem_from_search": True,
                    "route_declarations_all_retrieved": True,
                    "all_selected_facts_retrieved": True,
                    "candidate_metrics": {
                        "unique_policy_route_allowed_targets": int(
                            case.coverage["minimum_policy_allowed_target_count"]
                        )
                    },
                    "input_kind": case.input_kind,
                    "problem_match": (
                        {"accepts_exact_defeq": True}
                        if case.input_kind == "predicate"
                        else None
                    ),
                }
            )
        else:
            metrics = {}
            if case.id == "stage-i-no-eligible-transport-dependency-limit":
                metrics["unique_eligible_target_evidences"] = 0
            elif case.id in {
                "stage-i-forward-route-absent",
                "stage-i-reverse-only-hard-target",
            }:
                metrics.update(
                    {
                        "unique_eligible_target_evidences": 1,
                        "unique_policy_route_allowed_targets": 0,
                    }
                )
                if case.id == "stage-i-reverse-only-hard-target":
                    metrics["unique_reverse_route_targets"] = 1
            row.update(
                {
                    "final_status": "BLOCKED",
                    "final_failure_code": case.expected.final_failure_code,
                    "candidate_metrics": metrics,
                }
            )
        rows.append(row)
    return rows


def test_stage_i_real_runner_contract_requires_fresh_calls_and_one_final_gate() -> None:
    selected = cases()
    rows = _valid_contract_rows()
    arguments = {
        "lean_process_count": 1,
        "lean_ok": True,
        "lean_started_after_all_model_tasks": True,
        "model_task_count_at_lean_start": 8,
        "artifact_sha256": "a" * 64,
        "accepted_positive_case_count": 4,
        "assert_standard_axioms_count": 1,
        "predicate_grounding_count": 2,
        "target_hardness_count": 4,
        "routing_rule_count": 0,
        "prompt_rule_count": 0,
    }

    assert _contract_errors(rows, selected, **arguments) == ()

    replayed = deepcopy(rows)
    replayed[0]["replayed_from_resume"] = True
    replayed[0]["external_api_calls_this_run"] = 0
    errors = _contract_errors(replayed, selected, **arguments)
    assert any("prior model answer was replayed" in error for error in errors)
    assert any("no fresh DeepSeek call" in error for error in errors)

    uncompacted = deepcopy(rows)
    uncompacted[0]["compact_retrieved_view_all_rounds"] = False
    errors = _contract_errors(uncompacted, selected, **arguments)
    assert any("not every prompt used the compact" in error for error in errors)

    leaked_verbose_view = deepcopy(rows)
    leaked_verbose_view[0]["compact_retrieved_view_errors"] = [
        "retrieved.reductions[0] contains verbose fields: source"
    ]
    errors = _contract_errors(leaked_verbose_view, selected, **arguments)
    assert any("compact retrieved view failed" in error for error in errors)


def test_stage_i_real_runner_exposes_no_resume_or_replay_switch() -> None:
    command = parser()
    destinations = {action.dest for action in command._actions}
    assert "resume_report" not in destinations
    assert "replay" not in destinations
    assert "output_root" in destinations
    assert "canonical_report" in destinations
    parsed = command.parse_args([])
    assert parsed.model_timeout == DEFAULT_STAGE_I_MODEL_TIMEOUT
    assert parsed.model_max_tokens == DEFAULT_STAGE_I_MODEL_MAX_TOKENS
    assert parsed.jobs == DEFAULT_CASE_JOBS
    assert parsed.minimum_observed_parallelism == 1


def test_stage_i_real_runner_bounds_case_concurrency_at_four() -> None:
    assert validate_case_concurrency(1, 1) == (1, 1)
    assert validate_case_concurrency(MAX_CASE_JOBS, MAX_CASE_JOBS) == (4, 4)
    with pytest.raises(ValueError, match="--jobs must be in 1..4"):
        validate_case_concurrency(0, 1)
    with pytest.raises(ValueError, match="--jobs must be in 1..4"):
        validate_case_concurrency(5, 1)
    with pytest.raises(ValueError, match="must be in 1..--jobs"):
        validate_case_concurrency(2, 3)


def test_stage_i_case_executor_observes_four_way_parallelism() -> None:
    all_started = threading.Event()
    lock = threading.Lock()
    started = 0

    def worker(index: int, case_id: str) -> CaseExecutionOutcome:
        nonlocal started
        with lock:
            started += 1
            if started == 4:
                all_started.set()
        assert all_started.wait(timeout=3)
        return CaseExecutionOutcome(
            index=index,
            case_id=case_id,
            row={"id": case_id},
            artifact=None,
        )

    case_ids = [f"parallel-case-{index}" for index in range(1, 5)]
    outcomes, audit = run_case_tasks(
        [
            (index, case_id, case_id)
            for index, case_id in enumerate(case_ids, start=1)
        ],
        jobs=4,
        worker=worker,
    )

    assert [outcome.case_id for outcome in outcomes] == case_ids
    assert audit["maximum_concurrent_case_tasks"] == 4
    assert audit["active_case_task_count"] == 0
    assert parallel_execution_errors(
        audit,
        expected_case_ids=case_ids,
        minimum_observed_parallelism=4,
    ) == ()
