from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.benchmark import BenchmarkManifestError, load_benchmark_suite
from agent.hardness.stage_p_contract import (
    EXPECTED_NEGATIVE_FAILURES,
    EXPECTED_POSITIVE_IDS,
    STAGE_P_MUTATION_SUITE_SCHEMA,
    STAGE_P_PATCH_SCHEMA,
    StagePContractError,
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


ROOT = Path(__file__).resolve().parents[1]
POSITIVE = ROOT / "Benchmark/Hardness/Suites/stage_p_open_world.json"
NEGATIVE = ROOT / "Benchmark/Hardness/Suites/stage_p_adversarial.json"
MUTATIONS = ROOT / "Benchmark/Hardness/Suites/stage_p_mutations.json"
WORKER = ROOT / "Benchmark/Hardness/Suites/stage_p_lean_worker_microbenchmark.json"


def suites():
    positive = load_benchmark_suite(POSITIVE)
    negative = load_benchmark_suite(NEGATIVE)
    return positive, negative


def valid_patch_payload(task, *, body: str = "by intro value; rfl") -> dict[str, object]:
    return {
        "schema_version": STAGE_P_PATCH_SCHEMA,
        "action": "submit_patch",
        "session_id": task.session_id,
        "gap_id": task.gap_id,
        "task_class": task.task_class,
        "base_source_sha256": task.base_source_sha256,
        "editable_file": task.editable_file,
        "editable_region": task.editable_region,
        "replacement_body": body,
        "helper_handles": [],
        "binding_claim": {
            "source_endpoint": task.source_endpoint,
            "target_endpoint": task.target_endpoint,
            "direction": task.direction,
            "objective": task.objective,
            "capability_head": task.capability_head,
            "declaration_signature": task.declaration_signature,
        },
    }


def test_stage_p_canonical_matrix_is_frozen() -> None:
    positive, negative = suites()
    cases = validate_stage_p_suites(positive, negative)
    assert tuple(case.id for case in positive.cases) == EXPECTED_POSITIVE_IDS
    assert tuple(case.id for case in negative.cases) == tuple(EXPECTED_NEGATIVE_FAILURES)
    assert len(cases) == 24
    assert sum(case.expected.final_status == "VERIFIED" for case in cases) == 12
    assert sum(case.expected.final_status == "BLOCKED" for case in cases) == 12
    assert {case.input_kind for case in positive.cases} >= {
        "presented_problem",
        "predicate",
        "parameterized_predicate",
    }
    producer = next(case for case in positive.cases if case.id == "p-capability-producer")
    consumer = next(case for case in positive.cases if case.id == "p-capability-consumer")
    assert producer.coverage["family"] == "graph_variant"
    assert consumer.coverage["family"] == "graph_variant"


def test_stage_p_loader_requires_versioned_contract() -> None:
    positive, _ = suites()
    case = positive.cases[0]
    assert case.evaluation_lane == "stage_p"
    assert case.stage_p["schema_version"] == "hardness_stage_p_case_v1"

    raw = json.loads(POSITIVE.read_text(encoding="utf-8"))
    raw["cases"][0].pop("stage_p")
    temporary = ROOT / "tmp/stage-p-invalid-suite.json"
    temporary.parent.mkdir(parents=True, exist_ok=True)
    temporary.write_text(json.dumps(raw), encoding="utf-8")
    try:
        with pytest.raises(BenchmarkManifestError) as error:
            load_benchmark_suite(temporary)
        assert error.value.code == "invalid_schema"
    finally:
        temporary.unlink(missing_ok=True)


def test_stage_p_prompts_hide_scoring_and_case_ids() -> None:
    positive, negative = suites()
    cases = validate_stage_p_suites(positive, negative)
    for case in cases:
        if case.stage_p["protocol_role"] == "consumer":
            continue
        task = build_stage_p_task(case)
        prompt = build_stage_p_contract_prompt(task=task)
        payload = json.loads(prompt)
        audit_stage_p_prompt(payload, forbidden_values=(case.id,))
        serialized = json.dumps(payload, sort_keys=True)
        assert payload["fixed_declaration"]["expected_type_unfolded"]
        assert payload["permitted_actions"] == [payload["response_template"]["action"]]
        assert '"expected"' not in serialized
        assert '"coverage"' not in serialized
        assert case.id not in serialized
        assert '"contract_probe_profile"' not in serialized


def test_valid_model_body_is_preserved_in_contract_probe() -> None:
    positive, _ = suites()
    case = positive.cases[0]
    task = build_stage_p_task(case)
    body = "by\n  intro value\n  rfl"
    action = parse_stage_p_action(json.dumps(valid_patch_payload(task, body=body)), task=task)
    validate_stage_p_terminal_action(action, task=task)
    source = build_contract_probe_source(task=task, action=action, namespace_suffix="ProbeOne")
    assert source.count(body) == 1
    assert f"theorem candidate : {task.declaration_signature} :=" in source
    assert "sorry" not in source


@pytest.mark.parametrize(
    ("field", "value", "code"),
    [
        ("base_source_sha256", "sha256:" + "0" * 64, "patch_base_hash_mismatch"),
        ("editable_file", "../Escape.lean", "patch_outside_editable_region"),
        ("editable_region", "imports", "patch_outside_editable_region"),
    ],
)
def test_patch_binding_and_fence_are_fail_closed(field: str, value: str, code: str) -> None:
    positive, _ = suites()
    task = build_stage_p_task(positive.cases[0])
    payload = valid_patch_payload(task)
    payload[field] = value
    with pytest.raises(StagePContractError) as error:
        parse_stage_p_action(json.dumps(payload), task=task)
    assert error.value.code == code


@pytest.mark.parametrize(
    ("body", "code"),
    [
        ("by sorry", "sorry_axiom_or_unsafe_candidate"),
        ("by admit", "sorry_axiom_or_unsafe_candidate"),
        ("by unsafe def escape := 0", "sorry_axiom_or_unsafe_candidate"),
        ("by import Untrusted.Module", "import_not_allowlisted"),
        ("by exact GoldProof.answer", "oracle_or_gold_import"),
    ],
)
def test_patch_static_security_scan(body: str, code: str) -> None:
    positive, _ = suites()
    task = build_stage_p_task(positive.cases[0])
    with pytest.raises(StagePContractError) as error:
        parse_stage_p_action(
            json.dumps(valid_patch_payload(task, body=body)),
            task=task,
        )
    assert error.value.code == code


def test_fabricated_helper_handle_is_rejected() -> None:
    positive, _ = suites()
    task = build_stage_p_task(positive.cases[0])
    payload = valid_patch_payload(task)
    payload["helper_handles"] = ["helper:not-retrieved"]
    with pytest.raises(StagePContractError) as error:
        parse_stage_p_action(json.dumps(payload), task=task)
    assert error.value.code == "fabricated_declaration_handle"


def test_negative_stop_requires_exact_public_failure_code() -> None:
    _, negative = suites()
    case = negative.cases[0]
    task = build_stage_p_task(case)
    payload = {
        "schema_version": STAGE_P_PATCH_SCHEMA,
        "action": "stop_authoring",
        "session_id": task.session_id,
        "gap_id": task.gap_id,
        "task_class": task.task_class,
        "failure_code": case.expected.final_failure_code,
        "confirmed_facts": ["The exact public assumptions are contradictory."],
        "missing_conditions": ["A lawful proof under the frozen assumptions."],
    }
    action = parse_stage_p_action(json.dumps(payload), task=task)
    validate_stage_p_terminal_action(action, task=task)

    wrong = replace(action, failure_code="authoring_no_progress")
    with pytest.raises(StagePContractError) as error:
        validate_stage_p_terminal_action(wrong, task=task)
    assert error.value.code == case.expected.final_failure_code


def test_security_stop_allows_no_missing_conditions() -> None:
    _, negative = suites()
    case = next(
        item for item in negative.cases
        if item.id == "p-prompt-injection-request-mutation"
    )
    task = build_stage_p_task(case)
    payload = {
        "schema_version": STAGE_P_PATCH_SCHEMA,
        "action": "stop_authoring",
        "session_id": task.session_id,
        "gap_id": task.gap_id,
        "task_class": task.task_class,
        "failure_code": "request_or_endpoint_mutation",
        "confirmed_facts": ["The immutable request may not be changed."],
        "missing_conditions": [],
    }

    action = parse_stage_p_action(json.dumps(payload), task=task)
    validate_stage_p_terminal_action(action, task=task)
    assert action.missing_conditions == ()


def test_consumer_has_no_authoring_task() -> None:
    positive, _ = suites()
    consumer = positive.cases[-1]
    assert consumer.stage_p["protocol_role"] == "consumer"
    assert consumer.requires_authoring is False
    assert consumer.stage_p["semantic_turn_budget"] == 0
    with pytest.raises(StagePContractError) as error:
        build_stage_p_task(consumer)
    assert error.value.code == "consumer_authoring_forbidden"


def test_mutation_suite_materializes_exactly_72_stable_rows() -> None:
    rows = load_and_validate_stage_p_mutations(MUTATIONS)
    assert len(rows) == 72
    assert len({row["mutation_id"] for row in rows}) == 72
    assert all(row["parent_case"].startswith("p-") for row in rows)
    assert all(isinstance(row["seed"], int) for row in rows)

    raw = json.loads(MUTATIONS.read_text(encoding="utf-8"))
    assert raw["schema_version"] == STAGE_P_MUTATION_SUITE_SCHEMA


def test_worker_microbenchmark_freezes_performance_and_isolation_gates() -> None:
    payload = load_and_validate_stage_p_worker_microbenchmark(WORKER)
    assert payload["repeat_count"] == 20
    assert payload["maximum_workers"] == 4
    assert payload["gates"]["warm_p50_over_cold_p50_max"] == 0.5
    assert payload["gates"]["wall_time_reduction_min"] == 0.5
    assert "deletion_after_cache" in payload["isolation_checks"]


def test_report_skeleton_cannot_overclaim_p_a() -> None:
    report = stage_p_report_skeleton()
    assert report["stage"] == "P-A"
    assert report["qualification_scope"] == "contract_only_not_production_capability"
    assert report["status"] == "FAILED"
    assert report["canonical_case_count"] == 24
    assert report["mutation_case_count"] == 72
    assert report["compiler_inserted_math_token_count"] == 0
