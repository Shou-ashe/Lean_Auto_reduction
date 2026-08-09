import json
import sys
from copy import deepcopy
from pathlib import Path
from types import SimpleNamespace

import pytest

from agent.hardness.benchmark import load_benchmark_suite
from agent.hardness.model_client import DeepSeekConfig, ModelResponse
from agent.hardness.open_target import validate_open_target_suite
import scripts.run_deepseek_open_target_benchmark as runner_module
from scripts.run_deepseek_open_target_benchmark import (
    REQUIRED_USAGE_FIELDS,
    aggregate_usage,
    atomic_write_json,
    artifact_case_from_result,
    build_case_runner_error_row,
    build_round_records,
    build_stage_g_summary,
    finalize_report,
    model_term_changed_by_agent,
    negative_semantic_audit,
    open_target_candidate_metrics,
    parser,
    preflight_canonical_report,
    prepare_fresh_output_root,
    run_final_lean_after_all_model_tasks,
    selected_fact_audit,
    sha256_text,
    submitted_model_term,
    usage_contract_errors,
)


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "Benchmark" / "Hardness" / "Suites" / "open_target.json"
DYNAMIC_TARGET = "ComplexityReduction.Problems.Dynamic.problem"
DYNAMIC_EVIDENCE = "ComplexityReduction.Evidence.dynamicNativeNP"
DYNAMIC_TARGET_ID = "sha256:dynamic-target"
DYNAMIC_EVIDENCE_ID = "sha256:dynamic-evidence"
ROUTE = "ComplexityReduction.Routes.SourceToDynamic.route"


def cases():
    return validate_open_target_suite(load_benchmark_suite(SUITE))


def usage() -> dict[str, int]:
    return {
        "prompt_tokens": 10,
        "completion_tokens": 4,
        "total_tokens": 14,
        "prompt_cache_hit_tokens": 6,
        "prompt_cache_miss_tokens": 4,
    }


def response(content: str = '{"action":"stop"}') -> ModelResponse:
    return ModelResponse(
        called=True,
        ok=True,
        content=content,
        error=None,
        status_code=200,
        duration_seconds=0.1,
        usage=usage(),
        attempts=1,
        finish_reason="stop",
    )


def test_formal_runner_requires_fresh_root_and_has_no_resume_or_replay_cli(
    tmp_path: Path,
) -> None:
    output = tmp_path / "fresh"
    prepare_fresh_output_root(output)
    (output / "prior.json").write_text("{}", encoding="utf-8")
    with pytest.raises(ValueError, match="cannot resume, replay, or reuse"):
        prepare_fresh_output_root(output)

    command = parser()
    destinations = {action.dest for action in command._actions}
    assert "resume_report" not in destinations
    assert "replay" not in destinations
    parsed = command.parse_args([])
    assert parsed.canonical_report == (
        ROOT / "Benchmark" / "Hardness" / "OPEN_TARGET_REPORT.json"
    )


def test_canonical_preflight_and_atomic_publish_use_same_directory(
    tmp_path: Path,
) -> None:
    canonical = tmp_path / "nested" / "canonical.json"
    preflight_canonical_report(canonical)
    assert canonical.parent.is_dir()
    assert list(canonical.parent.iterdir()) == []

    atomic_write_json(canonical, {"status": "VERIFIED"})
    assert json.loads(canonical.read_text(encoding="utf-8")) == {
        "status": "VERIFIED"
    }
    assert not list(canonical.parent.glob(f".{canonical.name}.*.tmp"))


def test_canonical_publish_failure_turns_local_report_failed_and_redacts(
    tmp_path: Path,
) -> None:
    report_path = tmp_path / "run" / "report.json"
    canonical = tmp_path / "canonical.json"
    canonical.write_text('{"status":"OLD"}\n', encoding="utf-8")
    emitted: list[str] = []

    def fail_publish(path: Path, value: object) -> None:
        raise OSError("super-secret publish failure")

    report = {"summary": {"all_stage_g_thresholds_met": True}}
    exit_code = finalize_report(
        report=report,
        report_path=report_path,
        canonical_report=canonical,
        status="VERIFIED",
        exit_code=0,
        run_label="test",
        redactor=lambda value: value.replace("super-secret", "[REDACTED]"),
        atomic_publisher=fail_publish,
        emit=emitted.append,
    )
    saved = json.loads(report_path.read_text(encoding="utf-8"))
    assert exit_code == 1
    assert saved["status"] == "FAILED"
    assert saved["canonical_publish"]["published"] is False
    assert "super-secret" not in json.dumps(saved)
    assert json.loads(canonical.read_text(encoding="utf-8"))["status"] == "OLD"
    assert json.loads(emitted[-1])["canonical_report_published"] is False


def test_round_usage_contract_keeps_cache_fields_and_hashes(tmp_path: Path) -> None:
    assert usage_contract_errors(usage(), label="round") == ()
    missing_cache = usage()
    missing_cache.pop("prompt_cache_miss_tokens")
    assert usage_contract_errors(missing_cache, label="round") == (
        "round: usage.prompt_cache_miss_tokens is missing or invalid",
    )
    assert set(REQUIRED_USAGE_FIELDS).issubset(
        aggregate_usage([usage(), usage()])
    )

    prompt = json.dumps(
        {
            "request": {
                "required_hardness": "native_np",
                "allowed_target_evidence": ["native_membership"],
            },
            "retrieved": {"hardness_targets": []},
        },
        sort_keys=True,
    )
    config = DeepSeekConfig(api_key="test-key")
    records = build_round_records(
        case_id="case",
        prompts=[prompt],
        responses=[response()],
        output_root=tmp_path,
        config=config,
    )
    assert len(records) == 1
    record = records[0]
    assert record["usage"] == usage()
    assert record["usage_contract_ok"] is True
    assert record["replayed"] is False
    assert record["prompt_sha256"] == sha256_text(prompt)
    assert len(record["response_sha256"]) == 64
    saved = json.loads(Path(record["response_file"]).read_text(encoding="utf-8"))
    assert saved["usage"]["prompt_cache_hit_tokens"] == 6
    assert saved["usage"]["prompt_cache_miss_tokens"] == 4


def test_case_runner_exception_row_preserves_paid_calls_and_redacts() -> None:
    case = cases()[0]
    config = DeepSeekConfig(api_key="super-secret")
    result = SimpleNamespace(
        model_prompts=(json.dumps({"request": {}, "retrieved": {}}),),
        model_responses=(response(),),
        query_trace=(),
        protocol_accepted=False,
        problem_match=None,
        selected_connection=None,
        reduction_declarations=(),
        lean_term=None,
        plan=None,
    )
    row = build_case_runner_error_row(
        case=case,
        execution_position=1,
        error=RuntimeError("super-secret internal failure"),
        config=config,
        result=result,
    )
    assert row["final_status"] == "FAILED"
    assert row["protocol_matches_expected"] is False
    assert row["external_api_calls_this_run"] == 1
    assert len(row["model_rounds"]) == 1
    assert row["model_rounds"][0]["runner_recovery_record"] is True
    assert "super-secret" not in json.dumps(row)


def test_main_continues_after_one_case_exception_and_finishes_failed(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    output_root = tmp_path / "output"
    canonical = tmp_path / "canonical.json"
    dummy_catalog = tmp_path / "catalog.json"
    dummy_catalog.write_text("{}\n", encoding="utf-8")
    dummy_input = tmp_path / "Input.lean"
    dummy_input.write_text("def input : True := True.intro\n", encoding="utf-8")
    dummy_observation = tmp_path / "observation.json"
    dummy_observation.write_text("{}\n", encoding="utf-8")

    fingerprint = "lean:test"
    problem_catalog = SimpleNamespace(
        registry_fingerprint=fingerprint,
        catalog_id="problem-catalog",
        entries=(),
    )
    connection_catalog = SimpleNamespace(
        registry_fingerprint=fingerprint,
        catalog_id="connection-catalog",
        entries=(),
    )
    reduction_catalog = SimpleNamespace(
        registry_fingerprint=fingerprint,
        catalog_id="reduction-catalog",
        entries=(),
        mode="full",
    )
    target_catalog = SimpleNamespace(
        registry_fingerprint=fingerprint,
        catalog_id="target-catalog",
        entries=(),
        evidence_count=0,
    )
    monkeypatch.setattr(
        runner_module,
        "load_problem_catalog_snapshot",
        lambda *args, **kwargs: problem_catalog,
    )
    monkeypatch.setattr(
        runner_module,
        "load_connection_catalog_snapshot",
        lambda *args, **kwargs: connection_catalog,
    )
    monkeypatch.setattr(
        runner_module,
        "load_hardness_target_catalog_snapshot",
        lambda *args, **kwargs: target_catalog,
    )
    monkeypatch.setattr(
        runner_module,
        "build_reduction_catalog",
        lambda *args, **kwargs: reduction_catalog,
    )
    monkeypatch.setattr(runner_module, "module_file", lambda *args: dummy_input)
    monkeypatch.setattr(
        runner_module,
        "observation_snapshot_path",
        lambda *args, **kwargs: dummy_observation,
    )
    monkeypatch.setattr(
        runner_module,
        "load_input_observation_snapshot",
        lambda path, **kwargs: SimpleNamespace(
            observation_id=f"obs:{kwargs['expected_input_declaration']}",
            normalized_problem_node_id="lean-whnf:test",
            registry_fingerprint=fingerprint,
        ),
    )
    monkeypatch.setattr(
        runner_module.DeepSeekConfig,
        "from_environment",
        classmethod(lambda cls, **kwargs: DeepSeekConfig(api_key="test-key")),
    )

    generated_cases: list[str] = []

    def fake_generate(**kwargs):
        generated_cases.append(kwargs["observation"].observation_id)
        if len(generated_cases) == 1:
            raise RuntimeError("test-key synthetic case failure")
        return SimpleNamespace(
            model_prompts=(),
            model_responses=(),
            query_trace=(),
            protocol_accepted=False,
            problem_match=None,
            selected_connection=None,
            reduction_declarations=(),
            lean_term=None,
            plan=None,
            failure_code="synthetic_failure",
            explanation="synthetic failure",
        )

    def fake_result_row(**kwargs):
        case = kwargs["case"]
        return {
            "id": case.id,
            "expected_status": case.expected.final_status,
            "expected_failure_code": case.expected.final_failure_code,
            "protocol_accepted": False,
            "protocol_matches_expected": False,
            "failure_code": "synthetic_failure",
            "explanation": "synthetic failure",
            "model_rounds": [],
            "model_turn_count": 0,
            "external_api_calls_this_run": 0,
            "http_ok_count_this_run": 0,
            "http_request_attempts_this_run": 0,
            "called_this_run": False,
            "replayed_from_resume": False,
            "usage": {},
            "round_usage_complete": False,
            "prompt_oracle_errors": [],
            "query_action_counts": {},
            "candidate_metrics": {},
            "negative_semantic_audit": negative_semantic_audit(
                {"id": case.id, "candidate_metrics": {}}
            ),
            "query_round_count": 0,
            "model_term_changed_by_agent": False,
            "model_raw_lean_term": None,
            "plan": None,
            "selected_target_from_search": None,
            "selected_evidence_from_search": None,
            "selected_evidence_policy_satisfied": None,
            "matched_problem_from_search": None,
            "selected_connection_from_search": None,
            "route_declarations_all_retrieved": None,
            "all_selected_facts_retrieved": None,
            "final_status": None,
            "final_failure_code": None,
            "final_explanation": None,
        }

    monkeypatch.setattr(runner_module, "generate_lean_path_to_open_target", fake_generate)
    monkeypatch.setattr(runner_module, "result_row", fake_result_row)
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "run_deepseek_open_target_benchmark.py",
            "--output-root",
            str(output_root),
            "--canonical-report",
            str(canonical),
            "--problem-catalog",
            str(dummy_catalog),
            "--connection-catalog",
            str(dummy_catalog),
            "--target-catalog",
            str(dummy_catalog),
            "--observations-root",
            str(tmp_path / "observations"),
            "--env-file",
            str(tmp_path / "missing.env"),
        ],
    )
    assert runner_module.main() == 1
    saved = json.loads((output_root / "report.json").read_text(encoding="utf-8"))
    assert saved["status"] == "FAILED"
    assert len(generated_cases) == 7
    assert len(saved["cases"]) == 7
    assert saved["cases"][0]["final_failure_code"] == "runner_internal_error"
    assert "test-key" not in json.dumps(saved)
    assert not canonical.exists()


def test_model_term_preservation_is_byte_exact() -> None:
    raw = "  ComplexityReduction.Certificate.CertifiedPath.refl  "
    model = response(json.dumps({"action": "finish", "lean_term": raw}))
    assert submitted_model_term([model]) == raw
    assert model_term_changed_by_agent(raw, raw) is False
    assert model_term_changed_by_agent(raw, raw.strip()) is True


def positive_trace(case) -> list[dict[str, object]]:
    evidence = {
        "evidence_id": DYNAMIC_EVIDENCE_ID,
        "evidence_kind": "native_membership",
        "evidence_declaration": DYNAMIC_EVIDENCE,
        "evidence_lean_term": DYNAMIC_EVIDENCE,
        "satisfied_policies": ["native_np"],
        "provenance_declarations": [DYNAMIC_EVIDENCE],
        "request_eligible": True,
    }
    return [
        {
            "action": "search_problems",
            "results": [
                {
                    "entry_id": "sha256:problem",
                    "declaration": "ComplexityReduction.Problems.Source.problem",
                }
            ],
        },
        {
            "action": "search_hardness_targets",
            "results": [
                {
                    "target_entry_id": DYNAMIC_TARGET_ID,
                    "target_declaration": DYNAMIC_TARGET,
                    "reachable_from_input": True,
                    "shortest_route_length_from_input": 1,
                    "within_route_atom_limit": True,
                    "policy_route_allowed": True,
                    "reverse_route_exists": False,
                    "evidences": [evidence],
                }
            ],
        },
        {
            "action": "search_reductions",
            "results": [{"declaration": ROUTE}],
        },
    ]


def fake_positive_result(case):
    evidence = {
        "target_entry_id": DYNAMIC_TARGET_ID,
        "evidence_id": DYNAMIC_EVIDENCE_ID,
        "evidence_kind": "native_membership",
        "evidence_declaration": DYNAMIC_EVIDENCE,
        "evidence_lean_term": DYNAMIC_EVIDENCE,
        "satisfied_policies": ["native_np"],
        "provenance_declarations": [DYNAMIC_EVIDENCE],
        "policy_satisfied": True,
        "requested_hardness": "native_np",
    }
    plan = SimpleNamespace(
        target_declaration=DYNAMIC_TARGET,
        target_evidence=evidence,
    )
    return SimpleNamespace(
        plan=plan,
        lean_term=f"ComplexityReduction.Certificate.CertifiedPath.step {ROUTE}",
        query_trace=tuple(positive_trace(case)),
        problem_match=SimpleNamespace(
            candidate_declaration="ComplexityReduction.Problems.Source.problem"
        ),
        selected_connection=None,
        reduction_declarations=(ROUTE,),
    )


def test_dynamic_target_metrics_and_selected_fact_audit_use_search_results() -> None:
    case = cases()[0]
    assert case.target is None
    result = fake_positive_result(case)
    metrics = open_target_candidate_metrics(result.query_trace)
    assert metrics["unique_hardness_target_candidates"] == 1
    assert metrics["unique_target_evidence_candidates"] == 1
    assert metrics["unique_eligible_target_evidences"] == 1
    assert metrics["unique_reachable_eligible_targets"] == 1
    assert metrics["unique_policy_route_allowed_targets"] == 1
    assert metrics["unique_reduction_candidates"] == 1

    legacy_trace = deepcopy(result.query_trace)
    legacy_trace[1]["results"][0].pop("policy_route_allowed")
    legacy_metrics = open_target_candidate_metrics(legacy_trace)
    assert "unique_policy_route_allowed_targets" not in legacy_metrics

    audit = selected_fact_audit(case, result)
    assert audit["selected_target_from_search"] is True
    assert audit["selected_evidence_from_search"] is True
    assert audit["selected_evidence_policy_satisfied"] is True
    assert audit["route_declarations_all_retrieved"] is True
    assert audit["all_selected_facts_retrieved"] is True
    assert audit["selected_target_reachability"] == {
        "reachable_from_input": True,
        "shortest_route_length_from_input": 1,
        "within_route_atom_limit": True,
        "reverse_route_exists": False,
    }


def test_dynamic_target_artifact_and_final_lean_wait_for_all_models(
    tmp_path: Path,
) -> None:
    case = cases()[0]
    artifact = artifact_case_from_result(case, fake_positive_result(case))
    assert artifact.target_declaration == DYNAMIC_TARGET
    assert artifact.target_evidence_lean_term == DYNAMIC_EVIDENCE

    calls: list[list[str]] = []

    def fake_lean(command, **kwargs):
        calls.append(list(command))
        return SimpleNamespace(
            command=tuple(command),
            exit_code=0,
            ok=True,
            timed_out=False,
            duration_seconds=0.1,
            stdout="",
            stderr="",
        )

    artifact_path = tmp_path / "OpenTarget.lean"
    with pytest.raises(ValueError, match="before every model task"):
        run_final_lean_after_all_model_tasks(
            artifacts=[artifact],
            completed_model_task_count=6,
            expected_model_task_count=7,
            artifact_path=artifact_path,
            lean_root=tmp_path,
            timeout_seconds=10,
            command_runner=fake_lean,
        )
    assert calls == []
    execution = run_final_lean_after_all_model_tasks(
        artifacts=[artifact],
        completed_model_task_count=7,
        expected_model_task_count=7,
        artifact_path=artifact_path,
        lean_root=tmp_path,
        timeout_seconds=10,
        command_runner=fake_lean,
    )
    assert execution["process_count"] == 1
    assert execution["started_after_all_model_tasks"] is True
    assert len(calls) == 1
    source = artifact_path.read_text(encoding="utf-8")
    assert DYNAMIC_TARGET in source
    assert DYNAMIC_EVIDENCE in source
    assert source.count("assert_standard_axioms") == 1


def valid_report_rows() -> list[dict[str, object]]:
    round_row = {
        "called": True,
        "http_ok": True,
        "attempts": 1,
        "replayed": False,
        "usage": usage(),
        "system_sha256": "a" * 64,
        "prompt_sha256": "b" * 64,
        "response_sha256": "c" * 64,
    }
    rows = []
    for case in cases():
        positive = case.is_positive
        if positive:
            candidate_metrics = {
                "unique_hardness_target_candidates": 1,
                "unique_target_evidence_candidates": 1,
                "unique_eligible_target_evidences": 1,
                "unique_policy_route_allowed_targets": 1,
                "unique_reachable_eligible_targets": 1,
                "unique_reverse_route_targets": 0,
            }
        elif case.expected.final_failure_code == "no_eligible_hardness_target":
            candidate_metrics = {
                "unique_hardness_target_candidates": 1,
                "unique_target_evidence_candidates": 1,
                "unique_eligible_target_evidences": 0,
                "unique_policy_route_allowed_targets": 0,
                "unique_reachable_eligible_targets": 0,
                "unique_reverse_route_targets": 0,
            }
        else:
            candidate_metrics = {
                "unique_hardness_target_candidates": 1,
                "unique_target_evidence_candidates": 1,
                "unique_eligible_target_evidences": 1,
                "unique_policy_route_allowed_targets": 0,
                "unique_reachable_eligible_targets": 0,
                "unique_reverse_route_targets": (
                    1 if case.id == "open-target-exact-cover-reverse-only" else 0
                ),
            }
        row: dict[str, object] = {
            "id": case.id,
            "expected_status": case.expected.final_status,
            "expected_failure_code": case.expected.final_failure_code,
            "protocol_matches_expected": True,
            "protocol_accepted": positive,
            "failure_code": None if positive else case.expected.final_failure_code,
            "final_status": "VERIFIED" if positive else "BLOCKED",
            "final_failure_code": None if positive else case.expected.final_failure_code,
            "model_rounds": [deepcopy(round_row)],
            "model_turn_count": 1,
            "external_api_calls_this_run": 1,
            "http_ok_count_this_run": 1,
            "http_request_attempts_this_run": 1,
            "called_this_run": True,
            "replayed_from_resume": False,
            "usage": usage(),
            "round_usage_complete": True,
            "prompt_oracle_errors": [],
            "query_action_counts": {"search_hardness_targets": 1},
            "candidate_metrics": candidate_metrics,
            "query_round_count": 1,
            "model_term_changed_by_agent": False,
            "selected_target_from_search": True if positive else None,
            "selected_evidence_from_search": True if positive else None,
            "selected_evidence_policy_satisfied": True if positive else None,
            "matched_problem_from_search": True if positive else None,
            "selected_connection_from_search": True if positive else None,
            "route_declarations_all_retrieved": True if positive else None,
            "all_selected_facts_retrieved": True if positive else None,
            "model_raw_lean_term": "CertifiedPath.refl" if positive else None,
            "plan": {"plan_id": "sha256:plan"} if positive else None,
        }
        rows.append(row)
    return rows


def test_stage_g_report_thresholds_require_all_seven_fresh_cases_and_one_lean() -> None:
    rows = valid_report_rows()
    summary = build_stage_g_summary(
        rows,
        lean_process_count=1,
        lean_ok=True,
        lean_started_after_all_model_tasks=True,
        model_task_count_at_lean_start=7,
        artifact_sha256="d" * 64,
        accepted_positive_case_count=3,
        assert_standard_axioms_count=1,
    )
    assert summary["all_stage_g_thresholds_met"] is True
    assert summary["fresh_real_api_case_count"] == 7
    assert summary["positive_lean_verified"] == 3
    assert summary["negative_correctly_rejected"] == 4
    assert summary["prompt_cache_hit_tokens"] == 42
    assert summary["prompt_cache_miss_tokens"] == 28

    broken = deepcopy(rows)
    broken[0]["selected_evidence_from_search"] = False
    broken[1]["model_rounds"][0]["usage"].pop("prompt_cache_hit_tokens")
    rejected = build_stage_g_summary(
        broken,
        lean_process_count=1,
        lean_ok=True,
        lean_started_after_all_model_tasks=True,
        model_task_count_at_lean_start=7,
        artifact_sha256="d" * 64,
        accepted_positive_case_count=3,
        assert_standard_axioms_count=1,
    )
    assert rejected["all_stage_g_thresholds_met"] is False
    assert rejected["contract_error_count"] >= 2
    assert any(
        "selected_evidence_from_search" in error
        for error in rejected["contract_errors"]
    )
    assert any(
        "prompt_cache_hit_tokens" in error
        for error in rejected["contract_errors"]
    )


def test_stage_g_contract_gates_exact_ids_axiom_count_and_negative_semantics() -> None:
    def summarize(rows, *, axiom_count: int = 1):
        return build_stage_g_summary(
            rows,
            lean_process_count=1,
            lean_ok=True,
            lean_started_after_all_model_tasks=True,
            model_task_count_at_lean_start=7,
            artifact_sha256="d" * 64,
            accepted_positive_case_count=3,
            assert_standard_axioms_count=axiom_count,
        )

    rows = valid_report_rows()
    audits = {
        row["id"]: negative_semantic_audit(row)
        for row in rows
        if row["expected_status"] == "BLOCKED"
    }
    assert all(audit["ok"] for audit in audits.values())
    assert all(
        audit["forward_metric_source"]
        == "unique_policy_route_allowed_targets"
        for audit in audits.values()
    )

    duplicate = deepcopy(rows)
    duplicate[-1]["id"] = duplicate[0]["id"]
    duplicate_summary = summarize(duplicate)
    assert duplicate_summary["all_stage_g_thresholds_met"] is False
    assert any(
        "duplicate case IDs" in error
        for error in duplicate_summary["contract_errors"]
    )

    no_axiom = summarize(deepcopy(rows), axiom_count=0)
    assert no_axiom["all_stage_g_thresholds_met"] is False
    assert any("exactly one axiom gate" in error for error in no_axiom["contract_errors"])

    no_eligible_broken = deepcopy(rows)
    no_eligible_row = next(
        row
        for row in no_eligible_broken
        if row["expected_failure_code"] == "no_eligible_hardness_target"
    )
    no_eligible_row["candidate_metrics"]["unique_eligible_target_evidences"] = 1
    assert any(
        "no-eligible negative returned eligible" in error
        for error in summarize(no_eligible_broken)["contract_errors"]
    )

    no_route_broken = deepcopy(rows)
    no_route_row = next(
        row
        for row in no_route_broken
        if row["id"] == "open-target-graph-no-route"
    )
    no_route_row["candidate_metrics"]["unique_policy_route_allowed_targets"] = 1
    assert any(
        "policy-allowed forward target" in error
        for error in summarize(no_route_broken)["contract_errors"]
    )

    reverse_broken = deepcopy(rows)
    reverse_row = next(
        row
        for row in reverse_broken
        if row["id"] == "open-target-exact-cover-reverse-only"
    )
    reverse_row["candidate_metrics"]["unique_reverse_route_targets"] = 0
    assert any(
        "has no recorded reverse route" in error
        for error in summarize(reverse_broken)["contract_errors"]
    )

    fallback = deepcopy(rows)
    fallback_row = next(
        row for row in fallback if row["id"] == "open-target-graph-no-route"
    )
    fallback_row["candidate_metrics"].pop("unique_policy_route_allowed_targets")
    fallback_summary = summarize(fallback)
    assert fallback_summary["all_stage_g_thresholds_met"] is True
    assert fallback_summary["negative_semantic_fallback_case_count"] == 1
    assert fallback_summary["negative_semantic_forward_metric_sources"][
        "open-target-graph-no-route"
    ] == "unique_reachable_eligible_targets"
