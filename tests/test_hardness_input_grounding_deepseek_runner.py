import json
from copy import deepcopy
from pathlib import Path

import pytest

from agent.hardness.benchmark import load_benchmark_suite
from agent.hardness.catalog import build_all_catalogs
from agent.hardness.input_grounding import validate_representation_comparison_suite
from agent.hardness.model_client import ModelResponse
from agent.hardness.models import TypedInventoryEntry
from scripts.run_deepseek_input_grounding_benchmark import (
    ReplayModelClient,
    STAGE_F_REQUIRED_CASE_INTEGER_METRICS,
    STAGE_F_REQUIRED_USAGE_METRICS,
    aggregate_usage,
    build_representation_comparison_metrics,
    counterbalanced_representation_cases,
    prepare_fresh_output_root,
    representation_catalog_scope,
    sha256_text,
    submitted_model_term,
    validate_representation_comparison_report_contract,
)


ROOT = Path(__file__).resolve().parents[1]
COMPARISON_SUITE = (
    ROOT
    / "Benchmark"
    / "Hardness"
    / "Suites"
    / "input_grounding_representation_comparison.json"
)


def model_response(content: str) -> ModelResponse:
    return ModelResponse(
        called=True,
        ok=True,
        content=content,
        error=None,
        status_code=200,
        duration_seconds=0.1,
        usage={"prompt_tokens": 10, "total_tokens": 12},
        attempts=1,
        finish_reason="stop",
    )


def test_submitted_model_term_preserves_the_raw_finish_field() -> None:
    raw_term = "  ComplexityReduction.Certificate.CertifiedPath.step X.y  "
    response = model_response(
        json.dumps({"finish": {"lean_term": raw_term}}, ensure_ascii=False)
    )
    assert submitted_model_term((response,)) == raw_term


def test_replay_requires_both_current_prompt_and_raw_response_hashes() -> None:
    prompt = '{"task":"example"}'
    system = "system"
    content = '{"action":"stop"}'
    rounds = [
        {
            "system_sha256": sha256_text(system),
            "prompt_sha256": sha256_text(prompt),
            "response_sha256": sha256_text(content),
            "response_content": content,
            "status_code": 200,
            "usage": {"total_tokens": 5},
            "finish_reason": "stop",
        }
    ]
    client = ReplayModelClient(rounds)
    response = client.complete_json(system=system, prompt=prompt)
    assert response.ok is True
    assert response.called is False
    assert response.content == content

    stale = ReplayModelClient(rounds)
    rejected = stale.complete_json(system=system, prompt='{"task":"changed"}')
    assert rejected.ok is False
    assert "prompt hash" in (rejected.error or "")


def test_fresh_output_root_never_implicitly_reuses_existing_files(tmp_path) -> None:
    output = tmp_path / "fresh"
    prepare_fresh_output_root(output)
    (output / "old-report.json").write_text("{}", encoding="utf-8")
    with pytest.raises(ValueError, match="not empty"):
        prepare_fresh_output_root(output)


def test_usage_aggregation_keeps_deepseek_cache_counters() -> None:
    assert aggregate_usage(
        (
            {
                "prompt_tokens": 10,
                "completion_tokens": 2,
                "prompt_cache_hit_tokens": 6,
            },
            {
                "prompt_tokens": 4,
                "completion_tokens": 1,
                "prompt_cache_hit_tokens": 3,
                "prompt_cache_miss_tokens": 1,
            },
        )
    ) == {
        "completion_tokens": 3,
        "prompt_cache_hit_tokens": 9,
        "prompt_cache_miss_tokens": 1,
        "prompt_tokens": 14,
    }


def test_representation_metrics_keep_family_interfaces_and_declaration_reuse() -> None:
    rows = []
    for mode, role, declaration in (
        ("flat_api", "finalComposition", "Routes.flat"),
        ("component_catalog", "ingress", "Routes.ingress"),
    ):
        for form in ("direct", "abbrev"):
            rows.append(
                {
                    "id": f"{mode}-{form}",
                    "comparison_group_id": form,
                    "matched_pair_id": form,
                    "study_family": "graph",
                    "family_id": "graph-source",
                    "source_form_id": form,
                    "catalog_mode": mode,
                    "final_status": "VERIFIED",
                    "retrieved_ingress_count": int(role == "ingress"),
                    "selected_ingress_count": int(role == "ingress"),
                    "selected_shared_gadget_count": int(mode == "component_catalog"),
                    "selected_final_facade_count": int(role == "finalComposition"),
                    "independent_lean_adapter_count": int(role == "ingress"),
                    "specialized_lean_interface_count": 1,
                    "selected_reduction_declarations": [declaration],
                    "selected_reduction_roles": {
                        "route_atom_count": 1,
                        "declarations": {role: [declaration]},
                    },
                    "query_round_count": 2,
                    "prompt_characters": 100,
                    "usage": {"total_tokens": 10},
                }
            )

    metrics = build_representation_comparison_metrics(
        rows, python_rule_counts_by_family={"graph": 0}
    )
    assert metrics["matched_comparison_count"] == 2
    assert metrics["both_lean_verified_count"] == 2
    assert metrics["families"][0]["study_family"] == "graph"
    assert (
        metrics["families"][0]["flat_api_unique_specialized_interface_count"]
        == 1
    )
    assert (
        metrics["families"][0][
            "component_catalog_unique_specialized_interface_count"
        ]
        == 1
    )
    assert metrics["selected_declaration_reuse_by_mode"]["flat_api"][
        "shared_reuse_occurrences_beyond_first"
    ] == 1


def test_stage_f_execution_order_is_counterbalanced() -> None:
    cases = validate_representation_comparison_suite(
        load_benchmark_suite(COMPARISON_SUITE)
    )
    ordered = counterbalanced_representation_cases(cases)
    first_modes = [ordered[index].catalog_mode for index in range(0, len(ordered), 2)]
    assert first_modes.count("flat_api") == 9
    assert first_modes.count("component_catalog") == 9
    for index in range(0, len(ordered), 2):
        pair = ordered[index : index + 2]
        assert pair[0].comparison_group_id == pair[1].comparison_group_id
        assert {case.catalog_mode for case in pair} == {
            "flat_api",
            "component_catalog",
        }


def test_component_catalog_scope_is_a_strict_flat_superset() -> None:
    def entry(declaration: str, role: str, *, final: bool = False) -> TypedInventoryEntry:
        return TypedInventoryEntry(
            declaration=declaration,
            capability_kind="certified_reduction",
            component_role=role,
            source_fingerprint=f"source:{declaration}",
            target_fingerprint=f"target:{declaration}",
            is_final_facade=final,
            discovery="registered",
            registry_fingerprint="registry",
        )

    catalogs = build_all_catalogs(
        (
            entry("Route.flat", "finalComposition", final=True),
            entry("Route.direct", "unannotated"),
            entry("Route.ingress", "ingress"),
            entry("Route.shared", "sharedGadget"),
        ),
        registry_fingerprint="registry",
    )
    scope = representation_catalog_scope(catalogs)
    assert scope["baseline_is_subset_of_component"] is True
    assert scope["baseline_entry_count"] == 2
    assert scope["component_entry_count"] == 4
    assert scope["component_only_role_counts"] == {
        "ingress": 1,
        "sharedGadget": 1,
    }


def _valid_stage_f_contract_fixture() -> tuple[
    list[dict], dict, dict, dict
]:
    usage = {
        "prompt_tokens": 10,
        "completion_tokens": 2,
        "total_tokens": 12,
        "prompt_cache_hit_tokens": 6,
        "prompt_cache_miss_tokens": 4,
    }
    rows: list[dict] = []
    families = ("graph", "clause_csp", "incidence")
    for pair_index in range(18):
        family = families[pair_index // 6]
        for mode in ("flat_api", "component_catalog"):
            role = "finalComposition" if mode == "flat_api" else "ingress"
            declaration = f"Routes.{mode}.{pair_index}"
            rows.append(
                {
                    "id": f"case-{pair_index}-{mode}",
                    "comparison_group_id": f"pair-{pair_index}",
                    "matched_pair_id": f"pair-{pair_index}",
                    "study_family": family,
                    "family_id": f"logical-{pair_index}",
                    "source_form_id": f"form-{pair_index}",
                    "catalog_mode": mode,
                    "final_status": "VERIFIED",
                    "retrieved_ingress_count": int(role == "ingress"),
                    "selected_ingress_count": int(role == "ingress"),
                    "selected_shared_gadget_count": 0,
                    "selected_final_facade_count": int(
                        role == "finalComposition"
                    ),
                    "independent_lean_adapter_count": int(role == "ingress"),
                    "specialized_lean_interface_count": 1,
                    "selected_reduction_declarations": [declaration],
                    "selected_reduction_roles": {
                        "counts": {role: 1},
                        "route_atom_count": 1,
                        "declarations": {role: [declaration]},
                    },
                    "query_round_count": 2,
                    "model_turn_count": 1,
                    "prompt_characters": 100,
                    "external_api_calls_this_run": 1,
                    "http_ok_count_this_run": 1,
                    "http_request_attempts_this_run": 1,
                    "usage": dict(usage),
                    "model_rounds": [
                        {
                            "called": True,
                            "http_ok": True,
                            "replayed": False,
                            "usage": dict(usage),
                        }
                    ],
                    "called_this_run": True,
                    "replayed_from_resume": False,
                }
            )
    audit = {
        "python_family_specific_rule_count": 0,
        "families": [
            {
                "study_family": family,
                "python_family_specific_rule_count": 0,
            }
            for family in families
        ],
    }
    metrics = build_representation_comparison_metrics(
        rows,
        python_rule_counts_by_family={family: 0 for family in families},
    )
    scope = {"baseline_is_subset_of_component": True}
    return rows, metrics, audit, scope


def test_stage_f_report_contract_accepts_complete_metrics() -> None:
    rows, metrics, audit, scope = _valid_stage_f_contract_fixture()
    assert validate_representation_comparison_report_contract(
        rows,
        comparison_metrics=metrics,
        python_rule_audit=audit,
        catalog_scope=scope,
    ) == ()


@pytest.mark.parametrize("field", STAGE_F_REQUIRED_CASE_INTEGER_METRICS)
def test_stage_f_report_contract_rejects_missing_case_metric(field: str) -> None:
    rows, metrics, audit, scope = _valid_stage_f_contract_fixture()
    damaged = deepcopy(rows)
    damaged[0].pop(field)
    errors = validate_representation_comparison_report_contract(
        damaged,
        comparison_metrics=metrics,
        python_rule_audit=audit,
        catalog_scope=scope,
    )
    assert any(field in error for error in errors)


@pytest.mark.parametrize("field", STAGE_F_REQUIRED_USAGE_METRICS)
def test_stage_f_report_contract_rejects_missing_round_usage(field: str) -> None:
    rows, metrics, audit, scope = _valid_stage_f_contract_fixture()
    damaged = deepcopy(rows)
    damaged[0]["model_rounds"][0]["usage"].pop(field)
    errors = validate_representation_comparison_report_contract(
        damaged,
        comparison_metrics=metrics,
        python_rule_audit=audit,
        catalog_scope=scope,
    )
    assert any(f"usage.{field}" in error for error in errors)
