"""H-E inventory-backed held-out qualification through the production orchestrator."""

from __future__ import annotations

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping

from .model_client import DeepSeekConfig
from .np_hard_authoring import NPHardAuthoringTaskV2
from .np_hard_input import NPHardInputError
from .np_hard_inventory import build_np_hard_library_inventory
from .np_hard_orchestrator import NPHardOrchestratorConfigV2, NPHardOrchestratorV2
from .np_hard_release_benchmark import (
    _endpoint_mutation_rejected,
    _fresh,
    _relative,
    _secret_absent,
    _source_fingerprint,
    _token_usage,
)


NP_HARD_H_E_REPORT_SCHEMA_V1 = "hardness_np_hard_h_e_heldout_report_v1"
SUITE_SCHEMA = "hardness_np_hard_h_e_input_suite_v1"
ORACLE_SCHEMA = "hardness_np_hard_h_e_evaluation_oracle_v1"
SUITE_CASE_FIELDS = {"id", "module", "problem", "family"}
FORBIDDEN_SUITE_KEYS = {
    "expected",
    "expected_status",
    "failure_code",
    "gold",
    "gap_nodes",
    "task_class",
    "authoring_policy",
    "requires_model",
    "validation_mode",
}
EXISTING_MODEL_AUTHORING_PROBLEMS = {
    "Benchmark.Hardness.Inputs.NPHardMVP.ModelAuthoredTaggedThreeSAT.source",
    "Benchmark.Hardness.Inputs.NPHardGeneralization.GraphProofOnly.source",
    "Benchmark.Hardness.Inputs.NPHardGeneralization.SetSystemProgramComposition.source",
    "Benchmark.Hardness.Inputs.NPHardGeneralization.NumericProgramComposition.source",
    "Benchmark.Hardness.Inputs.NPHardGeneralization.GraphProgramSynthesis.source",
}


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def _load_suite(path: Path) -> tuple[dict[str, Any], ...]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if value.get("schema_version") != SUITE_SCHEMA:
        raise ValueError("unsupported H-E held-out input suite")
    cases = value.get("cases")
    if not isinstance(cases, list) or len(cases) != 12:
        raise ValueError("H-E held-out input suite must contain exactly 12 inputs")
    normalized: list[dict[str, Any]] = []
    seen: set[str] = set()
    for case in cases:
        if not isinstance(case, dict) or set(case) != SUITE_CASE_FIELDS:
            raise ValueError("H-E suite case contains task-answer metadata")
        if FORBIDDEN_SUITE_KEYS.intersection(case):
            raise ValueError("H-E suite contains a forbidden answer key")
        if case["id"] in seen:
            raise ValueError("H-E suite contains a duplicate case ID")
        seen.add(case["id"])
        normalized.append(case)
    return tuple(normalized)


def _load_oracle(path: Path, case_ids: set[str]) -> dict[str, dict[str, Any]]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if value.get("schema_version") != ORACLE_SCHEMA:
        raise ValueError("unsupported H-E evaluation oracle")
    cases = value.get("cases")
    if not isinstance(cases, list):
        raise ValueError("H-E evaluation oracle has no cases")
    oracle = {case["id"]: case for case in cases}
    if set(oracle) != case_ids or len(oracle) != len(cases):
        raise ValueError("H-E oracle and input suite case IDs differ")
    return oracle


def _failure_code(payload: Mapping[str, Any]) -> str | None:
    value = payload.get("failure_code")
    return str(value) if value else None


def run_np_hard_h_e_heldout(
    *,
    root: Path,
    suite_path: Path,
    oracle_path: Path,
    output_root: Path,
    report_path: Path,
    inventory_path: Path,
    deepseek: DeepSeekConfig,
    model_client: Any | None = None,
) -> dict[str, Any]:
    root = root.resolve()
    output_root = output_root.resolve()
    _fresh(output_root)
    cases = _load_suite(suite_path.resolve())
    oracle = _load_oracle(oracle_path.resolve(), {case["id"] for case in cases})
    rows: list[dict[str, Any]] = []
    qualification: dict[str, dict[str, Any]] = {}
    for case in cases:
        expected = oracle[case["id"]]
        if expected["validation_mode"] == "endpoint_mutation_audit":
            matched = _endpoint_mutation_rejected(
                root=root,
                suite_path=root / "Benchmark/Hardness/Suites/np_hard_generalization.json",
            )
            row = {
                "case_id": case["id"],
                "family": case["family"],
                "module": case["module"],
                "problem": case["problem"],
                "status": "BLOCKED" if matched else "FAILED",
                "failure_code": "candidate_wrong_endpoint" if matched else "mutation_audit_failed",
                "validation_mode": "endpoint_mutation_audit",
                "model_calls": 0,
                "task_class": None,
                "gap_count": 0,
                "matched": matched,
                "result": {"mutation_rejected": matched},
            }
            rows.append(row)
            qualification[case["id"]] = row
            continue
        try:
            result = NPHardOrchestratorV2(
                NPHardOrchestratorConfigV2(
                    root=root,
                    input_module=case["module"],
                    problem_declaration=case["problem"],
                    output_dir=output_root / "cases" / case["id"],
                    lean_timeout_seconds=600,
                    authoring_policy="model-auto",
                    attempt_budget=4,
                    call_budget=8,
                    deepseek=deepseek,
                ),
                model_client=model_client,
            ).run()
            payload = result.to_dict()
            status = result.status
            failure_code = result.failure_code
            model_calls = result.model_calls
        except NPHardInputError as error:
            payload = {
                "status": "BLOCKED",
                "failure_code": error.code,
                "explanation": error.message,
                "candidates": list(error.candidates),
                "model_call_ledger": [],
            }
            status = "BLOCKED"
            failure_code = error.code
            model_calls = 0
        task_payload = payload.get("capability_dag")
        task = (
            NPHardAuthoringTaskV2.from_dict(task_payload)
            if isinstance(task_payload, Mapping)
            else None
        )
        authoring_executed = payload.get("authoring_runtime") is not None
        task_class = task.task_class if task is not None and authoring_executed else None
        gap_count = len(task.gap_nodes) if task is not None and authoring_executed else 0
        ledger = list(payload.get("model_call_ledger") or [])
        requires_model = bool(expected["requires_model"])
        input_identity = payload.get("input_identity") or {}
        canonical_problem = input_identity.get("canonical_problem")
        artifact = payload.get("artifact") or {}
        replay = payload.get("independent_replay") or {}
        axiom = payload.get("axiom_audit") or {}
        deletion = payload.get("deletion_audit") or {}
        runtime = payload.get("authoring_runtime") or {}
        worker_fallback_count = sum(
            bool(item.get("fallback_used"))
            for item in runtime.get("worker_results", [])
        )
        verified_audits = (
            status != "VERIFIED"
            or (
                artifact.get("endpoint") == canonical_problem
                and replay.get("passed") is True
                and axiom.get("passed") is True
                and (
                    deletion.get("passed") is True
                    if requires_model
                    else payload.get("deletion_audit") is None
                )
            )
        )
        model_matched = (
            model_calls > 0
            and len(ledger) == model_calls
            and all(
                call.get("called")
                and call.get("ok")
                and call.get("status_code") == 200
                for call in ledger
            )
            if requires_model
            else model_calls == 0 and not ledger
        )
        matched = (
            status == expected["status"]
            and failure_code == expected["failure_code"]
            and task_class == expected["task_class"]
            and gap_count == expected["gap_count"]
            and model_matched
            and verified_audits
            and worker_fallback_count == 0
        )
        row = {
            "case_id": case["id"],
            "family": case["family"],
            "module": case["module"],
            "problem": case["problem"],
            "status": status,
            "failure_code": failure_code,
            "validation_mode": "production_entry",
            "model_calls": model_calls,
            "task_class": task_class,
            "gap_count": gap_count,
            "canonical_problem": canonical_problem,
            "worker_fallback_count": worker_fallback_count,
            "token_usage": _token_usage(ledger),
            "matched": matched,
            "result": payload,
        }
        rows.append(row)
        qualification[case["id"]] = row

    inventory = build_np_hard_library_inventory(
        root=root,
        report_path=inventory_path,
        suite_path=suite_path,
        oracle_path=oracle_path,
        qualification_cases=qualification,
    )
    positives = [row for row in rows if oracle[row["case_id"]]["status"] == "VERIFIED"]
    negatives = [row for row in rows if oracle[row["case_id"]]["status"] == "BLOCKED"]
    authoring = [row for row in positives if oracle[row["case_id"]]["requires_model"]]
    existing = [row for row in positives if not oracle[row["case_id"]]["requires_model"]]
    distinct_canonical = {row["canonical_problem"] for row in positives}
    outside_existing_authoring_samples = sum(
        row["problem"] not in EXISTING_MODEL_AUTHORING_PROBLEMS for row in positives
    )
    metrics = {
        "suite_case_count": len(rows),
        "positive_case_count": len(positives),
        "positive_verified_count": sum(row["matched"] for row in positives),
        "negative_case_count": len(negatives),
        "negative_matched_count": sum(row["matched"] for row in negatives),
        "family_count": len({row["family"] for row in positives}),
        "distinct_positive_endpoint_count": len(distinct_canonical),
        "outside_existing_five_authoring_sample_count": outside_existing_authoring_samples,
        "authoring_problem_count": len(authoring),
        "authoring_verified_count": sum(row["matched"] for row in authoring),
        "existing_route_count": len(existing),
        "existing_route_model_calls": sum(row["model_calls"] for row in existing),
        "structural_negative_model_calls": sum(row["model_calls"] for row in negatives),
        "real_api_calls": sum(row["model_calls"] for row in rows),
        "token_usage": _token_usage(
            [
                call
                for row in rows
                for call in (row.get("result", {}).get("model_call_ledger") or [])
            ]
        ),
        "independent_replay_count": sum(
            (row["result"].get("independent_replay") or {}).get("passed") is True
            for row in positives
        ),
        "standard_axiom_audit_count": sum(
            (row["result"].get("axiom_audit") or {}).get("passed") is True
            for row in positives
        ),
        "endpoint_equality_audit_count": sum(
            (row["result"].get("artifact") or {}).get("endpoint")
            == row["canonical_problem"]
            for row in positives
        ),
        "deletion_audit_problem_count": sum(
            (row["result"].get("deletion_audit") or {}).get("passed") is True
            for row in authoring
        ),
        "deletion_audit_node_count": sum(
            (row["result"].get("deletion_audit") or {}).get("node_count", 0)
            for row in authoring
        ),
        "fresh_core_rediscovery_count": sum(
            (row["result"].get("fresh_core") or {}).get("count", 0)
            for row in positives
        ),
        "worker_fallback_count": sum(row.get("worker_fallback_count", 0) for row in rows),
        "inventory_module_count": inventory["module_count"],
        "inventory_presented_problem_count": inventory["presented_problem_count"],
        "inventory_unique_problem_identity_count": inventory[
            "unique_problem_identity_count"
        ],
        "inventory_known_forward_route_count": inventory["known_forward_route_count"],
    }
    task_classes = {row["task_class"] for row in authoring}
    passed = (
        model_client is None
        and deepseek.api_key is not None
        and len(positives) == metrics["positive_verified_count"] == 8
        and len(negatives) == metrics["negative_matched_count"] == 4
        and metrics["family_count"] >= 4
        and metrics["distinct_positive_endpoint_count"] == 8
        and metrics["outside_existing_five_authoring_sample_count"] >= 4
        and len(authoring) == metrics["authoring_verified_count"] == 4
        and metrics["existing_route_model_calls"] == 0
        and metrics["structural_negative_model_calls"] == 0
        and sum(row["gap_count"] for row in authoring)
        <= metrics["real_api_calls"]
        <= 8 * len(authoring)
        and metrics["independent_replay_count"] == 8
        and metrics["standard_axiom_audit_count"] == 8
        and metrics["endpoint_equality_audit_count"] == 8
        and metrics["deletion_audit_problem_count"] == 4
        and metrics["deletion_audit_node_count"]
        == sum(row["gap_count"] for row in authoring)
        and metrics["worker_fallback_count"] == 0
        and {"semantic_proof", "program_composition", "program_synthesis"}.issubset(
            task_classes
        )
        and any(row["gap_count"] == 1 for row in authoring)
        and any(row["gap_count"] > 1 for row in authoring)
        and inventory["source_imports_forbidden_count"] == 0
        and _secret_absent(output_root, deepseek.api_key)
    )
    report = {
        "schema_version": NP_HARD_H_E_REPORT_SCHEMA_V1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "H-E-inventory-heldout-production-entrypoint",
        "passed": passed,
        "suite": {
            "file": _relative(suite_path, root),
            "contains_task_answer_metadata": False,
            "case_count": len(cases),
        },
        "oracle": {
            "file": _relative(oracle_path, root),
            "passed_to_production_orchestrator": False,
        },
        "model": deepseek.to_public_dict(),
        "metrics": metrics,
        "task_classes": sorted(task_classes),
        "inventory": {
            "file": _relative(inventory_path, root),
            "inventory_id": inventory["inventory_id"],
            "problem_catalog_id": inventory["problem_catalog_id"],
            "connection_catalog_id": inventory["connection_catalog_id"],
            "target_catalog_id": inventory["target_catalog_id"],
        },
        "cases": rows,
        "source_fingerprint": _source_fingerprint(root),
        "security": {
            "secret_absent": _secret_absent(output_root, deepseek.api_key),
            "fixture_model_used": model_client is not None,
            "cached_or_recorded_response_used": False,
            "hidden_or_gold_import_count": 0,
            "oracle_passed_to_orchestrator": False,
        },
    }
    _write_json(report_path, report)
    _write_json(output_root / "report.json", report)
    return report
