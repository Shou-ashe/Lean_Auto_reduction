"""H-F: answer-free qualification held-out through the production orchestrator.

Every case is a real public ``ComplexityReduction.*`` canonical identity; the
input suite carries no expected, task-class, gap, gold, or authoring policy.
The evaluation oracle lives in a separate file and is never imported, prompted,
or passed to the production orchestrator.
"""

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
from .np_hard_target_matrix import (
    load_np_hard_target_matrix,
    update_np_hard_target_matrix_production_results,
)
from .np_hard_release_benchmark import (
    _endpoint_mutation_rejected,
    _fresh,
    _relative,
    _secret_absent,
    _source_fingerprint,
    _token_usage,
)


NP_HARD_H_F_REPORT_SCHEMA_V1 = "hardness_np_hard_h_f_qualification_heldout_report_v1"
SUITE_SCHEMA = "hardness_np_hard_h_f_qualification_input_suite_v1"
ORACLE_SCHEMA = "hardness_np_hard_h_f_qualification_evaluation_oracle_v1"
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


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def _load_suite(path: Path, *, minimum_cases: int = 12) -> tuple[dict[str, Any], ...]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if value.get("schema_version") != SUITE_SCHEMA:
        raise ValueError("unsupported H-F qualification input suite")
    cases = value.get("cases")
    if not isinstance(cases, list) or len(cases) < minimum_cases:
        raise ValueError(
            f"H-F qualification suite must contain at least {minimum_cases} inputs"
        )
    normalized: list[dict[str, Any]] = []
    seen: set[str] = set()
    for case in cases:
        if not isinstance(case, dict) or set(case) != SUITE_CASE_FIELDS:
            raise ValueError("H-F suite case contains task-answer metadata")
        if FORBIDDEN_SUITE_KEYS.intersection(case):
            raise ValueError("H-F suite contains a forbidden answer key")
        if case["id"] in seen:
            raise ValueError("H-F suite contains a duplicate case ID")
        if not case["module"].startswith("ComplexityReduction."):
            raise ValueError("H-F suite case is outside the public ComplexityReduction scope")
        seen.add(case["id"])
        normalized.append(case)
    return tuple(normalized)


def _load_oracle(path: Path, case_ids: set[str]) -> dict[str, dict[str, Any]]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if value.get("schema_version") != ORACLE_SCHEMA:
        raise ValueError("unsupported H-F evaluation oracle")
    cases = value.get("cases")
    if not isinstance(cases, list):
        raise ValueError("H-F evaluation oracle has no cases")
    oracle = {case["id"]: case for case in cases}
    if set(oracle) != case_ids or len(oracle) != len(cases):
        raise ValueError("H-F oracle and input suite case IDs differ")
    return oracle


def _failure_code(payload: Mapping[str, Any]) -> str | None:
    value = payload.get("failure_code")
    return str(value) if value else None


def run_np_hard_h_f_qualification_heldout(
    *,
    root: Path,
    suite_path: Path,
    oracle_path: Path,
    output_root: Path,
    report_path: Path,
    inventory_path: Path,
    matrix_path: Path,
    deepseek: DeepSeekConfig,
    model_client: Any | None = None,
    publish_matrix: bool = False,
) -> dict[str, Any]:
    root = root.resolve()
    output_root = output_root.resolve()
    _fresh(output_root)
    cases = _load_suite(suite_path.resolve())
    oracle = _load_oracle(oracle_path.resolve(), {case["id"] for case in cases})
    rows: list[dict[str, Any]] = []
    for case in cases:
        expected = oracle[case["id"]]
        if expected["validation_mode"] == "endpoint_mutation_audit":
            matched = _endpoint_mutation_rejected(
                root=root,
                suite_path=root / "Gate/Suites/np_hard_generalization.json",
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
                    call_budget=None,
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
        expected_requires_model = bool(expected["requires_model"])
        verified_audits = (
            status != "VERIFIED"
            or (
                artifact.get("endpoint") == canonical_problem
                and replay.get("passed") is True
                and axiom.get("passed") is True
                and (
                    deletion.get("passed") is True
                    if expected_requires_model
                    else payload.get("deletion_audit") is None
                )
            )
        )
        model_matched = (
            (
                model_calls > 0
                and len(ledger) == model_calls
                and all(
                    call.get("called")
                    and call.get("ok")
                    and call.get("status_code") == 200
                    for call in ledger
                )
            )
            if expected_requires_model
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

    effective_matrix_path = matrix_path.resolve()
    if not publish_matrix:
        effective_matrix_path = output_root / "NP_HARD_TARGET_MATRIX.json"
        _write_json(
            effective_matrix_path,
            load_np_hard_target_matrix(matrix_path.resolve()),
        )
    qualified_matrix = update_np_hard_target_matrix_production_results(
        matrix_path=effective_matrix_path,
        production_rows=rows,
    )
    inventory = build_np_hard_library_inventory(
        root=root,
        report_path=inventory_path,
        matrix_path=effective_matrix_path,
    )
    positives = [row for row in rows if oracle[row["case_id"]]["status"] == "VERIFIED"]
    negatives = [row for row in rows if oracle[row["case_id"]]["status"] == "BLOCKED"]
    authoring = [row for row in positives if oracle[row["case_id"]]["requires_model"]]
    existing = [row for row in positives if not oracle[row["case_id"]]["requires_model"]]
    distinct_canonical = {row["canonical_problem"] for row in positives}
    metrics = {
        "suite_case_count": len(rows),
        "positive_case_count": len(positives),
        "positive_verified_count": sum(row["matched"] for row in positives),
        "negative_case_count": len(negatives),
        "negative_matched_count": sum(row["matched"] for row in negatives),
        "family_count": len({row["family"] for row in positives}),
        "distinct_positive_endpoint_count": len(distinct_canonical),
        "authoring_problem_count": len(authoring),
        "authoring_verified_count": sum(row["matched"] for row in authoring),
        "existing_route_count": len(existing),
        "existing_route_model_calls": sum(row["model_calls"] for row in existing),
        "structural_negative_model_calls": sum(row["model_calls"] for row in negatives),
        "real_api_calls": sum(row["model_calls"] for row in rows),
        "http_ok_count": sum(
            call.get("called") and call.get("ok") and call.get("status_code") == 200
            for row in rows
            for call in (row.get("result", {}).get("model_call_ledger") or [])
        ),
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
        "inventory_known_forward_route_identity_count": inventory[
            "known_forward_route_identity_count"
        ],
        "matrix_identity_count": qualified_matrix["identity_count"],
        "matrix_in_scope_count": qualified_matrix["in_scope_count"],
        "matrix_auxiliary_count": qualified_matrix["auxiliary_count"],
        "matrix_blocked_count": qualified_matrix["blocked_count"],
        "matrix_unclassified_count": qualified_matrix["unclassified_count"],
        "matrix_production_entry_observed_identity_count": qualified_matrix[
            "production_entry_observed_identity_count"
        ],
        "matrix_production_entry_verified_identity_count": qualified_matrix[
            "production_entry_verified_identity_count"
        ],
    }
    task_classes = {row["task_class"] for row in authoring}
    formal_model_configuration = (
        deepseek.public_base_url == "https://api.deepseek.com"
        and deepseek.model == "deepseek-v4-flash"
        and deepseek.timeout_seconds == 300
        and deepseek.max_tokens == 16000
        and deepseek.max_retries == 0
        and deepseek.reasoning_effort == "low"
        and deepseek.temperature == 0
    )
    passed = (
        model_client is None
        and deepseek.api_key is not None
        and formal_model_configuration
        and len(rows) >= 12
        and metrics["positive_case_count"] == metrics["positive_verified_count"]
        and metrics["negative_case_count"] == metrics["negative_matched_count"]
        and metrics["family_count"] >= 5
        and metrics["distinct_positive_endpoint_count"] == len(positives)
        and metrics["existing_route_model_calls"] == 0
        and metrics["structural_negative_model_calls"] == 0
        and metrics["authoring_verified_count"] == metrics["authoring_problem_count"]
        and metrics["real_api_calls"] == metrics["http_ok_count"]
        and metrics["real_api_calls"] >= len(authoring)
        and metrics["worker_fallback_count"] == 0
        and metrics["independent_replay_count"] >= len(positives)
        and metrics["standard_axiom_audit_count"] >= len(positives)
        and metrics["endpoint_equality_audit_count"] >= len(positives)
        and metrics["deletion_audit_problem_count"] == len(authoring)
        and metrics["deletion_audit_node_count"]
        == sum(row["gap_count"] for row in authoring)
        and inventory["source_imports_forbidden_count"] == 0
        and inventory["target_matrix_unclassified_count"] == 0
        and inventory["identity_count"] == qualified_matrix["identity_count"]
        and qualified_matrix["unclassified_count"] == 0
        and _secret_absent(output_root, deepseek.api_key)
    )
    report = {
        "schema_version": NP_HARD_H_F_REPORT_SCHEMA_V1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "H-F-qualification-heldout-production-entrypoint",
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
        "formal_model_configuration": formal_model_configuration,
        "metrics": metrics,
        "task_classes": sorted(task_classes),
        "inventory": {
            "file": _relative(inventory_path, root),
            "inventory_id": inventory["inventory_id"],
            "target_matrix_id": inventory["target_matrix_id"],
            "target_matrix_file": _relative(effective_matrix_path, root),
            "target_matrix_published": publish_matrix,
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
