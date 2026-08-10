"""H-H identity-level production qualification for every existing public route."""

from __future__ import annotations

import json
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Mapping

from .lean_runner import sha256_file
from .models import sha256_id
from .np_hard_input import NPHardInputError, resolve_np_hard_input_reference
from .np_hard_orchestrator import NPHardOrchestratorConfigV2, NPHardOrchestratorV2
from .np_hard_target_matrix import (
    load_np_hard_target_matrix,
    update_np_hard_target_matrix_production_results,
)


PUBLIC_EXISTING_ROUTE_QUALIFICATION_SCHEMA_V1 = (
    "hardness_public_existing_route_qualification_v1"
)
PUBLIC_EXISTING_ROUTE_HELDOUT_SUITE_SCHEMA_V1 = (
    "hardness_public_existing_route_heldout_suite_v1"
)
HELDOUT_CASE_FIELDS = {"id", "module", "problem", "family"}


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def _fresh(path: Path) -> None:
    if path.exists() and any(path.iterdir()):
        raise ValueError(f"H-H output must be fresh and empty: {path}")
    path.mkdir(parents=True, exist_ok=True)


def load_public_existing_route_heldout_suite(
    path: Path,
) -> tuple[dict[str, str], ...]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if value.get("schema_version") != PUBLIC_EXISTING_ROUTE_HELDOUT_SUITE_SCHEMA_V1:
        raise ValueError("unsupported H-H held-out suite schema")
    cases = value.get("cases")
    if not isinstance(cases, list) or len(cases) < 12:
        raise ValueError("H-H held-out suite needs at least 12 public inputs")
    normalized: list[dict[str, str]] = []
    seen_ids: set[str] = set()
    seen_problems: set[str] = set()
    for case in cases:
        if not isinstance(case, dict) or set(case) != HELDOUT_CASE_FIELDS:
            raise ValueError("H-H held-out suite contains answer metadata")
        if not all(isinstance(case[key], str) and case[key] for key in HELDOUT_CASE_FIELDS):
            raise ValueError("H-H held-out case field is invalid")
        if not case["module"].startswith("ComplexityReduction."):
            raise ValueError("H-H held-out case is outside the public library")
        if case["id"] in seen_ids or case["problem"] in seen_problems:
            raise ValueError("H-H held-out suite repeats an ID or endpoint")
        seen_ids.add(case["id"])
        seen_problems.add(case["problem"])
        normalized.append(dict(case))
    return tuple(normalized)


def _inventory_identities(path: Path) -> dict[str, dict[str, Any]]:
    value = json.loads(path.read_text(encoding="utf-8"))
    identities = value.get("identities")
    if not isinstance(identities, list):
        raise ValueError("H-H inventory lacks identity records")
    return {str(row["identity_id"]): dict(row) for row in identities}


def _alias_check(
    *, root: Path, matrix_row: Mapping[str, Any], inventory_row: Mapping[str, Any]
) -> dict[str, Any]:
    canonical = str(matrix_row["canonical_declaration"])
    aliases = [
        member
        for member in inventory_row.get("members", [])
        if member.get("declaration") != canonical
    ]
    if not aliases:
        return {
            "checked": False,
            "passed": True,
            "reason": "canonical identity has no declaration alias",
        }
    alias = sorted(aliases, key=lambda item: str(item["declaration"]))[0]
    declaration = str(alias["declaration"])
    module = str(alias["module"])
    try:
        try:
            reference = resolve_np_hard_input_reference(
                root=root, input_module=module, requested_term=declaration
            )
        except (NPHardInputError, ValueError):
            reference = resolve_np_hard_input_reference(
                root=root, input_module=None, requested_term=declaration
            )
    except (NPHardInputError, ValueError) as error:
        return {
            "checked": True,
            "passed": False,
            "requested_alias": declaration,
            "input_module": module,
            "failure_code": getattr(error, "code", "alias_module_discovery_failed"),
            "explanation": getattr(error, "message", str(error)),
            "candidates": list(getattr(error, "candidates", ())),
        }
    candidates = {
        candidate.declaration: candidate
        for candidate in reference.normalization_observation.candidates
    }
    normalized = candidates.get(reference.problem_declaration)
    problem_node = normalized.problem_node if normalized is not None else None
    passed = problem_node == matrix_row["problem_node_id"]
    return {
        "checked": True,
        "passed": passed,
        "requested_alias": declaration,
        "input_module": reference.input_module,
        "resolved_problem": reference.problem_declaration,
        "resolved_canonical_problem": reference.canonical_problem,
        "normalization_kind": reference.normalization_kind,
        "problem_node_id": problem_node,
        "expected_problem_node_id": matrix_row["problem_node_id"],
        "candidate_count": len(reference.normalization_observation.candidates),
    }


def _qualify_one(
    *,
    root: Path,
    row: Mapping[str, Any],
    inventory_row: Mapping[str, Any],
    output_root: Path,
    lean_timeout_seconds: int,
    heldout_ids: Mapping[str, str],
) -> dict[str, Any]:
    identity_id = str(row["identity_id"])
    case_root = output_root / "identities" / identity_id.removeprefix("sha256:")
    try:
        result = NPHardOrchestratorV2(
            NPHardOrchestratorConfigV2(
                root=root,
                input_module=str(row["canonical_module"]),
                problem_declaration=str(row["canonical_declaration"]),
                output_dir=case_root,
                lean_timeout_seconds=lean_timeout_seconds,
                authoring_policy="disabled",
                attempt_budget=4,
                call_budget=0,
                deepseek=None,
            )
        ).run()
        payload = result.to_dict()
        status = result.status
        failure_code = result.failure_code
    except NPHardInputError as error:
        payload = {
            "status": "BLOCKED",
            "failure_code": error.code,
            "explanation": error.message,
            "model_call_ledger": [],
        }
        status = "BLOCKED"
        failure_code = error.code

    deterministic = payload.get("deterministic_result") or {}
    identity = payload.get("input_identity") or {}
    route = deterministic.get("route") or {}
    artifact = payload.get("artifact") or {}
    replay = payload.get("independent_replay") or {}
    axiom = payload.get("axiom_audit") or {}
    fresh_core = payload.get("fresh_core") or {}
    atoms = list(route.get("atoms") or [])
    roles = list(route.get("roles") or [])
    expected_length = int(row["shortest_forward_route_length"])
    endpoint_audit = {
        "passed": (
            identity.get("canonical_problem") == row["canonical_declaration"]
            and identity.get("canonical_problem_node") == row["problem_node_id"]
            and artifact.get("endpoint") == row["canonical_declaration"]
        ),
        "expected_problem": row["canonical_declaration"],
        "actual_problem": identity.get("canonical_problem"),
        "expected_problem_node_id": row["problem_node_id"],
        "actual_problem_node_id": identity.get("canonical_problem_node"),
        "artifact_endpoint": artifact.get("endpoint"),
    }
    route_audit = {
        "passed": (
            route.get("direction") == "hardness_seed_to_problem"
            and len(atoms) == len(roles) == expected_length
        ),
        "direction": route.get("direction"),
        "expected_length": expected_length,
        "actual_length": len(atoms),
        "atoms": atoms,
        "roles": roles,
        "composition_route": len(atoms) > 1,
        "representation_adapter": any(
            marker in value.lower()
            for value in [*atoms, *roles]
            for marker in ("adapter", "standardtm", "finalroute", "ingress")
        ),
    }
    alias_audit = _alias_check(
        root=root, matrix_row=row, inventory_row=inventory_row
    )
    model_calls = int(payload.get("model_calls") or 0)
    matched = (
        status == "VERIFIED"
        and failure_code is None
        and model_calls == 0
        and not payload.get("model_call_ledger")
        and replay.get("passed") is True
        and axiom.get("passed") is True
        and fresh_core.get("passed") is True
        and endpoint_audit["passed"]
        and route_audit["passed"]
        and alias_audit["passed"]
    )
    return {
        "identity_id": identity_id,
        "family": row["family"],
        "canonical_module": row["canonical_module"],
        "canonical_problem": row["canonical_declaration"],
        "member_count": row["member_count"],
        "heldout_case_id": heldout_ids.get(str(row["canonical_declaration"])),
        "status": status,
        "failure_code": failure_code,
        "model_calls": model_calls,
        "endpoint_audit": endpoint_audit,
        "route_audit": route_audit,
        "alias_normalization_audit": alias_audit,
        "independent_replay": replay,
        "axiom_audit": axiom,
        "fresh_core": fresh_core,
        "artifact": artifact,
        "matched": matched,
        "result": payload,
    }


def _source_fingerprint(root: Path, files: tuple[Path, ...]) -> dict[str, Any]:
    hashes = {
        str(path.resolve().relative_to(root)): "sha256:" + sha256_file(path)
        for path in files
    }
    return {"files": hashes, "combined_sha256": sha256_id(hashes)}


def run_public_existing_route_qualification(
    *,
    root: Path,
    matrix_path: Path,
    inventory_path: Path,
    heldout_suite_path: Path,
    output_root: Path,
    report_path: Path,
    lean_timeout_seconds: int = 900,
    jobs: int = 2,
    publish_matrix: bool = False,
) -> dict[str, Any]:
    root = root.resolve()
    output_root = output_root.resolve()
    _fresh(output_root)
    matrix = load_np_hard_target_matrix(matrix_path.resolve())
    inventory_by_id = _inventory_identities(inventory_path.resolve())
    existing = [
        dict(row)
        for row in matrix["identities"]
        if row.get("has_forward_certified_reduction_route") is True
    ]
    existing.sort(key=lambda row: str(row["canonical_declaration"]))
    if len(existing) != matrix["known_forward_route_identity_count"]:
        raise ValueError("H-H matrix existing-route identity count drifted")
    heldout = load_public_existing_route_heldout_suite(heldout_suite_path.resolve())
    by_problem = {str(row["canonical_declaration"]): row for row in existing}
    heldout_ids: dict[str, str] = {}
    for case in heldout:
        row = by_problem.get(case["problem"])
        if row is None or row["canonical_module"] != case["module"]:
            raise ValueError("H-H held-out endpoint is not an existing-route canonical identity")
        if row["family"] != case["family"]:
            raise ValueError("H-H held-out family drifted from the identity matrix")
        heldout_ids[case["problem"]] = case["id"]

    def qualify(row: Mapping[str, Any]) -> dict[str, Any]:
        inventory_row = inventory_by_id.get(str(row["identity_id"]))
        if inventory_row is None:
            raise ValueError("H-H inventory is missing a matrix identity")
        return _qualify_one(
            root=root,
            row=row,
            inventory_row=inventory_row,
            output_root=output_root,
            lean_timeout_seconds=lean_timeout_seconds,
            heldout_ids=heldout_ids,
        )

    rows: list[dict[str, Any]] = []
    if jobs <= 1:
        rows = [qualify(row) for row in existing]
    else:
        with ThreadPoolExecutor(max_workers=min(jobs, len(existing))) as executor:
            pending = {executor.submit(qualify, row) for row in existing}
            for future in as_completed(pending):
                rows.append(future.result())
        rows.sort(key=lambda row: row["canonical_problem"])

    heldout_rows = [row for row in rows if row["heldout_case_id"] is not None]
    route_lengths = {row["route_audit"]["actual_length"] for row in heldout_rows}
    expected_route_lengths = {
        int(row["shortest_forward_route_length"]) for row in existing
    }
    metrics = {
        "matrix_identity_count": matrix["identity_count"],
        "existing_route_identity_count": len(existing),
        "verified_identity_count": sum(row["matched"] for row in rows),
        "declaration_member_count": sum(int(row["member_count"]) for row in rows),
        "model_calls": sum(row["model_calls"] for row in rows),
        "independent_replay_count": sum(
            row["independent_replay"].get("passed") is True for row in rows
        ),
        "standard_axiom_audit_count": sum(
            row["axiom_audit"].get("passed") is True for row in rows
        ),
        "endpoint_equality_audit_count": sum(
            row["endpoint_audit"]["passed"] for row in rows
        ),
        "shortest_route_audit_count": sum(row["route_audit"]["passed"] for row in rows),
        "alias_normalization_audit_count": sum(
            row["alias_normalization_audit"]["checked"]
            and row["alias_normalization_audit"]["passed"]
            for row in rows
        ),
        "heldout_case_count": len(heldout_rows),
        "heldout_verified_count": sum(row["matched"] for row in heldout_rows),
        "heldout_family_count": len({row["family"] for row in heldout_rows}),
        "heldout_route_lengths": sorted(route_lengths),
        "maximum_existing_route_length": max(expected_route_lengths),
        "composition_route_count": sum(
            row["route_audit"]["composition_route"] for row in rows
        ),
        "representation_adapter_route_count": sum(
            row["route_audit"]["representation_adapter"] for row in rows
        ),
    }
    passed = (
        len(existing) > 0
        and metrics["verified_identity_count"] == len(existing)
        and metrics["model_calls"] == 0
        and metrics["independent_replay_count"] == len(existing)
        and metrics["standard_axiom_audit_count"] == len(existing)
        and metrics["endpoint_equality_audit_count"] == len(existing)
        and metrics["shortest_route_audit_count"] == len(existing)
        and metrics["heldout_case_count"] >= 12
        and metrics["heldout_verified_count"] == metrics["heldout_case_count"]
        and metrics["heldout_family_count"] >= 5
        and route_lengths == expected_route_lengths
        and metrics["composition_route_count"] > 0
        and metrics["representation_adapter_route_count"] > 0
    )
    effective_matrix_path = matrix_path.resolve()
    if publish_matrix:
        production_rows = [
            {
                "status": row["status"],
                "failure_code": row["failure_code"],
                "model_calls": row["model_calls"],
                "result": row["result"],
            }
            for row in rows
        ]
        matrix = update_np_hard_target_matrix_production_results(
            matrix_path=effective_matrix_path, production_rows=production_rows
        )
        # Keep the published declaration-level inventory content-addressed to
        # the newly qualified identity matrix.
        from .np_hard_inventory import build_np_hard_library_inventory

        build_np_hard_library_inventory(
            root=root,
            report_path=inventory_path.resolve(),
            matrix_path=effective_matrix_path,
            timeout_seconds=max(lean_timeout_seconds, 1800),
        )
    report = {
        "schema_version": PUBLIC_EXISTING_ROUTE_QUALIFICATION_SCHEMA_V1,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "stage": "H-H-public-existing-route-identity-production-qualification",
        "passed": passed,
        "matrix": {
            "file": str(matrix_path.resolve()),
            "matrix_id": matrix["matrix_id"],
            "published": publish_matrix,
        },
        "inventory": {"file": str(inventory_path.resolve())},
        "heldout_suite": {
            "file": str(heldout_suite_path.resolve()),
            "answer_metadata_present": False,
        },
        "metrics": metrics,
        "identities": rows,
        "source_fingerprint": _source_fingerprint(
            root,
            (
                root / "ACTIVE_AGENT_IMPROVEMENT_PLAN.md",
                root / "agent/hardness/np_hard_existing_route_qualification.py",
                root / "agent/hardness/np_hard_orchestrator.py",
                root / "agent/hardness/np_hard_input.py",
                matrix_path.resolve(),
                inventory_path.resolve(),
                heldout_suite_path.resolve(),
            ),
        ),
    }
    _write_json(report_path.resolve(), report)
    _write_json(output_root / "report.json", report)
    return report
