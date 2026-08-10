"""H-F: identity-level NP-hard target qualification and trusted target matrix.

The target matrix upgrades the declaration-level inventory into per-identity
records keyed by ``problem_node_id + representation_node_id``.  Every unique
identity is qualified through the same production normalization, catalog,
route search, and deterministic planner pipeline; the matrix never reads a
benchmark oracle and never calls a model.
"""

from __future__ import annotations

import json
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
from typing import Any, Iterable, Mapping

from .lean_runner import sha256_file
from .models import sha256_id
from .np_hard_authoring_planner import (
    NPHardAuthoringPlannerError,
    NPHardAuthoringPlannerV2,
)
from .np_hard_input import NPHardInputError, resolve_np_hard_input_reference
from .np_hard_scope_policy import (
    NPHardScopePolicyEntryV1,
    load_np_hard_scope_policy,
    validate_scope_policy_against_inventory,
)


NP_HARD_TARGET_MATRIX_SCHEMA_V1 = "hardness_np_hard_target_matrix_v1"
NP_HARD_TARGET_MATRIX_ROW_SCHEMA_V1 = "hardness_np_hard_target_matrix_row_v1"
NP_HARD_TARGET_MATRIX_SCHEMA_V2 = "hardness_np_hard_target_matrix_v2"
NP_HARD_TARGET_MATRIX_ROW_SCHEMA_V2 = "hardness_np_hard_target_matrix_row_v2"

DISPOSITION_IN_SCOPE = "in_scope_np_hard"
DISPOSITION_AUXILIARY = "auxiliary_or_non_target"
DISPOSITION_BLOCKED = "blocked_missing_formal_prerequisite"
DISPOSITION_UNCLASSIFIED = "unclassified"
DISPOSITIONS = {
    DISPOSITION_IN_SCOPE,
    DISPOSITION_AUXILIARY,
    DISPOSITION_BLOCKED,
    DISPOSITION_UNCLASSIFIED,
}

FORWARD_HUB_MISSING = "forward_hardness_hub"


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def canonical_identity_member(rows: Iterable[Mapping[str, Any]]) -> Mapping[str, Any]:
    """Deterministically select one declaration as the canonical identity member.

    Preference order: registered entries, then the shortest declaration, then
    lexicographic module/declaration order.  The choice is stable and does not
    depend on oracle or benchmark data.
    """

    ordered = sorted(
        rows,
        key=lambda row: (
            not bool(row["registered"]),
            len(row["declaration"]),
            row["declaration_module"],
            row["declaration"],
        ),
    )
    return ordered[0]


def _identity_groups(rows: Iterable[Mapping[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    groups: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        groups.setdefault(row["identity_id"], []).append(dict(row))
    for members in groups.values():
        members.sort(key=lambda row: row["declaration"])
    return groups


def _planner_result(
    *,
    root: Path,
    declaration: str,
    module: str,
    work_dir: Path,
    lean_timeout_seconds: int,
) -> dict[str, Any]:
    """Run the deterministic production planner qualification for one identity.

    No model is invoked; ``model_calls`` stays zero.  The returned record keeps
    the planner failure code, missing capabilities, and the formed typed DAG.
    """

    work_dir.mkdir(parents=True, exist_ok=True)
    planner = NPHardAuthoringPlannerV2(
        root=root,
        input_module=module,
        input_problem_declaration=declaration,
        output_dir=work_dir,
        attempt_budget=1,
        timeout_seconds=60,
        max_output_tokens=3000,
        lean_timeout_seconds=lean_timeout_seconds,
    )
    try:
        plan = planner.plan()
    except NPHardAuthoringPlannerError as error:
        return {
            "status": "BLOCKED",
            "failure_code": error.code,
            "explanation": error.message,
            "missing_capabilities": [],
            "task_class": None,
            "gap_node_count": 0,
            "capability_dag_node_count": 0,
            "selected_hub": None,
            "model_calls": 0,
            "plan_id": None,
        }
    task = plan.task
    return {
        "status": plan.status,
        "failure_code": plan.failure_code,
        "explanation": None,
        "missing_capabilities": list(plan.missing_capabilities),
        "task_class": task.task_class if task is not None else None,
        "gap_node_count": len(task.gap_nodes) if task is not None else 0,
        "capability_dag_node_count": len(plan.capability_dag),
        "selected_hub": plan.selected_hub,
        "model_calls": plan.model_calls,
        "plan_id": plan.plan_id,
    }


def classify_identity_qualification(
    *,
    has_forward_route: bool,
    known_hardness_seed: bool,
    planner: Mapping[str, Any] | None,
    canonical_declaration: str,
    scope_policy: NPHardScopePolicyEntryV1 | None = None,
    identity_has_registered_member: bool = True,
) -> dict[str, Any]:
    """Deterministic, mutually exclusive disposition for one identity.

    Rules (auditable, in priority order):

    1. A forward route from a hardness seed makes the identity
       ``in_scope_np_hard`` with a deterministic typed DAG (H-H verifies it).
    2. An exact identity row in the content-addressed production scope policy
       is ``auxiliary_or_non_target`` even if a syntactic typed gap can be
       formed.  This prevents a program into a well-formedness predicate from
       being mistaken for a plausible NP-hard target.
    3. Without a route, a planner ``PLANNED`` task is ``in_scope_np_hard``
       with an executable typed authoring DAG (H-I authors it).
    4. A planner-blocked identity with no registered public member is an
       internal catalog/IR helper and is ``auxiliary_or_non_target``.
    5. Any other blocked identity is ``blocked_missing_formal_prerequisite``
       with the exact planner blocker and missing capabilities recorded.
    6. Everything else is ``unclassified``; the matrix must reach zero.
    """

    if has_forward_route:
        return {
            "disposition": DISPOSITION_IN_SCOPE,
            "basis": "forward_certified_reduction_route",
            "basis_reason": (
                "the identity is reachable from a hardness seed through "
                "forward CertifiedReduction edges in the Lean-observed catalog"
            ),
            "blocker": None,
            "missing_formal_prerequisite": [],
            "next_action": "H-H production verification of the canonical endpoint",
        }
    if scope_policy is not None:
        return {
            "disposition": DISPOSITION_AUXILIARY,
            "basis": "formal_scope_policy",
            "basis_reason": scope_policy.rationale,
            "blocker": "auxiliary_or_non_target",
            "missing_formal_prerequisite": [],
            "next_action": "excluded from the NP-hard success denominator",
        }
    if planner is None:
        return {
            "disposition": DISPOSITION_UNCLASSIFIED,
            "basis": "missing_planner_qualification",
            "basis_reason": "the deterministic planner qualification did not run",
            "blocker": None,
            "missing_formal_prerequisite": [],
            "next_action": "rerun identity qualification",
        }
    if planner.get("status") == "PLANNED":
        task_class = planner.get("task_class")
        return {
            "disposition": DISPOSITION_IN_SCOPE,
            "basis": "typed_authoring_dag",
            "basis_reason": (
                f"the deterministic planner formed a typed authoring DAG "
                f"(task_class={task_class}, gap_count={planner.get('gap_node_count')})"
            ),
            "blocker": None,
            "missing_formal_prerequisite": [],
            "next_action": "H-I model authoring of the typed gaps",
        }
    planner_code = planner.get("failure_code")
    if planner.get("status") == "BLOCKED" and not identity_has_registered_member:
        return {
            "disposition": DISPOSITION_AUXILIARY,
            "basis": "unregistered_internal_catalog_identity",
            "basis_reason": (
                "the exact identity has no registered public problem member, no forward "
                "hardness route, and no executable typed authoring DAG; it is retained "
                "as an internal IR/catalog helper rather than counted as an NP-hard target"
            ),
            "blocker": "auxiliary_or_non_target",
            "missing_formal_prerequisite": [],
            "next_action": "excluded from the NP-hard success denominator",
        }
    if planner.get("status") == "BLOCKED" and planner_code:
        return {
            "disposition": DISPOSITION_BLOCKED,
            "basis": "planner_blocked_missing_capability",
            "basis_reason": "the deterministic planner identified a precise missing component",
            "blocker": planner_code,
            "missing_formal_prerequisite": list(planner.get("missing_capabilities") or []),
            "next_action": "H-I capability node construction for the missing components",
        }
    return {
        "disposition": DISPOSITION_UNCLASSIFIED,
        "basis": "unknown_planner_outcome",
        "basis_reason": f"planner outcome {planner_code!r} has no defined disposition",
        "blocker": planner_code,
        "missing_formal_prerequisite": list(planner.get("missing_capabilities") or []),
        "next_action": "extend the classification rules after triage",
    }


def _normalization_summary(*, root: Path, module: str, declaration: str, timeout: int) -> dict[str, Any]:
    reference = resolve_np_hard_input_reference(
        root=root,
        input_module=module,
        requested_term=declaration,
        timeout_seconds=timeout,
    )
    observation = reference.normalization_observation
    return {
        "requested_term": reference.requested_term,
        "input_module": reference.input_module,
        "canonical_problem": reference.canonical_problem,
        "canonical_module": reference.canonical_module,
        "normalization_kind": reference.normalization_kind,
        "resolved_encoding": reference.resolved_encoding,
        "registry_fingerprint": observation.registry_fingerprint,
        "normalization_catalog_id": observation.catalog_id,
        "normalization_observation_id": observation.observation_id,
        "import_closure_sha256": observation.import_closure_sha256,
        "complete_problem_count": observation.complete_problem_count,
        "representation_match_count": observation.representation_match_count,
        "candidate_count": len(observation.candidates),
    }


def _physical_import_module(root: Path, module: str) -> str | None:
    """Map a logical library module to its physical import path in ``Lean/Reference``.

    Canonical identity members often live in ``ComplexityReduction.Domain.Core``
    while the logical namespace omits the ``Core`` segment (mirrors
    ``Domain/Core/GraphColoringIR.lean`` importing as
    ``ComplexityReduction.Domain.Core.GraphColoringIR``).
    """
    reference = root / "Lean" / "Reference"
    if (reference / Path(*module.split(".")).with_suffix(".lean")).is_file():
        return module
    prefix, _, leaf = module.rpartition(".")
    if prefix and (reference / Path(*f"{prefix}.Core.{leaf}".split(".")).with_suffix(".lean")).is_file():
        return f"{prefix}.Core.{leaf}"
    return None


def _route_row_value(row: Mapping[str, Any], name: str) -> Any:
    """Read identity-level route facts from either inventory schema generation."""
    if name in row:
        return row[name]
    aliases = {
        "has_forward_route": "known_forward_route",
        "has_hardness_seed": "known_hardness_seed",
    }
    return row.get(aliases.get(name, name))


def _qualify_identity(
    *,
    root: Path,
    identity_id: str,
    members: list[Mapping[str, Any]],
    work_root: Path,
    lean_timeout_seconds: int,
) -> dict[str, Any]:
    canonical = canonical_identity_member(members)
    declaration = str(canonical["declaration"])
    module = str(canonical["declaration_module"])
    physical_module = _physical_import_module(root, module) or module
    family = str(canonical["family"])
    work_dir = work_root / identity_id.removeprefix("sha256:")
    has_route = bool(_route_row_value(canonical, "has_forward_route"))
    has_seed = bool(_route_row_value(canonical, "has_hardness_seed"))
    has_registered_member = any(bool(member["registered"]) for member in members)
    problem_node_id = str(canonical["problem_node_id"])
    representation_node_id = str(canonical["representation_node_id"])
    scope_policy_entry = canonical.get("_scope_policy_entry")
    if scope_policy_entry is not None and not isinstance(
        scope_policy_entry, NPHardScopePolicyEntryV1
    ):
        raise TypeError("scope policy entry was not resolved before qualification")
    summary = {
        "schema_version": NP_HARD_TARGET_MATRIX_ROW_SCHEMA_V1,
        "identity_id": identity_id,
        "canonical_declaration": declaration,
        "canonical_module": physical_module if _physical_import_module(root, module) else module,
        "problem_node_id": problem_node_id,
        "representation_node_id": representation_node_id,
        "family": family,
        "registered": bool(canonical["registered"]),
        "has_registered_member": has_registered_member,
        "member_declarations": [str(member["declaration"]) for member in members],
        "member_count": len(members),
        "member_module_count": len({str(member["declaration_module"]) for member in members}),
        "known_hardness_seed": has_seed,
        "has_forward_route": has_route,
        "has_forward_certified_reduction_route": has_route,
        "shortest_forward_route_length": canonical.get("shortest_forward_route_length"),
        "normalization": None,
        "planner": None,
        "can_form_typed_authoring_dag": False,
        "scope_policy": (
            scope_policy_entry.to_dict(root=root) if scope_policy_entry is not None else None
        ),
        "disposition": DISPOSITION_UNCLASSIFIED,
        "basis": "pending_qualification",
        "basis_reason": "qualification has not completed",
        "blocker": None,
        "missing_formal_prerequisite": [],
        "next_action": "complete qualification",
        "production_entry_status": "not_run",
        "production_entry_verified": False,
        "production_entry_failure_code": None,
        "production_entry_model_calls": 0,
        "verified_artifact": None,
        "errors": [],
    }
    try:
        summary["normalization"] = _normalization_summary(
            root=root, module=physical_module, declaration=declaration, timeout=lean_timeout_seconds
        )
    except NPHardInputError as error:
        summary["errors"].append(f"{error.code}: {error.message}")
        summary["blocker"] = error.code
        return summary
    except (ValueError, FileNotFoundError) as error:
        summary["errors"].append(f"canonical_module_not_found: {error}")
        summary["blocker"] = "canonical_module_not_found"
        return summary
    try:
        summary["planner"] = _planner_result(
            root=root,
            declaration=declaration,
            module=physical_module,
            work_dir=work_dir,
            lean_timeout_seconds=lean_timeout_seconds,
        )
    except Exception as error:  # planner infra failures are audited, not hidden
        summary["errors"].append(f"planner_qualification_failed: {error}")
        return summary
    classification = classify_identity_qualification(
        has_forward_route=has_route,
        known_hardness_seed=has_seed,
        planner=summary["planner"],
        canonical_declaration=declaration,
        scope_policy=scope_policy_entry,
        identity_has_registered_member=has_registered_member,
    )
    summary.update(classification)
    summary["can_form_typed_authoring_dag"] = bool(
        summary["planner"].get("status") == "PLANNED"
        and summary["planner"].get("capability_dag_node_count", 0) > 0
    )
    summary["in_scope_np_hard"] = summary["disposition"] == DISPOSITION_IN_SCOPE
    return summary


def build_np_hard_target_matrix(
    *,
    root: Path,
    inventory_rows: list[Mapping[str, Any]],
    matrix_path: Path,
    work_root: Path,
    lean_timeout_seconds: int = 900,
    jobs: int = 4,
    scope_policy_path: Path | None = None,
) -> dict[str, Any]:
    """Qualify every unique identity and emit the content-addressed matrix."""

    root = root.resolve()
    policy = load_np_hard_scope_policy(root=root, path=scope_policy_path)
    validate_scope_policy_against_inventory(
        policy=policy, inventory_rows=inventory_rows
    )
    policy_by_identity = policy.by_identity()
    qualified_inventory_rows: list[dict[str, Any]] = []
    for inventory_row in inventory_rows:
        row = dict(inventory_row)
        row["_scope_policy_entry"] = policy_by_identity.get(str(row["identity_id"]))
        qualified_inventory_rows.append(row)
    groups = _identity_groups(qualified_inventory_rows)
    work_root = work_root.resolve()
    work_root.mkdir(parents=True, exist_ok=True)

    def qualify(identity_id: str, members: list[dict[str, Any]]) -> dict[str, Any]:
        return _qualify_identity(
            root=root,
            identity_id=identity_id,
            members=members,
            work_root=work_root,
            lean_timeout_seconds=lean_timeout_seconds,
        )

    rows: list[dict[str, Any]] = []
    if jobs <= 1 or len(groups) == 1:
        for identity_id, members in sorted(groups.items()):
            rows.append(qualify(identity_id, members))
    else:
        with ThreadPoolExecutor(max_workers=max(2, min(jobs, len(groups)))) as executor:
            pending = {
                executor.submit(qualify, identity_id, members)
                for identity_id, members in sorted(groups.items())
            }
            for future in as_completed(pending):
                rows.append(future.result())
    rows.sort(key=lambda row: (row["canonical_declaration"], row["identity_id"]))

    dispositions = {row["disposition"]: 0 for row in rows}
    for row in rows:
        dispositions[row["disposition"]] += 1
    toolchain = (root / "Lean" / "lean-toolchain").read_text(encoding="utf-8").strip()
    payload = {
        "schema_version": NP_HARD_TARGET_MATRIX_SCHEMA_V1,
        "scope": "public ComplexityReduction identities keyed by problem_node_id + representation_node_id",
        "toolchain": toolchain,
        "lake_manifest_sha256": "sha256:" + sha256_file(root / "Lean" / "lake-manifest.json"),
        "scope_policy": policy.to_dict(root=root),
        "declaration_count": sum(len(members) for members in groups.values()),
        "identity_count": len(rows),
        "known_hardness_seed_identity_count": sum(
            row["known_hardness_seed"] for row in rows
        ),
        "known_forward_route_identity_count": sum(row["has_forward_route"] for row in rows),
        "typed_authoring_dag_identity_count": sum(
            row["can_form_typed_authoring_dag"] for row in rows
        ),
        "production_entry_verified_identity_count": sum(
            row["production_entry_verified"] for row in rows
        ),
        "disposition_counts": dispositions,
        "in_scope_count": dispositions.get(DISPOSITION_IN_SCOPE, 0),
        "auxiliary_count": dispositions.get(DISPOSITION_AUXILIARY, 0),
        "blocked_count": dispositions.get(DISPOSITION_BLOCKED, 0),
        "unclassified_count": dispositions.get(DISPOSITION_UNCLASSIFIED, 0),
        "identities": rows,
    }
    payload["matrix_id"] = sha256_id(payload)
    _write_json(matrix_path, payload)
    return payload


def load_np_hard_target_matrix(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict) or value.get("schema_version") not in {
        NP_HARD_TARGET_MATRIX_SCHEMA_V1,
        NP_HARD_TARGET_MATRIX_SCHEMA_V2,
    }:
        raise ValueError("unsupported NP-hard target matrix schema")
    return value


def update_np_hard_target_matrix_production_results(
    *, matrix_path: Path, production_rows: Iterable[Mapping[str, Any]]
) -> dict[str, Any]:
    """Merge answer-free production observations into the identity matrix.

    This function consumes only the actual production result and its normalized
    endpoint.  Evaluation-oracle expectations are intentionally absent.
    """

    matrix = load_np_hard_target_matrix(matrix_path)
    identities = [dict(row) for row in matrix["identities"]]
    by_declaration: dict[str, dict[str, Any]] = {}
    for row in identities:
        for declaration in row["member_declarations"]:
            previous = by_declaration.setdefault(declaration, row)
            if previous["identity_id"] != row["identity_id"]:
                raise ValueError("one declaration belongs to multiple target-matrix identities")
    updated_identity_ids: set[str] = set()
    for production_row in production_rows:
        payload = production_row.get("result")
        if not isinstance(payload, Mapping):
            continue
        input_identity = payload.get("input_identity")
        if not isinstance(input_identity, Mapping):
            continue
        canonical_problem = input_identity.get("canonical_problem")
        if not isinstance(canonical_problem, str):
            continue
        target = by_declaration.get(canonical_problem)
        if target is None:
            raise ValueError(
                f"production endpoint is absent from the target matrix: {canonical_problem}"
            )
        identity_id = target["identity_id"]
        if identity_id in updated_identity_ids:
            raise ValueError("qualification held-out repeats a canonical identity")
        updated_identity_ids.add(identity_id)
        status = str(production_row.get("status") or payload.get("status") or "FAILED")
        failure_code = production_row.get("failure_code")
        model_calls = int(production_row.get("model_calls") or 0)
        if status == "VERIFIED":
            production_status = "verified"
        elif status == "BLOCKED" and failure_code == "auxiliary_or_non_target":
            production_status = "blocked_not_target"
        elif status == "BLOCKED":
            production_status = "blocked_missing_prerequisite"
        else:
            production_status = "failed"
        target["production_entry_status"] = production_status
        target["production_entry_verified"] = status == "VERIFIED"
        target["production_entry_failure_code"] = failure_code
        target["production_entry_model_calls"] = model_calls
        target["verified_artifact"] = (
            dict(payload.get("artifact") or {}) if status == "VERIFIED" else None
        )
    matrix["identities"] = identities
    matrix["production_entry_verified_identity_count"] = sum(
        row.get("production_entry_verified") is True for row in identities
    )
    matrix["production_entry_observed_identity_count"] = sum(
        row.get("production_entry_status") != "not_run" for row in identities
    )
    matrix.pop("matrix_id", None)
    matrix["matrix_id"] = sha256_id(matrix)
    _write_json(matrix_path, matrix)
    return matrix
