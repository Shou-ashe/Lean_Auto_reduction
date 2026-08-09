"""Content-addressed, Lean-exported inventory for the NP-hard production lane."""

from __future__ import annotations

import json
import secrets
import tempfile
from collections import deque
from pathlib import Path
from typing import Any, Mapping

from .connection_catalog import parse_connection_catalog
from .hardness_target_catalog import (
    NATIVE_NP_HARD_POLICY,
    parse_hardness_target_catalog,
)
from .lean_runner import (
    build_problem_catalog_source,
    run_command,
    sha256_file,
)
from .models import sha256_id
from .np_hard_target_matrix import (
    DISPOSITION_IN_SCOPE,
    canonical_identity_member,
    load_np_hard_target_matrix,
)
from .problem_catalog import parse_problem_catalog


NP_HARD_INVENTORY_SCHEMA_V2 = "hardness_np_hard_library_inventory_v2"
FORBIDDEN_MODULE_COMPONENTS = frozenset(
    {"Oracle", "Oracles", "Gold", "GoldProofs", "Expected", "HiddenTargets", "Legacy"}
)


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(
        json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def _command_audit(command: Any) -> dict[str, Any]:
    return {
        "command": list(command.command),
        "exit_code": command.exit_code,
        "duration_seconds": command.duration_seconds,
        "timed_out": command.timed_out,
        "stdout_sha256": sha256_id(command.stdout),
        "stderr_sha256": sha256_id(command.stderr),
        "stdout_bytes": len(command.stdout.encode("utf-8")),
        "stderr_bytes": len(command.stderr.encode("utf-8")),
    }


def _library_modules(root: Path) -> tuple[str, ...]:
    reference = root / "Lean" / "Reference"
    source_root = reference / "ComplexityReduction"
    modules: list[str] = []
    for path in source_root.rglob("*.lean"):
        relative = path.relative_to(reference).with_suffix("")
        module = ".".join(relative.parts)
        components = set(module.split("."))
        if FORBIDDEN_MODULE_COMPONENTS.intersection(components):
            continue
        if module.startswith("ComplexityReduction.Agent."):
            continue
        modules.append(module)
    if not modules:
        raise ValueError("ComplexityReduction library inventory scope is empty")
    return tuple(sorted(set(modules)))


def _family(declaration: str) -> str:
    lowered = declaration.lower()
    families = (
        ("sat-csp", ("sat", "cnf", "csp", "clause", "satisfiability")),
        (
            "graph",
            (
                "graph",
                "clique",
                "vertex",
                "hamiltonian",
                "steiner",
                "neighbor",
                "color",
                "feedback",
                "path",
                "cut",
            ),
        ),
        ("set-system", ("set", "cover", "incidence", "seeing")),
        (
            "numeric",
            ("knapsack", "partition", "sequencing", "subset", "integer", "zeroone"),
        ),
    )
    for family, needles in families:
        if any(needle in lowered for needle in needles):
            return family
    return "other"


def _declaration_module(declaration: str, modules: tuple[str, ...]) -> str:
    matches = [module for module in modules if declaration.startswith(module + ".")]
    return max(matches, key=len) if matches else declaration.rpartition(".")[0]


def _shortest_hardness_distances(
    *, seed_nodes: set[str], connections: tuple[Any, ...]
) -> dict[str, int]:
    adjacency: dict[str, set[str]] = {}
    for entry in connections:
        adjacency.setdefault(entry.source_node_id, set()).add(entry.target_node_id)
    distances = {node: 0 for node in seed_nodes}
    pending = deque(sorted(seed_nodes))
    while pending:
        source = pending.popleft()
        for target in sorted(adjacency.get(source, ())):
            if target in distances:
                continue
            distances[target] = distances[source] + 1
            pending.append(target)
    return distances


def build_np_hard_library_inventory(
    *,
    root: Path,
    report_path: Path,
    suite_path: Path | None = None,
    oracle_path: Path | None = None,
    qualification_cases: Mapping[str, Mapping[str, Any]] | None = None,
    matrix_path: Path | None = None,
    timeout_seconds: int = 1800,
) -> dict[str, Any]:
    """Export every public library ``PresentedProblem`` visible in a full build.

    The inventory is observational: Lean exports problem, connection, and target
    rows; Python only groups those rows and computes forward graph reachability.
    Each row carries the split identity-level qualification fields; the identity
    disposition of an existing ``NP_HARD_TARGET_MATRIX.json`` is merged when
    ``matrix_path`` is supplied.
    """

    root = root.resolve()
    matrix = load_np_hard_target_matrix(matrix_path) if matrix_path is not None else None
    matrix_by_identity = (
        {row["identity_id"]: row for row in matrix["identities"]} if matrix is not None else {}
    )
    modules = _library_modules(root)
    toolchain = (root / "Lean" / "lean-toolchain").read_text(encoding="utf-8").strip()
    manifest_hash = "sha256:" + sha256_file(root / "Lean" / "lake-manifest.json")
    build = run_command(
        ["lake", "build"],
        cwd=root / "Lean",
        timeout_seconds=timeout_seconds,
        output_limit=32 * 1024 * 1024,
    )
    if not build.ok:
        raise ValueError("full ComplexityReduction inventory build failed")
    nonce = secrets.token_hex(16)
    source = build_problem_catalog_source(nonce=nonce, additional_modules=modules)
    lowered_source = source.lower()
    if any(
        f".{component.lower()}." in lowered_source
        for component in FORBIDDEN_MODULE_COMPONENTS
    ):
        raise ValueError("forbidden hidden/gold module entered inventory imports")
    with tempfile.TemporaryDirectory(prefix="np-hard-library-inventory-") as directory:
        probe = Path(directory) / "LibraryInventory.lean"
        probe.write_text(source, encoding="utf-8")
        command = run_command(
            ["lake", "env", "lean", str(probe)],
            cwd=root / "Lean",
            timeout_seconds=timeout_seconds,
            output_limit=128 * 1024 * 1024,
        )
    if not command.ok:
        raise ValueError(command.stderr or command.stdout)
    problems = parse_problem_catalog(
        stdout=command.stdout,
        stderr=command.stderr,
        nonce=nonce,
        toolchain=toolchain,
        lake_manifest_sha256=manifest_hash,
    )
    connections = parse_connection_catalog(
        stdout=command.stdout,
        stderr=command.stderr,
        nonce=nonce,
        toolchain=toolchain,
        lake_manifest_sha256=manifest_hash,
    )
    targets = parse_hardness_target_catalog(
        stdout=command.stdout,
        stderr=command.stderr,
        nonce=nonce,
        toolchain=toolchain,
        lake_manifest_sha256=manifest_hash,
    )
    fingerprints = {
        problems.registry_fingerprint,
        connections.registry_fingerprint,
        targets.registry_fingerprint,
    }
    if len(fingerprints) != 1:
        raise ValueError("inventory catalogs do not share one Lean registry fingerprint")
    seed_nodes = {
        entry.target_node_id
        for entry in targets.entries
        if NATIVE_NP_HARD_POLICY in entry.satisfied_policies
    }
    distances = _shortest_hardness_distances(
        seed_nodes=seed_nodes, connections=connections.entries
    )

    suite_cases: dict[str, dict[str, Any]] = {}
    oracle_cases: dict[str, dict[str, Any]] = {}
    if suite_path is not None:
        suite = json.loads(suite_path.read_text(encoding="utf-8"))
        suite_cases = {case["id"]: case for case in suite["cases"]}
    if oracle_path is not None:
        oracle = json.loads(oracle_path.read_text(encoding="utf-8"))
        oracle_cases = {case["id"]: case for case in oracle["cases"]}
    del suite_cases
    del oracle_cases
    qualification_cases = qualification_cases or {}
    rows: list[dict[str, Any]] = []
    for entry in problems.entries:
        distance = distances.get(entry.problem_node_id)
        identity_id = sha256_id(
            {
                "problem_node_id": entry.problem_node_id,
                "representation_node_id": entry.representation_node_id,
            }
        )
        identity_record = matrix_by_identity.get(identity_id, {})
        planner = identity_record.get("planner") or {}
        rows.append(
            {
                "declaration": entry.declaration,
                "declaration_module": _declaration_module(entry.declaration, modules),
                "problem_node_id": entry.problem_node_id,
                "representation_node_id": entry.representation_node_id,
                "accepts_node_id": entry.accepts_node_id,
                "domain_node_id": entry.domain_node_id,
                "encoder_bound_identity_node_id": entry.encoder_bound_identity_node_id,
                "semantic_summary": entry.semantic_summary,
                "accepts_summary": entry.accepts_summary,
                "representation_summary": entry.representation_summary,
                "identity_id": identity_id,
                "family": _family(entry.declaration),
                "registered": entry.registered,
                "has_hardness_seed": entry.problem_node_id in seed_nodes,
                "has_forward_route": distance is not None,
                "shortest_forward_route_length": distance,
                "identity_disposition": identity_record.get("disposition"),
                "identity_disposition_basis": identity_record.get("basis"),
                "identity_blocker": identity_record.get("blocker"),
                "identity_missing_formal_prerequisite": list(
                    identity_record.get("missing_formal_prerequisite") or []
                ),
                "identity_next_action": identity_record.get("next_action"),
                "identity_canonical_declaration": identity_record.get(
                    "canonical_declaration"
                ),
                "identity_canonical_module": identity_record.get("canonical_module"),
                "identity_member_count": len(
                    identity_record.get("member_declarations") or []
                ),
                "planner_qualification_status": planner.get("status"),
                "planner_qualification_failure_code": planner.get("failure_code"),
                "planner_qualification_missing_capabilities": list(
                    planner.get("missing_capabilities") or []
                ),
                "planner_qualification_task_class": planner.get("task_class"),
                "planner_qualification_gap_node_count": planner.get("gap_node_count"),
                "planner_qualification_capability_dag_node_count": planner.get(
                    "capability_dag_node_count"
                ),
                "planner_qualification_selected_hub": planner.get("selected_hub"),
                "planner_qualification_model_calls": (
                    planner.get("model_calls", 0) or 0
                ),
                "can_form_typed_authoring_dag": bool(
                    planner.get("status") == "PLANNED"
                    and (planner.get("capability_dag_node_count") or 0) > 0
                ),
                "verified_through_production_entry": (
                    identity_record.get("production_entry_verified") is True
                ),
                "production_entry_status": (
                    identity_record.get("production_entry_status") or "not_run"
                ),
                "in_scope_np_hard": (
                    identity_record.get("disposition") == DISPOSITION_IN_SCOPE
                ),
            }
        )
    rows.sort(key=lambda row: row["declaration"])
    grouped_rows: dict[str, list[dict[str, Any]]] = {}
    for row in rows:
        grouped_rows.setdefault(row["identity_id"], []).append(row)
    identities: list[dict[str, Any]] = []
    for identity_id, members in sorted(grouped_rows.items()):
        matrix_row = matrix_by_identity.get(identity_id, {})
        canonical_declaration = matrix_row.get("canonical_declaration")
        canonical = next(
            (
                member
                for member in members
                if member["declaration"] == canonical_declaration
            ),
            None,
        )
        if canonical is None:
            canonical = dict(canonical_identity_member(members))
        shortest_lengths = [
            member["shortest_forward_route_length"]
            for member in members
            if member["shortest_forward_route_length"] is not None
        ]
        registered_members = [member for member in members if member["registered"]]
        identities.append(
            {
                "identity_id": identity_id,
                "problem_node_id": canonical["problem_node_id"],
                "representation_node_id": canonical["representation_node_id"],
                "canonical_declaration": canonical["declaration"],
                "canonical_module": matrix_row.get("canonical_module")
                or canonical["declaration_module"],
                "family": canonical["family"],
                "member_count": len(members),
                "member_module_count": len(
                    {member["declaration_module"] for member in members}
                ),
                "members": [
                    {
                        "declaration": member["declaration"],
                        "module": member["declaration_module"],
                        "registered": member["registered"],
                    }
                    for member in sorted(members, key=lambda item: item["declaration"])
                ],
                "registered_member_count": len(registered_members),
                "has_registered_member": bool(registered_members),
                "has_hardness_seed": any(
                    member["has_hardness_seed"] for member in members
                ),
                "has_forward_certified_reduction_route": any(
                    member["has_forward_route"] for member in members
                ),
                "shortest_forward_route_length": (
                    min(shortest_lengths) if shortest_lengths else None
                ),
                "can_form_typed_authoring_dag": bool(
                    matrix_row.get("can_form_typed_authoring_dag") is True
                ),
                "planner_qualification": matrix_row.get("planner"),
                "production_entry_verified": bool(
                    matrix_row.get("production_entry_verified") is True
                ),
                "production_entry_status": matrix_row.get("production_entry_status")
                or "not_run",
                "in_scope_np_hard": matrix_row.get("disposition")
                == DISPOSITION_IN_SCOPE,
                "disposition": matrix_row.get("disposition"),
                "disposition_basis": matrix_row.get("basis"),
                "blocker": matrix_row.get("blocker"),
                "missing_formal_prerequisite": list(
                    matrix_row.get("missing_formal_prerequisite") or []
                ),
                "next_action": matrix_row.get("next_action"),
            }
        )
    identities.sort(key=lambda row: (row["canonical_declaration"], row["identity_id"]))
    source_hashes = {
        module: "sha256:"
        + sha256_file(
            root
            / "Lean"
            / "Reference"
            / Path(*module.split(".")).with_suffix(".lean")
        )
        for module in modules
    }
    payload = {
        "schema_version": NP_HARD_INVENTORY_SCHEMA_V2,
        "scope": "public ComplexityReduction library modules excluding Agent and forbidden hidden/gold namespaces",
        "toolchain": toolchain,
        "lake_manifest_sha256": manifest_hash,
        "registry_fingerprint": problems.registry_fingerprint,
        "module_count": len(modules),
        "module_source_closure_id": sha256_id(source_hashes),
        "problem_catalog_id": problems.catalog_id,
        "connection_catalog_id": connections.catalog_id,
        "target_catalog_id": targets.catalog_id,
        "presented_problem_count": len(rows),
        "unique_problem_identity_count": len({row["identity_id"] for row in rows}),
        "declaration_count": len(rows),
        "identity_count": len(identities),
        "known_hardness_seed_count": sum(row["has_hardness_seed"] for row in rows),
        "known_forward_route_count": sum(row["has_forward_route"] for row in rows),
        "known_hardness_seed_declaration_count": sum(
            row["has_hardness_seed"] for row in rows
        ),
        "known_hardness_seed_identity_count": sum(
            row["has_hardness_seed"] for row in identities
        ),
        "known_forward_route_declaration_count": sum(
            row["has_forward_route"] for row in rows
        ),
        "known_forward_route_identity_count": sum(
            row["has_forward_certified_reduction_route"] for row in identities
        ),
        "typed_authoring_dag_identity_count": sum(
            row["can_form_typed_authoring_dag"] for row in identities
        ),
        "production_entry_verified_identity_count": sum(
            row["production_entry_verified"] for row in identities
        ),
        "family_counts": {
            family: sum(row["family"] == family for row in rows)
            for family in sorted({row["family"] for row in rows})
        },
        "identity_family_counts": {
            family: sum(row["family"] == family for row in identities)
            for family in sorted({row["family"] for row in identities})
        },
        "source_imports_forbidden_count": 0,
        "target_matrix_id": matrix.get("matrix_id") if matrix is not None else None,
        "target_matrix_unclassified_count": (
            matrix.get("unclassified_count") if matrix is not None else None
        ),
        "identities": identities,
        "entries": rows,
    }
    report = {
        **payload,
        "inventory_id": sha256_id(payload),
        "lean_command": _command_audit(command),
        "full_build": _command_audit(build),
    }
    _write_json(report_path, report)
    return report
