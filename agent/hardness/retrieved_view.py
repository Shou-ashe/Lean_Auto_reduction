"""Compact prompt views over fully retained retrieved catalog facts.

The planner keeps the complete Lean-validated objects in local session state.
Only the fields needed for model selection, directed topology, dependency
accounting, and audit are repeated in stateless model prompts.  Compact rows
are never proof authority: finish selectors are resolved back to the complete
same-fingerprint objects before a plan is accepted.
"""

from __future__ import annotations

import json
from collections.abc import Mapping, Sequence
from typing import Any

from .frontier_guidance import frontier_prompt_metrics


COMPACT_RETRIEVED_VIEW_SCHEMA = "hardness_retrieved_compact_v1"
COMPACT_RETRIEVED_VIEW_MODE = "authorization_complete_compact"


def _selected_fields(
    row: Mapping[str, Any], fields: Sequence[str]
) -> dict[str, Any]:
    return {field: row[field] for field in fields if field in row}


def compact_problem_row(row: Mapping[str, Any]) -> dict[str, Any]:
    return _selected_fields(
        row,
        (
            "entry_id",
            "declaration",
            "namespace",
            "problem_node_id",
            "accepts_node_id",
            "domain_node_id",
            "representation_node_id",
            "encoder_bound_identity_node_id",
            "codec_group_id",
            "registered",
            "exact_defeq",
            "accepts_exact_defeq",
            "validation_source",
        ),
    )


def compact_connection_row(row: Mapping[str, Any]) -> dict[str, Any]:
    return _selected_fields(
        row,
        (
            "entry_id",
            "certificate_declaration",
            "namespace",
            "capability_kind",
            "relation",
            "direction",
            "projection_declaration",
            "lean_term",
            "source_node_id",
            "target_node_id",
            "component_role",
            "validation_source",
        ),
    )


def compact_target_evidence_row(row: Mapping[str, Any]) -> dict[str, Any]:
    return _selected_fields(
        row,
        (
            "evidence_id",
            "evidence_kind",
            "evidence_declaration",
            "satisfied_policies",
            "allowed_evidence_kind",
            "request_eligible",
            "policy_route_allowed",
            "shortest_policy_route_atom_count",
            "target_evidence_dependency_count",
            "provenance_declarations",
            "validation_source",
        ),
    )


def compact_hardness_target_row(row: Mapping[str, Any]) -> dict[str, Any]:
    compact = _selected_fields(
        row,
        (
            "target_entry_id",
            "target_declaration",
            "target_namespace",
            "target_node_id",
            "satisfied_policies",
            "request_eligible_evidence_count",
            "reachable_from_input",
            "shortest_route_length_from_input",
            "within_route_atom_limit",
            "policy_route_allowed",
            "shortest_policy_route_atom_count",
            "reverse_route_exists",
            "route_declarations_included",
            "validation_source",
        ),
    )
    evidences = row.get("evidences")
    compact["evidences"] = (
        [
            compact_target_evidence_row(evidence)
            for evidence in evidences
            if isinstance(evidence, Mapping)
        ]
        if isinstance(evidences, list)
        else []
    )
    return compact


def compact_reduction_row(row: Mapping[str, Any]) -> dict[str, Any]:
    return _selected_fields(
        row,
        (
            "declaration",
            "namespace",
            "role",
            "source_node_id",
            "target_node_id",
        ),
    )


def compact_retrieved_payload(
    retrieved: Mapping[str, Any],
) -> dict[str, list[dict[str, Any]]]:
    problems = retrieved.get("problems")
    connections = retrieved.get("connections")
    targets = retrieved.get("hardness_targets")
    reductions = retrieved.get("reductions")
    return {
        "problems": (
            [compact_problem_row(row) for row in problems if isinstance(row, Mapping)]
            if isinstance(problems, list)
            else []
        ),
        "connections": (
            [
                compact_connection_row(row)
                for row in connections
                if isinstance(row, Mapping)
            ]
            if isinstance(connections, list)
            else []
        ),
        "hardness_targets": (
            [
                compact_hardness_target_row(row)
                for row in targets
                if isinstance(row, Mapping)
            ]
            if isinstance(targets, list)
            else []
        ),
        "reductions": (
            [
                compact_reduction_row(row)
                for row in reductions
                if isinstance(row, Mapping)
            ]
            if isinstance(reductions, list)
            else []
        ),
    }


def compact_retrieved_view_metadata(
    retrieved: Mapping[str, Any],
) -> dict[str, Any]:
    return {
        "schema_version": COMPACT_RETRIEVED_VIEW_SCHEMA,
        "mode": COMPACT_RETRIEVED_VIEW_MODE,
        "complete_objects_retained_by_agent": True,
        "finish_selectors_hydrated_and_validated_by_agent": True,
        "selection_and_topology_fields_complete": True,
        "verbose_descriptions_omitted": True,
        "counts": {
            key: len(value) if isinstance(value, list) else 0
            for key, value in retrieved.items()
        },
    }


_FORBIDDEN_VERBOSE_FIELDS = {
    "problems": {
        "display",
        "semantic_summary",
        "accepts_summary",
        "domain_summary",
        "representation_summary",
        "encoder_bound_identity_summary",
    },
    "connections": {
        "source_display",
        "target_display",
        "source_fingerprint",
        "target_fingerprint",
    },
    "hardness_targets": {
        "target_display",
        "registry_fingerprint",
    },
    "reductions": {
        "source",
        "target",
        "source_fingerprint",
        "target_fingerprint",
    },
}
_FORBIDDEN_VERBOSE_EVIDENCE_FIELDS = {
    "evidence_lean_term",
    "membership_lean_term",
    "registry_fingerprint",
    "schema_version",
    "target_declaration",
    "target_node_id",
}
_REQUIRED_FIELDS = {
    "problems": {
        "entry_id",
        "declaration",
        "problem_node_id",
        "codec_group_id",
        "registered",
        "exact_defeq",
        "accepts_exact_defeq",
        "validation_source",
    },
    "connections": {
        "entry_id",
        "relation",
        "direction",
        "lean_term",
        "source_node_id",
        "target_node_id",
        "validation_source",
    },
    "hardness_targets": {
        "target_entry_id",
        "target_declaration",
        "target_node_id",
        "policy_route_allowed",
        "evidences",
        "validation_source",
    },
    "reductions": {
        "declaration",
        "role",
        "source_node_id",
        "target_node_id",
    },
}
_REQUIRED_EVIDENCE_FIELDS = {
    "evidence_id",
    "evidence_kind",
    "request_eligible",
    "policy_route_allowed",
    "target_evidence_dependency_count",
    "provenance_declarations",
    "validation_source",
}


def compact_retrieved_view_errors(payload: Mapping[str, Any]) -> tuple[str, ...]:
    """Audit that a known-hardness prompt uses only the compact public view."""

    errors: list[str] = []
    metadata = payload.get("retrieved_view")
    if not isinstance(metadata, Mapping):
        errors.append("retrieved_view metadata is missing")
    else:
        if metadata.get("schema_version") != COMPACT_RETRIEVED_VIEW_SCHEMA:
            errors.append("retrieved_view schema_version is not compact v1")
        if metadata.get("mode") != COMPACT_RETRIEVED_VIEW_MODE:
            errors.append("retrieved_view mode is not authorization-complete compact")
    retrieved = payload.get("retrieved")
    if not isinstance(retrieved, Mapping):
        return (*errors, "retrieved payload is missing")
    for group, forbidden in _FORBIDDEN_VERBOSE_FIELDS.items():
        rows = retrieved.get(group)
        if not isinstance(rows, list):
            errors.append(f"retrieved.{group} is not a list")
            continue
        for index, row in enumerate(rows):
            if not isinstance(row, Mapping):
                errors.append(f"retrieved.{group}[{index}] is not an object")
                continue
            missing = sorted(_REQUIRED_FIELDS[group].difference(row))
            if missing:
                errors.append(
                    f"retrieved.{group}[{index}] is missing authorization fields: "
                    + ", ".join(missing)
                )
            leaked = sorted(forbidden.intersection(row))
            if leaked:
                errors.append(
                    f"retrieved.{group}[{index}] contains verbose fields: "
                    + ", ".join(leaked)
                )
            if group == "hardness_targets":
                evidences = row.get("evidences")
                if not isinstance(evidences, list):
                    errors.append(
                        f"retrieved.hardness_targets[{index}].evidences is not a list"
                    )
                    continue
                for evidence_index, evidence in enumerate(evidences):
                    if not isinstance(evidence, Mapping):
                        errors.append(
                            "retrieved.hardness_targets"
                            f"[{index}].evidences[{evidence_index}] is not an object"
                        )
                        continue
                    missing_evidence = sorted(
                        _REQUIRED_EVIDENCE_FIELDS.difference(evidence)
                    )
                    if missing_evidence:
                        errors.append(
                            "retrieved.hardness_targets"
                            f"[{index}].evidences[{evidence_index}] is missing "
                            "authorization fields: " + ", ".join(missing_evidence)
                        )
                    leaked_evidence = sorted(
                        _FORBIDDEN_VERBOSE_EVIDENCE_FIELDS.intersection(evidence)
                    )
                    if leaked_evidence:
                        errors.append(
                            "retrieved.hardness_targets"
                            f"[{index}].evidences[{evidence_index}] contains verbose "
                            "fields: " + ", ".join(leaked_evidence)
                        )
    return tuple(errors)


def retrieved_prompt_metrics(payload: Mapping[str, Any]) -> dict[str, Any]:
    retrieved = payload.get("retrieved")
    if not isinstance(retrieved, Mapping):
        return {
            "retrieved_characters": 0,
            "retrieved_counts": {},
            "retrieved_view_mode": None,
            "compact_view_errors": ["retrieved payload is missing"],
            **frontier_prompt_metrics(payload),
        }
    metadata = payload.get("retrieved_view")
    request = payload.get("request")
    compact_required = bool(
        isinstance(request, Mapping)
        and request.get("objective") == "reduce_to_known_hardness"
    )
    return {
        "retrieved_characters": len(
            json.dumps(
                retrieved,
                ensure_ascii=False,
                sort_keys=True,
                separators=(",", ":"),
            )
        ),
        "retrieved_counts": {
            key: len(value) if isinstance(value, list) else 0
            for key, value in retrieved.items()
        },
        "retrieved_view_mode": (
            metadata.get("mode")
            if isinstance(metadata, Mapping)
            else "full"
        ),
        "compact_view_errors": (
            list(compact_retrieved_view_errors(payload))
            if compact_required
            else []
        ),
        **frontier_prompt_metrics(payload),
    }
