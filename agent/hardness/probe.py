"""Parser for nonce-bound Lean probe observations."""

from __future__ import annotations

from .models import (
    ExactAuthoringTemplateCandidate,
    FamilyInstantiationCandidate,
    HardnessGap,
    NativeTarget,
    ProbeResult,
    RouteCandidate,
    TypedInventoryEntry,
)


MARKER = "HARDNESS_AGENT"
SCHEMA_VERSION = "hardness_probe_v1"


def _fields(line: str) -> list[str] | None:
    position = line.find(MARKER + "\t")
    if position < 0:
        return None
    return line[position:].split("\t")


def _optional_name(value: str) -> str | None:
    normalized = value.strip()
    return None if normalized in {"", "[anonymous]"} else normalized


def parse_probe_output(*, stdout: str, stderr: str, nonce: str) -> ProbeResult:
    source_declaration = ""
    source_display = ""
    source_node_id = ""
    registry_fingerprint = ""
    targets: dict[str, NativeTarget] = {}
    route_rows: list[
        tuple[
            str,
            str,
            str,
            tuple[str, ...],
            tuple[str, ...],
            int,
            str,
            str | None,
            str | None,
        ]
    ] = []
    inventory_rows: list[
        tuple[str, str, str, str, str, bool, str, str, str, str, str, str]
    ] = []
    gap_rows: list[tuple[str, str, str, str, str, str, str, str, str, str]] = []
    family_rows: list[tuple[str, tuple[str, ...], str, str, str, str, str]] = []
    template_rows: list[tuple[str, str, str, str, str, str, str, tuple[str, ...]]] = []
    for line in f"{stdout}\n{stderr}".splitlines():
        fields = _fields(line)
        if fields is None or len(fields) < 4:
            continue
        if fields[1] != SCHEMA_VERSION or fields[2] != nonce:
            continue
        kind = fields[3]
        if kind == "registry" and len(fields) >= 5:
            registry_fingerprint = fields[4].strip()
        elif kind == "source" and len(fields) >= 6:
            source_declaration = fields[4].strip()
            source_display = fields[5].strip()
            source_node_id = fields[6].strip() if len(fields) >= 7 else ""
        elif kind == "target" and len(fields) >= 7:
            target = NativeTarget(
                target_declaration=fields[4].strip(),
                membership_declaration=fields[5].strip(),
                display=fields[6].strip(),
                node_id=fields[7].strip() if len(fields) >= 8 else "",
            )
            targets[target.target_declaration] = target
        elif kind == "route" and len(fields) >= 10:
            try:
                final_penalty = int(fields[9].strip())
            except ValueError:
                continue
            route_rows.append(
                (
                    fields[4].strip(),
                    fields[5].strip(),
                    fields[6].strip(),
                    tuple(value for value in fields[7].split(",") if value),
                    tuple(value for value in fields[8].split(",") if value),
                    final_penalty,
                    fields[10].strip() if len(fields) >= 11 else "reduction",
                    _optional_name(fields[11]) if len(fields) >= 12 else None,
                    _optional_name(fields[12]) if len(fields) >= 13 else None,
                )
            )
        elif kind == "inventory" and len(fields) >= 14:
            final_facade = fields[9].strip().lower()
            if final_facade not in {"true", "false"}:
                continue
            inventory_rows.append(
                (
                    fields[4].strip(),
                    fields[5].strip(),
                    fields[6].strip(),
                    fields[7].strip(),
                    fields[8].strip(),
                    final_facade == "true",
                    fields[10].strip(),
                    fields[11].strip(),
                    fields[12].strip(),
                    fields[13].strip(),
                    fields[14].strip() if len(fields) >= 15 else "",
                    fields[15].strip() if len(fields) >= 16 else "",
                )
            )
        elif kind == "gap" and len(fields) >= 14:
            gap_rows.append(
                (
                    fields[4].strip(),
                    fields[5].strip(),
                    fields[6].strip(),
                    fields[7].strip(),
                    fields[8].strip(),
                    fields[9].strip(),
                    fields[10].strip(),
                    fields[11].strip(),
                    fields[12].strip(),
                    fields[13].strip(),
                )
            )
        elif kind == "family" and len(fields) >= 11:
            family_rows.append(
                (
                    fields[4].strip(),
                    tuple(value for value in fields[5].split(",") if value),
                    fields[6].strip(),
                    fields[7].strip(),
                    fields[8].strip(),
                    fields[9].strip(),
                    fields[10].strip(),
                )
            )
        elif kind == "template" and len(fields) >= 11:
            template_rows.append(
                (
                    fields[4].strip(),
                    fields[5].strip(),
                    fields[6].strip(),
                    fields[7].strip(),
                    fields[8].strip(),
                    fields[9].strip(),
                    fields[10].strip(),
                    tuple(
                        value.strip()
                        for value in (fields[11].split(",") if len(fields) >= 12 else ())
                        if value.strip()
                    ),
                )
            )
    if not registry_fingerprint:
        raise ValueError("probe output did not contain this job's registry fingerprint")
    if not source_declaration:
        raise ValueError("probe output did not contain this job's source declaration")
    allowed_evidence_kinds = {
        "reduction",
        "reduction_with_membership",
        "native_membership",
        "registered_completeness",
        "transported_completeness",
    }
    routes = tuple(
        sorted(
            (
                RouteCandidate(
                    probe_route_key=probe_key,
                    target_declaration=target_declaration,
                    membership_declaration=_optional_name(membership_declaration),
                    atoms=atoms,
                    roles=roles,
                    final_composition_edges=final_penalty,
                    registry_fingerprint=registry_fingerprint,
                    evidence_kind=evidence_kind,
                    completeness_declaration=completeness_declaration,
                    hub_declaration=hub_declaration,
                )
                for (
                    probe_key,
                    target_declaration,
                    membership_declaration,
                    atoms,
                    roles,
                    final_penalty,
                    evidence_kind,
                    completeness_declaration,
                    hub_declaration,
                ) in route_rows
                if evidence_kind in allowed_evidence_kinds
            ),
            key=lambda route: route.cost,
        )
    )
    allowed_inventory_kinds = {
        "certified_reduction",
        "certified_equiv",
        "certified_presentation_change",
    }
    allowed_inventory_roles = {
        "ingress",
        "sharedGadget",
        "egress",
        "finalComposition",
        "unannotated",
    }
    inventory_by_id: dict[str, TypedInventoryEntry] = {}
    for (
        declaration,
        capability_kind,
        component_role,
        source_fingerprint,
        target_fingerprint,
        is_final_facade,
        discovery,
        entry_fingerprint,
        inventory_source_display,
        inventory_target_display,
        source_node_id_value,
        target_node_id_value,
    ) in inventory_rows:
        if not (
            declaration
            and capability_kind in allowed_inventory_kinds
            and component_role in allowed_inventory_roles
            and source_fingerprint
            and target_fingerprint
            and discovery == "registered"
            and entry_fingerprint == registry_fingerprint
            and is_final_facade == (component_role == "finalComposition")
            and (not is_final_facade or capability_kind == "certified_reduction")
        ):
            continue
        entry = TypedInventoryEntry(
            declaration=declaration,
            capability_kind=capability_kind,
            component_role=component_role,
            source_fingerprint=source_fingerprint,
            target_fingerprint=target_fingerprint,
            is_final_facade=is_final_facade,
            discovery=discovery,
            registry_fingerprint=entry_fingerprint,
            source_display=inventory_source_display,
            target_display=inventory_target_display,
            source_node_id=source_node_id_value,
            target_node_id=target_node_id_value,
        )
        inventory_by_id.setdefault(entry.entry_id, entry)
    inventory_entries = tuple(
        sorted(inventory_by_id.values(), key=lambda entry: entry.entry_id)
    )
    gaps_by_id: dict[str, HardnessGap] = {}
    for (
        reason,
        failure_code,
        role,
        source_declaration,
        target_declaration,
        expected_capability_head,
        source_display,
        target_display,
        producer,
        gap_fingerprint,
    ) in gap_rows:
        if gap_fingerprint != registry_fingerprint or producer != "lean_gap_classifier":
            continue
        gap = HardnessGap(
            reason=reason,
            failure_code=failure_code,
            role=role,
            source_declaration=source_declaration,
            target_declaration=target_declaration,
            expected_capability_head=expected_capability_head,
            registry_fingerprint=registry_fingerprint,
            source_display=source_display,
            target_display=target_display,
            producer=producer,
        )
        gaps_by_id[gap.gap_id] = gap
    family_candidates_by_id: dict[str, FamilyInstantiationCandidate] = {}
    for (
        family_declaration,
        argument_declarations,
        role,
        family_source,
        family_target,
        producer,
        family_fingerprint,
    ) in family_rows:
        if (
            family_fingerprint != registry_fingerprint
            or producer != "lean_parameterized_family_matcher"
        ):
            continue
        candidate = FamilyInstantiationCandidate(
            family_declaration=family_declaration,
            argument_declarations=argument_declarations,
            role=role,
            source_declaration=family_source,
            target_declaration=family_target,
            registry_fingerprint=registry_fingerprint,
            producer=producer,
        )
        family_candidates_by_id[candidate.candidate_id] = candidate
    template_candidates_by_id: dict[str, ExactAuthoringTemplateCandidate] = {}
    for (
        template_kind,
        provider_declaration,
        role,
        template_source,
        template_target,
        producer,
        template_fingerprint,
        component_declarations,
    ) in template_rows:
        if (
            template_kind
            not in {
                "lawful_presentation",
                "primitive_admission",
                "program_indexed_reduction",
                "program_indexed_model",
                "native_membership",
            }
            or template_fingerprint != registry_fingerprint
            or producer != "lean_exact_authoring_template_matcher"
        ):
            continue
        if template_kind in {"program_indexed_reduction", "native_membership"}:
            if len(component_declarations) != 3:
                continue
        elif template_kind == "program_indexed_model":
            if len(component_declarations) != 2:
                continue
        elif component_declarations:
            continue
        candidate = ExactAuthoringTemplateCandidate(
            template_kind=template_kind,
            provider_declaration=provider_declaration,
            role=role,
            source_declaration=template_source,
            target_declaration=template_target,
            registry_fingerprint=registry_fingerprint,
            component_declarations=component_declarations,
            producer=producer,
        )
        template_candidates_by_id[candidate.candidate_id] = candidate
    return ProbeResult(
        nonce=nonce,
        source_declaration=source_declaration,
        source_display=source_display,
        registry_fingerprint=registry_fingerprint,
        targets=tuple(targets[name] for name in sorted(targets)),
        routes=routes,
        source_node_id=source_node_id,
        inventory_entries=inventory_entries,
        gaps=tuple(sorted(gaps_by_id.values(), key=lambda gap: gap.cost)),
        family_instantiations=tuple(
            sorted(family_candidates_by_id.values(), key=lambda candidate: candidate.cost)
        ),
        authoring_templates=tuple(
            sorted(template_candidates_by_id.values(), key=lambda candidate: candidate.cost)
        ),
        stdout=stdout,
        stderr=stderr,
    )
