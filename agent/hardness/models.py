"""Versioned observational records used by the untrusted hardness runner."""

from __future__ import annotations

import hashlib
import json
from dataclasses import asdict, dataclass, field
from typing import Any


HARDNESS_GOAL_SCHEMA = "hardness_goal_v2"
HARDNESS_ROUTE_SCHEMA = "hardness_route_v2"
TYPED_INVENTORY_SCHEMA = "hardness_typed_inventory_entry_v1"
TYPED_CATALOG_SCHEMA = "hardness_typed_catalog_v1"
HARDNESS_GAP_SCHEMA = "hardness_gap_v2"
AUTHORING_TASK_SCHEMA = "hardness_authoring_task_v1"
FAMILY_INSTANTIATION_SCHEMA = "hardness_family_instantiation_v1"
EXACT_AUTHORING_TEMPLATE_SCHEMA = "hardness_exact_authoring_template_v1"
AUTHORING_ATTEMPT_SCHEMA = "hardness_authoring_attempt_v1"
MODEL_PATCH_SCHEMA = "hardness_model_patch_v1"
MODEL_CALL_SCHEMA = "hardness_model_call_v1"
RESULT_SCHEMA = "hardness_agent_result_v1"


def canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=True, separators=(",", ":"), sort_keys=True)


def sha256_id(value: Any) -> str:
    digest = hashlib.sha256(canonical_json(value).encode("utf-8")).hexdigest()
    return f"sha256:{digest}"


@dataclass(frozen=True)
class HardnessGoal:
    job_id: str
    input_module: str
    source_declaration: str
    membership_declaration: str | None
    target_declaration: str | None
    objective: str
    toolchain: str
    input_sha256: str
    lake_manifest_sha256: str
    schema_version: str = HARDNESS_GOAL_SCHEMA
    presentation_policy: str = "exact_user"
    computation_policy: str = "polyprog_compiled_direct_tm"

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class NativeTarget:
    target_declaration: str
    membership_declaration: str
    display: str
    node_id: str = ""


@dataclass(frozen=True)
class TypedInventoryEntry:
    """One observational, type-validated certificate edge from Lean."""

    declaration: str
    capability_kind: str
    component_role: str
    source_fingerprint: str
    target_fingerprint: str
    is_final_facade: bool
    discovery: str
    registry_fingerprint: str
    source_display: str = ""
    target_display: str = ""
    source_node_id: str = ""
    target_node_id: str = ""
    schema_version: str = TYPED_INVENTORY_SCHEMA

    @property
    def entry_id(self) -> str:
        return sha256_id(
            {
                "schema_version": self.schema_version,
                "declaration": self.declaration,
                "capability_kind": self.capability_kind,
                "component_role": self.component_role,
                "source_fingerprint": self.source_fingerprint,
                "target_fingerprint": self.target_fingerprint,
                "is_final_facade": self.is_final_facade,
                "discovery": self.discovery,
                "source_node_id": self.source_node_id,
                "target_node_id": self.target_node_id,
            }
        )

    @property
    def is_semantic_atom(self) -> bool:
        return not self.is_final_facade

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["entry_id"] = self.entry_id
        value["is_semantic_atom"] = self.is_semantic_atom
        return value


@dataclass(frozen=True)
class TypedCatalog:
    """One filtered, observational view over a fingerprint-bound inventory."""

    mode: str
    registry_fingerprint: str
    entries: tuple[TypedInventoryEntry, ...]
    schema_version: str = TYPED_CATALOG_SCHEMA

    @property
    def catalog_id(self) -> str:
        return sha256_id(
            {
                "schema_version": self.schema_version,
                "mode": self.mode,
                "registry_fingerprint": self.registry_fingerprint,
                "entry_ids": [entry.entry_id for entry in self.entries],
            }
        )

    @property
    def agent_interface_count(self) -> int:
        return len(self.entries)

    @property
    def semantic_atomic_interface_count(self) -> int:
        return sum(1 for entry in self.entries if entry.is_semantic_atom)

    def to_dict(self) -> dict[str, Any]:
        role_counts: dict[str, int] = {}
        capability_counts: dict[str, int] = {}
        for entry in self.entries:
            role_counts[entry.component_role] = role_counts.get(entry.component_role, 0) + 1
            capability_counts[entry.capability_kind] = (
                capability_counts.get(entry.capability_kind, 0) + 1
            )
        return {
            "schema_version": self.schema_version,
            "catalog_id": self.catalog_id,
            "mode": self.mode,
            "registry_fingerprint": self.registry_fingerprint,
            "agent_interface_count": self.agent_interface_count,
            "semantic_atomic_interface_count": self.semantic_atomic_interface_count,
            "role_counts": dict(sorted(role_counts.items())),
            "capability_counts": dict(sorted(capability_counts.items())),
            "entries": [entry.to_dict() for entry in self.entries],
        }


@dataclass(frozen=True)
class RouteCandidate:
    target_declaration: str
    membership_declaration: str | None
    atoms: tuple[str, ...]
    roles: tuple[str, ...]
    final_composition_edges: int
    registry_fingerprint: str
    probe_route_key: str = ""
    evidence_kind: str = "reduction"
    completeness_declaration: str | None = None
    hub_declaration: str | None = None
    schema_version: str = HARDNESS_ROUTE_SCHEMA

    @property
    def route_id(self) -> str:
        return sha256_id(
            {
                "schema_version": self.schema_version,
                "target_declaration": self.target_declaration,
                "membership_declaration": self.membership_declaration,
                "atoms": list(self.atoms),
                "roles": list(self.roles),
                "registry_fingerprint": self.registry_fingerprint,
                "evidence_kind": self.evidence_kind,
                "completeness_declaration": self.completeness_declaration,
                "hub_declaration": self.hub_declaration,
            }
        )

    @property
    def cost(self) -> tuple[Any, ...]:
        return (
            0,
            self.final_composition_edges,
            len(self.atoms),
            self.target_declaration,
            self.atoms,
            self.roles,
            self.evidence_kind,
            self.completeness_declaration or "",
            self.hub_declaration or "",
            self.route_id,
        )

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["route_id"] = self.route_id
        value["cost"] = {
            "new_capabilities": 0,
            "final_composition_edges": self.final_composition_edges,
            "atom_count": len(self.atoms),
        }
        return value


@dataclass(frozen=True)
class HardnessGap:
    reason: str
    failure_code: str
    role: str
    source_declaration: str
    target_declaration: str
    expected_capability_head: str
    registry_fingerprint: str
    source_display: str = ""
    target_display: str = ""
    producer: str = "lean_gap_classifier"
    schema_version: str = HARDNESS_GAP_SCHEMA

    @property
    def gap_id(self) -> str:
        return sha256_id(
            {
                "schema_version": self.schema_version,
                "reason": self.reason,
                "failure_code": self.failure_code,
                "role": self.role,
                "source_declaration": self.source_declaration,
                "target_declaration": self.target_declaration,
                "expected_capability_head": self.expected_capability_head,
                "registry_fingerprint": self.registry_fingerprint,
                "producer": self.producer,
            }
        )

    @property
    def cost(self) -> tuple[str, ...]:
        return (
            self.source_declaration,
            self.target_declaration,
            self.reason,
            self.role,
            self.expected_capability_head,
            self.gap_id,
        )

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["gap_id"] = self.gap_id
        return value


@dataclass(frozen=True)
class FamilyInstantiationCandidate:
    family_declaration: str
    argument_declarations: tuple[str, ...]
    role: str
    source_declaration: str
    target_declaration: str
    registry_fingerprint: str
    producer: str = "lean_parameterized_family_matcher"
    schema_version: str = FAMILY_INSTANTIATION_SCHEMA

    @property
    def candidate_id(self) -> str:
        return sha256_id(
            {
                "schema_version": self.schema_version,
                "family_declaration": self.family_declaration,
                "argument_declarations": list(self.argument_declarations),
                "role": self.role,
                "source_declaration": self.source_declaration,
                "target_declaration": self.target_declaration,
                "registry_fingerprint": self.registry_fingerprint,
                "producer": self.producer,
            }
        )

    @property
    def cost(self) -> tuple[Any, ...]:
        return (
            self.family_declaration,
            self.argument_declarations,
            self.role,
            self.candidate_id,
        )

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["candidate_id"] = self.candidate_id
        return value


@dataclass(frozen=True)
class ExactAuthoringTemplateCandidate:
    template_kind: str
    provider_declaration: str
    role: str
    source_declaration: str
    target_declaration: str
    registry_fingerprint: str
    component_declarations: tuple[str, ...] = ()
    producer: str = "lean_exact_authoring_template_matcher"
    schema_version: str = EXACT_AUTHORING_TEMPLATE_SCHEMA

    @property
    def candidate_id(self) -> str:
        return sha256_id(
            {
                "schema_version": self.schema_version,
                "template_kind": self.template_kind,
                "provider_declaration": self.provider_declaration,
                "role": self.role,
                "source_declaration": self.source_declaration,
                "target_declaration": self.target_declaration,
                "registry_fingerprint": self.registry_fingerprint,
                "component_declarations": list(self.component_declarations),
                "producer": self.producer,
            }
        )

    @property
    def cost(self) -> tuple[str, ...]:
        return (
            self.template_kind,
            self.provider_declaration,
            *self.component_declarations,
            self.role,
            self.candidate_id,
        )

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["candidate_id"] = self.candidate_id
        return value


@dataclass(frozen=True)
class AuthoringStageBoundary:
    stage: str
    module: str
    declaration: str
    editable_file: str
    expected_type: str
    fixed_header_sha256: str
    fixed_footer_sha256: str

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class AuthoringTaskPacket:
    gap_id: str
    gap_reason: str
    source_declaration: str
    target_declaration: str
    role: str
    expected_capability_head: str
    expected_type: str = ""
    template_kind: str = ""
    candidate_module: str = ""
    candidate_declaration: str = ""
    allowed_imports: tuple[str, ...] = ()
    editable_files: tuple[str, ...] = ()
    attempt_budget: int = 0
    family_candidate_ids: tuple[str, ...] = ()
    template_candidate_ids: tuple[str, ...] = ()
    fixed_header_sha256: str = ""
    fixed_footer_sha256: str = ""
    stage_boundaries: tuple[AuthoringStageBoundary, ...] = ()
    producer: str = "lean_gap_classifier"
    schema_version: str = AUTHORING_TASK_SCHEMA

    @property
    def task_id(self) -> str:
        return sha256_id(
            {
                "schema_version": self.schema_version,
                "gap_id": self.gap_id,
                "gap_reason": self.gap_reason,
                "source_declaration": self.source_declaration,
                "target_declaration": self.target_declaration,
                "role": self.role,
                "expected_capability_head": self.expected_capability_head,
                "expected_type": self.expected_type,
                "template_kind": self.template_kind,
                "candidate_module": self.candidate_module,
                "candidate_declaration": self.candidate_declaration,
                "allowed_imports": list(self.allowed_imports),
                "editable_files": list(self.editable_files),
                "attempt_budget": self.attempt_budget,
                "family_candidate_ids": list(self.family_candidate_ids),
                "template_candidate_ids": list(self.template_candidate_ids),
                "fixed_header_sha256": self.fixed_header_sha256,
                "fixed_footer_sha256": self.fixed_footer_sha256,
                "stage_boundaries": [
                    boundary.to_dict() for boundary in self.stage_boundaries
                ],
                "producer": self.producer,
            }
        )

    @classmethod
    def from_gap(cls, gap: HardnessGap, **details: Any) -> "AuthoringTaskPacket":
        return cls(
            gap_id=gap.gap_id,
            gap_reason=gap.reason,
            source_declaration=gap.source_declaration,
            target_declaration=gap.target_declaration,
            role=gap.role,
            expected_capability_head=gap.expected_capability_head,
            producer=gap.producer,
            **details,
        )

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["task_id"] = self.task_id
        return value


@dataclass(frozen=True)
class ProbeResult:
    nonce: str
    source_declaration: str
    source_display: str
    registry_fingerprint: str
    targets: tuple[NativeTarget, ...]
    routes: tuple[RouteCandidate, ...]
    source_node_id: str = ""
    inventory_entries: tuple[TypedInventoryEntry, ...] = ()
    gaps: tuple[HardnessGap, ...] = ()
    family_instantiations: tuple[FamilyInstantiationCandidate, ...] = ()
    authoring_templates: tuple[ExactAuthoringTemplateCandidate, ...] = ()
    stdout: str = ""
    stderr: str = ""

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": "hardness_capability_snapshot_v1",
            "nonce": self.nonce,
            "source_declaration": self.source_declaration,
            "source_display": self.source_display,
            "source_node_id": self.source_node_id,
            "registry_fingerprint": self.registry_fingerprint,
            "targets": [asdict(target) for target in self.targets],
            "routes": [route.to_dict() for route in self.routes],
            "inventory_entries": [entry.to_dict() for entry in self.inventory_entries],
            "gaps": [gap.to_dict() for gap in self.gaps],
            "family_instantiations": [
                candidate.to_dict() for candidate in self.family_instantiations
            ],
            "authoring_templates": [
                candidate.to_dict() for candidate in self.authoring_templates
            ],
        }


@dataclass(frozen=True)
class CommandResult:
    command: tuple[str, ...]
    exit_code: int
    stdout: str
    stderr: str
    duration_seconds: float
    timed_out: bool = False

    @property
    def ok(self) -> bool:
        return self.exit_code == 0 and not self.timed_out

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class PlannerDecision:
    mode: str
    selected_route_id: str | None
    reason: str
    model_called: bool = False
    model_ok: bool = False
    model_error: str | None = None
    model_usage: dict[str, Any] | None = None


@dataclass(frozen=True)
class ModelCallRecord:
    call: int
    task_id: str
    stage: str
    editable_file: str
    model: str
    base_url: str
    called: bool
    ok: bool
    protocol_accepted: bool
    prompt_sha256: str
    response_sha256: str
    duration_seconds: float
    http_attempts: int
    status_code: int | None = None
    finish_reason: str | None = None
    usage: dict[str, Any] | None = None
    error: str | None = None
    diagnostics_sha256: str | None = None
    patch_sha256: str | None = None
    prompt_file: str | None = None
    response_file: str | None = None
    patch_file: str | None = None
    schema_version: str = MODEL_CALL_SCHEMA

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class FailureRecord:
    phase: str
    code: str
    retryable: bool
    evidence: str


@dataclass(frozen=True)
class AuthoringStageAttempt:
    stage: str
    module: str
    declaration: str
    candidate_file: str
    candidate_sha256: str
    fixed_header_sha256: str
    fixed_footer_sha256: str
    compile_command: CommandResult
    accepted: bool = False
    source_origin: str = "deterministic_fixture"
    checkpoint_reused: bool = False

    def to_dict(self) -> dict[str, Any]:
        return {
            "stage": self.stage,
            "module": self.module,
            "declaration": self.declaration,
            "candidate_file": self.candidate_file,
            "candidate_sha256": self.candidate_sha256,
            "fixed_header_sha256": self.fixed_header_sha256,
            "fixed_footer_sha256": self.fixed_footer_sha256,
            "compile_command": self.compile_command.to_dict(),
            "accepted": self.accepted,
            "source_origin": self.source_origin,
            "checkpoint_reused": self.checkpoint_reused,
        }


@dataclass(frozen=True)
class AuthoringAttempt:
    attempt: int
    family_candidate: FamilyInstantiationCandidate | None
    template_candidate: ExactAuthoringTemplateCandidate | None
    candidate_module: str
    candidate_declaration: str
    route_declaration: str
    primary_capability_head: str
    candidate_file: str
    candidate_sha256: str
    fixed_header_sha256: str
    fixed_footer_sha256: str
    compile_command: CommandResult
    validation_command: CommandResult | None = None
    accepted: bool = False
    stage_attempts: tuple[AuthoringStageAttempt, ...] = ()
    source_origin: str = "deterministic_fixture"
    model_call_numbers: tuple[int, ...] = ()
    schema_version: str = AUTHORING_ATTEMPT_SCHEMA

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "attempt": self.attempt,
            "family_candidate": (
                self.family_candidate.to_dict() if self.family_candidate else None
            ),
            "template_candidate": (
                self.template_candidate.to_dict() if self.template_candidate else None
            ),
            "candidate_module": self.candidate_module,
            "candidate_declaration": self.candidate_declaration,
            "route_declaration": self.route_declaration,
            "primary_capability_head": self.primary_capability_head,
            "candidate_file": self.candidate_file,
            "candidate_sha256": self.candidate_sha256,
            "fixed_header_sha256": self.fixed_header_sha256,
            "fixed_footer_sha256": self.fixed_footer_sha256,
            "compile_command": self.compile_command.to_dict(),
            "validation_command": (
                self.validation_command.to_dict() if self.validation_command else None
            ),
            "accepted": self.accepted,
            "stage_attempts": [stage.to_dict() for stage in self.stage_attempts],
            "source_origin": self.source_origin,
            "model_call_numbers": list(self.model_call_numbers),
        }


@dataclass
class AgentResult:
    job_id: str
    status: str
    goal: HardnessGoal
    output_dir: str
    route_policy: str = "deterministic"
    catalog_mode: str = "full"
    authoring_policy: str = "disabled"
    authoring_attempt_budget: int = 0
    model_configuration: dict[str, Any] | None = None
    resume_requested: bool = False
    resumed_from_status: str | None = None
    resume_candidate_integrity: str | None = None
    selected_route: RouteCandidate | None = None
    gap: HardnessGap | None = None
    authoring_task: AuthoringTaskPacket | None = None
    planner: PlannerDecision | None = None
    probe: ProbeResult | None = None
    selected_catalog: TypedCatalog | None = None
    post_authoring_probe: ProbeResult | None = None
    authoring_attempts: list[AuthoringAttempt] = field(default_factory=list)
    model_calls: list[ModelCallRecord] = field(default_factory=list)
    authored_source_origin: str | None = None
    authored_candidate_module: str | None = None
    authored_candidate_declaration: str | None = None
    authored_route_declaration: str | None = None
    authored_capability_head: str | None = None
    authored_candidate_file: str | None = None
    authored_candidate_sha256: str | None = None
    authored_stage_files: tuple[str, ...] = ()
    authored_stage_sha256: tuple[str, ...] = ()
    commands: list[CommandResult] = field(default_factory=list)
    failures: list[FailureRecord] = field(default_factory=list)
    artifact_file: str | None = None
    artifact_sha256: str | None = None
    report_file: str | None = None
    schema_version: str = RESULT_SCHEMA

    @property
    def verified(self) -> bool:
        return self.status == "VERIFIED"

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema_version": self.schema_version,
            "job_id": self.job_id,
            "status": self.status,
            "goal": self.goal.to_dict(),
            "output_dir": self.output_dir,
            "execution_policy": {
                "route": self.route_policy,
                "catalog_mode": self.catalog_mode,
                "authoring": self.authoring_policy,
                "authoring_attempt_budget": self.authoring_attempt_budget,
                "model": self.model_configuration,
            },
            "resume_requested": self.resume_requested,
            "resumed_from_status": self.resumed_from_status,
            "resume_candidate_integrity": self.resume_candidate_integrity,
            "selected_route": self.selected_route.to_dict() if self.selected_route else None,
            "gap": self.gap.to_dict() if self.gap else None,
            "authoring_task": (
                self.authoring_task.to_dict() if self.authoring_task else None
            ),
            "planner": asdict(self.planner) if self.planner else None,
            "probe": self.probe.to_dict() if self.probe else None,
            "selected_catalog": (
                self.selected_catalog.to_dict() if self.selected_catalog else None
            ),
            "post_authoring_probe": (
                self.post_authoring_probe.to_dict() if self.post_authoring_probe else None
            ),
            "authoring_attempts": [attempt.to_dict() for attempt in self.authoring_attempts],
            "model_calls": [call.to_dict() for call in self.model_calls],
            "model_called": any(call.called for call in self.model_calls),
            "authored_source_origin": self.authored_source_origin,
            "authored_candidate_module": self.authored_candidate_module,
            "authored_candidate_declaration": self.authored_candidate_declaration,
            "authored_route_declaration": self.authored_route_declaration,
            "authored_capability_head": self.authored_capability_head,
            "authored_candidate_file": self.authored_candidate_file,
            "authored_candidate_sha256": self.authored_candidate_sha256,
            "authored_stage_files": list(self.authored_stage_files),
            "authored_stage_sha256": list(self.authored_stage_sha256),
            "commands": [command.to_dict() for command in self.commands],
            "failures": [asdict(failure) for failure in self.failures],
            "artifact_file": self.artifact_file,
            "artifact_sha256": self.artifact_sha256,
            "report_file": self.report_file,
            "trust_boundary": {
                "lean_reconstructs_final_result": True,
                "route_ir_is_observational": True,
                "typed_inventory_is_observational": True,
                "catalog_filter_cannot_manufacture_capability": True,
                "gap_ir_is_observational": True,
                "gap_ir_cannot_upgrade_blocked_to_success": True,
                "family_ir_is_observational": True,
                "exact_template_ir_is_observational": True,
                "candidate_requires_canonical_head_validation": True,
                "candidate_bundle_requires_exact_primary_and_route_validation": True,
                "program_indexed_stage_bundle_validation": True,
                "per_stage_checkpoint_and_axiom_gate": True,
                "retry_prefix_reuse_requires_same_locked_job_and_source_hash": True,
                "candidate_is_job_local": True,
                "missing_or_changed_resume_candidate_restores_typed_blocker": True,
                "model_output_is_observational": True,
                "model_cannot_select_route_or_task": True,
                "model_patch_is_fenced_to_one_editable_body": True,
            },
        }
