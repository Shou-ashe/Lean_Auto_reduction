"""Typed control records for the general NP-hard reduction agent.

The records in this module are planning and audit data, never proof authority.
Every successful result is backed by a separately elaborated Lean artifact.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass, field, is_dataclass
from enum import Enum
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Sequence


REQUEST_SCHEMA = "general_np_hard_request_v1"
RESULT_SCHEMA = "general_np_hard_result_v1"
GENERATION_EVIDENCE_SCHEMA = "general_np_hard_generation_evidence_v1"
ROOT_GOAL_HEAD = "ComplexityReduction.Certificate.NativeTMNPHard"


class StringEnum(str, Enum):
    def __str__(self) -> str:
        return self.value


class Strategy(StringEnum):
    REUSE_FIRST = "reuse-first"
    BALANCED = "balanced"
    SYNTHESIS_REQUIRED = "synthesis-required"


class ModelPolicy(StringEnum):
    DISABLED = "disabled"
    AUTO = "auto"
    REQUIRED = "required"


class ProofStatus(StringEnum):
    VERIFIED = "VERIFIED"
    BLOCKED = "BLOCKED"
    FAILED_MODEL = "FAILED_MODEL"
    FAILED_LEAN = "FAILED_LEAN"
    INPUT_ERROR = "INPUT_ERROR"
    BUDGET_EXHAUSTED = "BUDGET_EXHAUSTED"


class SolutionClassification(StringEnum):
    VERIFIED_REUSE = "VERIFIED_REUSE"
    VERIFIED_GENERATED = "VERIFIED_GENERATED"
    VERIFIED_AUXILIARY_GENERATION = "VERIFIED_AUXILIARY_GENERATION"
    NONE = "NONE"


class QualificationStatus(StringEnum):
    NOT_REQUESTED = "NOT_REQUESTED"
    NOT_RUN = "NOT_RUN"
    PASSED = "PASSED"
    FAILED = "FAILED"
    INCONCLUSIVE = "INCONCLUSIVE"


class ActionDisposition(StringEnum):
    CLOSED = "CLOSED"
    DECOMPOSED = "DECOMPOSED"
    SYNTHESIS_REQUIRED = "SYNTHESIS_REQUIRED"
    BLOCKED = "BLOCKED"


class ProviderKind(StringEnum):
    REUSE = "reuse"
    THEOREM = "theorem"
    SYNTHESIS = "synthesis"


class GoalKind(StringEnum):
    HARDNESS = "hardness"
    COMPLETENESS = "completeness"
    REDUCTION = "certified-reduction"
    PATH = "certified-path"
    EQUIVALENCE = "certified-equivalence"
    PRESENTATION = "presentation-change"
    PROGRAM = "program"
    SEMANTICS = "semantics"
    COMPLEXITY = "complexity"
    COMPONENT = "component"
    TYPECLASS = "typeclass"
    PROPOSITION = "proposition"
    DATA = "data"
    UNKNOWN = "unknown"


class PremiseKind(StringEnum):
    EXPLICIT = "explicit"
    IMPLICIT = "implicit"
    TYPECLASS = "typeclass"
    PROPOSITION = "proposition"
    DATA = "data"


class SlotStatus(StringEnum):
    DORMANT = "dormant"
    READY = "ready"
    BOUND = "bound"
    VERIFIED = "verified"
    FAILED = "failed"


class FrameStatus(StringEnum):
    WAITING_BINDINGS = "waiting-bindings"
    ACTIVE = "active"
    SATURATED = "saturated"
    VERIFIED = "verified"
    FAILED = "failed"


def _jsonable(value: Any) -> Any:
    if isinstance(value, Enum):
        return value.value
    if isinstance(value, Path):
        return str(value)
    if is_dataclass(value):
        return {key: _jsonable(item) for key, item in asdict(value).items()}
    if isinstance(value, Mapping):
        return {str(key): _jsonable(item) for key, item in value.items()}
    if isinstance(value, (tuple, list, set, frozenset)):
        return [_jsonable(item) for item in value]
    return value


def stable_json(value: Any) -> str:
    return json.dumps(
        _jsonable(value), ensure_ascii=False, sort_keys=True, separators=(",", ":")
    )


def stable_sha256(value: Any) -> str:
    return "sha256:" + hashlib.sha256(stable_json(value).encode("utf-8")).hexdigest()


@dataclass(frozen=True)
class RootGoal:
    input_module: str
    problem_declaration: str
    exact_type: str
    endpoint_fingerprint: str

    @classmethod
    def for_problem(
        cls,
        *,
        input_module: str,
        problem_declaration: str,
        endpoint_fingerprint: str,
    ) -> "RootGoal":
        return cls(
            input_module=input_module,
            problem_declaration=problem_declaration,
            exact_type=f"{ROOT_GOAL_HEAD} {problem_declaration}",
            endpoint_fingerprint=endpoint_fingerprint,
        )


@dataclass(frozen=True)
class GoalKey:
    normalized_goal_fingerprint: str
    local_context_fingerprint: str
    transparency_mode: str
    import_closure_fingerprint: str

    @classmethod
    def create(
        cls,
        *,
        exact_type: str,
        local_context: Sequence[str] = (),
        transparency_mode: str = "reducible",
        import_closure_fingerprint: str = "",
    ) -> "GoalKey":
        return cls(
            normalized_goal_fingerprint=stable_sha256(
                {"exact_type": exact_type.strip()}
            ),
            local_context_fingerprint=stable_sha256(tuple(local_context)),
            transparency_mode=transparency_mode,
            import_closure_fingerprint=import_closure_fingerprint,
        )

    @property
    def fingerprint(self) -> str:
        return stable_sha256(self)


@dataclass(frozen=True)
class OpenGoal:
    goal_id: str
    key: GoalKey
    exact_type: str
    normalized_fingerprint: str
    local_context: tuple[str, ...] = ()
    parent_rule: str | None = None
    producer_frame_id: str | None = None
    producer_slot_id: str | None = None
    dependency_slot_ids: tuple[str, ...] = ()
    ready: bool = True
    attempted_actions: tuple[str, ...] = ()
    last_lean_diagnostics: str | None = None
    normalized_last_diagnostic_hash: str | None = None
    estimated_cost: float = 1.0
    kind: GoalKind = GoalKind.UNKNOWN

    @classmethod
    def create(
        cls,
        *,
        goal_id: str,
        exact_type: str,
        local_context: Sequence[str] = (),
        import_closure_fingerprint: str = "",
        parent_rule: str | None = None,
        producer_frame_id: str | None = None,
        producer_slot_id: str | None = None,
        dependency_slot_ids: Sequence[str] = (),
        ready: bool = True,
        kind: GoalKind = GoalKind.UNKNOWN,
    ) -> "OpenGoal":
        key = GoalKey.create(
            exact_type=exact_type,
            local_context=local_context,
            import_closure_fingerprint=import_closure_fingerprint,
        )
        return cls(
            goal_id=goal_id,
            key=key,
            exact_type=exact_type,
            normalized_fingerprint=key.normalized_goal_fingerprint,
            local_context=tuple(local_context),
            parent_rule=parent_rule,
            producer_frame_id=producer_frame_id,
            producer_slot_id=producer_slot_id,
            dependency_slot_ids=tuple(dependency_slot_ids),
            ready=ready,
            kind=kind,
        )


@dataclass(frozen=True)
class TheoremPremise:
    ordinal: int
    exact_type: str
    kind: PremiseKind
    fingerprint: str

    @classmethod
    def create(
        cls, *, ordinal: int, exact_type: str, kind: PremiseKind
    ) -> "TheoremPremise":
        return cls(
            ordinal=ordinal,
            exact_type=exact_type,
            kind=kind,
            fingerprint=stable_sha256(
                {"ordinal": ordinal, "exact_type": exact_type, "kind": kind.value}
            ),
        )


@dataclass(frozen=True)
class TheoremIndexEntry:
    declaration: str
    module: str
    declaration_type: str
    conclusion_type: str
    conclusion_head: str
    result_fingerprint: str
    universe_parameters: tuple[str, ...] = ()
    premises: tuple[TheoremPremise, ...] = ()
    provenance: str = "environment"
    role_hints: tuple[str, ...] = ()

    @property
    def premise_count(self) -> int:
        return len(self.premises)

    @property
    def candidate_id(self) -> str:
        return stable_sha256(
            {
                "declaration": self.declaration,
                "result_fingerprint": self.result_fingerprint,
            }
        )


@dataclass(frozen=True)
class ReusableFragment:
    exact_type: str
    proof_term: str
    declaration: str | None = None
    module: str | None = None
    imports: tuple[str, ...] = ()
    provenance: str = "environment"
    lean_verified: bool = True
    source_hash: str | None = None


@dataclass(frozen=True)
class BinderSlot:
    slot_id: str
    ordinal: int
    binder_name: str
    binder_kind: PremiseKind
    exact_type: str
    dependency_slot_ids: tuple[str, ...] = ()
    bound_term: str | None = None
    bound_declaration: str | None = None
    module: str | None = None
    imports: tuple[str, ...] = ()
    provenance: str | None = None
    attempted_actions: tuple[str, ...] = ()
    status: SlotStatus = SlotStatus.DORMANT
    type_template_receipt: str | None = None


@dataclass(frozen=True)
class PremiseSlot:
    slot_id: str
    ordinal: int
    premise_kind: PremiseKind
    type_template_receipt: str
    dependency_slot_ids: tuple[str, ...] = ()
    instantiated_exact_type: str | None = None
    child_goal_id: str | None = None
    proof_term: str | None = None
    declaration: str | None = None
    module: str | None = None
    imports: tuple[str, ...] = ()
    provenance: str | None = None
    attempted_actions: tuple[str, ...] = ()
    status: SlotStatus = SlotStatus.DORMANT


@dataclass(frozen=True)
class ApplicationFrame:
    frame_id: str
    parent_goal_id: str
    parent_exact_type: str
    parent_local_context: tuple[str, ...]
    parent_import_closure_fingerprint: str
    parent_kind: GoalKind
    parent_attempted_actions: tuple[str, ...]
    parent_depth: int
    action_id: str
    declaration: str
    declaration_module: str | None
    guidance_id: str | None
    application_skeleton: str
    binder_slots: tuple[BinderSlot, ...] = ()
    premise_slots: tuple[PremiseSlot, ...] = ()
    result_proof_term: str | None = None
    status: FrameStatus = FrameStatus.WAITING_BINDINGS
    lean_receipt_hash: str | None = None
    parent_producer_frame_id: str | None = None
    parent_producer_slot_id: str | None = None
    failure_code: str | None = None
    diagnostic_hash: str | None = None

    @property
    def slots(self) -> tuple[BinderSlot | PremiseSlot, ...]:
        return tuple(sorted((*self.binder_slots, *self.premise_slots), key=lambda slot: slot.ordinal))

    @property
    def saturated(self) -> bool:
        return bool(self.slots) and all(
            slot.status in {SlotStatus.BOUND, SlotStatus.VERIFIED}
            for slot in self.slots
        )


@dataclass(frozen=True)
class GeneratedCapability:
    capability_id: str
    exact_type: str
    declaration: str
    namespace: str
    implementation: str
    source_hash: str
    action_id: str
    module: str | None = None
    provenance: str = "job-local-generated"
    lean_verified: bool = True


@dataclass(frozen=True)
class ResidualObligation:
    obligation_id: str
    exact_type: str
    kind: GoalKind
    suggested_solver: str | None = None
    estimated_cost: float = 1.0
    diagnostics: str | None = None


@dataclass(frozen=True)
class ExactClosureResult:
    goal_key: GoalKey
    closed: bool
    proof_term: str | None = None
    declaration: str | None = None
    provenance: str | None = None
    lean_verified: bool = False
    diagnostics: tuple[str, ...] = ()
    checked_candidate_count: int = 0


@dataclass(frozen=True)
class ProofGuidance:
    guidance_id: str
    goal_key: GoalKey
    candidate_declaration: str
    declaration_provenance: str
    instantiated_universe_arguments: tuple[str, ...]
    application_skeleton: str
    generated_premises: tuple[TheoremPremise, ...]
    already_closed_premises: tuple[ReusableFragment, ...]
    reusable_fragments: tuple[ReusableFragment, ...]
    residual_obligations: tuple[ResidualObligation, ...]
    suggested_proof_mode: str
    coverage_score: float
    estimated_cost: float
    confidence: float
    diagnostics: tuple[str, ...] = ()
    alternative_action_ids: tuple[str, ...] = ()

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "ProofGuidance":
        goal = value["goal_key"]
        premises = tuple(
            TheoremPremise(
                ordinal=int(item["ordinal"]),
                exact_type=str(item["exact_type"]),
                kind=PremiseKind(item["kind"]),
                fingerprint=str(item["fingerprint"]),
            )
            for item in value.get("generated_premises", ())
        )
        fragments = tuple(
            ReusableFragment(**item)
            for item in value.get("reusable_fragments", ())
        )
        closed = tuple(
            ReusableFragment(**item)
            for item in value.get("already_closed_premises", ())
        )
        residuals = tuple(
            ResidualObligation(
                obligation_id=item["obligation_id"],
                exact_type=item["exact_type"],
                kind=GoalKind(item["kind"]),
                suggested_solver=item.get("suggested_solver"),
                estimated_cost=float(item.get("estimated_cost", 1.0)),
                diagnostics=item.get("diagnostics"),
            )
            for item in value.get("residual_obligations", ())
        )
        return cls(
            guidance_id=str(value["guidance_id"]),
            goal_key=GoalKey(**goal),
            candidate_declaration=str(value["candidate_declaration"]),
            declaration_provenance=str(value["declaration_provenance"]),
            instantiated_universe_arguments=tuple(
                value.get("instantiated_universe_arguments", ())
            ),
            application_skeleton=str(value["application_skeleton"]),
            generated_premises=premises,
            already_closed_premises=closed,
            reusable_fragments=fragments,
            residual_obligations=residuals,
            suggested_proof_mode=str(value["suggested_proof_mode"]),
            coverage_score=float(value["coverage_score"]),
            estimated_cost=float(value["estimated_cost"]),
            confidence=float(value["confidence"]),
            diagnostics=tuple(value.get("diagnostics", ())),
            alternative_action_ids=tuple(value.get("alternative_action_ids", ())),
        )


@dataclass(frozen=True)
class ConstructionContract:
    contract_id: str
    goal_key: GoalKey
    exact_expected_lean_type: str
    frozen_source_handle: str | None
    frozen_target_handle: str | None
    available_inputs: tuple[str, ...]
    reusable_declarations: tuple[str, ...]
    already_closed_fragments: tuple[ReusableFragment, ...]
    residual_obligations: tuple[ResidualObligation, ...]
    semantic_requirements: tuple[str, ...]
    complexity_requirements: tuple[str, ...]
    composition_requirements: tuple[str, ...]
    allowed_construction_modes: tuple[str, ...]
    forbidden_declarations: tuple[str, ...]
    forbidden_edits: tuple[str, ...]
    validation_commands: tuple[tuple[str, ...], ...]


@dataclass(frozen=True)
class CandidateAction:
    action_id: str
    provider: ProviderKind
    disposition: ActionDisposition
    goal_key: GoalKey
    estimated_cost: float
    declaration: str | None = None
    proof_term: str | None = None
    guidance_id: str | None = None
    contract_id: str | None = None
    residual_obligation_ids: tuple[str, ...] = ()
    provenance: str = "environment"
    lean_verified: bool = False
    metadata: Mapping[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class SubstepPlan:
    goal_key: GoalKey
    exact_closure_result: ExactClosureResult
    ranked_proof_guidance: tuple[ProofGuidance, ...]
    reusable_fragments: tuple[ReusableFragment, ...]
    residual_obligations: tuple[ResidualObligation, ...]
    construction_contract: ConstructionContract | None
    candidate_actions: tuple[CandidateAction, ...]
    recommended_action_id: str | None
    cache_key: str
    plan_fingerprint: str


@dataclass
class ProviderStatistics:
    candidate_count: int = 0
    expanded_action_count: int = 0
    lean_checks: int = 0
    model_calls: int = 0
    wall_clock_seconds: float = 0.0
    successful_closures: int = 0
    failed_actions: int = 0


@dataclass(frozen=True)
class ProofStep:
    action_id: str
    provider: ProviderKind
    disposition: ActionDisposition
    goal_id: str
    exact_type: str
    declaration: str | None = None
    solver: str | None = None
    status: str = "verified"


@dataclass(frozen=True)
class ModelCallRecord:
    purpose: str
    called: bool
    ok: bool
    status_code: int | None
    duration_seconds: float
    usage: Mapping[str, Any] | None
    attempts: int
    response_sha256: str
    error: str | None = None
    proposal_id: str | None = None
    provider: str | None = None
    model: str | None = None


@dataclass(frozen=True)
class GenerationEvidence:
    attempted: bool = False
    strategy_call_count: int = 0
    authoring_call_count: int = 0
    new_helper_declarations: tuple[str, ...] = ()
    new_intermediate_declarations: tuple[str, ...] = ()
    new_program_declarations: tuple[str, ...] = ()
    new_semantic_proofs: tuple[str, ...] = ()
    new_complexity_proofs: tuple[str, ...] = ()
    new_certified_reductions: tuple[str, ...] = ()
    substantive_generated_dependencies: tuple[str, ...] = ()
    generated_edge_used_by_final_artifact: bool = False
    generated_source_hashes: tuple[str, ...] = ()
    environment_snapshot_hash: str | None = None
    provenance_verified: bool = False
    mutation_status: QualificationStatus = QualificationStatus.NOT_RUN
    classification: str = "no-generation-needed"
    schema_version: str = GENERATION_EVIDENCE_SCHEMA


@dataclass(frozen=True)
class VerificationSummary:
    exact_type_verified: bool = False
    kernel_verified: bool = False
    axiom_audit_passed: bool = False
    independent_replay_passed: bool = False
    endpoint_equality_audit_passed: bool = False
    placeholder_scan_passed: bool = False
    same_index_audit_passed: bool = False


@dataclass(frozen=True)
class GeneralNPHardRequest:
    input_module: str
    problem_declaration: str
    strategy: Strategy = Strategy.REUSE_FIRST
    profile: str = "research"
    model_policy: ModelPolicy = ModelPolicy.AUTO
    plugins: tuple[str, ...] = ()
    forbidden_declarations: tuple[str, ...] = ()
    schema_version: str = REQUEST_SCHEMA

    def canonical_dict(self) -> dict[str, Any]:
        return _jsonable(self)

    @property
    def fingerprint(self) -> str:
        return stable_sha256(self.canonical_dict())

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "GeneralNPHardRequest":
        if value.get("schema_version", REQUEST_SCHEMA) != REQUEST_SCHEMA:
            raise ValueError("unsupported general NP-hard request schema")
        return cls(
            input_module=str(value["input_module"]),
            problem_declaration=str(value["problem_declaration"]),
            strategy=Strategy(value.get("strategy", Strategy.REUSE_FIRST.value)),
            profile=str(value.get("profile", "research")),
            model_policy=ModelPolicy(value.get("model_policy", ModelPolicy.AUTO.value)),
            plugins=tuple(value.get("plugins", ())),
            forbidden_declarations=tuple(value.get("forbidden_declarations", ())),
        )


@dataclass
class GeneralNPHardResult:
    proof_status: ProofStatus
    solution_classification: SolutionClassification
    qualification_status: QualificationStatus
    root_goal: RootGoal
    strategy: Strategy
    profile: str
    output_dir: str
    job_id: str = ""
    display_status: str | None = None
    selected_proof_route: tuple[str, ...] = ()
    proof_tree: tuple[ProofStep, ...] = ()
    capability_planner_decisions: tuple[Mapping[str, Any], ...] = ()
    substep_plans: tuple[SubstepPlan, ...] = ()
    action_provider_statistics: Mapping[str, ProviderStatistics] = field(default_factory=dict)
    theorem_candidates: tuple[TheoremIndexEntry, ...] = ()
    construction_frontiers: tuple[Mapping[str, Any], ...] = ()
    synthesis_designs: tuple[Mapping[str, Any], ...] = ()
    generated_declarations: tuple[str, ...] = ()
    model_calls: tuple[ModelCallRecord, ...] = ()
    lean_commands: tuple[Mapping[str, Any], ...] = ()
    verification: VerificationSummary = VerificationSummary()
    blocker: Mapping[str, Any] | None = None
    generation_evidence: GenerationEvidence = GenerationEvidence()
    artifact_file: str | None = None
    artifact_sha256: str | None = None
    input_identity: Mapping[str, Any] | None = None
    environment_snapshot: Mapping[str, Any] | None = None
    expanded_state_count: int = 0
    requeued_failure_state_count: int = 0
    pruned_cycle_count: int = 0
    max_observed_search_depth: int = 0
    application_frame_count: int = 0
    verified_application_frame_count: int = 0
    data_binding_count: int = 0
    dependent_goal_activation_count: int = 0
    recursive_substep_plan_count: int = 0
    generated_capability_count: int = 0
    final_frontier_size: int = 0
    frontier_exhaustion_receipt: Mapping[str, Any] | None = None
    per_goal_attempted_actions: Mapping[str, tuple[str, ...]] = field(default_factory=dict)
    final_route_audit_receipt: Mapping[str, Any] | None = None
    schema_version: str = RESULT_SCHEMA

    def __post_init__(self) -> None:
        if self.display_status is None:
            if self.proof_status == ProofStatus.VERIFIED:
                self.display_status = self.solution_classification.value
            else:
                self.display_status = self.proof_status.value

    @property
    def verified(self) -> bool:
        return self.proof_status == ProofStatus.VERIFIED and self.verification.kernel_verified

    @property
    def model_call_count(self) -> int:
        return sum(record.called for record in self.model_calls)

    def to_dict(self) -> dict[str, Any]:
        payload = _jsonable(self)
        payload["model_call_count"] = self.model_call_count
        payload["trust_boundary"] = {
            "python_and_model_are_observational": True,
            "typed_unification_runs_in_lean": True,
            "core_proof_and_qualification_are_separate": True,
            "final_authority": "lean-kernel",
        }
        return payload


__all__ = [
    "ActionDisposition",
    "ApplicationFrame",
    "BinderSlot",
    "CandidateAction",
    "ConstructionContract",
    "ExactClosureResult",
    "GENERATION_EVIDENCE_SCHEMA",
    "GeneralNPHardRequest",
    "GeneralNPHardResult",
    "GenerationEvidence",
    "GeneratedCapability",
    "GoalKey",
    "GoalKind",
    "ModelCallRecord",
    "ModelPolicy",
    "OpenGoal",
    "PremiseKind",
    "PremiseSlot",
    "FrameStatus",
    "ProofGuidance",
    "ProofStatus",
    "ProofStep",
    "ProviderKind",
    "ProviderStatistics",
    "QualificationStatus",
    "REQUEST_SCHEMA",
    "RESULT_SCHEMA",
    "ResidualObligation",
    "ReusableFragment",
    "RootGoal",
    "SolutionClassification",
    "Strategy",
    "SlotStatus",
    "SubstepPlan",
    "TheoremIndexEntry",
    "TheoremPremise",
    "VerificationSummary",
    "stable_json",
    "stable_sha256",
]
