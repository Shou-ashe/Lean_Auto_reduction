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
    STRUCTURAL = "structural"
    PLUGIN = "plugin"
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


class CandidateRole(StringEnum):
    EXACT_CLOSURE = "exact-closure"
    CONDITIONAL_CLOSURE = "conditional-closure"
    SCAFFOLD = "scaffold"
    PRIMITIVE = "primitive"
    CONSTRUCTOR = "constructor"
    VERIFIED_EXAMPLE = "verified-example"


class CapabilityKind(StringEnum):
    GADGET = "gadget"
    LANGUAGE_INTERPRETATION = "language-interpretation"
    DIRECT_TM = "direct-tm"
    SEMANTIC = "semantic"
    FINAL_PACKAGING = "final-packaging"
    GENERIC_HELPER = "generic-helper"


class GeneratorStatus(StringEnum):
    PROPOSED = "proposed"
    PLAN_INFEASIBLE = "plan-infeasible"
    NEEDS_LOOKUP = "needs-lookup"
    NEEDS_REPLAN = "needs-replan"
    PROTOCOL_INVALID = "protocol-invalid"


class ContributionClass(StringEnum):
    THEOREM_REUSE = "THEOREM_REUSE"
    THEOREM_COMPOSITION = "THEOREM_COMPOSITION"
    THEOREM_GUIDED_GENERATION = "THEOREM_GUIDED_GENERATION"
    GENERATED_GLUE = "GENERATED_GLUE"
    GENERATED_CAPABILITY = "GENERATED_CAPABILITY"
    DETERMINISTIC_GENERATED_CAPABILITY = "DETERMINISTIC_GENERATED_CAPABILITY"
    MODEL_GENERATED_CAPABILITY = "MODEL_GENERATED_CAPABILITY"
    HYBRID_GENERATED_CAPABILITY = "HYBRID_GENERATED_CAPABILITY"


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
    declaration_kind: str | None = None
    target_binders: tuple[str, ...] = ()
    target_body: str | None = None

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
class CandidateReceipt:
    """Lean-grounded classification of one actually instantiated candidate."""

    candidate_id: str
    declaration: str
    exact_type: str
    module: str | None
    declaration_kind: str | None
    candidate_role: CandidateRole
    exact_closure: bool
    residual_obligations: tuple[str, ...] = ()
    application_skeleton: str | None = None
    dependency_distance: int = 0
    forbidden_status: str = "allowed"
    historical_success: float = 0.0
    estimated_cost: float = 1.0

    @classmethod
    def create(
        cls,
        *,
        entry: TheoremIndexEntry,
        role: CandidateRole,
        exact_closure: bool,
        residual_obligations: Sequence[str] = (),
        application_skeleton: str | None = None,
        dependency_distance: int = 0,
        forbidden_status: str = "allowed",
        historical_success: float = 0.0,
        estimated_cost: float = 1.0,
    ) -> "CandidateReceipt":
        if exact_closure and residual_obligations:
            raise ValueError("an exact-closure candidate cannot retain residual obligations")
        if exact_closure and role != CandidateRole.EXACT_CLOSURE:
            raise ValueError("exact closure requires the exact-closure candidate role")
        return cls(
            candidate_id=entry.candidate_id,
            declaration=entry.declaration,
            exact_type=entry.declaration_type,
            module=entry.module,
            declaration_kind=entry.declaration_kind,
            candidate_role=role,
            exact_closure=exact_closure,
            residual_obligations=tuple(residual_obligations),
            application_skeleton=application_skeleton,
            dependency_distance=max(0, dependency_distance),
            forbidden_status=forbidden_status,
            historical_success=max(0.0, min(1.0, historical_success)),
            estimated_cost=max(0.0, estimated_cost),
        )

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "CandidateReceipt":
        return cls(
            candidate_id=str(value["candidate_id"]),
            declaration=str(value["declaration"]),
            exact_type=str(value["exact_type"]),
            module=value.get("module"),
            declaration_kind=value.get("declaration_kind"),
            candidate_role=CandidateRole(value["candidate_role"]),
            exact_closure=bool(value["exact_closure"]),
            residual_obligations=tuple(value.get("residual_obligations", ())),
            application_skeleton=value.get("application_skeleton"),
            dependency_distance=int(value.get("dependency_distance", 0)),
            forbidden_status=str(value.get("forbidden_status", "allowed")),
            historical_success=float(value.get("historical_success", 0.0)),
            estimated_cost=float(value.get("estimated_cost", 1.0)),
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
    candidate_kind: str | None = None
    target_binders: tuple[str, ...] = ()
    target_body: str | None = None

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
            candidate_kind=value.get("candidate_kind"),
            target_binders=tuple(value.get("target_binders", ())),
            target_body=value.get("target_body"),
        )


@dataclass(frozen=True)
class TheoremApplicationPlan:
    plan_id: str
    candidate_id: str
    exact_instantiation: str
    application_skeleton: str
    solved_premises: tuple[str, ...]
    residual_obligations: tuple[str, ...]
    expected_result_type: str
    contribution_class: ContributionClass
    forbidden_receipt: str = "allowed"

    @classmethod
    def create(
        cls,
        *,
        candidate_id: str,
        exact_instantiation: str,
        application_skeleton: str,
        solved_premises: Sequence[str],
        residual_obligations: Sequence[str],
        expected_result_type: str,
        contribution_class: ContributionClass,
        forbidden_receipt: str = "allowed",
    ) -> "TheoremApplicationPlan":
        payload = {
            "candidate_id": candidate_id,
            "exact_instantiation": exact_instantiation,
            "application_skeleton": application_skeleton,
            "solved_premises": tuple(solved_premises),
            "residual_obligations": tuple(residual_obligations),
            "expected_result_type": expected_result_type,
            "contribution_class": contribution_class,
            "forbidden_receipt": forbidden_receipt,
        }
        return cls(
            plan_id="theorem-plan-"
            + stable_sha256(payload).removeprefix("sha256:")[:24],
            **payload,
        )

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "TheoremApplicationPlan":
        return cls(
            plan_id=str(value["plan_id"]),
            candidate_id=str(value["candidate_id"]),
            exact_instantiation=str(value["exact_instantiation"]),
            application_skeleton=str(value["application_skeleton"]),
            solved_premises=tuple(value.get("solved_premises", ())),
            residual_obligations=tuple(value.get("residual_obligations", ())),
            expected_result_type=str(value["expected_result_type"]),
            contribution_class=ContributionClass(value["contribution_class"]),
            forbidden_receipt=str(value.get("forbidden_receipt", "allowed")),
        )


@dataclass(frozen=True)
class CapabilityPlan:
    plan_id: str
    capability_kind: CapabilityKind
    goal_id: str
    exact_goal: str
    selected_route: str
    selected_action_id: str | None
    selected_design_id: str | None
    selected_candidate_ids: tuple[str, ...]
    construction_basis_ids: tuple[str, ...]
    forbidden_closure_ids: tuple[str, ...]
    proof_outline: tuple[str, ...]
    helper_specs: tuple[Mapping[str, Any], ...]
    witness_schema: Mapping[str, Any] | None
    residual_goal_dag: tuple[Mapping[str, Any], ...]
    budget_allocation: Mapping[str, int]
    fallback_plans: tuple[Mapping[str, Any], ...]
    context_requirements: tuple[str, ...]
    plan_fingerprint: str

    @classmethod
    def create(
        cls,
        *,
        capability_kind: CapabilityKind,
        goal_id: str,
        exact_goal: str,
        selected_route: str,
        selected_action_id: str | None = None,
        selected_design_id: str | None = None,
        selected_candidate_ids: Sequence[str] = (),
        construction_basis_ids: Sequence[str] = (),
        forbidden_closure_ids: Sequence[str] = (),
        proof_outline: Sequence[str] = (),
        helper_specs: Sequence[Mapping[str, Any]] = (),
        witness_schema: Mapping[str, Any] | None = None,
        residual_goal_dag: Sequence[Mapping[str, Any]] = (),
        budget_allocation: Mapping[str, int] | None = None,
        fallback_plans: Sequence[Mapping[str, Any]] = (),
        context_requirements: Sequence[str] = (),
    ) -> "CapabilityPlan":
        payload = {
            "capability_kind": capability_kind,
            "goal_id": goal_id,
            "exact_goal": exact_goal,
            "selected_route": selected_route,
            "selected_action_id": selected_action_id,
            "selected_design_id": selected_design_id,
            "selected_candidate_ids": tuple(dict.fromkeys(selected_candidate_ids)),
            "construction_basis_ids": tuple(dict.fromkeys(construction_basis_ids)),
            "forbidden_closure_ids": tuple(dict.fromkeys(forbidden_closure_ids)),
            "proof_outline": tuple(proof_outline),
            "helper_specs": tuple(dict(item) for item in helper_specs),
            "witness_schema": None if witness_schema is None else dict(witness_schema),
            "residual_goal_dag": tuple(dict(item) for item in residual_goal_dag),
            "budget_allocation": dict(budget_allocation or {}),
            "fallback_plans": tuple(dict(item) for item in fallback_plans),
            "context_requirements": tuple(context_requirements),
        }
        fingerprint = stable_sha256(payload)
        return cls(
            plan_id="capability-plan-" + fingerprint.removeprefix("sha256:")[:24],
            plan_fingerprint=fingerprint,
            **payload,
        )

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "CapabilityPlan":
        return cls(
            plan_id=str(value["plan_id"]),
            capability_kind=CapabilityKind(value["capability_kind"]),
            goal_id=str(value["goal_id"]),
            exact_goal=str(value["exact_goal"]),
            selected_route=str(value["selected_route"]),
            selected_action_id=value.get("selected_action_id"),
            selected_design_id=value.get("selected_design_id"),
            selected_candidate_ids=tuple(value.get("selected_candidate_ids", ())),
            construction_basis_ids=tuple(value.get("construction_basis_ids", ())),
            forbidden_closure_ids=tuple(value.get("forbidden_closure_ids", ())),
            proof_outline=tuple(value.get("proof_outline", ())),
            helper_specs=tuple(dict(item) for item in value.get("helper_specs", ())),
            witness_schema=(
                dict(value["witness_schema"])
                if isinstance(value.get("witness_schema"), Mapping)
                else None
            ),
            residual_goal_dag=tuple(
                dict(item) for item in value.get("residual_goal_dag", ())
            ),
            budget_allocation={
                str(key): int(item)
                for key, item in dict(value.get("budget_allocation", {})).items()
            },
            fallback_plans=tuple(
                dict(item) for item in value.get("fallback_plans", ())
            ),
            context_requirements=tuple(value.get("context_requirements", ())),
            plan_fingerprint=str(value["plan_fingerprint"]),
        )


@dataclass(frozen=True)
class GeneratorBrief:
    brief_id: str
    plan_id: str
    plan_fingerprint: str
    exact_declaration_name: str
    exact_declaration_type: str
    fixed_declaration_envelope: Mapping[str, str]
    selected_design: Mapping[str, Any]
    selected_candidate_ids: tuple[str, ...]
    ordered_proof_hints: tuple[Mapping[str, Any], ...]
    helper_contracts: tuple[Mapping[str, Any], ...]
    witness_contract: Mapping[str, Any] | None
    expected_residuals: tuple[str, ...]
    allowed_identifier_manifest: tuple[str, ...]
    forbidden_declarations: tuple[str, ...]
    generated_capability_signatures: tuple[Mapping[str, str], ...]
    local_context: tuple[str, ...]
    relevant_definitions: tuple[Mapping[str, str], ...]
    prior_counterexamples: tuple[Mapping[str, Any], ...]
    prior_diagnostics: tuple[str, ...]
    failed_source_hashes: tuple[str, ...]
    brief_fingerprint: str

    @classmethod
    def create(
        cls,
        *,
        plan: CapabilityPlan,
        exact_declaration_name: str,
        exact_declaration_type: str,
        fixed_declaration_envelope: Mapping[str, str],
        selected_design: Mapping[str, Any],
        selected_candidate_ids: Sequence[str] = (),
        ordered_proof_hints: Sequence[Mapping[str, Any]] = (),
        helper_contracts: Sequence[Mapping[str, Any]] = (),
        witness_contract: Mapping[str, Any] | None = None,
        expected_residuals: Sequence[str] = (),
        allowed_identifier_manifest: Sequence[str] = (),
        forbidden_declarations: Sequence[str] = (),
        generated_capability_signatures: Sequence[Mapping[str, str]] = (),
        local_context: Sequence[str] = (),
        relevant_definitions: Sequence[Mapping[str, str]] = (),
        prior_counterexamples: Sequence[Mapping[str, Any]] = (),
        prior_diagnostics: Sequence[str] = (),
        failed_source_hashes: Sequence[str] = (),
    ) -> "GeneratorBrief":
        selected = tuple(dict.fromkeys(selected_candidate_ids))
        permitted = set(plan.selected_candidate_ids) | set(plan.construction_basis_ids)
        if any(candidate not in permitted for candidate in selected):
            raise ValueError("generator brief selected a candidate outside its capability plan")
        payload = {
            "plan_id": plan.plan_id,
            "plan_fingerprint": plan.plan_fingerprint,
            "exact_declaration_name": exact_declaration_name,
            "exact_declaration_type": exact_declaration_type,
            "fixed_declaration_envelope": dict(fixed_declaration_envelope),
            "selected_design": dict(selected_design),
            "selected_candidate_ids": selected,
            "ordered_proof_hints": tuple(dict(item) for item in ordered_proof_hints),
            "helper_contracts": tuple(dict(item) for item in helper_contracts),
            "witness_contract": None if witness_contract is None else dict(witness_contract),
            "expected_residuals": tuple(expected_residuals),
            "allowed_identifier_manifest": tuple(
                dict.fromkeys(allowed_identifier_manifest)
            ),
            "forbidden_declarations": tuple(dict.fromkeys(forbidden_declarations)),
            "generated_capability_signatures": tuple(
                dict(item) for item in generated_capability_signatures
            ),
            "local_context": tuple(local_context),
            "relevant_definitions": tuple(dict(item) for item in relevant_definitions),
            "prior_counterexamples": tuple(dict(item) for item in prior_counterexamples),
            "prior_diagnostics": tuple(prior_diagnostics),
            "failed_source_hashes": tuple(failed_source_hashes),
        }
        fingerprint = stable_sha256(payload)
        return cls(
            brief_id="generator-brief-" + fingerprint.removeprefix("sha256:")[:24],
            brief_fingerprint=fingerprint,
            **payload,
        )

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "GeneratorBrief":
        return cls(
            brief_id=str(value["brief_id"]),
            plan_id=str(value["plan_id"]),
            plan_fingerprint=str(value["plan_fingerprint"]),
            exact_declaration_name=str(value["exact_declaration_name"]),
            exact_declaration_type=str(value["exact_declaration_type"]),
            fixed_declaration_envelope=dict(value.get("fixed_declaration_envelope", {})),
            selected_design=dict(value.get("selected_design", {})),
            selected_candidate_ids=tuple(value.get("selected_candidate_ids", ())),
            ordered_proof_hints=tuple(
                dict(item) for item in value.get("ordered_proof_hints", ())
            ),
            helper_contracts=tuple(
                dict(item) for item in value.get("helper_contracts", ())
            ),
            witness_contract=(
                dict(value["witness_contract"])
                if isinstance(value.get("witness_contract"), Mapping)
                else None
            ),
            expected_residuals=tuple(value.get("expected_residuals", ())),
            allowed_identifier_manifest=tuple(
                value.get("allowed_identifier_manifest", ())
            ),
            forbidden_declarations=tuple(value.get("forbidden_declarations", ())),
            generated_capability_signatures=tuple(
                dict(item)
                for item in value.get("generated_capability_signatures", ())
            ),
            local_context=tuple(value.get("local_context", ())),
            relevant_definitions=tuple(
                dict(item) for item in value.get("relevant_definitions", ())
            ),
            prior_counterexamples=tuple(
                dict(item) for item in value.get("prior_counterexamples", ())
            ),
            prior_diagnostics=tuple(value.get("prior_diagnostics", ())),
            failed_source_hashes=tuple(value.get("failed_source_hashes", ())),
            brief_fingerprint=str(value["brief_fingerprint"]),
        )


@dataclass(frozen=True)
class GeneratorResult:
    result_id: str
    brief_id: str
    status: GeneratorStatus
    implementation_body: str | None = None
    helper_declarations: tuple[str, ...] = ()
    used_candidate_ids: tuple[str, ...] = ()
    used_generated_capabilities: tuple[str, ...] = ()
    planner_hints_followed: tuple[str, ...] = ()
    planner_hints_rejected: tuple[str, ...] = ()
    rejection_reason: str | None = None
    requested_lookup: tuple[str, ...] = ()
    requested_replan: bool = False
    implementation_hash: str | None = None

    @classmethod
    def create(
        cls,
        *,
        brief: GeneratorBrief,
        status: GeneratorStatus,
        implementation_body: str | None = None,
        helper_declarations: Sequence[str] = (),
        used_candidate_ids: Sequence[str] = (),
        used_generated_capabilities: Sequence[str] = (),
        planner_hints_followed: Sequence[str] = (),
        planner_hints_rejected: Sequence[str] = (),
        rejection_reason: str | None = None,
        requested_lookup: Sequence[str] = (),
        requested_replan: bool = False,
    ) -> "GeneratorResult":
        used = tuple(dict.fromkeys(used_candidate_ids))
        if any(candidate not in brief.selected_candidate_ids for candidate in used):
            raise ValueError("generator result used a candidate absent from its brief")
        if status == GeneratorStatus.PROPOSED and not (implementation_body or "").strip():
            raise ValueError("a proposed generator result requires an implementation body")
        if status == GeneratorStatus.NEEDS_LOOKUP and not tuple(requested_lookup):
            raise ValueError("needs-lookup requires at least one requested identifier")
        implementation_hash = (
            stable_sha256(
                {
                    "helpers": tuple(helper_declarations),
                    "body": implementation_body,
                }
            )
            if implementation_body is not None
            else None
        )
        payload = {
            "brief_id": brief.brief_id,
            "status": status,
            "implementation_body": implementation_body,
            "helper_declarations": tuple(helper_declarations),
            "used_candidate_ids": used,
            "used_generated_capabilities": tuple(used_generated_capabilities),
            "planner_hints_followed": tuple(planner_hints_followed),
            "planner_hints_rejected": tuple(planner_hints_rejected),
            "rejection_reason": rejection_reason,
            "requested_lookup": tuple(requested_lookup),
            "requested_replan": requested_replan,
            "implementation_hash": implementation_hash,
        }
        return cls(
            result_id="generator-result-"
            + stable_sha256(payload).removeprefix("sha256:")[:24],
            **payload,
        )

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "GeneratorResult":
        return cls(
            result_id=str(value["result_id"]),
            brief_id=str(value["brief_id"]),
            status=GeneratorStatus(value["status"]),
            implementation_body=value.get("implementation_body"),
            helper_declarations=tuple(value.get("helper_declarations", ())),
            used_candidate_ids=tuple(value.get("used_candidate_ids", ())),
            used_generated_capabilities=tuple(
                value.get("used_generated_capabilities", ())
            ),
            planner_hints_followed=tuple(value.get("planner_hints_followed", ())),
            planner_hints_rejected=tuple(value.get("planner_hints_rejected", ())),
            rejection_reason=value.get("rejection_reason"),
            requested_lookup=tuple(value.get("requested_lookup", ())),
            requested_replan=bool(value.get("requested_replan", False)),
            implementation_hash=value.get("implementation_hash"),
        )


@dataclass(frozen=True)
class ContributionReceipt:
    capability_declaration: str
    contribution_class: ContributionClass
    capability_kind: CapabilityKind | None = None
    plan_id: str | None = None
    brief_id: str | None = None
    generator_result_id: str | None = None
    exact_closure_candidates_used: tuple[str, ...] = ()
    scaffold_candidates_used: tuple[str, ...] = ()
    primitive_candidates_used: tuple[str, ...] = ()
    planner_advice_ids: tuple[str, ...] = ()
    generated_helpers: tuple[str, ...] = ()
    generated_data_objects: tuple[str, ...] = ()
    deterministic_solver_steps: tuple[str, ...] = ()
    model_generated_source_hashes: tuple[str, ...] = ()
    final_artifact_used: bool = False
    forbidden_audit_passed: bool = False
    independent_lean_passed: bool = False

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "ContributionReceipt":
        kind = value.get("capability_kind")
        return cls(
            capability_declaration=str(value["capability_declaration"]),
            contribution_class=ContributionClass(value["contribution_class"]),
            capability_kind=(CapabilityKind(kind) if kind is not None else None),
            plan_id=value.get("plan_id"),
            brief_id=value.get("brief_id"),
            generator_result_id=value.get("generator_result_id"),
            exact_closure_candidates_used=tuple(
                value.get("exact_closure_candidates_used", ())
            ),
            scaffold_candidates_used=tuple(value.get("scaffold_candidates_used", ())),
            primitive_candidates_used=tuple(value.get("primitive_candidates_used", ())),
            planner_advice_ids=tuple(value.get("planner_advice_ids", ())),
            generated_helpers=tuple(value.get("generated_helpers", ())),
            generated_data_objects=tuple(value.get("generated_data_objects", ())),
            deterministic_solver_steps=tuple(
                value.get("deterministic_solver_steps", ())
            ),
            model_generated_source_hashes=tuple(
                value.get("model_generated_source_hashes", ())
            ),
            final_artifact_used=bool(value.get("final_artifact_used", False)),
            forbidden_audit_passed=bool(value.get("forbidden_audit_passed", False)),
            independent_lean_passed=bool(value.get("independent_lean_passed", False)),
        )


@dataclass(frozen=True)
class PlannerEffectReceipt:
    plan_id: str
    selected_action_id: str | None
    selected_candidate_ids: tuple[str, ...]
    selected_design_id: str | None
    generated_brief_id: str | None
    applied_effect: str
    subsequent_event_id: str | None = None
    override_reason: str | None = None

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "PlannerEffectReceipt":
        return cls(
            plan_id=str(value["plan_id"]),
            selected_action_id=value.get("selected_action_id"),
            selected_candidate_ids=tuple(value.get("selected_candidate_ids", ())),
            selected_design_id=value.get("selected_design_id"),
            generated_brief_id=value.get("generated_brief_id"),
            applied_effect=str(value["applied_effect"]),
            subsequent_event_id=value.get("subsequent_event_id"),
            override_reason=value.get("override_reason"),
        )


@dataclass(frozen=True)
class TypedProgramNode:
    """One normalized, typed node in a direct-TM program DAG."""

    node_id: str
    operation: str
    input_encoded_type: str
    output_encoded_type: str
    function_term: str
    primitive_declaration: str | None = None
    dependency_node_ids: tuple[str, ...] = ()
    endpoint_equality: str | None = None
    generated_helper_name: str | None = None
    status: str = "planned"

    @classmethod
    def create(
        cls,
        *,
        operation: str,
        input_encoded_type: str,
        output_encoded_type: str,
        function_term: str,
        primitive_declaration: str | None = None,
        dependency_node_ids: Sequence[str] = (),
        endpoint_equality: str | None = None,
        generated_helper_name: str | None = None,
        status: str = "planned",
    ) -> "TypedProgramNode":
        payload = {
            "operation": operation,
            "input_encoded_type": input_encoded_type,
            "output_encoded_type": output_encoded_type,
            "function_term": function_term,
            "primitive_declaration": primitive_declaration,
            "dependency_node_ids": tuple(dependency_node_ids),
            "endpoint_equality": endpoint_equality,
            "generated_helper_name": generated_helper_name,
            "status": status,
        }
        return cls(
            node_id="program-node-"
            + stable_sha256(payload).removeprefix("sha256:")[:24],
            **payload,
        )

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "TypedProgramNode":
        return cls(
            node_id=str(value["node_id"]),
            operation=str(value["operation"]),
            input_encoded_type=str(value["input_encoded_type"]),
            output_encoded_type=str(value["output_encoded_type"]),
            function_term=str(value["function_term"]),
            primitive_declaration=value.get("primitive_declaration"),
            dependency_node_ids=tuple(value.get("dependency_node_ids", ())),
            endpoint_equality=value.get("endpoint_equality"),
            generated_helper_name=value.get("generated_helper_name"),
            status=str(value.get("status", "planned")),
        )


@dataclass(frozen=True)
class DirectTMCapabilityPlan:
    plan_id: str
    exact_goal: str
    source_language: str
    target_language: str
    interpretation_term: str
    nodes: tuple[TypedProgramNode, ...]
    final_node_id: str
    missing_node_ids: tuple[str, ...]
    endpoint_goal: str
    normalization_receipt: Mapping[str, Any]
    plan_fingerprint: str

    @classmethod
    def create(
        cls,
        *,
        exact_goal: str,
        source_language: str,
        target_language: str,
        interpretation_term: str,
        nodes: Sequence[TypedProgramNode],
        final_node_id: str,
        endpoint_goal: str,
        normalization_receipt: Mapping[str, Any],
        missing_node_ids: Sequence[str] = (),
    ) -> "DirectTMCapabilityPlan":
        normalized_nodes = tuple(nodes)
        ids = tuple(node.node_id for node in normalized_nodes)
        if len(ids) != len(set(ids)):
            raise ValueError("direct-TM program DAG contains duplicate node IDs")
        known = set(ids)
        if final_node_id not in known:
            raise ValueError("direct-TM final node is absent from the program DAG")
        if any(
            dependency not in known
            for node in normalized_nodes
            for dependency in node.dependency_node_ids
        ):
            raise ValueError("direct-TM program DAG references an unknown dependency")

        dependencies = {
            node.node_id: node.dependency_node_ids for node in normalized_nodes
        }
        visiting: set[str] = set()
        visited: set[str] = set()

        def visit(node_id: str) -> None:
            if node_id in visiting:
                raise ValueError("direct-TM program graph is cyclic")
            if node_id in visited:
                return
            visiting.add(node_id)
            for dependency in dependencies[node_id]:
                visit(dependency)
            visiting.remove(node_id)
            visited.add(node_id)

        for node_id in ids:
            visit(node_id)

        missing = tuple(dict.fromkeys(missing_node_ids))
        if any(node_id not in known for node_id in missing):
            raise ValueError("direct-TM missing-node receipt references an unknown node")
        payload = {
            "exact_goal": exact_goal,
            "source_language": source_language,
            "target_language": target_language,
            "interpretation_term": interpretation_term,
            "nodes": normalized_nodes,
            "final_node_id": final_node_id,
            "missing_node_ids": missing,
            "endpoint_goal": endpoint_goal,
            "normalization_receipt": dict(normalization_receipt),
        }
        fingerprint = stable_sha256(payload)
        return cls(
            plan_id="direct-tm-plan-" + fingerprint.removeprefix("sha256:")[:24],
            plan_fingerprint=fingerprint,
            **payload,
        )

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "DirectTMCapabilityPlan":
        return cls(
            plan_id=str(value["plan_id"]),
            exact_goal=str(value["exact_goal"]),
            source_language=str(value["source_language"]),
            target_language=str(value["target_language"]),
            interpretation_term=str(value["interpretation_term"]),
            nodes=tuple(
                TypedProgramNode.from_dict(item) for item in value.get("nodes", ())
            ),
            final_node_id=str(value["final_node_id"]),
            missing_node_ids=tuple(value.get("missing_node_ids", ())),
            endpoint_goal=str(value["endpoint_goal"]),
            normalization_receipt=dict(value.get("normalization_receipt", {})),
            plan_fingerprint=str(value["plan_fingerprint"]),
        )


@dataclass(frozen=True)
class SemanticDirectionPlan:
    direction_id: str
    direction: str
    exact_helper_type: str
    witness_schema: Mapping[str, Any]
    invariant_specs: tuple[Mapping[str, Any], ...]
    primitive_declarations: tuple[str, ...]
    dependency_helper_ids: tuple[str, ...]
    proof_outline: tuple[str, ...]
    preserve_on_sibling_failure: bool
    plan_fingerprint: str

    @classmethod
    def create(
        cls,
        *,
        direction: str,
        exact_helper_type: str,
        witness_schema: Mapping[str, Any],
        invariant_specs: Sequence[Mapping[str, Any]],
        primitive_declarations: Sequence[str],
        dependency_helper_ids: Sequence[str] = (),
        proof_outline: Sequence[str] = (),
        preserve_on_sibling_failure: bool = True,
    ) -> "SemanticDirectionPlan":
        if direction not in {"forward", "reverse"}:
            raise ValueError("semantic direction must be forward or reverse")
        payload = {
            "direction": direction,
            "exact_helper_type": exact_helper_type,
            "witness_schema": dict(witness_schema),
            "invariant_specs": tuple(dict(item) for item in invariant_specs),
            "primitive_declarations": tuple(
                dict.fromkeys(primitive_declarations)
            ),
            "dependency_helper_ids": tuple(
                dict.fromkeys(dependency_helper_ids)
            ),
            "proof_outline": tuple(proof_outline),
            "preserve_on_sibling_failure": preserve_on_sibling_failure,
        }
        fingerprint = stable_sha256(payload)
        return cls(
            direction_id=f"semantic-{direction}-"
            + fingerprint.removeprefix("sha256:")[:20],
            plan_fingerprint=fingerprint,
            **payload,
        )

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "SemanticDirectionPlan":
        return cls(
            direction_id=str(value["direction_id"]),
            direction=str(value["direction"]),
            exact_helper_type=str(value["exact_helper_type"]),
            witness_schema=dict(value.get("witness_schema", {})),
            invariant_specs=tuple(
                dict(item) for item in value.get("invariant_specs", ())
            ),
            primitive_declarations=tuple(
                value.get("primitive_declarations", ())
            ),
            dependency_helper_ids=tuple(
                value.get("dependency_helper_ids", ())
            ),
            proof_outline=tuple(value.get("proof_outline", ())),
            preserve_on_sibling_failure=bool(
                value.get("preserve_on_sibling_failure", True)
            ),
            plan_fingerprint=str(value["plan_fingerprint"]),
        )


@dataclass(frozen=True)
class SemanticCapabilityPlan:
    plan_id: str
    exact_goal: str
    source_language: str
    target_language: str
    interpretation_term: str
    forward: SemanticDirectionPlan
    reverse: SemanticDirectionPlan
    final_helper_type: str
    final_dependency_ids: tuple[str, ...]
    residual_goal_dag: tuple[Mapping[str, Any], ...]
    plan_fingerprint: str

    @classmethod
    def create(
        cls,
        *,
        exact_goal: str,
        source_language: str,
        target_language: str,
        interpretation_term: str,
        forward: SemanticDirectionPlan,
        reverse: SemanticDirectionPlan,
        final_helper_type: str,
        residual_goal_dag: Sequence[Mapping[str, Any]],
    ) -> "SemanticCapabilityPlan":
        if forward.direction != "forward" or reverse.direction != "reverse":
            raise ValueError("semantic plan requires one forward and one reverse direction")
        dependencies = (forward.direction_id, reverse.direction_id)
        payload = {
            "exact_goal": exact_goal,
            "source_language": source_language,
            "target_language": target_language,
            "interpretation_term": interpretation_term,
            "forward": forward,
            "reverse": reverse,
            "final_helper_type": final_helper_type,
            "final_dependency_ids": dependencies,
            "residual_goal_dag": tuple(dict(item) for item in residual_goal_dag),
        }
        fingerprint = stable_sha256(payload)
        return cls(
            plan_id="semantic-plan-" + fingerprint.removeprefix("sha256:")[:24],
            plan_fingerprint=fingerprint,
            **payload,
        )

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "SemanticCapabilityPlan":
        return cls(
            plan_id=str(value["plan_id"]),
            exact_goal=str(value["exact_goal"]),
            source_language=str(value["source_language"]),
            target_language=str(value["target_language"]),
            interpretation_term=str(value["interpretation_term"]),
            forward=SemanticDirectionPlan.from_dict(value["forward"]),
            reverse=SemanticDirectionPlan.from_dict(value["reverse"]),
            final_helper_type=str(value["final_helper_type"]),
            final_dependency_ids=tuple(value.get("final_dependency_ids", ())),
            residual_goal_dag=tuple(
                dict(item) for item in value.get("residual_goal_dag", ())
            ),
            plan_fingerprint=str(value["plan_fingerprint"]),
        )


@dataclass(frozen=True)
class GadgetCapabilityPlan:
    plan_id: str
    source_relation_receipt: Mapping[str, Any]
    target_gamma_receipt: Mapping[str, Any]
    design_kind: str
    variable_bound: int
    constraint_bound: int
    witness_grammar: Mapping[str, Any]
    output_schema: Mapping[str, Any]
    symmetry_breaking: tuple[str, ...]
    seed_patterns: tuple[Mapping[str, Any], ...]
    selected_generated_gadgets: tuple[str, ...]
    selected_primitive_ids: tuple[str, ...]
    counterexample_policy: Mapping[str, Any]
    enumeration_order: tuple[str, ...]
    fallback_designs: tuple[Mapping[str, Any], ...]
    plan_fingerprint: str

    @classmethod
    def create(
        cls,
        *,
        source_relation_receipt: Mapping[str, Any],
        target_gamma_receipt: Mapping[str, Any],
        design_kind: str,
        variable_bound: int,
        constraint_bound: int,
        witness_grammar: Mapping[str, Any],
        output_schema: Mapping[str, Any],
        symmetry_breaking: Sequence[str] = (),
        seed_patterns: Sequence[Mapping[str, Any]] = (),
        selected_generated_gadgets: Sequence[str] = (),
        selected_primitive_ids: Sequence[str] = (),
        counterexample_policy: Mapping[str, Any] | None = None,
        enumeration_order: Sequence[str] = (),
        fallback_designs: Sequence[Mapping[str, Any]] = (),
    ) -> "GadgetCapabilityPlan":
        if variable_bound < 1 or constraint_bound < 1:
            raise ValueError("gadget search bounds must be positive")
        payload = {
            "source_relation_receipt": dict(source_relation_receipt),
            "target_gamma_receipt": dict(target_gamma_receipt),
            "design_kind": design_kind,
            "variable_bound": variable_bound,
            "constraint_bound": constraint_bound,
            "witness_grammar": dict(witness_grammar),
            "output_schema": dict(output_schema),
            "symmetry_breaking": tuple(symmetry_breaking),
            "seed_patterns": tuple(dict(item) for item in seed_patterns),
            "selected_generated_gadgets": tuple(
                dict.fromkeys(selected_generated_gadgets)
            ),
            "selected_primitive_ids": tuple(
                dict.fromkeys(selected_primitive_ids)
            ),
            "counterexample_policy": dict(counterexample_policy or {}),
            "enumeration_order": tuple(enumeration_order),
            "fallback_designs": tuple(dict(item) for item in fallback_designs),
        }
        fingerprint = stable_sha256(payload)
        return cls(
            plan_id="gadget-plan-" + fingerprint.removeprefix("sha256:")[:24],
            plan_fingerprint=fingerprint,
            **payload,
        )

    @classmethod
    def from_dict(cls, value: Mapping[str, Any]) -> "GadgetCapabilityPlan":
        return cls(
            plan_id=str(value["plan_id"]),
            source_relation_receipt=dict(value.get("source_relation_receipt", {})),
            target_gamma_receipt=dict(value.get("target_gamma_receipt", {})),
            design_kind=str(value["design_kind"]),
            variable_bound=int(value["variable_bound"]),
            constraint_bound=int(value["constraint_bound"]),
            witness_grammar=dict(value.get("witness_grammar", {})),
            output_schema=dict(value.get("output_schema", {})),
            symmetry_breaking=tuple(value.get("symmetry_breaking", ())),
            seed_patterns=tuple(dict(item) for item in value.get("seed_patterns", ())),
            selected_generated_gadgets=tuple(
                value.get("selected_generated_gadgets", ())
            ),
            selected_primitive_ids=tuple(value.get("selected_primitive_ids", ())),
            counterexample_policy=dict(value.get("counterexample_policy", {})),
            enumeration_order=tuple(value.get("enumeration_order", ())),
            fallback_designs=tuple(
                dict(item) for item in value.get("fallback_designs", ())
            ),
            plan_fingerprint=str(value["plan_fingerprint"]),
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
    candidate_receipts: tuple[CandidateReceipt, ...] = ()


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
class StrategyDecision:
    """One model proposal interpreted against an exact proof-search state.

    This record is control data only.  It can select an already typed action or
    synthesis design, or request that the current branch be abandoned; it can
    never certify a proof or create a top-level blocker.
    """

    decision_id: str
    goal_id: str
    state_fingerprint: str
    decision_kind: str
    selected_action_id: str | None = None
    selected_design_id: str | None = None
    requested_backtrack: bool = False
    rationale: str = ""
    confidence: float = 0.0
    proposal_hash: str = ""
    applicable: bool = False


@dataclass(frozen=True)
class StrategyEffectReceipt:
    """Auditable link from a strategy proposal to the next search effect."""

    decision_id: str
    proposal_status: str
    proposed_action_id: str | None
    applied_action_id: str | None
    applied_design_id: str | None
    effect: str
    override_reason: str | None = None
    next_state_fingerprint: str | None = None


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
    excluded_candidate_declarations: tuple[str, ...] = ()
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
            excluded_candidate_declarations=tuple(
                value.get("excluded_candidate_declarations", ())
            ),
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
    context_capsules: tuple[Mapping[str, Any], ...] = ()
    repair_lineage: tuple[Mapping[str, Any], ...] = ()
    capability_plans: tuple[CapabilityPlan, ...] = ()
    theorem_application_plans: tuple[TheoremApplicationPlan, ...] = ()
    generator_briefs: tuple[GeneratorBrief, ...] = ()
    generator_results: tuple[GeneratorResult, ...] = ()
    contribution_receipts: tuple[ContributionReceipt, ...] = ()
    planner_effect_receipts: tuple[PlannerEffectReceipt, ...] = ()
    typed_capability_plans: tuple[Mapping[str, Any], ...] = ()
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
    strategy_valid_proposal_count: int = 0
    strategy_applied_decision_count: int = 0
    strategy_fallback_count: int = 0
    strategy_rejected_count: int = 0
    unused_strategy_call_count: int = 0
    strategy_effect_receipts: tuple[StrategyEffectReceipt, ...] = ()
    finite_candidate_count: int = 0
    finite_counterexample_count: int = 0
    finite_certificate_count: int = 0
    capability_compiler_candidate_count: int = 0
    capability_compiler_certificate_count: int = 0
    generated_lean_check_count: int = 0
    generated_lean_success_count: int = 0
    capability_registration_count: int = 0
    synthesis_design_count: int = 0
    context_expansion_count: int = 0
    repair_authoring_count: int = 0
    duplicate_candidate_rejection_count: int = 0
    repeated_diagnostic_count: int = 0
    context_insufficient_count: int = 0
    unresolved_probe_handle_count: int = 0
    rejected_nonexecutable_design_count: int = 0
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

    def capability_metrics(self) -> dict[str, Any]:
        """Derive the phase/gate metrics from typed receipts, never heuristics."""

        candidate_receipts = tuple(
            receipt
            for plan in self.substep_plans
            for receipt in plan.candidate_receipts
        )
        final_used = tuple(
            receipt for receipt in self.contribution_receipts if receipt.final_artifact_used
        )
        typed_plans = tuple(
            item for item in self.typed_capability_plans if isinstance(item, Mapping)
        )
        direct_plans = tuple(
            item
            for item in typed_plans
            if str(item.get("plan_id") or "").startswith("direct-tm-plan-")
        )
        semantic_plans = tuple(
            item
            for item in typed_plans
            if str(item.get("plan_id") or "").startswith("semantic-plan-")
        )
        gadget_plans = tuple(
            item
            for item in typed_plans
            if str(item.get("plan_id") or "").startswith("gadget-plan-")
        )
        direct_nodes = tuple(
            node
            for plan in direct_plans
            for node in plan.get("nodes", ())
            if isinstance(node, Mapping)
        )
        semantic_directions = tuple(
            direction
            for plan in semantic_plans
            for direction in (plan.get("forward"), plan.get("reverse"))
            if isinstance(direction, Mapping)
        )
        contributions_by_kind = {
            kind: tuple(
                receipt
                for receipt in self.contribution_receipts
                if receipt.capability_kind == kind
            )
            for kind in CapabilityKind
        }
        final_by_kind = {
            kind: tuple(
                receipt
                for receipt in final_used
                if receipt.capability_kind == kind
            )
            for kind in CapabilityKind
        }
        generator_replans = sum(
            result.requested_replan for result in self.generator_results
        )
        generator_lookup_requests = sum(
            result.status == GeneratorStatus.NEEDS_LOOKUP
            for result in self.generator_results
        )
        used_primitive_candidate_ids = {
            candidate_id
            for receipt in self.contribution_receipts
            for candidate_id in receipt.primitive_candidates_used
        }
        theorem_application_plan_count = len(self.theorem_application_plans)
        planner_backtrack_count = sum(
            "backtrack" in receipt.effect for receipt in self.strategy_effect_receipts
        )
        planner_plan_count = (
            len(self.generator_briefs)
            + theorem_application_plan_count
            + generator_replans
            + planner_backtrack_count
        )
        gadget_design_kind_counts: dict[str, int] = {}
        for plan in gadget_plans:
            kind = str(plan.get("design_kind") or "unknown")
            gadget_design_kind_counts[kind] = gadget_design_kind_counts.get(kind, 0) + 1
        prior_counterexamples = tuple(
            item
            for brief in self.generator_briefs
            for item in brief.prior_counterexamples
        )
        semantic_helpers = tuple(
            helper
            for receipt in contributions_by_kind[CapabilityKind.SEMANTIC]
            for helper in receipt.generated_helpers
        )
        direct_contributions = contributions_by_kind[CapabilityKind.DIRECT_TM]
        semantic_contributions = contributions_by_kind[CapabilityKind.SEMANTIC]
        gadget_contributions = contributions_by_kind[CapabilityKind.GADGET]
        metrics: dict[str, Any] = {
            "theorem_exact_closure_count": sum(
                receipt.candidate_role == CandidateRole.EXACT_CLOSURE
                for receipt in candidate_receipts
            ),
            "theorem_scaffold_count": sum(
                receipt.candidate_role
                in {
                    CandidateRole.SCAFFOLD,
                    CandidateRole.CONDITIONAL_CLOSURE,
                    CandidateRole.CONSTRUCTOR,
                }
                for receipt in candidate_receipts
            ),
            "theorem_primitive_count": sum(
                receipt.candidate_role == CandidateRole.PRIMITIVE
                for receipt in candidate_receipts
            )
            + len(used_primitive_candidate_ids),
            "planner_call_count": sum(
                call.called and call.purpose == "strategy-proposal"
                for call in self.model_calls
            ),
            "planner_plan_count": planner_plan_count,
            "planner_brief_count": len(self.generator_briefs),
            "theorem_application_plan_count": theorem_application_plan_count,
            "planner_replan_count": generator_replans,
            "planner_backtrack_count": planner_backtrack_count,
            "planner_advice_used_count": sum(
                len(result.planner_hints_followed) for result in self.generator_results
            ),
            "planner_advice_rejected_count": sum(
                len(result.planner_hints_rejected) for result in self.generator_results
            ),
            "generator_initial_count": sum(
                result.status == GeneratorStatus.PROPOSED
                for result in self.generator_results
            ),
            "generator_repair_count": self.repair_authoring_count,
            "generator_replan_request_count": generator_replans,
            "generator_lookup_request_count": generator_lookup_requests,
            "context_insufficient_count": self.context_insufficient_count,
            "unresolved_probe_handle_count": self.unresolved_probe_handle_count,
            "executable_design_count": sum(
                item.get("status") != "abandoned"
                for item in self.synthesis_designs
                if isinstance(item, Mapping)
            ),
            "rejected_nonexecutable_design_count": self.rejected_nonexecutable_design_count,
            "capability_contribution_receipt_count": len(self.contribution_receipts),
            "lean_verified_generated_capability_count": self.capability_registration_count,
            "registered_generated_capability_count": self.capability_registration_count,
            "generated_capability_final_used_count": len(final_used),
            "gadget_plan_count": len(gadget_plans),
            "gadget_design_kind_counts": gadget_design_kind_counts,
            "finite_candidate_count": self.finite_candidate_count,
            "truth_table_rejection_count": sum(
                item.get("kind")
                in {
                    "lean-truth-table-rejection",
                    "finite-truth-table-counterexample",
                }
                for item in prior_counterexamples
                if isinstance(item, Mapping)
            ),
            "counterexample_count": self.finite_counterexample_count,
            "bound_expansion_count": sum(
                bool((plan.get("counterexample_policy") or {}).get("bound_expanded"))
                for plan in gadget_plans
                if isinstance(plan.get("counterexample_policy"), Mapping)
            ),
            "gadget_certificate_count": len(gadget_contributions),
            "gadget_registered_count": len(gadget_contributions),
            "gadget_final_used_count": len(final_by_kind[CapabilityKind.GADGET]),
            "direct_tm_plan_count": len(direct_plans),
            "program_dag_count": len(direct_plans),
            "program_node_count": len(direct_nodes),
            "primitive_covered_node_count": sum(
                bool(node.get("primitive_declaration")) for node in direct_nodes
            ),
            "generated_node_count": sum(
                node.get("status") == "generator-required" for node in direct_nodes
            ),
            "node_lean_success_count": sum(
                len(receipt.generated_helpers) for receipt in direct_contributions
            ),
            "endpoint_equality_attempt_count": sum(
                node.get("operation") == "endpoint-equality" for node in direct_nodes
            ),
            "endpoint_equality_success_count": sum(
                any("endpoint" in helper for helper in receipt.generated_helpers)
                for receipt in direct_contributions
            ),
            "direct_tm_registered_count": len(direct_contributions),
            "direct_tm_final_used_count": len(final_by_kind[CapabilityKind.DIRECT_TM]),
            "semantic_plan_count": len(semantic_plans),
            "forward_plan_count": sum(
                direction.get("direction") == "forward"
                for direction in semantic_directions
            ),
            "reverse_plan_count": sum(
                direction.get("direction") == "reverse"
                for direction in semantic_directions
            ),
            "witness_schema_count": sum(
                bool(direction.get("witness_schema"))
                for direction in semantic_directions
            ),
            "semantic_helper_count": len(semantic_helpers),
            "forward_helper_success_count": sum(
                "forward" in helper for helper in semantic_helpers
            ),
            "reverse_helper_success_count": sum(
                "reverse" in helper for helper in semantic_helpers
            ),
            "semantic_iff_registered_count": len(semantic_contributions),
            "semantic_iff_final_used_count": len(final_by_kind[CapabilityKind.SEMANTIC]),
        }
        metrics["planner_accounting_consistent"] = (
            metrics["planner_plan_count"]
            == metrics["planner_brief_count"]
            + metrics["theorem_application_plan_count"]
            + metrics["planner_replan_count"]
            + metrics["planner_backtrack_count"]
        )
        metrics["generated_capability_accounting_consistent"] = (
            metrics["generated_capability_final_used_count"]
            <= metrics["registered_generated_capability_count"]
            <= metrics["lean_verified_generated_capability_count"]
        )
        return metrics

    def to_dict(self) -> dict[str, Any]:
        payload = _jsonable(self)
        payload["model_call_count"] = self.model_call_count
        metrics = self.capability_metrics()
        payload["capability_metrics"] = metrics
        payload.update(metrics)
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
    "CandidateReceipt",
    "CandidateRole",
    "CandidateAction",
    "CapabilityKind",
    "CapabilityPlan",
    "ConstructionContract",
    "ContributionClass",
    "ContributionReceipt",
    "DirectTMCapabilityPlan",
    "ExactClosureResult",
    "GENERATION_EVIDENCE_SCHEMA",
    "GeneralNPHardRequest",
    "GeneralNPHardResult",
    "GenerationEvidence",
    "GeneratorBrief",
    "GeneratorResult",
    "GeneratorStatus",
    "GeneratedCapability",
    "GoalKey",
    "GoalKind",
    "ModelCallRecord",
    "ModelPolicy",
    "OpenGoal",
    "PremiseKind",
    "PremiseSlot",
    "FrameStatus",
    "GadgetCapabilityPlan",
    "ProofGuidance",
    "ProofStatus",
    "ProofStep",
    "PlannerEffectReceipt",
    "ProviderKind",
    "ProviderStatistics",
    "QualificationStatus",
    "REQUEST_SCHEMA",
    "RESULT_SCHEMA",
    "ResidualObligation",
    "ReusableFragment",
    "RootGoal",
    "SemanticCapabilityPlan",
    "SemanticDirectionPlan",
    "SolutionClassification",
    "Strategy",
    "StrategyDecision",
    "StrategyEffectReceipt",
    "SlotStatus",
    "SubstepPlan",
    "TheoremIndexEntry",
    "TheoremApplicationPlan",
    "TheoremPremise",
    "TypedProgramNode",
    "VerificationSummary",
    "stable_json",
    "stable_sha256",
]
