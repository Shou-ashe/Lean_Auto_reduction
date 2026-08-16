"""Bridge typed substep planning to an independent, brief-bound generator."""

from __future__ import annotations

from dataclasses import asdict
import re
from typing import Mapping, Sequence

from .context_capsule import ContextCapsule
from .model.protocol import AuthoringProposal
from .models import (
    CandidateAction,
    CandidateRole,
    CapabilityKind,
    CapabilityPlan,
    ContributionClass,
    ContributionReceipt,
    GeneratedCapability,
    GeneratorBrief,
    GeneratorResult,
    GeneratorStatus,
    OpenGoal,
    SubstepPlan,
    stable_sha256,
)


_DECLARATION = re.compile(
    r"(?m)^\s*(?:private\s+)?(?:noncomputable\s+)?"
    r"(?:def|theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)
_PROJECT_IDENTIFIER = re.compile(
    r"\b(?:ComplexityReduction|Benchmark)(?:\.[A-Za-z_][A-Za-z0-9_']*)+\b"
)


def out_of_brief_project_identifiers(
    *, brief: GeneratorBrief, implementation: str
) -> tuple[str, ...]:
    """Return project declarations referenced outside the frozen brief manifest."""

    permitted = set(brief.allowed_identifier_manifest)
    permitted.update(
        str(item.get("declaration") or "")
        for item in brief.generated_capability_signatures
    )
    permitted.update(_PROJECT_IDENTIFIER.findall(brief.exact_declaration_type))
    return tuple(
        identifier
        for identifier in dict.fromkeys(_PROJECT_IDENTIFIER.findall(implementation))
        if identifier not in permitted
    )


def capability_kind_for_goal(goal: OpenGoal) -> CapabilityKind:
    text = " ".join(goal.exact_type.split())
    if "TMPolyTimeMap" in text:
        return CapabilityKind.DIRECT_TM
    if "Satisfiable" in text and (" Iff " in f" {text} " or "↔" in text):
        return CapabilityKind.SEMANTIC
    if ".Gadget" in text:
        return CapabilityKind.GADGET
    if "LanguageInterpretation" in text:
        return CapabilityKind.LANGUAGE_INTERPRETATION
    if "CertifiedReduction" in text or "NativeTMNPHard" in text:
        return CapabilityKind.FINAL_PACKAGING
    return CapabilityKind.GENERIC_HELPER


def build_capability_plan(
    *,
    goal: OpenGoal,
    substep_plan: SubstepPlan,
    action: CandidateAction,
    design: Mapping[str, object],
    capsule: ContextCapsule,
    forbidden_declarations: Sequence[str],
    prior_diagnostics: str | None,
) -> CapabilityPlan:
    feedback_fingerprint = (
        stable_sha256(" ".join(prior_diagnostics.split()))
        if prior_diagnostics
        else None
    )
    selected_candidate_ids = tuple(
        receipt.candidate_id for receipt in substep_plan.candidate_receipts
    )
    basis_ids = tuple(
        dict.fromkeys(
            signature.basis_id
            for signature in (
                *capsule.relevant_definitions,
                *capsule.relevant_lemmas,
                *capsule.constructors,
            )
            if signature.basis_id is not None
        )
    )
    helper_specs = tuple(
        {
            "helper_id": obligation.obligation_id,
            "exact_type": obligation.exact_type,
            "kind": obligation.kind.value,
            "suggested_solver": obligation.suggested_solver,
        }
        for obligation in substep_plan.residual_obligations
    )
    residual_dag = tuple(
        {
            "goal_id": obligation.obligation_id,
            "exact_type": obligation.exact_type,
            "dependencies": (),
            "estimated_cost": obligation.estimated_cost,
        }
        for obligation in substep_plan.residual_obligations
    )
    proof_outline = tuple(
        dict.fromkeys(
            (
                *(
                    f"apply candidate {guidance.candidate_declaration}"
                    for guidance in substep_plan.ranked_proof_guidance
                ),
                *(
                    f"close residual {obligation.obligation_id}"
                    for obligation in substep_plan.residual_obligations
                ),
                "materialize exact frozen declaration",
            )
        )
    )
    return CapabilityPlan.create(
        capability_kind=capability_kind_for_goal(goal),
        goal_id=goal.goal_id,
        exact_goal=goal.exact_type,
        selected_route=str(
            design.get("design_kind")
            or action.metadata.get("construction_mode")
            or "brief-bound-generation"
        ),
        selected_action_id=action.action_id,
        selected_design_id=str(design.get("design_id") or "") or None,
        selected_candidate_ids=selected_candidate_ids,
        construction_basis_ids=basis_ids,
        forbidden_closure_ids=forbidden_declarations,
        proof_outline=proof_outline,
        helper_specs=helper_specs,
        residual_goal_dag=residual_dag,
        budget_allocation={
            "planner_decision": 1,
            "initial_generation": 1,
            "lean_check": 1,
            "diagnostic_repair_reserve": 1,
            "final_verification_reserve": 1,
        },
        fallback_plans=(
            {
                "trigger": "needs-lookup",
                "effect": "expand construction basis and issue a new brief",
                "planning_feedback_fingerprint": feedback_fingerprint,
            },
            {
                "trigger": "needs-replan|plan-infeasible",
                "effect": "return to planner with a new plan fingerprint",
                "planning_feedback_fingerprint": feedback_fingerprint,
            },
        ),
        context_requirements=(
            "nonempty typed construction context",
            "resolvable exact goal constants",
            "fixed declaration envelope",
        ),
    )


def build_generator_brief(
    *,
    capability_plan: CapabilityPlan,
    substep_plan: SubstepPlan,
    capsule: ContextCapsule,
    declaration_name: str,
    exact_type: str,
    design: Mapping[str, object],
    prior_diagnostics: str | None,
    failed_source_hashes: Sequence[str],
) -> GeneratorBrief:
    receipt_by_declaration = {
        receipt.declaration: receipt for receipt in substep_plan.candidate_receipts
    }
    hints = tuple(
        {
            "hint_id": guidance.guidance_id,
            "hint_kind": "apply-candidate",
            "candidate_id": (
                receipt_by_declaration[guidance.candidate_declaration].candidate_id
                if guidance.candidate_declaration in receipt_by_declaration
                else None
            ),
            "candidate_declaration": guidance.candidate_declaration,
            "application_skeleton": guidance.application_skeleton,
            "residual_exact_types": tuple(
                item.exact_type for item in guidance.residual_obligations
            ),
        }
        for guidance in substep_plan.ranked_proof_guidance
    )
    selected_ids = tuple(
        hint["candidate_id"] for hint in hints if hint["candidate_id"] is not None
    )
    helper_contracts = tuple(capability_plan.helper_specs)
    relevant = tuple(
        {
            "declaration": item.declaration,
            "exact_type": item.exact_type,
            "definition": item.definition or "",
            "basis_id": item.basis_id or "",
        }
        for item in (
            *capsule.relevant_definitions,
            *capsule.relevant_lemmas,
        )
    )
    generated = tuple(
        {"declaration": item.declaration, "exact_type": item.exact_type}
        for item in capsule.generated_capability_signatures
    )
    return GeneratorBrief.create(
        plan=capability_plan,
        exact_declaration_name=declaration_name,
        exact_declaration_type=exact_type,
        fixed_declaration_envelope={
            "header": f"noncomputable def {declaration_name} : {exact_type} := by",
            "model_may_edit_header": "false",
            "owner": "recursive-runtime",
        },
        selected_design=dict(design),
        selected_candidate_ids=selected_ids,
        ordered_proof_hints=hints,
        helper_contracts=helper_contracts,
        expected_residuals=tuple(capsule.residual_exact_types),
        allowed_identifier_manifest=capsule.allowed_identifier_manifest,
        forbidden_declarations=capability_plan.forbidden_closure_ids,
        generated_capability_signatures=generated,
        local_context=capsule.local_context,
        relevant_definitions=relevant,
        prior_diagnostics=((prior_diagnostics,) if prior_diagnostics else ()),
        failed_source_hashes=failed_source_hashes,
    )


def generator_result_from_proposal(
    *,
    brief: GeneratorBrief,
    proposal: AuthoringProposal,
    substep_plan: SubstepPlan,
    generated_capabilities: Sequence[GeneratedCapability],
) -> GeneratorResult:
    status = GeneratorStatus(proposal.status)
    implementation = proposal.implementation or ""
    outside_manifest = (
        out_of_brief_project_identifiers(brief=brief, implementation=implementation)
        if status == GeneratorStatus.PROPOSED
        else ()
    )
    if outside_manifest:
        return GeneratorResult.create(
            brief=brief,
            status=GeneratorStatus.NEEDS_LOOKUP,
            planner_hints_rejected=tuple(
                str(hint.get("hint_id")) for hint in brief.ordered_proof_hints
            ),
            rejection_reason=(
                "proposed source referenced project identifiers outside the frozen brief"
            ),
            requested_lookup=outside_manifest,
        )
    declaration_to_id = {
        receipt.declaration: receipt.candidate_id
        for receipt in substep_plan.candidate_receipts
    }
    used_candidate_ids = tuple(
        candidate_id
        for declaration, candidate_id in declaration_to_id.items()
        if declaration in implementation and candidate_id in brief.selected_candidate_ids
    )
    used_generated = tuple(
        capability.declaration
        for capability in generated_capabilities
        if capability.declaration in implementation
    )
    followed = tuple(
        str(hint.get("hint_id"))
        for hint in brief.ordered_proof_hints
        if (
            hint.get("candidate_declaration") in implementation
            or hint.get("hint_kind") in {"construct-witness", "split-structurally"}
        )
    )
    return GeneratorResult.create(
        brief=brief,
        status=status,
        implementation_body=(
            (proposal.implementation_body or proposal.implementation)
            if status == GeneratorStatus.PROPOSED
            else None
        ),
        helper_declarations=proposal.helper_declarations,
        used_candidate_ids=used_candidate_ids,
        used_generated_capabilities=used_generated,
        planner_hints_followed=followed,
        planner_hints_rejected=tuple(
            str(hint.get("hint_id"))
            for hint in brief.ordered_proof_hints
            if str(hint.get("hint_id")) not in followed
        ),
        rejection_reason=proposal.rejection_reason,
        requested_lookup=proposal.requested_lookup,
        requested_replan=proposal.requested_replan,
    )


def contribution_from_verified_generation(
    *,
    capability_plan: CapabilityPlan,
    brief: GeneratorBrief,
    generator_result: GeneratorResult,
    substep_plan: SubstepPlan,
    declaration: str,
    implementation: str,
    source_hash: str,
) -> ContributionReceipt:
    receipt_by_id = {
        receipt.candidate_id: receipt for receipt in substep_plan.candidate_receipts
    }
    exact: list[str] = []
    scaffold: list[str] = []
    primitive: list[str] = []
    for candidate_id in generator_result.used_candidate_ids:
        receipt = receipt_by_id.get(candidate_id)
        if receipt is None:
            continue
        if receipt.candidate_role == CandidateRole.EXACT_CLOSURE:
            exact.append(candidate_id)
        elif receipt.candidate_role in {
            CandidateRole.SCAFFOLD,
            CandidateRole.CONDITIONAL_CLOSURE,
            CandidateRole.CONSTRUCTOR,
        }:
            scaffold.append(candidate_id)
        else:
            primitive.append(candidate_id)
    helper_names = tuple(_DECLARATION.findall(implementation))
    return ContributionReceipt(
        capability_declaration=declaration,
        contribution_class=ContributionClass.MODEL_GENERATED_CAPABILITY,
        capability_kind=capability_plan.capability_kind,
        plan_id=capability_plan.plan_id,
        brief_id=brief.brief_id,
        generator_result_id=generator_result.result_id,
        exact_closure_candidates_used=tuple(exact),
        scaffold_candidates_used=tuple(scaffold),
        primitive_candidates_used=tuple(primitive),
        planner_advice_ids=generator_result.planner_hints_followed,
        generated_helpers=helper_names,
        generated_data_objects=tuple(
            item.get("helper_id", "")
            for item in capability_plan.helper_specs
            if item.get("helper_id")
        ),
        model_generated_source_hashes=(source_hash,),
        forbidden_audit_passed=True,
        independent_lean_passed=True,
    )


__all__ = [
    "build_capability_plan",
    "build_generator_brief",
    "capability_kind_for_goal",
    "contribution_from_verified_generation",
    "generator_result_from_proposal",
    "out_of_brief_project_identifiers",
]
