"""Fenced initial-authoring and stateful-repair protocols."""

from __future__ import annotations

from dataclasses import asdict
import hashlib
import json
import textwrap
from typing import Any, Mapping

from agent.hardness.model_client import extract_json_object

from ..context_capsule import ContextCapsule
from ..models import ConstructionContract, GeneratorBrief, ModelCallRecord, ProofGuidance
from .protocol import AuthoringProposal, JSONModel


def implementation_sha256(implementation: str) -> str:
    return "sha256:" + hashlib.sha256(implementation.strip().encode("utf-8")).hexdigest()


def fixed_declaration_header(*, declaration: str, exact_type: str) -> str:
    return f"noncomputable def {declaration} : {exact_type.strip()} := by"


def render_fixed_declaration(
    *,
    declaration: str,
    exact_type: str,
    proof_body: str,
    helper_declarations: tuple[str, ...] = (),
) -> str:
    """Wrap model-authored content in the runtime-owned declaration envelope."""

    body = textwrap.dedent(proof_body).strip()
    if body == "by":
        body = ""
    elif body.startswith("by\n"):
        body = body[3:].lstrip("\n")
    if not body:
        raise ValueError("fixed declaration proof body is empty")
    helpers = tuple(item.strip() for item in helper_declarations if item.strip())
    rendered_body = "\n".join(
        "  " + line if line else "" for line in body.splitlines()
    )
    target = fixed_declaration_header(declaration=declaration, exact_type=exact_type)
    return "\n\n".join((*helpers, target + "\n" + rendered_body))


def _helper_declarations(value: object) -> tuple[str, ...] | None:
    if value is None:
        return ()
    if isinstance(value, str):
        return (value,) if value.strip() else ()
    if isinstance(value, list) and all(isinstance(item, str) for item in value):
        return tuple(item for item in value if item.strip())
    return None


def _implementation_from_payload(
    *,
    parsed: Mapping[str, Any],
    required_declaration: str,
    exact_type: str,
) -> tuple[str | None, str | None, tuple[str, ...], str | None]:
    proof_body = parsed.get("proof_body")
    helpers = _helper_declarations(parsed.get("helper_declarations"))
    if isinstance(proof_body, str) and helpers is not None:
        try:
            implementation = render_fixed_declaration(
                declaration=required_declaration,
                exact_type=exact_type,
                proof_body=proof_body,
                helper_declarations=helpers,
            )
        except ValueError as error:
            return None, None, (), str(error)
        return implementation, proof_body, helpers, None

    # Backward-compatible parsing for stored fixtures and older providers.  The
    # materializer still verifies the frozen signature before Lean is called.
    implementation = parsed.get("implementation")
    if isinstance(implementation, str) and implementation.strip():
        return implementation, None, (), None
    return (
        None,
        None,
        (),
        "model authoring proposal omitted proof_body/helper_declarations",
    )


def _call_record(*, response, proposal, error: str | None, purpose: str) -> ModelCallRecord:
    return ModelCallRecord(
        purpose=purpose,
        called=response.called,
        ok=response.ok and proposal is not None,
        status_code=response.status_code,
        duration_seconds=response.duration_seconds,
        usage=response.usage,
        attempts=response.attempts,
        response_sha256=hashlib.sha256(response.content.encode("utf-8")).hexdigest(),
        error=error,
    )


def _base_payload(
    *,
    contract: ConstructionContract,
    guidance: tuple[ProofGuidance, ...],
    context_capsule: ContextCapsule,
    required_declaration: str,
    design: Mapping[str, Any],
    generator_brief: GeneratorBrief | None = None,
) -> dict[str, Any]:
    payload = {
        "expected_lean_type": contract.exact_expected_lean_type,
        "fixed_declaration_envelope": {
            "header": fixed_declaration_header(
                declaration=required_declaration,
                exact_type=contract.exact_expected_lean_type,
            ),
            "footer": "<runtime closes the surrounding namespace>",
            "model_may_edit_header": False,
        },
        "required_capability_declaration": fixed_declaration_header(
            declaration=required_declaration,
            exact_type=contract.exact_expected_lean_type,
        ),
        "frozen_source": contract.frozen_source_handle,
        "frozen_target": contract.frozen_target_handle,
        "executable_design": dict(design),
        "allowed_modes": list(contract.allowed_construction_modes),
        "context_capsule_id": context_capsule.capsule_id,
    }
    if generator_brief is not None:
        # The independent Generator is brief-bound.  In particular, it must not
        # receive the Planner's complete candidate index or unselected guidance
        # through the broader ContextCapsule.  The brief already freezes the
        # exact selected candidates, definitions, generated signatures, local
        # context, residuals, and identifier manifest needed for authoring.
        payload.update(
            {
                "forbidden_declarations": list(
                    generator_brief.forbidden_declarations
                ),
                "residual_obligations": list(generator_brief.expected_residuals),
                "allowed_identifier_manifest": list(
                    generator_brief.allowed_identifier_manifest
                ),
                "generator_context": {
                    "local_context": list(generator_brief.local_context),
                    "relevant_definitions": list(
                        generator_brief.relevant_definitions
                    ),
                    "generated_capability_signatures": list(
                        generator_brief.generated_capability_signatures
                    ),
                    "ordered_proof_hints": list(
                        generator_brief.ordered_proof_hints
                    ),
                    "helper_contracts": list(generator_brief.helper_contracts),
                },
            }
        )
        payload["generator_brief"] = asdict(generator_brief)
        payload["brief_binding"] = {
            "brief_id": generator_brief.brief_id,
            "brief_fingerprint": generator_brief.brief_fingerprint,
            "plan_id": generator_brief.plan_id,
            "plan_fingerprint": generator_brief.plan_fingerprint,
            "generator_may_change_plan": False,
        }
    else:
        payload.update(
            {
                "forbidden_declarations": list(contract.forbidden_declarations),
                "reusable_declarations": list(contract.reusable_declarations),
                "residual_obligations": [
                    {
                        "exact_type": item.exact_type,
                        "suggested_solver": item.suggested_solver,
                    }
                    for item in contract.residual_obligations
                ],
                "guidance": [
                    {
                        "candidate": item.candidate_declaration,
                        "application_skeleton": item.application_skeleton,
                        "candidate_exact_type": next(
                            (
                                signature.exact_type
                                for signature in context_capsule.candidate_signatures
                                if signature.declaration == item.candidate_declaration
                            ),
                            None,
                        ),
                        "residual_exact_types": [
                            residual.exact_type for residual in item.residual_obligations
                        ],
                        "coverage": item.coverage_score,
                    }
                    for item in guidance
                ],
                "context_capsule": context_capsule.prompt_payload(),
                "allowed_identifier_manifest": list(
                    context_capsule.allowed_identifier_manifest
                ),
            }
        )
    return payload


def propose_initial_implementation(
    *,
    model: JSONModel,
    contract: ConstructionContract,
    guidance: tuple[ProofGuidance, ...],
    context_capsule: ContextCapsule,
    required_declaration: str = "problemIsNPHard",
    design: Mapping[str, Any] | None = None,
    generator_brief: GeneratorBrief | None = None,
) -> tuple[AuthoringProposal | None, ModelCallRecord]:
    payload = _base_payload(
        contract=contract,
        guidance=guidance,
        context_capsule=context_capsule,
        required_declaration=required_declaration,
        design=design or {},
        generator_brief=generator_brief,
    )
    payload["required_output"] = {
        "status": "proposed|needs-lookup|needs-replan|plan-infeasible",
        "helper_declarations": (
            "zero or more complete Lean helper declarations; no imports, namespace "
            "commands, or copy of the fixed capability declaration"
        ),
        "proof_body": (
            "only the tactic/proof body placed after the runtime-owned ':= by'; "
            "it must not reference, alias, or invoke a resolver that uses any "
            "forbidden declaration"
        ),
        "reason": "short explanation grounded in exact signatures from the capsule",
        "requested_lookup": "qualified identifiers required when status is needs-lookup",
    }
    response = model.complete_json(
        system=(
            "Author Lean only for the fixed expected type and job-local editable region. "
            "Use the exact declaration signatures in the context capsule; do not guess APIs. "
            "Do not add axioms, sorry/admit, imports, namespace commands, or change endpoints. "
            "The runtime owns the exact noncomputable-def header: return helper_declarations "
            "and only the proof_body after ':= by'. The supplied GeneratorBrief is frozen: "
            "follow its typed hints or explicitly return needs-lookup/needs-replan/plan-infeasible. "
            "Do not repeat or edit the fixed header. "
            "Do not use any forbidden declaration, directly or through an alias or resolver. "
            "Return one compact JSON object."
        ),
        prompt=json.dumps(payload, ensure_ascii=False),
    )
    parsed = extract_json_object(response.content) if response.ok else None
    proposal = None
    error = response.error
    if isinstance(parsed, dict):
        reason = parsed.get("reason")
        status = parsed.get("status", "proposed")
        requested_lookup = parsed.get("requested_lookup", [])
        lookup = (
            tuple(item for item in requested_lookup if isinstance(item, str))
            if isinstance(requested_lookup, list)
            else ()
        )
        if status in {"needs-lookup", "needs-replan", "plan-infeasible"}:
            if not isinstance(reason, str) or not reason.strip():
                error = "generator control response omitted reason"
            elif status == "needs-lookup" and not lookup:
                error = "needs-lookup response omitted requested_lookup"
            else:
                proposal = AuthoringProposal(
                    implementation=None,
                    reason=reason,
                    raw=parsed,
                    status=str(status),
                    requested_lookup=lookup,
                    requested_replan=status in {"needs-replan", "plan-infeasible"},
                    rejection_reason=reason,
                )
        elif status == "proposed":
            implementation, proof_body, helpers, implementation_error = (
                _implementation_from_payload(
                    parsed=parsed,
                    required_declaration=required_declaration,
                    exact_type=contract.exact_expected_lean_type,
                )
            )
            if implementation is not None and isinstance(reason, str):
                proposal = AuthoringProposal(
                    implementation=implementation,
                    reason=reason,
                    raw=parsed,
                    implementation_body=proof_body,
                    helper_declarations=helpers,
                )
            else:
                error = implementation_error or (
                    "model initial-authoring proposal omitted proof body or reason"
                )
        else:
            error = "model initial-authoring proposal returned an invalid status"
    elif response.ok:
        error = "model initial-authoring response did not contain one JSON object"
    return proposal, _call_record(
        response=response,
        proposal=proposal,
        error=error,
        purpose="lean-authoring-initial",
    )


def propose_repair(
    *,
    model: JSONModel,
    contract: ConstructionContract,
    guidance: tuple[ProofGuidance, ...],
    context_capsule: ContextCapsule,
    required_declaration: str,
    design: Mapping[str, Any],
    previous_implementation: str,
    base_sha256: str,
    diagnostic_classification: str,
    normalized_diagnostics: str,
    source_window: str,
    failed_source_hashes: tuple[str, ...] = (),
    generator_brief: GeneratorBrief | None = None,
) -> tuple[AuthoringProposal | None, ModelCallRecord]:
    actual_base = implementation_sha256(previous_implementation)
    if base_sha256 != actual_base:
        raise ValueError("repair base hash does not match the previous implementation")
    payload = _base_payload(
        contract=contract,
        guidance=guidance,
        context_capsule=context_capsule,
        required_declaration=required_declaration,
        design=design,
        generator_brief=generator_brief,
    )
    payload.update(
        {
            "previous_implementation": previous_implementation,
            "base_sha256": base_sha256,
            "lean_error_classification": diagnostic_classification,
            "normalized_diagnostics": normalized_diagnostics[-6000:],
            "error_source_window": source_window[-6000:],
            "failed_source_hashes": list(failed_source_hashes),
            "repair_policy": (
                "Return a complete replacement implementation. Preserve unrelated correct "
                "parts and change the region implicated by the classified Lean diagnostic."
            ),
            "required_output": {
                "base_sha256": base_sha256,
                "helper_declarations": (
                    "complete replacement helper declarations inside the editable region"
                ),
                "proof_body": (
                    "complete replacement body after the runtime-owned ':= by'"
                ),
                "changed_reason": "what changed and how it addresses the Lean diagnostic",
                "addressed_diagnostic_codes": [diagnostic_classification],
            },
        }
    )
    response = model.complete_json(
        system=(
            "Repair the supplied Lean implementation against the exact typed context capsule. "
            "This is a stateful repair: keep correct unrelated code, address the classified "
            "diagnostic, and return the exact supplied base_sha256. The declaration header is "
            "runtime-owned: return helper_declarations and proof_body only. Do not add axioms, "
            "sorry/admit, imports, namespaces, or forbidden declarations. Return one compact "
            "JSON object containing the complete editable replacement."
        ),
        prompt=json.dumps(payload, ensure_ascii=False),
    )
    parsed = extract_json_object(response.content) if response.ok else None
    proposal = None
    error = response.error
    if isinstance(parsed, dict):
        returned_base = parsed.get("base_sha256")
        changed_reason = parsed.get("changed_reason")
        addressed = parsed.get("addressed_diagnostic_codes")
        valid_codes = (
            tuple(item for item in addressed if isinstance(item, str))
            if isinstance(addressed, list)
            else ()
        )
        implementation, proof_body, helpers, implementation_error = (
            _implementation_from_payload(
                parsed=parsed,
                required_declaration=required_declaration,
                exact_type=contract.exact_expected_lean_type,
            )
        )
        if returned_base != base_sha256:
            error = "model repair proposal returned a stale or mismatched base_sha256"
        elif implementation is None:
            error = implementation_error or "model repair proposal omitted proof body"
        elif not isinstance(changed_reason, str) or not changed_reason.strip():
            error = "model repair proposal omitted changed_reason"
        else:
            proposal = AuthoringProposal(
                implementation=implementation,
                reason=changed_reason,
                raw=parsed,
                implementation_body=proof_body,
                helper_declarations=helpers,
                base_sha256=returned_base,
                changed_reason=changed_reason,
                addressed_diagnostic_codes=valid_codes,
            )
    elif response.ok:
        error = "model repair response did not contain one JSON object"
    return proposal, _call_record(
        response=response,
        proposal=proposal,
        error=error,
        purpose="lean-authoring-repair",
    )


def propose_implementation(
    *,
    model: JSONModel,
    contract: ConstructionContract,
    guidance: tuple[ProofGuidance, ...],
    diagnostics: str | None,
    required_declaration: str = "problemIsNPHard",
    context_capsule: ContextCapsule | None = None,
) -> tuple[AuthoringProposal | None, ModelCallRecord]:
    """Compatibility wrapper for older callers; new runtime code uses both protocols."""

    if context_capsule is None:
        raise ValueError("initial authoring requires a Lean-grounded context capsule")
    del diagnostics
    return propose_initial_implementation(
        model=model,
        contract=contract,
        guidance=guidance,
        context_capsule=context_capsule,
        required_declaration=required_declaration,
    )


__all__ = [
    "fixed_declaration_header",
    "implementation_sha256",
    "propose_implementation",
    "propose_initial_implementation",
    "propose_repair",
    "render_fixed_declaration",
]
