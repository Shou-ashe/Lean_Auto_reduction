"""Fenced initial-authoring and stateful-repair protocols."""

from __future__ import annotations

import hashlib
import json
from typing import Any, Mapping

from agent.hardness.model_client import extract_json_object

from ..context_capsule import ContextCapsule
from ..models import ConstructionContract, ModelCallRecord, ProofGuidance
from .protocol import AuthoringProposal, JSONModel


def implementation_sha256(implementation: str) -> str:
    return "sha256:" + hashlib.sha256(implementation.strip().encode("utf-8")).hexdigest()


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
) -> dict[str, Any]:
    return {
        "expected_lean_type": contract.exact_expected_lean_type,
        "required_capability_declaration": (
            f"noncomputable def {required_declaration} : "
            + contract.exact_expected_lean_type
            + " := by"
        ),
        "frozen_source": contract.frozen_source_handle,
        "frozen_target": contract.frozen_target_handle,
        "executable_design": dict(design),
        "allowed_modes": list(contract.allowed_construction_modes),
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
        "context_capsule_id": context_capsule.capsule_id,
    }


def propose_initial_implementation(
    *,
    model: JSONModel,
    contract: ConstructionContract,
    guidance: tuple[ProofGuidance, ...],
    context_capsule: ContextCapsule,
    required_declaration: str = "problemIsNPHard",
    design: Mapping[str, Any] | None = None,
) -> tuple[AuthoringProposal | None, ModelCallRecord]:
    payload = _base_payload(
        contract=contract,
        guidance=guidance,
        context_capsule=context_capsule,
        required_declaration=required_declaration,
        design=design or {},
    )
    payload["required_output"] = {
        "implementation": (
            "Lean helper declarations plus the exact required capability declaration, "
            "with no imports or namespace commands; it must not reference, alias, "
            "or invoke a resolver that uses any forbidden declaration"
        ),
        "reason": "short explanation grounded in exact signatures from the capsule",
    }
    response = model.complete_json(
        system=(
            "Author Lean only for the fixed expected type and job-local editable region. "
            "Use the exact declaration signatures in the context capsule; do not guess APIs. "
            "Do not add axioms, sorry/admit, imports, namespace commands, or change endpoints. "
            "The required capability must be a noncomputable def so proposition-valued and "
            "data-valued exact types are accepted. Do not use any forbidden declaration, "
            "directly or through an alias or resolver. Return one compact JSON object."
        ),
        prompt=json.dumps(payload, ensure_ascii=False),
    )
    parsed = extract_json_object(response.content) if response.ok else None
    proposal = None
    error = response.error
    if isinstance(parsed, dict):
        implementation = parsed.get("implementation")
        reason = parsed.get("reason")
        if isinstance(implementation, str) and implementation.strip() and isinstance(reason, str):
            proposal = AuthoringProposal(implementation, reason, parsed)
        else:
            error = "model initial-authoring proposal omitted implementation or reason"
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
                "implementation": "complete replacement for the editable implementation",
                "changed_reason": "what changed and how it addresses the Lean diagnostic",
                "addressed_diagnostic_codes": [diagnostic_classification],
            },
        }
    )
    response = model.complete_json(
        system=(
            "Repair the supplied Lean implementation against the exact typed context capsule. "
            "This is a stateful repair: keep correct unrelated code, address the classified "
            "diagnostic, and return the exact supplied base_sha256. Do not add axioms, "
            "sorry/admit, imports, namespaces, or forbidden declarations. Return one compact "
            "JSON object containing the complete replacement implementation."
        ),
        prompt=json.dumps(payload, ensure_ascii=False),
    )
    parsed = extract_json_object(response.content) if response.ok else None
    proposal = None
    error = response.error
    if isinstance(parsed, dict):
        implementation = parsed.get("implementation")
        returned_base = parsed.get("base_sha256")
        changed_reason = parsed.get("changed_reason")
        addressed = parsed.get("addressed_diagnostic_codes")
        valid_codes = (
            tuple(item for item in addressed if isinstance(item, str))
            if isinstance(addressed, list)
            else ()
        )
        if returned_base != base_sha256:
            error = "model repair proposal returned a stale or mismatched base_sha256"
        elif not isinstance(implementation, str) or not implementation.strip():
            error = "model repair proposal omitted implementation"
        elif not isinstance(changed_reason, str) or not changed_reason.strip():
            error = "model repair proposal omitted changed_reason"
        else:
            proposal = AuthoringProposal(
                implementation=implementation,
                reason=changed_reason,
                raw=parsed,
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
    "implementation_sha256",
    "propose_implementation",
    "propose_initial_implementation",
    "propose_repair",
]
