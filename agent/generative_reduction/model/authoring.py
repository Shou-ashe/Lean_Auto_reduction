"""Fenced Lean implementation authoring protocol."""

from __future__ import annotations

import hashlib
import json

from agent.hardness.model_client import extract_json_object

from ..models import ConstructionContract, ModelCallRecord, ProofGuidance
from .protocol import AuthoringProposal, JSONModel


def propose_implementation(
    *,
    model: JSONModel,
    contract: ConstructionContract,
    guidance: tuple[ProofGuidance, ...],
    diagnostics: str | None,
) -> tuple[AuthoringProposal | None, ModelCallRecord]:
    prompt = json.dumps(
        {
            "expected_lean_type": contract.exact_expected_lean_type,
            "required_root_declaration": (
                "theorem problemIsNPHard : "
                + contract.exact_expected_lean_type
                + " := by"
            ),
            "frozen_source": contract.frozen_source_handle,
            "frozen_target": contract.frozen_target_handle,
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
                    "coverage": item.coverage_score,
                }
                for item in guidance
            ],
            "lean_diagnostics": (diagnostics or "")[-4000:],
            "required_output": {
                "implementation": (
                    "Lean helper declarations plus the exact required root declaration, "
                    "with no imports or namespace commands; it must not reference, alias, "
                    "or invoke a resolver that uses any forbidden declaration"
                ),
                "reason": "short explanation",
            },
        },
        ensure_ascii=False,
    )
    response = model.complete_json(
        system=(
            "Author Lean only for the fixed expected type and job-local editable region. "
            "Do not add axioms, sorry/admit, imports, namespace commands, or change endpoints. "
            "Do not use any forbidden declaration, directly or through an alias or resolver. "
            "Return one compact JSON object."
        ),
        prompt=prompt,
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
            error = "model authoring proposal omitted implementation or reason"
    elif response.ok:
        error = "model authoring response did not contain one JSON object"
    record = ModelCallRecord(
        purpose="lean-authoring",
        called=response.called,
        ok=response.ok and proposal is not None,
        status_code=response.status_code,
        duration_seconds=response.duration_seconds,
        usage=response.usage,
        attempts=response.attempts,
        response_sha256=hashlib.sha256(response.content.encode("utf-8")).hexdigest(),
        error=error,
    )
    return proposal, record


__all__ = ["propose_implementation"]
