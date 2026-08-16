"""Lean-grounded, bounded context passed to proof authoring models.

The capsule is assembled only from the exact open goal, the typed theorem
index emitted by Lean, verified job-local capabilities, and normalized Lean
diagnostics.  It deliberately contains no provider configuration or process
environment, which keeps credentials outside the model prompt and audit log.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
import re
from typing import Any, Mapping, Sequence

from .construction_basis import ConstructionBasisReceipt
from .models import (
    GeneratedCapability,
    OpenGoal,
    ProofGuidance,
    TheoremIndexEntry,
    stable_sha256,
)


_SECRET_PATTERNS = (
    re.compile(r"\bsk-[A-Za-z0-9_-]{12,}\b"),
    re.compile(r"(?i)authorization\s*:\s*bearer\s+\S+"),
    re.compile(r"(?i)(?:api[_-]?key|token)\s*[=:]\s*\S+"),
)
_IDENTIFIER_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*(?:\.[A-Za-z_][A-Za-z0-9_']*)+")


def _redact(value: str) -> str:
    result = value
    for pattern in _SECRET_PATTERNS:
        result = pattern.sub("<redacted>", result)
    return result


def classify_structural_declaration(declaration: str) -> str | None:
    """Classify only generic constructor spellings on Lean-typed candidates."""

    tail = declaration.rsplit(".", 1)[-1]
    if tail == "mk":
        return "structure-constructor"
    if declaration.endswith("Exists.intro"):
        return "exists-constructor"
    if declaration.endswith("Nonempty.intro"):
        return "nonempty-constructor"
    if declaration.endswith("And.intro"):
        return "and-constructor"
    if declaration.endswith(("Or.inl", "Or.inr")):
        return "or-constructor"
    if declaration.endswith("Subtype.mk"):
        return "subtype-constructor"
    if declaration.endswith(("Sigma.mk", "PSigma.mk")):
        return "sigma-constructor"
    if declaration.endswith("Eq.refl"):
        return "equality-reflexivity"
    return None


@dataclass(frozen=True)
class DeclarationSignature:
    declaration: str
    module: str | None
    exact_type: str
    role: str
    source: str = "lean-typed-index"
    definition: str | None = None
    dependency_distance: int = 0
    basis_id: str | None = None


@dataclass(frozen=True)
class OmittedContextItem:
    item: str
    reason: str


@dataclass(frozen=True)
class ContextCapsule:
    capsule_id: str
    exact_goal: str
    local_context: tuple[str, ...]
    goal_head: str | None
    goal_head_type: str | None
    goal_head_definition: str | None
    pi_binders: tuple[str, ...]
    goal_body: str | None
    constructors: tuple[DeclarationSignature, ...]
    candidate_signatures: tuple[DeclarationSignature, ...]
    relevant_definitions: tuple[DeclarationSignature, ...]
    relevant_lemmas: tuple[DeclarationSignature, ...]
    verified_examples: tuple[Mapping[str, str], ...]
    application_skeletons: tuple[str, ...]
    residual_exact_types: tuple[str, ...]
    generated_capability_signatures: tuple[DeclarationSignature, ...]
    diagnostics: str
    diagnostic_fingerprint: str | None
    imports: tuple[str, ...]
    omitted_item_receipts: tuple[OmittedContextItem, ...]
    token_estimate: int
    environment_fingerprint: str
    allowed_identifier_manifest: tuple[str, ...] = ()
    generation_context_ready: bool = False
    context_blocker: str | None = None
    expansion_ordinal: int = 0

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)

    def prompt_payload(self) -> Mapping[str, Any]:
        """Return the complete auditable payload used by authoring protocols."""

        return self.to_dict()


def build_context_capsule(
    *,
    goal: OpenGoal,
    candidates: Sequence[TheoremIndexEntry],
    guidance: Sequence[ProofGuidance],
    generated_capabilities: Sequence[GeneratedCapability],
    imports: Sequence[str],
    environment_fingerprint: str,
    diagnostics: str | None = None,
    construction_basis: ConstructionBasisReceipt | None = None,
    expansion_ordinal: int = 0,
    max_rendered_chars: int = 24000,
) -> ContextCapsule:
    """Build one bounded capsule from Lean-extracted typed records."""

    clean_goal = _redact(goal.exact_type.strip())
    clean_context = tuple(_redact(item.strip()) for item in goal.local_context)
    clean_diagnostics = _redact((diagnostics or "")[-6000:])
    goal_identifiers = tuple(dict.fromkeys(_IDENTIFIER_RE.findall(clean_goal)))
    goal_head = next(
        (entry.conclusion_head for entry in candidates),
        (
            construction_basis.goal_head
            if construction_basis is not None
            else (goal_identifiers[0] if goal_identifiers else None)
        ),
    )

    signatures = tuple(
        DeclarationSignature(
            declaration=entry.declaration,
            module=entry.module,
            exact_type=_redact(entry.declaration_type),
            role="typed-candidate",
        )
        for entry in candidates
    )
    constructors = tuple(
        DeclarationSignature(
            declaration=entry.declaration,
            module=entry.module,
            exact_type=_redact(entry.declaration_type),
            role=kind,
        )
        for entry in candidates
        if (
            kind := (
                "lean-environment-constructor"
                if entry.declaration_kind == "constructor"
                else classify_structural_declaration(entry.declaration)
            )
        )
        is not None
    )

    diagnostic_names = frozenset(_IDENTIFIER_RE.findall(clean_diagnostics))
    goal_names = frozenset(
        (*goal_identifiers, *(_IDENTIFIER_RE.findall(" ".join(clean_context))))
    )
    relevant = tuple(
        signature
        for signature in signatures
        if signature.declaration in diagnostic_names
        or signature.declaration in goal_names
        or signature.declaration.rsplit(".", 1)[-1]
        in {
            name.rsplit(".", 1)[-1]
            for name in (*diagnostic_names, *goal_names)
        }
        or next(
            (
                entry.declaration_kind
                in {"definition", "opaque", "inductive", "recursor"}
                for entry in candidates
                if entry.declaration == signature.declaration
            ),
            False,
        )
    )
    relevant_ids = {item.declaration for item in relevant}
    lemmas = tuple(
        signature
        for signature in signatures
        if signature.declaration in {
            item.candidate_declaration for item in guidance
        }
        and signature.declaration not in relevant_ids
    )
    generated = tuple(
        DeclarationSignature(
            declaration=item.declaration,
            module=item.module,
            exact_type=_redact(item.exact_type),
            role="lean-verified-generated-capability",
            source=item.provenance,
        )
        for item in generated_capabilities
        if item.lean_verified
    )
    skeletons = tuple(
        dict.fromkeys(_redact(item.application_skeleton) for item in guidance)
    )
    residuals = tuple(
        dict.fromkeys(
            _redact(obligation.exact_type)
            for item in guidance
            for obligation in item.residual_obligations
        )
    )
    basis_signatures = tuple(
        DeclarationSignature(
            declaration=item.declaration,
            module=item.module,
            exact_type=_redact(item.exact_type),
            role=item.role,
            source="lean-construction-basis",
            definition=(
                _redact(item.definition) if item.definition is not None else None
            ),
            dependency_distance=item.dependency_distance,
            basis_id=item.basis_id,
        )
        for item in (construction_basis.entries if construction_basis else ())
    )

    # Exact signatures are never silently truncated.  Lower-value candidates
    # are omitted as complete records with explicit receipts.
    selected: list[DeclarationSignature] = []
    omitted: list[OmittedContextItem] = []
    rendered_chars = len(clean_goal) + sum(map(len, clean_context))
    priority_names = {
        *(item.declaration for item in constructors),
        *(item.declaration for item in relevant),
        *(item.declaration for item in lemmas),
    }
    ordered = sorted(
        signatures,
        key=lambda item: (item.declaration not in priority_names, item.declaration),
    )
    for item in ordered:
        size = len(item.declaration) + len(item.exact_type) + len(item.module or "")
        if rendered_chars + size <= max_rendered_chars or item.declaration in priority_names:
            selected.append(item)
            rendered_chars += size
        else:
            omitted.append(
                OmittedContextItem(
                    item=item.declaration,
                    reason="context-token-budget-lower-ranked-typed-candidate",
                )
            )

    selected_basis: list[DeclarationSignature] = []
    for item in basis_signatures:
        size = (
            len(item.declaration)
            + len(item.exact_type)
            + len(item.module or "")
            + len(item.definition or "")
        )
        if rendered_chars + size <= max_rendered_chars:
            selected_basis.append(item)
            rendered_chars += size
        else:
            omitted.append(
                OmittedContextItem(
                    item=item.declaration,
                    reason="context-token-budget-construction-basis",
                )
            )

    constructors = tuple(
        {
            item.declaration: item
            for item in (
                *constructors,
                *(item for item in selected_basis if item.role == "constructor"),
            )
        }.values()
    )
    relevant = tuple(
        {
            item.declaration: item
            for item in (
                *relevant,
                *(
                    item
                    for item in selected_basis
                    if item.role in {"goal-constant", "definition"}
                ),
            )
        }.values()
    )
    lemmas = tuple(
        {
            item.declaration: item
            for item in (
                *lemmas,
                *(item for item in selected_basis if item.role == "lemma"),
            )
        }.values()
    )
    allowed_identifiers = tuple(
        dict.fromkeys(
            (
                *goal_identifiers,
                *(
                    identifier
                    for item in clean_context
                    for identifier in _IDENTIFIER_RE.findall(item)
                ),
                *(item.declaration for item in signatures),
                *(item.declaration for item in generated),
                *(item.declaration for item in selected_basis),
                *(
                    identifier
                    for item in (*signatures, *generated, *selected_basis)
                    for identifier in _IDENTIFIER_RE.findall(
                        item.exact_type + " " + (item.definition or "")
                    )
                ),
            )
        )
    )

    payload_without_id = {
        "exact_goal": clean_goal,
        "local_context": clean_context,
        "goal_head": goal_head,
        "goal_head_type": (
            construction_basis.goal_head_type if construction_basis else None
        ),
        "goal_head_definition": (
            construction_basis.goal_head_definition if construction_basis else None
        ),
        "pi_binders": next(
            (entry.target_binders for entry in candidates if entry.target_binders),
            (),
        ),
        "goal_body": next(
            (entry.target_body for entry in candidates if entry.target_body),
            None,
        ),
        "constructors": constructors,
        "candidate_signatures": tuple(selected),
        "relevant_definitions": relevant,
        "relevant_lemmas": lemmas,
        "generated": generated,
        "application_skeletons": skeletons,
        "residuals": residuals,
        "diagnostics": clean_diagnostics,
        "imports": tuple(dict.fromkeys(imports)),
        "environment": environment_fingerprint,
        "expansion": expansion_ordinal,
        "omitted": omitted,
        "allowed_identifier_manifest": allowed_identifiers,
        "construction_basis_receipt": (
            construction_basis.receipt_hash if construction_basis else None
        ),
    }
    digest = stable_sha256(payload_without_id)
    diagnostic_fingerprint = (
        stable_sha256(" ".join(clean_diagnostics.split()))
        if clean_diagnostics
        else None
    )
    generation_context_ready = bool(
        selected
        or relevant
        or lemmas
        or constructors
        or skeletons
        or (construction_basis and construction_basis.goal_head_definition)
    )
    context_blocker = (
        None
        if generation_context_ready
        else (
            "context-insufficient: no typed candidates, goal-head definition, "
            "relevant definitions or lemmas, constructors, or application skeletons"
        )
    )
    return ContextCapsule(
        capsule_id=f"capsule-{digest.removeprefix('sha256:')[:24]}",
        exact_goal=clean_goal,
        local_context=clean_context,
        goal_head=goal_head,
        goal_head_type=(construction_basis.goal_head_type if construction_basis else None),
        goal_head_definition=(
            construction_basis.goal_head_definition if construction_basis else None
        ),
        pi_binders=payload_without_id["pi_binders"],
        goal_body=payload_without_id["goal_body"],
        constructors=constructors,
        candidate_signatures=tuple(selected),
        relevant_definitions=relevant,
        relevant_lemmas=lemmas,
        verified_examples=(),
        application_skeletons=skeletons,
        residual_exact_types=residuals,
        generated_capability_signatures=generated,
        diagnostics=clean_diagnostics,
        diagnostic_fingerprint=diagnostic_fingerprint,
        imports=tuple(dict.fromkeys(imports)),
        omitted_item_receipts=tuple(omitted),
        token_estimate=max(1, rendered_chars // 4),
        environment_fingerprint=environment_fingerprint,
        allowed_identifier_manifest=allowed_identifiers,
        generation_context_ready=generation_context_ready,
        context_blocker=context_blocker,
        expansion_ordinal=expansion_ordinal,
    )


__all__ = [
    "ContextCapsule",
    "DeclarationSignature",
    "OmittedContextItem",
    "build_context_capsule",
    "classify_structural_declaration",
]
