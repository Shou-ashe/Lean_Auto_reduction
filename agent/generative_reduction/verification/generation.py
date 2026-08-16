"""Layer B: provenance-based solution classification."""

from __future__ import annotations

import hashlib
import re

from ..models import GenerationEvidence, QualificationStatus, SolutionClassification


DECLARATION_RE = re.compile(
    r"(?m)^\s*(?:noncomputable\s+)?(?:def|theorem|abbrev)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
)
REDUCTION_RE = re.compile(
    r"(?ms)^\s*(?:noncomputable\s+)?(?:def|theorem|abbrev)\s+"
    r"([A-Za-z_][A-Za-z0-9_']*)\b[^\n:]*:\s*.*?CertifiedReduction\b.*?:="
)


def evidence_from_generated_source(
    *,
    source: str,
    environment_snapshot_hash: str,
    strategy_call_count: int,
    authoring_call_count: int,
    core_verified: bool,
) -> GenerationEvidence:
    declarations = tuple(dict.fromkeys(DECLARATION_RE.findall(source)))
    reductions = tuple(dict.fromkeys(REDUCTION_RE.findall(source)))
    helpers = tuple(
        name
        for name in declarations
        if name != "problemIsNPHard"
        and name not in reductions
        and not name.startswith("stable_binding_")
    )
    programs = tuple(
        name
        for name in declarations
        if re.search(
            rf"(?s)\b{name}\b.*?(?:PolyProg|Program\.Primitive)", source
        )
    )
    semantic = tuple(
        name
        for name in helpers
        if re.search(rf"(?s)\b{name}\b.*?(?:accepts|↔)", source)
    )
    complexity = tuple(
        name
        for name in helpers
        if re.search(rf"(?s)\b{name}\b.*?TMPolyTimeMap", source)
    )
    root_at = source.find("theorem problemIsNPHard")
    root_source = source[root_at:] if root_at >= 0 else ""
    used_reductions = tuple(
        name
        for name in reductions
        if len(re.findall(rf"\b{re.escape(name)}\b", root_source)) >= 1
    )
    substantive = tuple(
        name
        for name in declarations
        if name not in {"problemIsNPHard", *reductions}
        and not name.startswith("stable_binding_")
    )
    if reductions and used_reductions and substantive and core_verified:
        classification = "verified-generative-success"
    elif reductions and used_reductions:
        classification = "generated-certified-edge"
    elif reductions:
        classification = "generated-unused"
    elif helpers:
        classification = "helper-only"
    else:
        classification = "generation-attempted-blocked"
    digest = "sha256:" + hashlib.sha256(source.encode("utf-8")).hexdigest()
    return GenerationEvidence(
        attempted=True,
        strategy_call_count=strategy_call_count,
        authoring_call_count=authoring_call_count,
        new_helper_declarations=helpers,
        new_program_declarations=programs,
        new_semantic_proofs=semantic,
        new_complexity_proofs=complexity,
        new_certified_reductions=reductions,
        substantive_generated_dependencies=substantive,
        generated_edge_used_by_final_artifact=bool(used_reductions),
        generated_source_hashes=(digest,),
        environment_snapshot_hash=environment_snapshot_hash,
        provenance_verified=True,
        mutation_status=QualificationStatus.NOT_RUN,
        classification=classification,
    )


def classify_generation(evidence: GenerationEvidence) -> SolutionClassification:
    if (
        evidence.provenance_verified
        and evidence.new_certified_reductions
        and evidence.substantive_generated_dependencies
        and evidence.generated_edge_used_by_final_artifact
    ):
        return SolutionClassification.VERIFIED_GENERATED
    if evidence.attempted and (
        evidence.new_helper_declarations
        or evidence.new_program_declarations
        or evidence.new_semantic_proofs
        or evidence.new_complexity_proofs
    ):
        return SolutionClassification.VERIFIED_AUXILIARY_GENERATION
    return SolutionClassification.VERIFIED_REUSE


__all__ = ["classify_generation", "evidence_from_generated_source"]
