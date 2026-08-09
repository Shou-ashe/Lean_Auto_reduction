"""Fail-closed deterministic authoring plans for one typed capability gap."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path

from .lean_runner import (
    AUTHORING_MODULE,
    AXIOM_GATE_MODULE,
    CandidateSource,
    MODEL_AUTHORING_MODULE,
    RUNTIME_MODULE,
    build_closed_family_candidate_source,
    build_lawful_presentation_candidate_source,
    build_native_membership_candidate_sources,
    build_primitive_admission_candidate_source,
    build_program_indexed_reduction_candidate_sources,
    native_membership_stage_modules,
    program_indexed_reduction_stage_modules,
)
from .models import (
    AuthoringStageBoundary,
    AuthoringTaskPacket,
    ExactAuthoringTemplateCandidate,
    FamilyInstantiationCandidate,
    HardnessGap,
    ProbeResult,
)


DETERMINISTIC_TEMPLATE_MODE = "deterministic-template"
DISABLED_MODE = "disabled"
MODEL_AUTO_MODE = "model-auto"
MODEL_REQUIRED_MODE = "model-required"
MODEL_MODES = {MODEL_AUTO_MODE, MODEL_REQUIRED_MODE}
SUPPORTED_MODES = {
    DISABLED_MODE,
    DETERMINISTIC_TEMPLATE_MODE,
    MODEL_AUTO_MODE,
    MODEL_REQUIRED_MODE,
}
CLOSED_FAMILY_TEMPLATE_KIND = "closed_family_instantiation"
LAWFUL_PRESENTATION_TEMPLATE_KIND = "lawful_presentation"
PRIMITIVE_ADMISSION_TEMPLATE_KIND = "primitive_admission"
PROGRAM_INDEXED_REDUCTION_TEMPLATE_KIND = "program_indexed_reduction"
PROGRAM_INDEXED_MODEL_TEMPLATE_KIND = "program_indexed_model"
NATIVE_MEMBERSHIP_TEMPLATE_KIND = "native_membership"


@dataclass(frozen=True)
class JobLocalCandidateStageLayout:
    stage: str
    module: str
    declaration: str
    source_relative: str
    olean_relative: str


@dataclass(frozen=True)
class JobLocalCandidateLayout:
    module: str
    declaration: str
    route_declaration: str
    source_relative: str
    olean_relative: str
    validation_relative: str = "CandidateValidation.lean"
    post_probe_relative: str = "PostAuthoringProbe.lean"
    stages: tuple[JobLocalCandidateStageLayout, ...] = ()

    @property
    def source_parts(self) -> tuple[str, ...]:
        return tuple(Path(self.source_relative).parts)

    @property
    def all_stages(self) -> tuple[JobLocalCandidateStageLayout, ...]:
        if self.stages:
            return self.stages
        return (
            JobLocalCandidateStageLayout(
                stage="candidate",
                module=self.module,
                declaration=self.declaration,
                source_relative=self.source_relative,
                olean_relative=self.olean_relative,
            ),
        )

    @property
    def source_relatives(self) -> tuple[str, ...]:
        return tuple(stage.source_relative for stage in self.all_stages)


@dataclass(frozen=True)
class RenderedCandidateStage:
    layout: JobLocalCandidateStageLayout
    candidate: CandidateSource


@dataclass(frozen=True)
class DeterministicAuthoringPlan:
    task: AuthoringTaskPacket
    layout: JobLocalCandidateLayout
    candidates: tuple[FamilyInstantiationCandidate | ExactAuthoringTemplateCandidate, ...]
    primary_capability_head: str


def candidate_layout(job_id: str) -> JobLocalCandidateLayout:
    return _candidate_layout(job_id, "ClosedFamily", route_is_primary=True)


def _job_segment(job_id: str) -> str:
    digest = job_id.removeprefix("sha256:")
    if len(digest) < 16 or any(character not in "0123456789abcdef" for character in digest):
        raise ValueError("job id is not a canonical SHA-256 identifier")
    return f"J{digest[:16]}"


def _candidate_layout(
    job_id: str, segment: str, *, route_is_primary: bool = False
) -> JobLocalCandidateLayout:
    job_segment = _job_segment(job_id)
    module = f"Generated.Hardness.{job_segment}.{segment}"
    module_path = Path("work", *module.split("."))
    return JobLocalCandidateLayout(
        module=module,
        declaration=f"{module}.capability",
        route_declaration=(f"{module}.capability" if route_is_primary else f"{module}.route"),
        source_relative=str(module_path.with_suffix(".lean")),
        olean_relative=str(module_path.with_suffix(".olean")),
    )


def _program_indexed_reduction_layout(job_id: str) -> JobLocalCandidateLayout:
    base = f"Generated.Hardness.{_job_segment(job_id)}.ProgramIndexedReduction"
    modules = program_indexed_reduction_stage_modules(base)
    stages: list[JobLocalCandidateStageLayout] = []
    for stage, module in modules.items():
        module_path = Path("work", *module.split("."))
        stages.append(
            JobLocalCandidateStageLayout(
                stage=stage,
                module=module,
                declaration=f"{module}.capability",
                source_relative=str(module_path.with_suffix(".lean")),
                olean_relative=str(module_path.with_suffix(".olean")),
            )
        )
    final = stages[-1]
    return JobLocalCandidateLayout(
        module=final.module,
        declaration=final.declaration,
        route_declaration=final.declaration,
        source_relative=final.source_relative,
        olean_relative=final.olean_relative,
        stages=tuple(stages),
    )


def _native_membership_layout(job_id: str) -> JobLocalCandidateLayout:
    base = f"Generated.Hardness.{_job_segment(job_id)}.NativeMembership"
    modules = native_membership_stage_modules(base)
    stages: list[JobLocalCandidateStageLayout] = []
    for stage, module in modules.items():
        module_path = Path("work", *module.split("."))
        stages.append(
            JobLocalCandidateStageLayout(
                stage=stage,
                module=module,
                declaration=f"{module}.capability",
                source_relative=str(module_path.with_suffix(".lean")),
                olean_relative=str(module_path.with_suffix(".olean")),
            )
        )
    final = stages[-1]
    return JobLocalCandidateLayout(
        module=final.module,
        declaration=final.declaration,
        route_declaration=final.declaration,
        source_relative=final.source_relative,
        olean_relative=final.olean_relative,
        stages=tuple(stages),
    )


def _matching_family_candidates(
    gap: HardnessGap, probe: ProbeResult
) -> tuple[FamilyInstantiationCandidate, ...]:
    return tuple(sorted((
        candidate
        for candidate in probe.family_instantiations
        if candidate.source_declaration == gap.source_declaration
        and candidate.target_declaration == gap.target_declaration
        and candidate.role == gap.role
        and candidate.registry_fingerprint == gap.registry_fingerprint
    ), key=lambda candidate: candidate.cost))


def plan_closed_family_authoring(
    *,
    gap: HardnessGap,
    probe: ProbeResult,
    job_id: str,
    input_module: str,
    attempt_budget: int,
) -> DeterministicAuthoringPlan | None:
    if gap.reason != "unresolvedFamilyPremise":
        return None
    if attempt_budget <= 0:
        raise ValueError("authoring attempt budget must be positive")
    layout = candidate_layout(job_id)
    candidates = _matching_family_candidates(gap, probe)
    fixed_header_sha256 = ""
    fixed_footer_sha256 = ""
    if candidates:
        sample = build_closed_family_candidate_source(
            input_module=input_module,
            candidate_module=layout.module,
            candidate_declaration=layout.declaration,
            source_declaration=gap.source_declaration,
            target_declaration=gap.target_declaration,
            family_declaration=candidates[0].family_declaration,
            argument_declarations=candidates[0].argument_declarations,
            role=gap.role,
        )
        fixed_header_sha256 = sample.fixed_header_sha256
        fixed_footer_sha256 = sample.fixed_footer_sha256
    expected_type = (
        "ComplexityReduction.Certificate.CertifiedReduction "
        f"{gap.source_declaration} {gap.target_declaration}"
    )
    task = AuthoringTaskPacket.from_gap(
        gap,
        expected_type=expected_type,
        template_kind=CLOSED_FAMILY_TEMPLATE_KIND,
        candidate_module=layout.module,
        candidate_declaration=layout.declaration,
        allowed_imports=(RUNTIME_MODULE, input_module),
        editable_files=(layout.source_relative,),
        attempt_budget=attempt_budget,
        family_candidate_ids=tuple(candidate.candidate_id for candidate in candidates),
        fixed_header_sha256=fixed_header_sha256,
        fixed_footer_sha256=fixed_footer_sha256,
    )
    return DeterministicAuthoringPlan(
        task=task,
        layout=layout,
        candidates=candidates,
        primary_capability_head="ComplexityReduction.Certificate.CertifiedReduction",
    )


def _matching_exact_templates(
    gap: HardnessGap, probe: ProbeResult, *, template_kind: str
) -> tuple[ExactAuthoringTemplateCandidate, ...]:
    return tuple(sorted((
        candidate
        for candidate in probe.authoring_templates
        if candidate.template_kind == template_kind
        and candidate.source_declaration == gap.source_declaration
        and candidate.target_declaration == gap.target_declaration
        and candidate.role == gap.role
        and candidate.registry_fingerprint == gap.registry_fingerprint
    ), key=lambda candidate: candidate.cost))


def plan_lawful_presentation_authoring(
    *,
    gap: HardnessGap,
    probe: ProbeResult,
    job_id: str,
    input_module: str,
    attempt_budget: int,
) -> DeterministicAuthoringPlan | None:
    if gap.reason != "lawfulPresentation":
        return None
    if attempt_budget <= 0:
        raise ValueError("authoring attempt budget must be positive")
    layout = _candidate_layout(job_id, "LawfulPresentation")
    candidates = _matching_exact_templates(
        gap, probe, template_kind=LAWFUL_PRESENTATION_TEMPLATE_KIND
    )
    fixed_header_sha256 = ""
    fixed_footer_sha256 = ""
    if candidates:
        sample = build_lawful_presentation_candidate_source(
            input_module=input_module,
            candidate_module=layout.module,
            candidate_declaration=layout.declaration,
            route_declaration=layout.route_declaration,
            source_declaration=gap.source_declaration,
            target_declaration=gap.target_declaration,
            provider_declaration=candidates[0].provider_declaration,
            role=gap.role,
        )
        fixed_header_sha256 = sample.fixed_header_sha256
        fixed_footer_sha256 = sample.fixed_footer_sha256
    expected_type = (
        "ComplexityReduction.Encoding.StructuralRepresentationCertificate "
        f"{gap.source_declaration}.representation.encodedType "
        f"{gap.source_declaration}.representation.representation"
    )
    task = AuthoringTaskPacket.from_gap(
        gap,
        expected_type=expected_type,
        template_kind=LAWFUL_PRESENTATION_TEMPLATE_KIND,
        candidate_module=layout.module,
        candidate_declaration=layout.declaration,
        allowed_imports=(RUNTIME_MODULE, input_module),
        editable_files=(layout.source_relative,),
        attempt_budget=attempt_budget,
        template_candidate_ids=tuple(candidate.candidate_id for candidate in candidates),
        fixed_header_sha256=fixed_header_sha256,
        fixed_footer_sha256=fixed_footer_sha256,
    )
    return DeterministicAuthoringPlan(
        task=task,
        layout=layout,
        candidates=candidates,
        primary_capability_head=(
            "ComplexityReduction.Encoding.StructuralRepresentationCertificate"
        ),
    )


def plan_primitive_admission_authoring(
    *,
    gap: HardnessGap,
    probe: ProbeResult,
    job_id: str,
    input_module: str,
    attempt_budget: int,
) -> DeterministicAuthoringPlan | None:
    if gap.reason != "primitive":
        return None
    if attempt_budget <= 0:
        raise ValueError("authoring attempt budget must be positive")
    layout = _candidate_layout(job_id, "PrimitiveAdmission")
    candidates = _matching_exact_templates(
        gap, probe, template_kind=PRIMITIVE_ADMISSION_TEMPLATE_KIND
    )
    fixed_header_sha256 = ""
    fixed_footer_sha256 = ""
    if candidates:
        sample = build_primitive_admission_candidate_source(
            input_module=input_module,
            candidate_module=layout.module,
            candidate_declaration=layout.declaration,
            route_declaration=layout.route_declaration,
            source_declaration=gap.source_declaration,
            target_declaration=gap.target_declaration,
            provider_declaration=candidates[0].provider_declaration,
            role=gap.role,
        )
        fixed_header_sha256 = sample.fixed_header_sha256
        fixed_footer_sha256 = sample.fixed_footer_sha256
    expected_type = (
        "ComplexityReduction.Program.Primitive "
        f"{gap.source_declaration}.representation {gap.target_declaration}.representation"
    )
    task = AuthoringTaskPacket.from_gap(
        gap,
        expected_type=expected_type,
        template_kind=PRIMITIVE_ADMISSION_TEMPLATE_KIND,
        candidate_module=layout.module,
        candidate_declaration=layout.declaration,
        allowed_imports=(RUNTIME_MODULE, input_module),
        editable_files=(layout.source_relative,),
        attempt_budget=attempt_budget,
        template_candidate_ids=tuple(candidate.candidate_id for candidate in candidates),
        fixed_header_sha256=fixed_header_sha256,
        fixed_footer_sha256=fixed_footer_sha256,
    )
    return DeterministicAuthoringPlan(
        task=task,
        layout=layout,
        candidates=candidates,
        primary_capability_head="ComplexityReduction.Program.Primitive",
    )


def _program_reduction_stage_boundaries(
    *,
    layout: JobLocalCandidateLayout,
    input_module: str,
    source_declaration: str,
    target_declaration: str,
    provider_declaration: str,
    component_declarations: tuple[str, ...],
    role: str,
    model_semantic_body: bool = False,
) -> tuple[AuthoringStageBoundary, ...]:
    base_module = layout.stages[0].module.rsplit(".", 1)[0]
    rendered = build_program_indexed_reduction_candidate_sources(
        input_module=input_module,
        candidate_base_module=base_module,
        source_declaration=source_declaration,
        target_declaration=target_declaration,
        provider_declaration=provider_declaration,
        component_declarations=component_declarations,
        role=role,
        model_semantic_body=model_semantic_body,
    )
    expected_types = {
        "executable": (
            f"{source_declaration}.representation.Carrier → "
            f"{target_declaration}.representation.Carrier"
        ),
        "executable_direct_tm": (
            "ComplexityReduction.Agent.Hardness.Authoring.ExecutableDirectTMEvidence "
            f"{source_declaration} {target_declaration} "
            f"{rendered[0].declaration}"
        ),
        "primitive": (
            "ComplexityReduction.Program.Primitive "
            f"{source_declaration}.representation {target_declaration}.representation"
        ),
        "program": (
            "ComplexityReduction.Program.PolyProg "
            f"{source_declaration}.representation {target_declaration}.representation"
        ),
        "semantic_proof": (
            "ComplexityReduction.Agent.Hardness.Authoring.ProgramSemanticProof "
            f"{source_declaration} {target_declaration} "
            f"{next(stage.declaration for stage in rendered if stage.stage == 'program')}"
        ),
        "direct_tm": (
            "ComplexityReduction.Agent.Hardness.Authoring.ProgramDirectTMEvidence "
            f"{source_declaration} {target_declaration} "
            f"{next(stage.declaration for stage in rendered if stage.stage == 'program')}"
        ),
        "certified_reduction": (
            "ComplexityReduction.Certificate.CertifiedReduction "
            f"{source_declaration} {target_declaration}"
        ),
    }
    layout_by_stage = {stage.stage: stage for stage in layout.stages}
    return tuple(
        AuthoringStageBoundary(
            stage=stage.stage,
            module=stage.module,
            declaration=stage.declaration,
            editable_file=layout_by_stage[stage.stage].source_relative,
            expected_type=expected_types[stage.stage],
            fixed_header_sha256=stage.candidate.fixed_header_sha256,
            fixed_footer_sha256=stage.candidate.fixed_footer_sha256,
        )
        for stage in rendered
    )


def plan_program_indexed_reduction_authoring(
    *,
    gap: HardnessGap,
    probe: ProbeResult,
    job_id: str,
    input_module: str,
    attempt_budget: int,
) -> DeterministicAuthoringPlan | None:
    if gap.reason not in {
        "primitive",
        "semanticProof",
        "directTM",
        "noRegistryPath",
        "reductionCapability",
    }:
        return None
    if attempt_budget <= 0:
        raise ValueError("authoring attempt budget must be positive")
    layout = _program_indexed_reduction_layout(job_id)
    candidates = _matching_exact_templates(
        gap, probe, template_kind=PROGRAM_INDEXED_REDUCTION_TEMPLATE_KIND
    )
    boundaries: tuple[AuthoringStageBoundary, ...] = ()
    if candidates:
        boundaries = _program_reduction_stage_boundaries(
            layout=layout,
            input_module=input_module,
            source_declaration=gap.source_declaration,
            target_declaration=gap.target_declaration,
            provider_declaration=candidates[0].provider_declaration,
            component_declarations=candidates[0].component_declarations,
            role=gap.role,
        )
    final_boundary = boundaries[-1] if boundaries else None
    expected_type = (
        "ComplexityReduction.Certificate.CertifiedReduction "
        f"{gap.source_declaration} {gap.target_declaration}"
    )
    task = AuthoringTaskPacket.from_gap(
        gap,
        expected_type=expected_type,
        template_kind=PROGRAM_INDEXED_REDUCTION_TEMPLATE_KIND,
        candidate_module=layout.module,
        candidate_declaration=layout.declaration,
        allowed_imports=(
            AUTHORING_MODULE,
            AXIOM_GATE_MODULE,
            input_module,
            *(stage.module for stage in layout.stages),
        ),
        editable_files=layout.source_relatives,
        attempt_budget=attempt_budget,
        template_candidate_ids=tuple(candidate.candidate_id for candidate in candidates),
        fixed_header_sha256=(final_boundary.fixed_header_sha256 if final_boundary else ""),
        fixed_footer_sha256=(final_boundary.fixed_footer_sha256 if final_boundary else ""),
        stage_boundaries=boundaries,
    )
    return DeterministicAuthoringPlan(
        task=task,
        layout=layout,
        candidates=candidates,
        primary_capability_head="ComplexityReduction.Certificate.CertifiedReduction",
    )


def plan_program_indexed_model_authoring(
    *,
    gap: HardnessGap,
    probe: ProbeResult,
    job_id: str,
    input_module: str,
    attempt_budget: int,
) -> DeterministicAuthoringPlan | None:
    """Plan the Phase-7 semantic-proof lane without an exposed proof oracle."""

    if gap.reason not in {"semanticProof", "noRegistryPath"}:
        return None
    if attempt_budget <= 0:
        raise ValueError("authoring attempt budget must be positive")
    layout = _program_indexed_reduction_layout(job_id)
    candidates = _matching_exact_templates(
        gap, probe, template_kind=PROGRAM_INDEXED_MODEL_TEMPLATE_KIND
    )
    boundaries: tuple[AuthoringStageBoundary, ...] = ()
    if candidates:
        boundaries = _program_reduction_stage_boundaries(
            layout=layout,
            input_module=input_module,
            source_declaration=gap.source_declaration,
            target_declaration=gap.target_declaration,
            provider_declaration=candidates[0].provider_declaration,
            component_declarations=candidates[0].component_declarations,
            role=gap.role,
            model_semantic_body=True,
        )
    final_boundary = boundaries[-1] if boundaries else None
    context_module = (
        candidates[0].component_declarations[0].rsplit(".", 1)[0]
        if candidates
        else input_module
    )
    task = AuthoringTaskPacket.from_gap(
        gap,
        expected_type=(
            "ComplexityReduction.Certificate.CertifiedReduction "
            f"{gap.source_declaration} {gap.target_declaration}"
        ),
        template_kind=PROGRAM_INDEXED_MODEL_TEMPLATE_KIND,
        candidate_module=layout.module,
        candidate_declaration=layout.declaration,
        allowed_imports=(
            MODEL_AUTHORING_MODULE,
            AXIOM_GATE_MODULE,
            context_module,
            *(stage.module for stage in layout.stages),
        ),
        editable_files=layout.source_relatives,
        attempt_budget=attempt_budget,
        template_candidate_ids=tuple(candidate.candidate_id for candidate in candidates),
        fixed_header_sha256=(final_boundary.fixed_header_sha256 if final_boundary else ""),
        fixed_footer_sha256=(final_boundary.fixed_footer_sha256 if final_boundary else ""),
        stage_boundaries=boundaries,
    )
    return DeterministicAuthoringPlan(
        task=task,
        layout=layout,
        candidates=candidates,
        primary_capability_head="ComplexityReduction.Certificate.CertifiedReduction",
    )


def _native_membership_stage_boundaries(
    *,
    layout: JobLocalCandidateLayout,
    input_module: str,
    problem_declaration: str,
    provider_declaration: str,
    component_declarations: tuple[str, ...],
) -> tuple[AuthoringStageBoundary, ...]:
    base_module = layout.stages[0].module.rsplit(".", 1)[0]
    rendered = build_native_membership_candidate_sources(
        input_module=input_module,
        candidate_base_module=base_module,
        problem_declaration=problem_declaration,
        provider_declaration=provider_declaration,
        component_declarations=component_declarations,
    )
    verifier = next(stage.declaration for stage in rendered if stage.stage == "verifier")
    expected_types = {
        "verifier": (
            "ComplexityReduction.Certificate.CertifiedVerifier "
            f"{problem_declaration}"
        ),
        "witness_presentation": (
            "ComplexityReduction.Encoding.StructuralRepresentationCertificate "
            f"{verifier}.witness.encodedType {verifier}.witness.representation"
        ),
        "discipline": (
            "ComplexityReduction.Certificate.CertifiedVerifierEncodingDiscipline "
            f"{verifier}"
        ),
        "native_membership": (
            "ComplexityReduction.Certificate.NativeTMInNP "
            f"{problem_declaration}"
        ),
    }
    layout_by_stage = {stage.stage: stage for stage in layout.stages}
    return tuple(
        AuthoringStageBoundary(
            stage=stage.stage,
            module=stage.module,
            declaration=stage.declaration,
            editable_file=layout_by_stage[stage.stage].source_relative,
            expected_type=expected_types[stage.stage],
            fixed_header_sha256=stage.candidate.fixed_header_sha256,
            fixed_footer_sha256=stage.candidate.fixed_footer_sha256,
        )
        for stage in rendered
    )


def plan_native_membership_authoring(
    *,
    gap: HardnessGap,
    probe: ProbeResult,
    job_id: str,
    input_module: str,
    attempt_budget: int,
) -> DeterministicAuthoringPlan | None:
    if gap.reason not in {
        "verifierProgram",
        "witnessLawfulPresentation",
        "verifierEncodingDiscipline",
        "checkerCombinatorPairList",
        "checkerCombinatorUnsupported",
        "witnessBound",
        "soundnessLemma",
        "problemToKnownNP",
        "nativeMembership",
    }:
        return None
    if attempt_budget <= 0:
        raise ValueError("authoring attempt budget must be positive")
    layout = _native_membership_layout(job_id)
    candidates = _matching_exact_templates(
        gap, probe, template_kind=NATIVE_MEMBERSHIP_TEMPLATE_KIND
    )
    boundaries: tuple[AuthoringStageBoundary, ...] = ()
    if candidates:
        boundaries = _native_membership_stage_boundaries(
            layout=layout,
            input_module=input_module,
            problem_declaration=gap.source_declaration,
            provider_declaration=candidates[0].provider_declaration,
            component_declarations=candidates[0].component_declarations,
        )
    final_boundary = boundaries[-1] if boundaries else None
    expected_type = (
        "ComplexityReduction.Certificate.NativeTMInNP "
        f"{gap.source_declaration}"
    )
    task = AuthoringTaskPacket.from_gap(
        gap,
        expected_type=expected_type,
        template_kind=NATIVE_MEMBERSHIP_TEMPLATE_KIND,
        candidate_module=layout.module,
        candidate_declaration=layout.declaration,
        allowed_imports=(
            AUTHORING_MODULE,
            AXIOM_GATE_MODULE,
            input_module,
            *(stage.module for stage in layout.stages),
        ),
        editable_files=layout.source_relatives,
        attempt_budget=attempt_budget,
        template_candidate_ids=tuple(candidate.candidate_id for candidate in candidates),
        fixed_header_sha256=(final_boundary.fixed_header_sha256 if final_boundary else ""),
        fixed_footer_sha256=(final_boundary.fixed_footer_sha256 if final_boundary else ""),
        stage_boundaries=boundaries,
    )
    return DeterministicAuthoringPlan(
        task=task,
        layout=layout,
        candidates=candidates,
        primary_capability_head="ComplexityReduction.Certificate.NativeTMInNP",
    )


def render_deterministic_candidate(
    *,
    plan: DeterministicAuthoringPlan,
    authoring_candidate: FamilyInstantiationCandidate | ExactAuthoringTemplateCandidate,
    input_module: str,
    gap: HardnessGap,
) -> tuple[RenderedCandidateStage, ...]:
    task = plan.task
    if task.template_kind == CLOSED_FAMILY_TEMPLATE_KIND:
        if not isinstance(authoring_candidate, FamilyInstantiationCandidate):
            raise ValueError("closed-family plan received a non-family observation")
        candidate = build_closed_family_candidate_source(
            input_module=input_module,
            candidate_module=plan.layout.module,
            candidate_declaration=plan.layout.declaration,
            source_declaration=gap.source_declaration,
            target_declaration=gap.target_declaration,
            family_declaration=authoring_candidate.family_declaration,
            argument_declarations=authoring_candidate.argument_declarations,
            role=gap.role,
        )
    elif task.template_kind == LAWFUL_PRESENTATION_TEMPLATE_KIND:
        if not isinstance(authoring_candidate, ExactAuthoringTemplateCandidate):
            raise ValueError("lawful-presentation plan received a non-template observation")
        candidate = build_lawful_presentation_candidate_source(
            input_module=input_module,
            candidate_module=plan.layout.module,
            candidate_declaration=plan.layout.declaration,
            route_declaration=plan.layout.route_declaration,
            source_declaration=gap.source_declaration,
            target_declaration=gap.target_declaration,
            provider_declaration=authoring_candidate.provider_declaration,
            role=gap.role,
        )
    elif task.template_kind == PRIMITIVE_ADMISSION_TEMPLATE_KIND:
        if not isinstance(authoring_candidate, ExactAuthoringTemplateCandidate):
            raise ValueError("primitive-admission plan received a non-template observation")
        candidate = build_primitive_admission_candidate_source(
            input_module=input_module,
            candidate_module=plan.layout.module,
            candidate_declaration=plan.layout.declaration,
            route_declaration=plan.layout.route_declaration,
            source_declaration=gap.source_declaration,
            target_declaration=gap.target_declaration,
            provider_declaration=authoring_candidate.provider_declaration,
            role=gap.role,
        )
    elif task.template_kind in {
        PROGRAM_INDEXED_REDUCTION_TEMPLATE_KIND,
        PROGRAM_INDEXED_MODEL_TEMPLATE_KIND,
    }:
        if not isinstance(authoring_candidate, ExactAuthoringTemplateCandidate):
            raise ValueError("program-indexed plan received a non-template observation")
        base_module = plan.layout.stages[0].module.rsplit(".", 1)[0]
        sources = build_program_indexed_reduction_candidate_sources(
            input_module=input_module,
            candidate_base_module=base_module,
            source_declaration=gap.source_declaration,
            target_declaration=gap.target_declaration,
            provider_declaration=authoring_candidate.provider_declaration,
            component_declarations=authoring_candidate.component_declarations,
            role=gap.role,
            model_semantic_body=(
                task.template_kind == PROGRAM_INDEXED_MODEL_TEMPLATE_KIND
            ),
        )
        layout_by_stage = {stage.stage: stage for stage in plan.layout.stages}
        return tuple(
            RenderedCandidateStage(
                layout=layout_by_stage[source.stage],
                candidate=source.candidate,
            )
            for source in sources
        )
    elif task.template_kind == NATIVE_MEMBERSHIP_TEMPLATE_KIND:
        if not isinstance(authoring_candidate, ExactAuthoringTemplateCandidate):
            raise ValueError("native-membership plan received a non-template observation")
        base_module = plan.layout.stages[0].module.rsplit(".", 1)[0]
        sources = build_native_membership_candidate_sources(
            input_module=input_module,
            candidate_base_module=base_module,
            problem_declaration=gap.source_declaration,
            provider_declaration=authoring_candidate.provider_declaration,
            component_declarations=authoring_candidate.component_declarations,
        )
        layout_by_stage = {stage.stage: stage for stage in plan.layout.stages}
        return tuple(
            RenderedCandidateStage(
                layout=layout_by_stage[source.stage],
                candidate=source.candidate,
            )
            for source in sources
        )
    else:
        raise ValueError(f"unsupported deterministic template: {task.template_kind}")

    layout = plan.layout.all_stages[0]
    return (
        RenderedCandidateStage(
            layout=JobLocalCandidateStageLayout(
                stage=task.template_kind,
                module=layout.module,
                declaration=layout.declaration,
                source_relative=layout.source_relative,
                olean_relative=layout.olean_relative,
            ),
            candidate=candidate,
        ),
    )


def plan_deterministic_authoring(
    *,
    gap: HardnessGap,
    probe: ProbeResult,
    job_id: str,
    input_module: str,
    attempt_budget: int,
) -> DeterministicAuthoringPlan | None:
    planners = (
        plan_closed_family_authoring,
        plan_lawful_presentation_authoring,
        plan_primitive_admission_authoring,
        plan_program_indexed_reduction_authoring,
        plan_native_membership_authoring,
    )
    fallback: DeterministicAuthoringPlan | None = None
    for planner in planners:
        plan = planner(
            gap=gap,
            probe=probe,
            job_id=job_id,
            input_module=input_module,
            attempt_budget=attempt_budget,
        )
        if plan is not None:
            if plan.candidates:
                return plan
            if fallback is None:
                fallback = plan
    return fallback


def plan_authoring(
    *,
    gap: HardnessGap,
    probe: ProbeResult,
    job_id: str,
    input_module: str,
    attempt_budget: int,
    mode: str,
    model_available: bool = True,
) -> DeterministicAuthoringPlan | None:
    """Choose a task deterministically; the model never selects a task or route."""

    if mode not in SUPPORTED_MODES:
        raise ValueError(f"unsupported authoring mode: {mode}")
    if mode in MODEL_MODES and model_available:
        model_plan = plan_program_indexed_model_authoring(
            gap=gap,
            probe=probe,
            job_id=job_id,
            input_module=input_module,
            attempt_budget=attempt_budget,
        )
        if model_plan is not None and model_plan.candidates:
            return model_plan
    return plan_deterministic_authoring(
        gap=gap,
        probe=probe,
        job_id=job_id,
        input_module=input_module,
        attempt_budget=attempt_budget,
    )
