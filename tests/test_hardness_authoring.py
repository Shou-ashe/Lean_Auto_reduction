from agent.hardness.authoring import (
    candidate_layout,
    plan_authoring,
    plan_closed_family_authoring,
    plan_deterministic_authoring,
    render_deterministic_candidate,
)
from agent.hardness.models import (
    ExactAuthoringTemplateCandidate,
    FamilyInstantiationCandidate,
    HardnessGap,
    ProbeResult,
)


def gap() -> HardnessGap:
    return HardnessGap(
        reason="unresolvedFamilyPremise",
        failure_code="unresolved_family_premise",
        role="sharedGadget",
        source_declaration="Input.Module.source",
        target_declaration="Input.Module.target",
        expected_capability_head=(
            "ComplexityReduction.Registry.ParameterizedCapabilityFamilyObservation"
        ),
        registry_fingerprint="registry-1",
    )


def probe() -> ProbeResult:
    candidate = FamilyInstantiationCandidate(
        family_declaration="Family.edge",
        argument_declarations=("Input.Module.language",),
        role="sharedGadget",
        source_declaration="Input.Module.source",
        target_declaration="Input.Module.target",
        registry_fingerprint="registry-1",
    )
    return ProbeResult(
        nonce="nonce",
        source_declaration="Input.Module.source",
        source_display="source",
        registry_fingerprint="registry-1",
        targets=(),
        routes=(),
        gaps=(gap(),),
        family_instantiations=(candidate,),
    )


def test_closed_family_task_fixes_workspace_type_and_budget() -> None:
    plan = plan_closed_family_authoring(
        gap=gap(),
        probe=probe(),
        job_id="sha256:" + "a" * 64,
        input_module="Input.Module",
        attempt_budget=2,
    )
    assert plan is not None
    assert plan.task.template_kind == "closed_family_instantiation"
    assert plan.task.attempt_budget == 2
    assert plan.task.candidate_module.startswith("Generated.Hardness.J")
    assert plan.task.editable_files == (plan.layout.source_relative,)
    assert plan.task.fixed_header_sha256
    assert plan.task.fixed_footer_sha256
    assert len(plan.candidates) == 1


def test_non_family_gap_has_no_deterministic_authoring_lane() -> None:
    other = HardnessGap(
        reason="primitive",
        failure_code="missing_primitive",
        role="sharedGadget",
        source_declaration="Input.Module.source",
        target_declaration="Input.Module.target",
        expected_capability_head="ComplexityReduction.Program.Primitive",
        registry_fingerprint="registry-1",
    )
    assert (
        plan_closed_family_authoring(
            gap=other,
            probe=probe(),
            job_id="sha256:" + "a" * 64,
            input_module="Input.Module",
            attempt_budget=1,
        )
        is None
    )


def test_candidate_layout_is_content_addressed_and_has_no_hyphen_segment() -> None:
    layout = candidate_layout("sha256:" + "1" * 64)
    assert layout.module == "Generated.Hardness.J1111111111111111.ClosedFamily"
    assert layout.declaration == layout.module + ".capability"
    assert layout.route_declaration == layout.declaration
    assert layout.source_relative.endswith("ClosedFamily.lean")


def exact_gap(reason: str) -> HardnessGap:
    return HardnessGap(
        reason=reason,
        failure_code=(
            "missing_lawful_presentation"
            if reason == "lawfulPresentation"
            else "missing_primitive"
        ),
        role="ingress" if reason == "lawfulPresentation" else "sharedGadget",
        source_declaration="Input.Module.source",
        target_declaration="Input.Module.target",
        expected_capability_head=(
            "ComplexityReduction.Encoding.StructuralRepresentationCertificate"
            if reason == "lawfulPresentation"
            else "ComplexityReduction.Program.Primitive"
        ),
        registry_fingerprint="registry-1",
    )


def exact_probe(reason: str) -> ProbeResult:
    gap_value = exact_gap(reason)
    template_kind = (
        "lawful_presentation" if reason == "lawfulPresentation" else "primitive_admission"
    )
    candidate = ExactAuthoringTemplateCandidate(
        template_kind=template_kind,
        provider_declaration="Input.Module.template",
        role=gap_value.role,
        source_declaration=gap_value.source_declaration,
        target_declaration=gap_value.target_declaration,
        registry_fingerprint=gap_value.registry_fingerprint,
    )
    return ProbeResult(
        nonce="nonce",
        source_declaration=gap_value.source_declaration,
        source_display="source",
        registry_fingerprint=gap_value.registry_fingerprint,
        targets=(),
        routes=(),
        gaps=(gap_value,),
        authoring_templates=(candidate,),
    )


def test_lawful_presentation_plan_fixes_structural_primary_and_derived_route() -> None:
    gap_value = exact_gap("lawfulPresentation")
    plan = plan_deterministic_authoring(
        gap=gap_value,
        probe=exact_probe("lawfulPresentation"),
        job_id="sha256:" + "b" * 64,
        input_module="Input.Module",
        attempt_budget=1,
    )
    assert plan is not None
    assert plan.task.template_kind == "lawful_presentation"
    assert plan.layout.module.endswith(".LawfulPresentation")
    assert plan.layout.route_declaration.endswith(".route")
    assert plan.primary_capability_head.endswith("StructuralRepresentationCertificate")
    assert len(plan.candidates) == 1


def test_primitive_plan_admits_only_exact_existing_executable_template() -> None:
    gap_value = exact_gap("primitive")
    plan = plan_deterministic_authoring(
        gap=gap_value,
        probe=exact_probe("primitive"),
        job_id="sha256:" + "c" * 64,
        input_module="Input.Module",
        attempt_budget=1,
    )
    assert plan is not None
    assert plan.task.template_kind == "primitive_admission"
    assert plan.layout.module.endswith(".PrimitiveAdmission")
    assert plan.primary_capability_head == "ComplexityReduction.Program.Primitive"
    assert plan.task.template_candidate_ids


def test_program_indexed_plan_fixes_seven_stage_boundaries_and_final_certificate() -> None:
    gap_value = HardnessGap(
        reason="semanticProof",
        failure_code="missing_semantic_proof",
        role="sharedGadget",
        source_declaration="Input.Module.source",
        target_declaration="Input.Module.target",
        expected_capability_head="ComplexityReduction.Certificate.CertifiedReduction",
        registry_fingerprint="registry-1",
    )
    candidate = ExactAuthoringTemplateCandidate(
        template_kind="program_indexed_reduction",
        provider_declaration="Input.Module.template",
        role=gap_value.role,
        source_declaration=gap_value.source_declaration,
        target_declaration=gap_value.target_declaration,
        registry_fingerprint=gap_value.registry_fingerprint,
        component_declarations=(
            "Input.Module.executable",
            "Input.Module.executableDirectTM",
            "Input.Module.executableCorrect",
        ),
    )
    probe_value = ProbeResult(
        nonce="nonce",
        source_declaration=gap_value.source_declaration,
        source_display="source",
        registry_fingerprint=gap_value.registry_fingerprint,
        targets=(),
        routes=(),
        gaps=(gap_value,),
        authoring_templates=(candidate,),
    )
    plan = plan_deterministic_authoring(
        gap=gap_value,
        probe=probe_value,
        job_id="sha256:" + "d" * 64,
        input_module="Input.Module",
        attempt_budget=2,
    )
    assert plan is not None
    assert plan.task.template_kind == "program_indexed_reduction"
    assert plan.primary_capability_head == "ComplexityReduction.Certificate.CertifiedReduction"
    assert plan.task.allowed_imports[:3] == (
        "ComplexityReduction.Agent.Hardness.Authoring",
        "ComplexityReduction.AxiomGate",
        "Input.Module",
    )
    assert "ComplexityReduction.Agent.Hardness.Runtime" not in plan.task.allowed_imports
    assert [boundary.stage for boundary in plan.task.stage_boundaries] == [
        "executable",
        "executable_direct_tm",
        "primitive",
        "program",
        "semantic_proof",
        "direct_tm",
        "certified_reduction",
    ]
    assert plan.layout.module.endswith(".Reduction")
    assert plan.layout.route_declaration == plan.layout.declaration
    rendered = render_deterministic_candidate(
        plan=plan,
        authoring_candidate=candidate,
        input_module="Input.Module",
        gap=gap_value,
    )
    assert tuple(stage.layout.source_relative for stage in rendered) == plan.layout.source_relatives


def test_native_membership_plan_fixes_four_stage_boundaries_and_exact_problem() -> None:
    gap_value = HardnessGap(
        reason="verifierProgram",
        failure_code="missing_verifier_program",
        role="finalComposition",
        source_declaration="Input.Module.problem",
        target_declaration="Input.Module.problem",
        expected_capability_head="ComplexityReduction.Certificate.CertifiedVerifier",
        registry_fingerprint="registry-1",
    )
    candidate = ExactAuthoringTemplateCandidate(
        template_kind="native_membership",
        provider_declaration="Input.Module.template",
        role=gap_value.role,
        source_declaration=gap_value.source_declaration,
        target_declaration=gap_value.target_declaration,
        registry_fingerprint=gap_value.registry_fingerprint,
        component_declarations=(
            "Input.Module.verifier",
            "Input.Module.witnessPresentation",
            "Input.Module.discipline",
        ),
    )
    probe_value = ProbeResult(
        nonce="nonce",
        source_declaration=gap_value.source_declaration,
        source_display="source",
        registry_fingerprint=gap_value.registry_fingerprint,
        targets=(),
        routes=(),
        gaps=(gap_value,),
        authoring_templates=(candidate,),
    )
    plan = plan_deterministic_authoring(
        gap=gap_value,
        probe=probe_value,
        job_id="sha256:" + "e" * 64,
        input_module="Input.Module",
        attempt_budget=1,
    )
    assert plan is not None
    assert plan.task.template_kind == "native_membership"
    assert plan.primary_capability_head == "ComplexityReduction.Certificate.NativeTMInNP"
    assert [boundary.stage for boundary in plan.task.stage_boundaries] == [
        "verifier",
        "witness_presentation",
        "discipline",
        "native_membership",
    ]
    assert plan.task.stage_boundaries[-1].expected_type == (
        "ComplexityReduction.Certificate.NativeTMInNP Input.Module.problem"
    )
    rendered = render_deterministic_candidate(
        plan=plan,
        authoring_candidate=candidate,
        input_module="Input.Module",
        gap=gap_value,
    )
    assert tuple(stage.layout.source_relative for stage in rendered) == plan.layout.source_relatives


def test_model_plan_exposes_no_semantic_proof_oracle_and_selects_task_deterministically() -> None:
    gap_value = HardnessGap(
        reason="semanticProof",
        failure_code="missing_semantic_proof",
        role="sharedGadget",
        source_declaration="Input.Module.source",
        target_declaration="Input.Module.target",
        expected_capability_head="ComplexityReduction.Certificate.CertifiedReduction",
        registry_fingerprint="registry-1",
    )
    candidate = ExactAuthoringTemplateCandidate(
        template_kind="program_indexed_model",
        provider_declaration="Input.Module.template",
        role=gap_value.role,
        source_declaration=gap_value.source_declaration,
        target_declaration=gap_value.target_declaration,
        registry_fingerprint=gap_value.registry_fingerprint,
        component_declarations=("Input.Module.executable", "Input.Module.directTM"),
    )
    probe_value = ProbeResult(
        nonce="nonce",
        source_declaration=gap_value.source_declaration,
        source_display="source",
        registry_fingerprint=gap_value.registry_fingerprint,
        targets=(),
        routes=(),
        gaps=(gap_value,),
        authoring_templates=(candidate,),
    )
    plan = plan_authoring(
        gap=gap_value,
        probe=probe_value,
        job_id="sha256:" + "f" * 64,
        input_module="Input.Module",
        attempt_budget=3,
        mode="model-required",
    )
    assert plan is not None
    assert plan.task.template_kind == "program_indexed_model"
    assert candidate.component_declarations == (
        "Input.Module.executable",
        "Input.Module.directTM",
    )
    rendered = render_deterministic_candidate(
        plan=plan,
        authoring_candidate=candidate,
        input_module="Input.Module",
        gap=gap_value,
    )
    semantic = next(stage for stage in rendered if stage.layout.stage == "semantic_proof")
    assert semantic.candidate.editable_body == "  by\n    intro input\n"
