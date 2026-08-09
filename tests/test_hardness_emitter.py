import pytest

from agent.hardness.lean_runner import (
    assert_candidate_source_fences,
    build_artifact_source,
    build_candidate_validation_source,
    build_closed_family_candidate_source,
    build_goal_source,
    build_input_observation_batch_source,
    build_input_observation_source,
    build_lawful_presentation_candidate_source,
    build_module_command,
    build_native_membership_candidate_sources,
    build_problem_catalog_source,
    build_primitive_admission_candidate_source,
    build_program_indexed_reduction_candidate_sources,
    build_probe_source,
)
from agent.hardness.models import HardnessGap, RouteCandidate


def route() -> RouteCandidate:
    return RouteCandidate(
        target_declaration="Known.target",
        membership_declaration="Known.membership",
        atoms=("Known.edge",),
        roles=("sharedGadget",),
        final_composition_edges=0,
        registry_fingerprint="registry",
    )


def test_build_module_command_rebuilds_runtime_and_deduplicated_inputs() -> None:
    assert build_module_command(["Input.Second", "Input.First", "Input.Second"]) == [
        "lake",
        "build",
        "ComplexityReduction.Agent.Hardness.Runtime",
        "Input.First",
        "Input.Second",
    ]


def test_input_observation_source_imports_only_inspector_and_user_module() -> None:
    source = build_input_observation_source(
        input_module="Input.Module",
        nonce="nonce",
        input_declaration="Input.Module.problem",
    )
    assert "import ComplexityReduction.Agent.Hardness.InputInspection" in source
    assert "import Input.Module" in source
    assert '#hardness_inspect_input "nonce" Input.Module.problem' in source
    assert "source_node_id" not in source


def test_input_observation_batch_uses_one_import_context_and_unique_nonces() -> None:
    source = build_input_observation_batch_source(
        input_module="Input.Module",
        requests=(("first", "Input.Module.first"), ("second", "Input.Module.second")),
    )
    assert source.count("import ComplexityReduction.Agent.Hardness.InputInspection") == 1
    assert source.count("import Input.Module") == 1
    assert '#hardness_inspect_input "first" Input.Module.first' in source
    assert '#hardness_inspect_input "second" Input.Module.second' in source
    with pytest.raises(ValueError, match="unique"):
        build_input_observation_batch_source(
            input_module="Input.Module",
            requests=(("same", "Input.Module.first"), ("same", "Input.Module.second")),
        )


def test_problem_catalog_source_is_nonce_bound_and_has_no_input_oracle() -> None:
    source = build_problem_catalog_source(nonce="catalog-nonce")
    assert "import ComplexityReduction.Agent.Hardness.ProblemCatalog" in source
    assert "import ComplexityReduction.Agent.Hardness.TargetCatalog" in source
    assert '#hardness_export_problem_catalog "catalog-nonce"' in source
    assert '#hardness_export_target_catalog "catalog-nonce"' in source
    assert "Benchmark" not in source
    assert "Expected" not in source


def test_probe_imports_module_without_copying_input_source() -> None:
    source = build_probe_source(
        input_module="Input.Module",
        nonce="nonce",
        source_declaration="Input.Module.source",
        membership_declaration=None,
        objective="reduce_to_known_np",
        target_declaration=None,
    )
    assert "import Input.Module" in source
    assert '#hardness_probe "nonce" Input.Module.source' in source


def test_goal_gate_checks_exact_source_target_and_membership_types() -> None:
    source = build_goal_source(
        input_module="Input.Module",
        source_declaration="Input.Module.source",
        membership_declaration="Input.Module.membership",
        target_declaration="Known.target",
    )
    assert "import ComplexityReduction.Agent.Hardness.InputGate" in source
    assert "import ComplexityReduction.Agent.Hardness.Runtime" not in source
    assert "example : ComplexityReduction.Encoding.PresentedProblem := Input.Module.source" in source
    assert "example : ComplexityReduction.Encoding.PresentedProblem := Known.target" in source
    assert (
        "example : ComplexityReduction.Certificate.NativeTMInNP Input.Module.source := "
        "Input.Module.membership"
    ) in source


def test_artifact_uses_stable_declaration_handles_only() -> None:
    source = build_artifact_source(
        input_module="Input.Module",
        source_declaration="Input.Module.source",
        membership_declaration=None,
        objective="reduce_to_known_np",
        route=route(),
    )
    assert "Known.target" in source
    assert "Known.edge" in source
    assert "CertifiedPath.step Known.edge" in source
    assert "reduceToKnownNPPath" in source
    assert "by_hardness_resolver" not in source
    assert "assert_standard_axioms" in source


def test_fixed_target_probe_uses_the_requested_catalog_command() -> None:
    flat = build_probe_source(
        input_module="Input.Module",
        nonce="nonce",
        source_declaration="Input.Module.source",
        membership_declaration=None,
        objective="reduce_to",
        target_declaration="Input.Module.target",
        catalog_mode="flat_api",
    )
    ir = build_probe_source(
        input_module="Input.Module",
        nonce="nonce",
        source_declaration="Input.Module.source",
        membership_declaration=None,
        objective="reduce_to",
        target_declaration="Input.Module.target",
        catalog_mode="ir_components",
    )
    assert '#hardness_probe_to_flat "nonce" Input.Module.source Input.Module.target' in flat
    assert '#hardness_probe_to_ir "nonce" Input.Module.source Input.Module.target' in ir


def test_artifact_explicitly_composes_every_selected_route_atom() -> None:
    selected = RouteCandidate(
        target_declaration="Input.Module.target",
        membership_declaration=None,
        atoms=("Edge.ingress", "Edge.shared", "Edge.egress"),
        roles=("ingress", "sharedGadget", "egress"),
        final_composition_edges=0,
        registry_fingerprint="registry",
    )
    source = build_artifact_source(
        input_module="Input.Module",
        source_declaration="Input.Module.source",
        membership_declaration=None,
        objective="reduce_to",
        route=selected,
    )
    assert "CertifiedPath.step Edge.ingress" in source
    assert source.count("CertifiedPath.cons") == 2
    assert "Edge.shared" in source
    assert "Edge.egress" in source
    assert "reduceToPath" in source


def test_membership_probe_and_artifact_install_checked_cook_levin_root() -> None:
    probe = build_probe_source(
        input_module="Input.Module",
        nonce="nonce",
        source_declaration="Input.Module.source",
        membership_declaration="Input.Module.membership",
        objective="reduce_to_known_np",
        target_declaration=None,
    )
    assert "GeneratedProbe.nativeCookLevinRoot" not in probe
    assert "noncomputable def nativeCookLevinRoot" in probe
    assert "NativeCookLevin.reduce Input.Module.membership" in probe
    assert "complexity_reduction_ir_component_ingress" in probe

    artifact = build_artifact_source(
        input_module="Input.Module",
        source_declaration="Input.Module.source",
        membership_declaration="Input.Module.membership",
        objective="reduce_to_known_np",
        route=route(),
    )
    assert "noncomputable def nativeCookLevinRoot" in artifact
    assert "NativeCookLevin.reduce Input.Module.membership" in artifact
    assert "GeneratedArtifact.nativeCookLevinRoot" in artifact
    assert "GeneratedArtifact.result" in artifact


def test_capability_probes_use_exact_closed_resolver_commands() -> None:
    membership_probe = build_probe_source(
        input_module="Input.Module",
        nonce="nonce",
        source_declaration="Input.Module.source",
        membership_declaration=None,
        objective="prove_in_np",
        target_declaration=None,
    )
    completeness_probe = build_probe_source(
        input_module="Input.Module",
        nonce="nonce",
        source_declaration="Input.Module.source",
        membership_declaration=None,
        objective="prove_np_complete",
        target_declaration=None,
    )
    assert '#hardness_probe_in_np "nonce" Input.Module.source' in membership_probe
    assert '#hardness_probe_np_complete "nonce" Input.Module.source' in completeness_probe


def test_capability_artifacts_project_and_independently_audit_exact_evidence() -> None:
    membership_route = RouteCandidate(
        target_declaration="Input.Module.source",
        membership_declaration="Input.Module.membership",
        atoms=(),
        roles=(),
        final_composition_edges=0,
        registry_fingerprint="registry",
        evidence_kind="native_membership",
    )
    membership_artifact = build_artifact_source(
        input_module="Input.Module",
        source_declaration="Input.Module.source",
        membership_declaration=None,
        objective="prove_in_np",
        route=membership_route,
    )
    assert ".proveInNP Input.Module.source" in membership_artifact
    assert "extractNativeMembership result" in membership_artifact
    assert "GeneratedArtifact.membershipEvidence" in membership_artifact

    completeness_route = RouteCandidate(
        target_declaration="Input.Module.source",
        membership_declaration="Input.Module.membership",
        atoms=("Route.forward",),
        roles=("sharedGadget",),
        final_composition_edges=0,
        registry_fingerprint="registry",
        evidence_kind="transported_completeness",
        completeness_declaration="Complete.hub",
        hub_declaration="Hub.problem",
    )
    completeness_artifact = build_artifact_source(
        input_module="Input.Module",
        source_declaration="Input.Module.source",
        membership_declaration=None,
        objective="prove_np_complete",
        route=completeness_route,
    )
    assert ".proveNPComplete Input.Module.source" in completeness_artifact
    assert "extractNativeCompleteness result" in completeness_artifact
    assert "GeneratedArtifact.completenessEvidence" in completeness_artifact


def test_explicit_capability_membership_is_installed_as_exact_attributed_alias() -> None:
    probe = build_probe_source(
        input_module="Input.Module",
        nonce="nonce",
        source_declaration="Input.Module.source",
        membership_declaration="Input.Module.membership",
        objective="prove_np_complete",
        target_declaration=None,
    )
    assert "complexity_reduction_ir_typed_native_membership" in probe
    assert "theorem providedNativeMembership" in probe
    assert "NativeCookLevin.reduce" not in probe


def test_declaration_injection_is_rejected() -> None:
    with pytest.raises(ValueError):
        build_probe_source(
            input_module="Input.Module",
            nonce="n",
            source_declaration="Input.source\n#exit",
            membership_declaration=None,
            objective="reduce_to_known_np",
            target_declaration=None,
        )


def test_hardness_gap_cannot_be_used_as_an_artifact_route() -> None:
    gap = HardnessGap(
        reason="primitive",
        failure_code="missing_primitive",
        role="sharedGadget",
        source_declaration="Input.Module.source",
        target_declaration="Known.target",
        expected_capability_head="ComplexityReduction.Program.Primitive",
        registry_fingerprint="registry",
    )
    with pytest.raises(TypeError):
        build_artifact_source(
            input_module="Input.Module",
            source_declaration="Input.Module.source",
            membership_declaration=None,
            objective="reduce_to",
            route=gap,  # type: ignore[arg-type]
        )


def test_closed_family_candidate_has_fixed_exact_endpoint_fences() -> None:
    candidate = build_closed_family_candidate_source(
        input_module="Input.Module",
        candidate_module="Generated.Hardness.J0123456789abcdef.ClosedFamily",
        candidate_declaration=(
            "Generated.Hardness.J0123456789abcdef.ClosedFamily.capability"
        ),
        source_declaration="Input.Module.source",
        target_declaration="Input.Module.target",
        family_declaration="Family.edge",
        argument_declarations=("Input.Module.language",),
        role="sharedGadget",
    )
    assert "CertifiedReduction Input.Module.source Input.Module.target" in candidate.fixed_header
    assert "@Family.edge Input.Module.language" in candidate.editable_body
    assert "assert_standard_axioms" in candidate.fixed_footer
    assert_candidate_source_fences(candidate.source, candidate)

    changed_body = candidate.source.replace(
        "@Family.edge Input.Module.language", "@Family.other Input.Module.language"
    )
    assert_candidate_source_fences(changed_body, candidate)
    with pytest.raises(ValueError):
        assert_candidate_source_fences(
            candidate.source.replace("Input.Module.target", "Input.Module.otherTarget", 1),
            candidate,
        )


def test_candidate_validation_uses_declaration_handles_and_job_local_import() -> None:
    source = build_candidate_validation_source(
        candidate_module="Generated.Hardness.J0123456789abcdef.ClosedFamily",
        nonce="nonce",
        candidate_declaration=(
            "Generated.Hardness.J0123456789abcdef.ClosedFamily.capability"
        ),
        source_declaration="Input.Module.source",
        target_declaration="Input.Module.target",
    )
    assert "import Generated.Hardness.J0123456789abcdef.ClosedFamily" in source
    assert '#hardness_validate_candidate "nonce"' in source


def test_probe_and_artifact_import_validated_job_local_candidate() -> None:
    candidate_module = "Generated.Hardness.J0123456789abcdef.ClosedFamily"
    probe = build_probe_source(
        input_module="Input.Module",
        nonce="nonce",
        source_declaration="Input.Module.source",
        membership_declaration=None,
        objective="reduce_to",
        target_declaration="Input.Module.target",
        extra_imports=(candidate_module,),
    )
    artifact = build_artifact_source(
        input_module="Input.Module",
        source_declaration="Input.Module.source",
        membership_declaration=None,
        objective="reduce_to",
        route=route(),
        extra_imports=(candidate_module,),
    )
    assert f"import {candidate_module}" in probe
    assert f"import {candidate_module}" in artifact


def test_lawful_presentation_candidate_fixes_structural_head_and_route_bundle() -> None:
    module = "Generated.Hardness.J0123456789abcdef.LawfulPresentation"
    candidate = build_lawful_presentation_candidate_source(
        input_module="Input.Module",
        candidate_module=module,
        candidate_declaration=f"{module}.capability",
        route_declaration=f"{module}.route",
        source_declaration="Input.Module.source",
        target_declaration="Input.Module.target",
        provider_declaration="Input.Module.template",
        role="ingress",
    )
    assert "StructuralRepresentationCertificate" in candidate.fixed_header
    assert "Input.Module.template.toStructuralCertificate" in candidate.editable_body
    assert "Input.Module.template.toReduction capability" in candidate.fixed_footer
    assert "complexity_reduction_ir_component_ingress" in candidate.fixed_footer
    assert_candidate_source_fences(candidate.source, candidate)

    validation = build_candidate_validation_source(
        candidate_module=module,
        nonce="nonce",
        candidate_declaration=f"{module}.capability",
        route_declaration=f"{module}.route",
        template_kind="lawful_presentation",
        source_declaration="Input.Module.source",
        target_declaration="Input.Module.target",
    )
    assert '#hardness_validate_lawful_candidate "nonce"' in validation


def test_primitive_candidate_embeds_the_same_admitted_executable_in_route() -> None:
    module = "Generated.Hardness.J0123456789abcdef.PrimitiveAdmission"
    candidate = build_primitive_admission_candidate_source(
        input_module="Input.Module",
        candidate_module=module,
        candidate_declaration=f"{module}.capability",
        route_declaration=f"{module}.route",
        source_declaration="Input.Module.source",
        target_declaration="Input.Module.target",
        provider_declaration="Input.Module.template",
        role="sharedGadget",
    )
    assert "ComplexityReduction.Program.Primitive" in candidate.fixed_header
    assert "Input.Module.template.toPrimitive" in candidate.editable_body
    assert "Input.Module.template.toReduction capability rfl" in candidate.fixed_footer
    assert_candidate_source_fences(candidate.source, candidate)

    validation = build_candidate_validation_source(
        candidate_module=module,
        nonce="nonce",
        candidate_declaration=f"{module}.capability",
        route_declaration=f"{module}.route",
        template_kind="primitive_admission",
        source_declaration="Input.Module.source",
        target_declaration="Input.Module.target",
    )
    assert '#hardness_validate_primitive_candidate "nonce"' in validation


def test_program_indexed_reduction_has_seven_fenced_same_program_stages() -> None:
    base = "Generated.Hardness.J0123456789abcdef.ProgramIndexedReduction"
    stages = build_program_indexed_reduction_candidate_sources(
        input_module="Input.Module",
        candidate_base_module=base,
        source_declaration="Input.Module.source",
        target_declaration="Input.Module.target",
        provider_declaration="Input.Module.template",
        component_declarations=(
            "Input.Module.executable",
            "Input.Module.executableDirectTM",
            "Input.Module.executableCorrect",
        ),
        role="sharedGadget",
    )
    assert [stage.stage for stage in stages] == [
        "executable",
        "executable_direct_tm",
        "primitive",
        "program",
        "semantic_proof",
        "direct_tm",
        "certified_reduction",
    ]
    first_source = stages[0].candidate.source
    assert "import ComplexityReduction.Agent.Hardness.Authoring" in first_source
    assert "import ComplexityReduction.AxiomGate" in first_source
    assert "import Input.Module" in first_source
    assert "import ComplexityReduction.Agent.Hardness.Runtime" not in first_source
    assert "Input.Module.executable\n" in stages[0].candidate.editable_body
    assert "Input.Module.executableCorrect" not in stages[0].candidate.source
    assert "Input.Module.executableDirectTM" in stages[1].candidate.editable_body
    assert "Input.Module.executableCorrect" in stages[4].candidate.editable_body
    for stage in stages:
        assert_candidate_source_fences(stage.candidate.source, stage.candidate)
        assert stage.candidate.fixed_header_sha256
        assert stage.candidate.fixed_footer_sha256
    declarations = {stage.stage: stage.declaration for stage in stages}
    program = declarations["program"]
    assert program in stages[4].candidate.fixed_header
    assert program in stages[5].candidate.fixed_header
    assert "ProgramDirectTMEvidence" in stages[5].candidate.fixed_header
    assert "CostedMap" not in stages[5].candidate.source
    validation = build_candidate_validation_source(
        candidate_module=stages[-1].module,
        nonce="nonce",
        candidate_declaration=stages[-1].declaration,
        route_declaration=stages[-1].declaration,
        template_kind="program_indexed_reduction",
        stage_declarations=declarations,
        source_declaration="Input.Module.source",
        target_declaration="Input.Module.target",
    )
    assert '#hardness_validate_program_reduction_candidate "nonce"' in validation
    assert declarations["semantic_proof"] in validation
    assert declarations["direct_tm"] in validation


def test_native_membership_has_four_fenced_same_verifier_stages() -> None:
    base = "Generated.Hardness.J0123456789abcdef.NativeMembership"
    stages = build_native_membership_candidate_sources(
        input_module="Input.Module",
        candidate_base_module=base,
        problem_declaration="Input.Module.problem",
        provider_declaration="Input.Module.template",
        component_declarations=(
            "Input.Module.verifier",
            "Input.Module.witnessPresentation",
            "Input.Module.discipline",
        ),
    )
    assert [stage.stage for stage in stages] == [
        "verifier",
        "witness_presentation",
        "discipline",
        "native_membership",
    ]
    assert "Input.Module.verifier" in stages[0].candidate.editable_body
    assert "Input.Module.witnessPresentation" in stages[1].candidate.editable_body
    assert "Input.Module.discipline" in stages[2].candidate.editable_body
    assert "NativeTMInNP Input.Module.problem" in stages[3].candidate.fixed_header
    for stage in stages:
        assert_candidate_source_fences(stage.candidate.source, stage.candidate)
        assert "assert_standard_axioms" in stage.candidate.fixed_footer
    declarations = {stage.stage: stage.declaration for stage in stages}
    validation = build_candidate_validation_source(
        candidate_module=stages[-1].module,
        nonce="nonce",
        candidate_declaration=stages[-1].declaration,
        route_declaration=stages[-1].declaration,
        template_kind="native_membership",
        stage_declarations=declarations,
        source_declaration="Input.Module.problem",
        target_declaration="Input.Module.problem",
    )
    assert '#hardness_validate_native_membership_candidate "nonce"' in validation
    assert declarations["verifier"] in validation
    assert declarations["discipline"] in validation
