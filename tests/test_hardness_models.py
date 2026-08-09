from agent.hardness.models import (
    AgentResult,
    AuthoringTaskPacket,
    ExactAuthoringTemplateCandidate,
    FamilyInstantiationCandidate,
    HardnessGap,
    HardnessGoal,
    RouteCandidate,
    TypedCatalog,
    TypedInventoryEntry,
)
from agent.hardness.model_client import DeepSeekConfig


def route(*, atoms: tuple[str, ...] = ("Edge.one",)) -> RouteCandidate:
    return RouteCandidate(
        target_declaration="Target.problem",
        membership_declaration="Target.membership",
        atoms=atoms,
        roles=("sharedGadget",) * len(atoms),
        final_composition_edges=0,
        registry_fingerprint="registry-1",
    )


def test_route_id_is_content_addressed_and_stable() -> None:
    assert route().route_id == route().route_id
    assert route().route_id.startswith("sha256:")
    assert route().route_id != route(atoms=("Edge.two",)).route_id


def test_route_cost_penalizes_final_composition_before_length() -> None:
    atomic = route(atoms=("Edge.one", "Edge.two"))
    final = RouteCandidate(
        target_declaration="Target.problem",
        membership_declaration="Target.membership",
        atoms=("Edge.final",),
        roles=("finalComposition",),
        final_composition_edges=1,
        registry_fingerprint="registry-1",
    )
    assert atomic.cost < final.cost


def gap(*, reason: str = "primitive") -> HardnessGap:
    return HardnessGap(
        reason=reason,
        failure_code="missing_primitive" if reason == "primitive" else "no_registry_path",
        role="sharedGadget",
        source_declaration="Input.source",
        target_declaration="Input.target",
        expected_capability_head="ComplexityReduction.Program.Primitive",
        registry_fingerprint="registry-1",
    )


def test_gap_and_task_ids_are_content_addressed_and_stable() -> None:
    first = gap()
    assert first.gap_id == gap().gap_id
    assert first.gap_id != gap(reason="noRegistryPath").gap_id
    task = AuthoringTaskPacket.from_gap(first)
    assert task.gap_id == first.gap_id
    assert task.task_id == AuthoringTaskPacket.from_gap(first).task_id
    assert task.expected_capability_head == "ComplexityReduction.Program.Primitive"


def test_closed_family_candidate_id_binds_exact_handles_and_fingerprint() -> None:
    candidate = FamilyInstantiationCandidate(
        family_declaration="Family.edge",
        argument_declarations=("Input.language",),
        role="sharedGadget",
        source_declaration="Input.source",
        target_declaration="Input.target",
        registry_fingerprint="registry-1",
    )
    assert candidate.candidate_id == candidate.candidate_id
    changed = FamilyInstantiationCandidate(
        family_declaration="Family.edge",
        argument_declarations=("Input.otherLanguage",),
        role="sharedGadget",
        source_declaration="Input.source",
        target_declaration="Input.target",
        registry_fingerprint="registry-1",
    )
    assert candidate.candidate_id != changed.candidate_id


def test_exact_template_candidate_id_binds_kind_provider_endpoints_and_registry() -> None:
    candidate = ExactAuthoringTemplateCandidate(
        template_kind="primitive_admission",
        provider_declaration="Input.template",
        role="sharedGadget",
        source_declaration="Input.source",
        target_declaration="Input.target",
        registry_fingerprint="registry-1",
    )
    changed = ExactAuthoringTemplateCandidate(
        template_kind="primitive_admission",
        provider_declaration="Input.otherTemplate",
        role="sharedGadget",
        source_declaration="Input.source",
        target_declaration="Input.target",
        registry_fingerprint="registry-1",
    )
    assert candidate.candidate_id.startswith("sha256:")
    assert candidate.candidate_id != changed.candidate_id


def test_program_template_candidate_id_binds_independent_component_declarations() -> None:
    candidate = ExactAuthoringTemplateCandidate(
        template_kind="program_indexed_reduction",
        provider_declaration="Input.template",
        role="sharedGadget",
        source_declaration="Input.source",
        target_declaration="Input.target",
        registry_fingerprint="registry-1",
        component_declarations=("Input.run", "Input.directTM", "Input.correct"),
    )
    changed = ExactAuthoringTemplateCandidate(
        template_kind="program_indexed_reduction",
        provider_declaration="Input.template",
        role="sharedGadget",
        source_declaration="Input.source",
        target_declaration="Input.target",
        registry_fingerprint="registry-1",
        component_declarations=("Input.run", "Input.directTM", "Input.otherCorrect"),
    )
    assert candidate.candidate_id != changed.candidate_id


def test_route_id_binds_capability_evidence_and_completeness_provenance() -> None:
    registered = RouteCandidate(
        target_declaration="Target.problem",
        membership_declaration=None,
        atoms=(),
        roles=(),
        final_composition_edges=0,
        registry_fingerprint="registry-1",
        evidence_kind="registered_completeness",
        completeness_declaration="Complete.registered",
        hub_declaration="Target.problem",
    )
    transported = RouteCandidate(
        target_declaration="Target.problem",
        membership_declaration="Target.membership",
        atoms=(),
        roles=(),
        final_composition_edges=0,
        registry_fingerprint="registry-1",
        evidence_kind="transported_completeness",
        completeness_declaration="Complete.registered",
        hub_declaration="Hub.problem",
    )
    assert registered.route_id != transported.route_id
    assert transported.to_dict()["hub_declaration"] == "Hub.problem"


def test_agent_report_records_phase7_policy_without_serializing_the_key() -> None:
    goal = HardnessGoal(
        job_id="sha256:" + "a" * 64,
        input_module="Input.Module",
        source_declaration="Input.Module.source",
        membership_declaration=None,
        target_declaration="Input.Module.target",
        objective="reduce_to",
        toolchain="leanprover/lean4:v4.29.0",
        input_sha256="b" * 64,
        lake_manifest_sha256="c" * 64,
    )
    config = DeepSeekConfig(api_key="deepseek-secret")
    result = AgentResult(
        job_id=goal.job_id,
        status="RECEIVED",
        goal=goal,
        output_dir=".reduction-agent/jobs/example",
        authoring_policy="model-required",
        authoring_attempt_budget=3,
        model_configuration=config.to_public_dict(),
    ).to_dict()
    assert result["execution_policy"]["route"] == "deterministic"
    assert result["execution_policy"]["authoring"] == "model-required"
    assert result["execution_policy"]["model"]["api_key_configured"] is True
    assert "deepseek-secret" not in str(result)


def test_typed_inventory_and_catalog_serialization_separates_facades_from_atoms() -> None:
    atom = TypedInventoryEntry(
        declaration="Edge.ingress",
        capability_kind="certified_reduction",
        component_role="ingress",
        source_fingerprint="lean:source",
        target_fingerprint="lean:hub",
        is_final_facade=False,
        discovery="registered",
        registry_fingerprint="registry-1",
    )
    facade = TypedInventoryEntry(
        declaration="Edge.final",
        capability_kind="certified_reduction",
        component_role="finalComposition",
        source_fingerprint="lean:source",
        target_fingerprint="lean:target",
        is_final_facade=True,
        discovery="registered",
        registry_fingerprint="registry-1",
    )
    catalog = TypedCatalog(
        mode="full", registry_fingerprint="registry-1", entries=(atom, facade)
    )
    serialized = catalog.to_dict()
    assert serialized["catalog_id"].startswith("sha256:")
    assert serialized["agent_interface_count"] == 2
    assert serialized["semantic_atomic_interface_count"] == 1
    assert serialized["role_counts"] == {"finalComposition": 1, "ingress": 1}
    assert serialized["entries"][0]["entry_id"] == atom.entry_id
    assert serialized["entries"][0]["is_semantic_atom"] is True
    assert serialized["entries"][1]["is_semantic_atom"] is False
