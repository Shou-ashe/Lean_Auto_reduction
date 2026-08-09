import json
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.benchmark import load_benchmark_suite
from agent.hardness.certificate_dag import (
    CertificateDAGValidationError,
    build_certificate_dag,
    complete_certificate_dag,
    validate_certificate_dag,
)
from agent.hardness.finite_witness import (
    finite_witness_registry,
    precise_finite_witness_blocker,
)
from agent.hardness.models import ExactAuthoringTemplateCandidate, ProbeResult
from agent.hardness.runner import _authoring_prompt_diagnostics
from agent.hardness.typed_authoring import (
    TYPED_AUTHORING_SYSTEM_PROMPT,
    TypedAuthoringArtifactCase,
    TypedAuthoringRequest,
    build_packet_selection_prompt,
    build_typed_authoring_batch_artifact_source,
    parse_packet_selection,
    typed_authoring_task_id,
    validate_typed_authoring_suite,
)
from agent.hardness.typed_authoring_simulation import SimulatedTypedAuthoringClient
from agent.hardness.typed_packets import (
    PacketValidationError,
    adversarial_packet,
    build_packet_index,
    candidate_bundle_integrity,
    compile_packet_selection,
    validate_packet,
)
from scripts.typed_authoring_benchmark import merge_candidate_work_roots


ROOT = Path(__file__).resolve().parents[1]
SUITE = ROOT / "Benchmark" / "Hardness" / "Suites" / "typed_authoring.json"
SOURCE = "Benchmark.Hardness.Inputs.TypedAuthoring.SingleEdgeProgram.source"
TARGET = "Benchmark.Hardness.Inputs.TypedAuthoring.SingleEdgeProgram.target"


def test_stage_m_suite_freezes_eight_cases_and_five_positive_capabilities() -> None:
    suite = load_benchmark_suite(SUITE)
    validate_typed_authoring_suite(suite.cases)
    assert len(suite.cases) == 8
    assert sum(case.is_positive for case in suite.cases) == 5
    assert {case.expected.baseline_failure_code for case in suite.cases} >= {
        "missing_lawful_presentation",
        "missing_semantic_proof",
        "missing_reduction_capability",
        "missing_verifier_program",
        "missing_checker_combinator:pair_list",
        "missing_direct_tm",
        "missing_checker_combinator:unsupported_local_checker",
    }


def test_typed_authoring_request_is_public_and_separate_from_coverage() -> None:
    case = load_benchmark_suite(SUITE).cases[0]
    request = TypedAuthoringRequest.from_case(case).to_dict()
    assert "coverage" not in request
    assert "expected" not in request
    assert "final_status" not in request
    assert request["active_node"] == "presentation_capability"


def reduction_dag():
    return build_certificate_dag(
        source_declaration=SOURCE,
        target_declaration=TARGET,
        objective="reduce_to",
        active_node="reduction_capability",
        candidate_source_hash="sha256:" + "1" * 64,
    )


def _replace_active(dag, **changes):
    active = replace(dag.node(dag.active_node), **changes)
    nodes = tuple(
        active
        if node.kind == dag.active_node
        else (
            replace(node, preconditions=(active.node_id,))
            if node.kind == "final_request"
            else node
        )
        for node in dag.nodes
    )
    return replace(dag, nodes=nodes)


@pytest.mark.parametrize(
    ("changes", "code"),
    [
        ({"output_type": SOURCE}, "endpoint_mismatch"),
        ({"direction": "identity"}, "wrong_direction"),
        ({"capability_head": "ComplexityReduction.Certificate.NativeTMInNP"}, "wrong_capability_head"),
        ({"preconditions": ("sha256:" + "0" * 64,)}, "unmet_precondition"),
    ],
)
def test_certificate_dag_rejects_endpoint_direction_head_and_precondition_before_model(
    changes, code
) -> None:
    with pytest.raises(CertificateDAGValidationError) as captured:
        validate_certificate_dag(_replace_active(reduction_dag(), **changes))
    assert captured.value.code == code


def probe_with_program_packet() -> ProbeResult:
    candidate = ExactAuthoringTemplateCandidate(
        template_kind="program_indexed_reduction",
        provider_declaration=(
            "Benchmark.Hardness.Inputs.TypedAuthoring.SingleEdgeProgram.template"
        ),
        role="sharedGadget",
        source_declaration=SOURCE,
        target_declaration=TARGET,
        registry_fingerprint="lean:test",
        component_declarations=(
            "Benchmark.Hardness.Inputs.TypedAuthoring.SingleEdgeProgram.executable",
            "Benchmark.Hardness.Inputs.TypedAuthoring.SingleEdgeProgram.executableDirectTM",
            "Benchmark.Hardness.Inputs.TypedAuthoring.SingleEdgeProgram.executableCorrect",
        ),
    )
    return ProbeResult(
        nonce="nonce",
        source_declaration=SOURCE,
        source_display=SOURCE,
        registry_fingerprint="lean:test",
        targets=(),
        routes=(),
        authoring_templates=(candidate,),
    )


def test_packet_index_compiler_binds_one_lean_confirmed_candidate() -> None:
    dag = reduction_dag()
    index = build_packet_index(
        root=ROOT,
        dag=dag,
        probe=probe_with_program_packet(),
        allowed_packet_kinds=("tm_certificate_packet",),
        required_combinators=(),
    )
    assert len(index.packets) == 1
    compiled = compile_packet_selection(
        dag=dag, index=index, packet_id=index.packets[0].packet_id
    )
    assert compiled.candidate_id == probe_with_program_packet().authoring_templates[0].candidate_id
    assert "program_indexed_reduction_shell" in compiled.compiler_insertions


@pytest.mark.parametrize(
    "mutation",
    [
        "endpoint_mismatch",
        "wrong_direction",
        "oracle_import_forbidden",
        "nonstandard_axiom_forbidden",
    ],
)
def test_adversarial_packet_mutations_are_rejected_before_candidate_write(mutation: str) -> None:
    dag = reduction_dag()
    index = build_packet_index(
        root=ROOT,
        dag=dag,
        probe=probe_with_program_packet(),
        allowed_packet_kinds=("tm_certificate_packet",),
        required_combinators=(),
    )
    with pytest.raises(PacketValidationError) as captured:
        validate_packet(adversarial_packet(index.packets[0], mutation), dag=dag)
    assert captured.value.code == mutation


def test_packet_selection_prompt_and_response_fix_task_and_candidate() -> None:
    request = TypedAuthoringRequest(
        source_declaration=SOURCE,
        target_declaration=TARGET,
        objective="reduce_to",
        active_node="reduction_capability",
        expected_capability_head="ComplexityReduction.Certificate.CertifiedReduction",
        allowed_packet_kinds=("tm_certificate_packet",),
        required_checker_combinators=(),
        witness_shape="none",
        model_selection_required=True,
        attempt_budget=1,
        authoring_mode="deterministic-template",
    )
    dag = reduction_dag()
    index = build_packet_index(
        root=ROOT,
        dag=dag,
        probe=probe_with_program_packet(),
        allowed_packet_kinds=request.allowed_packet_kinds,
        required_combinators=(),
    )
    task_id = typed_authoring_task_id(
        request=request,
        gap_id="sha256:" + "a" * 64,
        dag=dag,
        index=index,
    )
    prompt = build_packet_selection_prompt(
        task_id=task_id,
        request=request,
        gap={
            "gap_id": "sha256:" + "a" * 64,
            "failure_code": "missing_reduction_capability",
            "role": "sharedGadget",
            "source_declaration": SOURCE,
            "target_declaration": TARGET,
            "expected_capability_head": (
                "ComplexityReduction.Certificate.CertifiedReduction"
            ),
            "registry_fingerprint": "lean:test",
        },
        dag=dag,
        index=index,
    )
    prompt_payload = json.loads(prompt)
    assert SOURCE not in prompt
    assert TARGET not in prompt
    assert "SingleEdgeProgram.template" not in prompt
    assert "SingleEdgeProgram.executable" not in prompt
    assert "source_declaration" not in prompt
    assert "target_declaration" not in prompt
    assert "provider_declaration" not in prompt
    assert "component_declarations" not in prompt
    assert prompt_payload["request"]["expected_capability_kind"] == "certified_reduction"
    assert prompt_payload["packet_index"]["packets"][0]["candidate_id"] == (
        index.packets[0].candidate_id
    )
    response = SimulatedTypedAuthoringClient().complete_json(
        system=TYPED_AUTHORING_SYSTEM_PROMPT,
        prompt=prompt,
    )
    selection = parse_packet_selection(response.content, task_id=task_id, index=index)
    assert selection.packet_id == index.packets[0].packet_id
    bad = json.loads(response.content)
    bad["bindings"]["candidate_id"] = "sha256:" + "0" * 64
    with pytest.raises(PacketValidationError):
        parse_packet_selection(json.dumps(bad), task_id=task_id, index=index)


def test_finite_witness_registry_has_required_shapes_and_precise_blockers() -> None:
    names = {row["name"] for row in finite_witness_registry()["combinators"]}
    assert {
        "list_nat",
        "pair_list",
        "path_legality",
        "disjointness",
        "nat_budget",
        "deletion_coloring",
    } <= names
    assert precise_finite_witness_blocker(required=("unknown_checker",)) == (
        "missing_checker_combinator:unknown_checker"
    )
    assert precise_finite_witness_blocker(required=(), witness_bound=False) == (
        "missing_witness_bound"
    )
    assert precise_finite_witness_blocker(required=(), soundness=False) == (
        "missing_soundness_lemma"
    )


def test_completed_dag_records_candidate_hash_and_verified_final_request() -> None:
    completed = complete_certificate_dag(
        reduction_dag(), candidate_source_hash="sha256:" + "f" * 64
    )
    assert completed.node("reduction_capability").verification_status == "verified"
    assert completed.node("final_request").verification_status == "verified"
    assert completed.node("final_request").preconditions == (
        completed.node("reduction_capability").node_id,
    )


def test_completed_presentation_dag_rewrites_all_downstream_dependencies() -> None:
    dag = build_certificate_dag(
        source_declaration=SOURCE,
        target_declaration=TARGET,
        objective="reduce_to",
        active_node="presentation_capability",
        candidate_source_hash="sha256:" + "1" * 64,
    )
    completed = complete_certificate_dag(
        dag, candidate_source_hash="sha256:" + "f" * 64
    )
    presentation_id = completed.node("presentation_capability").node_id
    assert presentation_id in completed.node("reduction_capability").preconditions
    assert presentation_id in completed.node("membership_capability").preconditions
    assert completed.node("final_request").preconditions == (presentation_id,)


def test_candidate_deletion_or_hash_change_invalidates_bundle(tmp_path: Path) -> None:
    candidate = tmp_path / "Candidate.lean"
    candidate.write_text("def x := 1\n", encoding="utf-8")
    digest = __import__("hashlib").sha256(candidate.read_bytes()).hexdigest()
    assert candidate_bundle_integrity((candidate,), (digest,))
    candidate.write_text("def x := 2\n", encoding="utf-8")
    assert not candidate_bundle_integrity((candidate,), (digest,))
    candidate.unlink()
    assert not candidate_bundle_integrity((candidate,), (digest,))


def test_batch_artifact_has_one_final_request_per_positive_case() -> None:
    cases = (
        TypedAuthoringArtifactCase(
            case_id="a",
            input_module="Benchmark.Hardness.Inputs.TypedAuthoring.SingleEdgeProgram",
            objective="reduce_to",
            source_declaration=SOURCE,
            target_declaration=TARGET,
            route_atoms=("Some.route",),
            candidate_modules=("Some.Module",),
        ),
        TypedAuthoringArtifactCase(
            case_id="b",
            input_module="Benchmark.Hardness.Inputs.TypedAuthoring.BoundedSubsetMembership",
            objective="prove_in_np",
            source_declaration=(
                "Benchmark.Hardness.Inputs.TypedAuthoring.BoundedSubsetMembership.source"
            ),
            target_declaration=(
                "Benchmark.Hardness.Inputs.TypedAuthoring.BoundedSubsetMembership.source"
            ),
            membership_declaration="Some.membership",
            candidate_modules=("Some.Membership",),
        ),
    )
    source = build_typed_authoring_batch_artifact_source(cases)
    assert source.count("TypedAutoReductionResult") >= 2
    assert "reduceToPath" in source
    assert "proveInNP" in source
    assert "assert_standard_axioms" in source


def test_candidate_work_roots_merge_without_generated_namespace_shadowing(
    tmp_path: Path,
) -> None:
    first = tmp_path / "first"
    second = tmp_path / "second"
    first_module = first / "Generated" / "Hardness" / "Jfirst" / "Capability.olean"
    second_module = second / "Generated" / "Hardness" / "Jsecond" / "Capability.olean"
    first_module.parent.mkdir(parents=True)
    second_module.parent.mkdir(parents=True)
    first_module.write_bytes(b"first")
    second_module.write_bytes(b"second")

    manifest = merge_candidate_work_roots(
        (first, second), destination=tmp_path / "combined"
    )

    assert manifest["work_root_count"] == 2
    assert manifest["copied_file_count"] == 2
    assert (tmp_path / "combined" / first_module.relative_to(first)).read_bytes() == b"first"
    assert (tmp_path / "combined" / second_module.relative_to(second)).read_bytes() == b"second"


def test_candidate_work_root_merge_rejects_conflicting_module_artifacts(
    tmp_path: Path,
) -> None:
    first = tmp_path / "first"
    second = tmp_path / "second"
    relative = Path("Generated/Hardness/Jshared/Capability.olean")
    (first / relative).parent.mkdir(parents=True)
    (second / relative).parent.mkdir(parents=True)
    (first / relative).write_bytes(b"first")
    (second / relative).write_bytes(b"second")

    with pytest.raises(ValueError, match="conflicting generated module artifact"):
        merge_candidate_work_roots(
            (first, second), destination=tmp_path / "combined"
        )


def test_transient_model_failure_does_not_replace_last_lean_diagnostics() -> None:
    lean_error = "Candidate.lean:17:4: unknown identifier 'source'"
    assert _authoring_prompt_diagnostics(
        last_lean_diagnostics=lean_error,
        diagnostics=[lean_error, "empty assistant content (finish_reason=length)"],
    ) == lean_error
