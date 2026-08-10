import json
from pathlib import Path

import pytest

from agent.hardness.artifact import (
    CoreGeneralizationArtifactCase,
    build_core_generalization_batch_artifact_source,
)
from agent.hardness.benchmark import load_benchmark_suite
from agent.hardness.core_capability_catalog import (
    NATIVE_COMPLETENESS,
    NATIVE_MEMBERSHIP,
    CoreNativeEvidenceCatalog,
    CoreNativeEvidenceEntry,
    CoreReductionCatalog,
    CoreReductionEntry,
    search_native_evidence,
)
from agent.hardness.core_generalization import (
    CORE_GENERALIZATION_FINISH_ABI,
    CORE_GENERALIZATION_OFFLINE_REPORT_SCHEMA,
    CORE_GENERALIZATION_REPORT_SCHEMA,
    core_generalization_report_skeleton,
    objective_finish_payload,
    validate_core_generalization_suite,
)
from agent.hardness.core_generalization_planner import (
    CoreGeneralizationPlanningSession,
    CoreGeneralizationRequest,
    _connection_reduction_retrieval_gaps,
    _model_stop_explanation,
    audit_core_generalization_prompt,
)
from agent.hardness.connection_catalog import ConnectionCatalog, ConnectionCatalogEntry
from agent.hardness.hardness_target_catalog import (
    HardnessTargetCatalog,
    HardnessTargetCatalogEntry,
    HardnessTargetEvidence,
)
from agent.hardness.input_observation import LeanInputObservation
from agent.hardness.input_planner import STATIC_PATH_DECLARATIONS, InputPlanningError
from agent.hardness.problem_catalog import ProblemCatalog
from agent.hardness.lean_runner import build_problem_catalog_source


ROOT = Path(__file__).resolve().parents[1]


def test_stage_l_suite_freezes_the_full_16_case_matrix() -> None:
    suite = load_benchmark_suite(
        ROOT / "Gate" / "Suites" / "core_generalization.json"
    )
    cases = validate_core_generalization_suite(suite)
    assert len(cases) == 16
    assert sum(case.is_positive for case in cases) == 8
    assert sum(not case.is_positive for case in cases) == 8
    assert sum(case.coverage["comparable_subset"] is True for case in cases) == 8
    assert {case.coverage["objective_class"] for case in cases} == {
        "reduction",
        "membership",
        "completeness",
    }
    assert {case.coverage["route_band"] for case in cases if case.is_positive} >= {
        "0",
        "1",
        "2_3",
        "5_7",
    }


@pytest.mark.parametrize(
    ("objective", "kind", "required", "forbidden"),
    (
        ("reduce_to", "reduction", "lean_term", "membership_lean_term"),
        ("reduce_to_known_np", "reduction", "target_evidence_id", "completeness_lean_term"),
        ("reduce_to_known_hardness", "reduction", "target_entry_id", "membership_evidence_id"),
        ("prove_in_np", "membership", "membership_lean_term", "lean_term"),
        ("prove_np_complete", "completeness", "completeness_lean_term", "membership_lean_term"),
    ),
)
def test_stage_l_finish_payloads_are_objective_specific(
    objective: str, kind: str, required: str, forbidden: str
) -> None:
    payload = objective_finish_payload(objective)
    assert payload["schema_version"] == CORE_GENERALIZATION_FINISH_ABI
    assert payload["payload_kind"] == kind
    assert required in payload["required_fields"]
    assert forbidden in payload["forbidden_fields"]


def test_stage_l_request_rejects_cross_objective_target_policy() -> None:
    with pytest.raises(ValueError, match="forbid target policy"):
        CoreGeneralizationRequest(
            objective="prove_in_np",
            minimum_route_atoms=0,
            maximum_route_atoms=0,
            maximum_dependencies=8,
            allow_reflexive_target=True,
            require_simple_path=True,
            required_hardness="native_np",
            allowed_target_evidence=("native_membership",),
        )


def test_stage_l_report_skeleton_separates_core_and_authoring_costs() -> None:
    offline = core_generalization_report_skeleton(offline=True)
    real = core_generalization_report_skeleton(offline=False)
    assert offline["schema_version"] == CORE_GENERALIZATION_OFFLINE_REPORT_SCHEMA
    assert real["schema_version"] == CORE_GENERALIZATION_REPORT_SCHEMA
    assert offline["execution_layers"]["optional_authoring"] == {
        "attempt_count": 0,
        "candidate_file_count": 0,
        "lean_precheck_count": 0,
    }
    assert set(real["grouped_metrics"]) == {
        "family",
        "input_kind",
        "objective",
        "route_band",
        "outcome_class",
        "comparable_subset",
    }


def test_stage_l_prompt_audit_rejects_expected_route_oracle() -> None:
    with pytest.raises(ValueError, match="benchmark answer fields"):
        audit_core_generalization_prompt(
            {
                "schema_version": "hardness_core_generalization_prompt_v1",
                "expected_target": "Forbidden.target",
            }
        )

    with pytest.raises(ValueError, match="benchmark answer fields"):
        audit_core_generalization_prompt(
            {
                "schema_version": "hardness_core_generalization_prompt_v1",
                "retrieved": {
                    "hardness_targets": [
                        {"shortest_policy_route_atom_count": 3}
                    ]
                },
            }
        )


def test_stage_l_target_prompt_exposes_policy_eligibility_without_route_oracle() -> None:
    fingerprint = "lean:stage-l-unit"
    evidence = HardnessTargetEvidence(
        target_declaration="Example.target",
        target_node_id="lean-whnf:2",
        evidence_kind="transported_native_hardness",
        evidence_declaration="Example.hardness",
        evidence_lean_term="Example.hardness",
        membership_lean_term="",
        satisfied_policies=("native_np_hard",),
        validation_source="unit_test",
        provenance_declarations=("Example.hardness",),
        registry_fingerprint=fingerprint,
    )
    target = HardnessTargetCatalogEntry(
        target_declaration="Example.target",
        target_display="Example.target",
        target_node_id="lean-whnf:2",
        target_namespace="Example",
        registry_fingerprint=fingerprint,
        evidences=(evidence,),
    )
    observation = LeanInputObservation(
        input_module="Example.Input",
        input_declaration="Example.Input.source",
        declaration_kind="def",
        supported=True,
        input_kind="presented_problem",
        elaborated_type="ComplexityReduction.Encoding.PresentedProblem",
        whnf_type="ComplexityReduction.Encoding.PresentedProblem",
        closed=True,
        universe_parameters=(),
        has_metavariables=False,
        presented_problem_compatible=True,
        predicate_domain=None,
        normalized_problem_node_id="lean-whnf:1",
        referenced_constants=(),
        semantic_summary="semantic",
        representation_summary="representation",
        predicate_summary=None,
        accepts_summary="accepts",
        registry_fingerprint=fingerprint,
        failure_code=None,
        explanation=None,
    )
    session = CoreGeneralizationPlanningSession(
        observation=observation,
        target_observation=None,
        problem_catalog=ProblemCatalog(fingerprint, ()),
        connection_catalog=ConnectionCatalog(fingerprint, ()),
        reduction_catalog=CoreReductionCatalog(fingerprint, ()),
        native_evidence_catalog=CoreNativeEvidenceCatalog(fingerprint, ()),
        hardness_target_catalog=HardnessTargetCatalog(fingerprint, (target,)),
        request=CoreGeneralizationRequest(
            objective="reduce_to_known_hardness",
            minimum_route_atoms=1,
            maximum_route_atoms=3,
            maximum_dependencies=4,
            allow_reflexive_target=False,
            require_simple_path=True,
            required_hardness="native_np_hard",
            allowed_target_evidence=("transported_native_hardness",),
        ),
    )
    rendered = session._hardness_target_prompt_result(target)
    assert rendered["request_eligible_evidence_count"] == 1
    assert rendered["evidences"][0]["request_eligible"] is True
    assert "policy_route_allowed" not in json.dumps(rendered)
    assert "shortest_policy_route_atom_count" not in json.dumps(rendered)


def test_stage_l_terminal_stop_may_omit_explanation_only_for_exact_guidance() -> None:
    guidance = {
        "mode": "stop_now",
        "failure_code": "missing_native_membership",
    }
    assert _model_stop_explanation(
        {},
        failure_code="missing_native_membership",
        terminal_guidance=guidance,
    ) == "The model followed the exact Lean-audited terminal blocker."

    with pytest.raises(InputPlanningError, match="non-terminal stop"):
        _model_stop_explanation(
            {},
            failure_code="missing_native_membership",
            terminal_guidance=None,
        )
    with pytest.raises(InputPlanningError, match="non-terminal stop"):
        _model_stop_explanation(
            {},
            failure_code="missing_native_completeness",
            terminal_guidance=guidance,
        )


def test_stage_l_completeness_prompt_requests_target_membership_and_global_hubs() -> None:
    fingerprint = "lean:stage-l-completeness-prompt"
    observation = LeanInputObservation(
        input_module="Example.Input",
        input_declaration="Example.Input.target",
        declaration_kind="def",
        supported=True,
        input_kind="presented_problem",
        elaborated_type="ComplexityReduction.Encoding.PresentedProblem",
        whnf_type="ComplexityReduction.Encoding.PresentedProblem",
        closed=True,
        universe_parameters=(),
        has_metavariables=False,
        presented_problem_compatible=True,
        predicate_domain=None,
        normalized_problem_node_id="lean-whnf:target",
        referenced_constants=(),
        semantic_summary="semantic",
        representation_summary="representation",
        predicate_summary=None,
        accepts_summary="accepts",
        registry_fingerprint=fingerprint,
        failure_code=None,
        explanation=None,
    )
    session = CoreGeneralizationPlanningSession(
        observation=observation,
        target_observation=None,
        problem_catalog=ProblemCatalog(fingerprint, ()),
        connection_catalog=ConnectionCatalog(fingerprint, ()),
        reduction_catalog=CoreReductionCatalog(fingerprint, ()),
        native_evidence_catalog=CoreNativeEvidenceCatalog(fingerprint, ()),
        hardness_target_catalog=HardnessTargetCatalog(fingerprint, ()),
        request=CoreGeneralizationRequest(
            objective="prove_np_complete",
            minimum_route_atoms=0,
            maximum_route_atoms=7,
            maximum_dependencies=8,
            allow_reflexive_target=True,
            require_simple_path=True,
        ),
    )
    searches = session.prompt_payload()["response_options"][
        "search_native_evidence"
    ]["searches"]
    assert searches == [
        {
            "evidence_kinds": [NATIVE_MEMBERSHIP],
            "endpoint_node_ids": ["lean-whnf:target"],
            "limit": 8,
        },
        {"evidence_kinds": [NATIVE_COMPLETENESS], "limit": 8},
    ]


def test_stage_l_accepts_a_valid_nonempty_path_built_by_cons_from_refl() -> None:
    session = CoreGeneralizationPlanningSession.__new__(
        CoreGeneralizationPlanningSession
    )
    term = (
        "ComplexityReduction.Certificate.CertifiedPath.cons "
        "(ComplexityReduction.Certificate.CertifiedPath.cons "
        "(ComplexityReduction.Certificate.CertifiedPath.refl Example.Source) "
        "Example.firstEdge) Example.secondEdge"
    )
    assert session._validate_model_term(
        term=term,
        expected_fragments=("Example.firstEdge", "Example.secondEdge"),
        allowed_declarations=(
            *STATIC_PATH_DECLARATIONS,
            "Example.Source",
            "Example.firstEdge",
            "Example.secondEdge",
        ),
        require_path=True,
        edge_count=2,
    ) == term


def test_stage_l_requires_connection_rows_to_be_retrieved_as_reductions() -> None:
    fingerprint = "lean:stage-l-connection-gap"
    connection = ConnectionCatalogEntry(
        certificate_declaration="Example.edge",
        capability_kind="certified_reduction",
        relation="existing_reduction",
        direction="forward",
        term_kind="certificate",
        projection_declaration="Example.edge",
        lean_term="Example.edge",
        source_fingerprint="lean:source",
        target_fingerprint="lean:target",
        source_node_id="lean-whnf:source",
        target_node_id="lean-whnf:target",
        source_display="source",
        target_display="target",
        component_role="sharedGadget",
        registry_fingerprint=fingerprint,
    )
    reduction = CoreReductionEntry(
        certificate_declaration="Example.edge",
        lean_term="Example.edge",
        capability_kind="certified_reduction",
        component_role="sharedGadget",
        source_declaration="Example.source",
        target_declaration="Example.target",
        source_fingerprint="lean:source",
        target_fingerprint="lean:target",
        source_node_id="lean-whnf:source",
        target_node_id="lean-whnf:target",
        source_display="source",
        target_display="target",
        provenance_declarations=("Example.edge",),
        discovery="unit_test",
        registry_fingerprint=fingerprint,
    )
    gaps = _connection_reduction_retrieval_gaps(
        connections=(connection,),
        reduction_catalog=CoreReductionCatalog(fingerprint, (reduction,)),
        retrieved_reduction_ids=(),
        preferred_source_nodes=("lean-whnf:source",),
    )
    assert gaps == (
        {
            "connection_entry_id": connection.entry_id,
            "source_node_id": "lean-whnf:source",
            "target_node_id": "lean-whnf:target",
            "lean_term": "Example.edge",
            "usable_in_reduction_entry_ids": False,
            "required_search": {
                "action": "search_reductions",
                "searches": [{"terms": ["Example.edge"], "limit": 8}],
            },
        },
    )
    assert not _connection_reduction_retrieval_gaps(
        connections=(connection,),
        reduction_catalog=CoreReductionCatalog(fingerprint, (reduction,)),
        retrieved_reduction_ids=(reduction.entry_id,),
    )
    reduction_shape = objective_finish_payload("reduce_to")["response_shape"]
    assert "retrieved.reductions only" in reduction_shape["reduction_entry_ids"][0]


def test_native_evidence_search_requires_exact_typed_kind_and_endpoint() -> None:
    entry = CoreNativeEvidenceEntry(
        evidence_kind=NATIVE_MEMBERSHIP,
        endpoint_declaration="Example.problem",
        endpoint_node_id="lean-whnf:1",
        evidence_declaration="Example.membership",
        lean_term="Example.membership",
        capability_head="ComplexityReduction.Certificate.NativeTMInNP",
        provenance_declarations=("Example.membership",),
        source_evidence_id="sha256:source",
        validation_source="unit_test",
        registry_fingerprint="lean:unit",
    )
    catalog = CoreNativeEvidenceCatalog(
        registry_fingerprint="lean:unit",
        entries=(entry,),
    )
    assert search_native_evidence(
        catalog,
        evidence_kinds=(NATIVE_MEMBERSHIP,),
        endpoint_node_ids=("lean-whnf:1",),
    ) == (entry,)
    assert not search_native_evidence(
        catalog,
        evidence_kinds=(NATIVE_MEMBERSHIP,),
        endpoint_node_ids=("lean-whnf:2",),
    )


def test_catalog_export_can_share_the_exact_input_module_environment() -> None:
    source = build_problem_catalog_source(
        nonce="stage-l",
        additional_modules=(
            "Benchmark.Hardness.Inputs.CoreGeneralization.Inputs",
        ),
    )
    assert "import Benchmark.Hardness.Inputs.CoreGeneralization.Inputs" in source
    assert '#hardness_export_problem_catalog "stage-l"' in source
    assert "Expected" not in source

    registered = build_problem_catalog_source(
        nonce="stage-l-registered",
        additional_modules=(
            "Benchmark.Hardness.Inputs.CoreGeneralization.Inputs",
        ),
        registered_only=True,
    )
    assert '#hardness_export_registered_problem_catalog "stage-l-registered"' in registered
    assert '#hardness_export_problem_catalog "stage-l-registered"' not in registered


def test_stage_l_artifact_emits_all_objective_kinds_under_one_axiom_gate() -> None:
    source = build_core_generalization_batch_artifact_source(
        (
            CoreGeneralizationArtifactCase(
                case_id="fixed-reduction",
                input_module="Benchmark.Input",
                objective="reduce_to",
                source_declaration="Benchmark.Input.source",
                target_declaration="Benchmark.Input.target",
                proof_term="Example.path",
            ),
            CoreGeneralizationArtifactCase(
                case_id="known-np",
                input_module="Benchmark.Input",
                objective="reduce_to_known_np",
                source_declaration="Benchmark.Input.source",
                target_declaration="Example.npTarget",
                proof_term="Example.npPath",
                target_membership_term="Example.targetMembership",
            ),
            CoreGeneralizationArtifactCase(
                case_id="known-hardness",
                input_module="Benchmark.Input",
                objective="reduce_to_known_hardness",
                source_declaration="Benchmark.Input.source",
                target_declaration="Example.hardTarget",
                proof_term="Example.hardPath",
                target_evidence_kind="transported_native_hardness",
                target_evidence_term="Example.targetHardness",
            ),
            CoreGeneralizationArtifactCase(
                case_id="membership",
                input_module="Benchmark.Input",
                objective="prove_in_np",
                source_declaration="Benchmark.Input.memberProblem",
                proof_term="Example.nativeMembership",
            ),
            CoreGeneralizationArtifactCase(
                case_id="completeness",
                input_module="Benchmark.Input",
                objective="prove_np_complete",
                source_declaration="Benchmark.Input.completeProblem",
                proof_term="Example.nativeCompleteness",
            ),
        )
    )
    assert source.count("assert_standard_axioms") == 1
    assert ".reduceToKnownNP" in source
    assert ".proveInNP" in source
    assert ".proveNPComplete" in source
    assert "NativeTMNPHard Example.hardTarget" in source
    assert "NativeTMInNP Benchmark.Input.memberProblem" in source
    assert "NativeTMNPComplete Benchmark.Input.completeProblem" in source
    assert json.dumps("stage-l") not in source


def test_stage_l_artifact_rejects_cross_objective_fields() -> None:
    with pytest.raises(ValueError, match="exact PresentedProblem"):
        build_core_generalization_batch_artifact_source(
            (
                CoreGeneralizationArtifactCase(
                    case_id="bad-membership",
                    input_module="Benchmark.Input",
                    objective="prove_in_np",
                    source_declaration="Benchmark.Input.source",
                    proof_term="Example.membership",
                    target_declaration="Benchmark.Input.target",
                ),
            )
        )
