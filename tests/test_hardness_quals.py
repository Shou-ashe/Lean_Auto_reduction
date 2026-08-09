import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from agent.hardness.benchmark import load_benchmark_suite
from agent.hardness.quals import (
    N_C_ADVERSARIAL_IDS,
    N_C_FORMALIZATION_IDS,
    N_C_PRIMARY_IDS,
    build_quals_batch_artifact_source,
    build_quals_formalization_gate_source,
    load_quals_formalization_suite,
    quals_report_skeleton,
    validate_quals_adversarial_suite,
    validate_quals_completeness_suite,
)
from agent.hardness.typed_authoring import TypedAuthoringArtifactCase, TypedAuthoringRequest
from scripts.quals_benchmark import run_adversarial_case, run_full_suite


ROOT = Path(__file__).resolve().parents[1]
FORMALIZATION = ROOT / "Benchmark" / "Hardness" / "Suites" / "quals_formalization.json"
COMPLETENESS = ROOT / "Benchmark" / "Hardness" / "Suites" / "quals_completeness.json"
ADVERSARIAL = ROOT / "Benchmark" / "Hardness" / "Suites" / "quals_adversarial.json"


def test_n_c_contract_freezes_five_formalizations_primaries_and_seven_adversarials() -> None:
    formalization = load_quals_formalization_suite(FORMALIZATION)
    completeness = load_benchmark_suite(COMPLETENESS)
    adversarial = load_benchmark_suite(ADVERSARIAL)
    validate_quals_completeness_suite(completeness.cases)
    validate_quals_adversarial_suite(adversarial.cases)

    assert tuple(case.id for case in formalization.cases) == N_C_FORMALIZATION_IDS
    assert tuple(case.id for case in completeness.cases) == N_C_PRIMARY_IDS
    assert tuple(case.id for case in adversarial.cases) == N_C_ADVERSARIAL_IDS
    assert sum(case.is_positive for case in completeness.cases) == 5
    assert sum(not case.is_positive for case in adversarial.cases) == 7


def test_formalization_gate_is_exact_axiom_checked_and_non_scoring() -> None:
    suite = load_quals_formalization_suite(FORMALIZATION)
    source = build_quals_formalization_gate_source(suite.cases)
    for case in suite.cases:
        assert case.problem_declaration in source
        assert case.production_endpoint in source
        assert case.representation_declaration in source
        assert case.semantic_theorem in source
        assert case.validation["oracle_visible_to_model"] is False
        assert case.validation["gold_route_visible_to_model"] is False
        assert json.loads(case.validation_record.read_text())["public_module_sha256"] == (
            __import__("hashlib").sha256(case.public_module_file.read_bytes()).hexdigest()
        )
    assert "assert_standard_axioms" in source
    assert "NativeTMNPComplete" not in source


def test_primary_request_exposes_only_typed_membership_authoring_data() -> None:
    case = load_benchmark_suite(COMPLETENESS).cases[0]
    request = TypedAuthoringRequest.from_case(case).to_dict()

    assert case.objective == "prove_np_complete"
    assert case.evaluation_lane == "quals_completeness"
    assert request["active_node"] == "membership_capability"
    assert request["expected_capability_head"] == (
        "ComplexityReduction.Certificate.NativeTMInNP"
    )
    assert request["allowed_packet_kinds"] == ("membership_packet",)
    assert "coverage" not in request
    assert "formalization_case_id" not in request
    assert "expected" not in request


def test_n_c_primary_requests_activate_exactly_one_capability_each() -> None:
    cases = load_benchmark_suite(COMPLETENESS).cases
    requests = {case.id: TypedAuthoringRequest.from_case(case) for case in cases}

    seeing = requests["uiuc2022-seeing-set"]
    assert seeing.active_node == "reduction_capability"
    assert seeing.allowed_packet_kinds == ("tm_certificate_packet",)
    assert seeing.witness_shape == "none"

    deletion = requests["fall2016-node-deletion-bipartite"]
    assert deletion.active_node == "membership_capability"
    assert deletion.allowed_packet_kinds == ("membership_packet",)
    assert deletion.witness_shape == "deletion_coloring"
    assert "deletion_coloring" in deletion.required_checker_combinators

    most_neighbors = requests["fall2014-most-neighbors"]
    assert most_neighbors.active_node == "membership_capability"
    assert most_neighbors.allowed_packet_kinds == ("membership_packet",)
    assert most_neighbors.witness_shape == "list_nat"
    assert "external_neighborhood" in most_neighbors.required_checker_combinators

    two_paths = requests["uiuc2020-two-disjoint-bounded-paths"]
    assert two_paths.active_node == "membership_capability"
    assert two_paths.allowed_packet_kinds == ("membership_packet",)
    assert two_paths.witness_shape == "pair_list"
    assert {
        "edge_index_path",
        "binary_path_cost",
        "disjointness",
    }.issubset(two_paths.required_checker_combinators)


def test_adversarial_contract_is_core_only_and_pre_model() -> None:
    cases = load_benchmark_suite(ADVERSARIAL).cases
    assert [case.coverage["negative_class"] for case in cases] == [
        "missing_membership",
        "reversed_reduction",
        "wrong_endpoint",
        "missing_reduction",
        "missing_membership",
        "missing_membership",
        "missing_membership",
    ]
    assert all(case.execution_layer == "core_reuse" for case in cases)
    assert all(case.verification_profile == "core" for case in cases)
    assert all(not case.requires_authoring for case in cases)
    assert all(case.coverage["forbid_model_call"] is True for case in cases)


def test_adversarial_runner_checks_the_real_model_call_collection(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    case = load_benchmark_suite(ADVERSARIAL).cases[0]
    gap = SimpleNamespace(
        reason=case.coverage["required_gap_reason"],
        to_dict=lambda: {"reason": case.coverage["required_gap_reason"]},
    )
    result = SimpleNamespace(
        status=case.expected.final_status,
        failures=(SimpleNamespace(code=case.expected.final_failure_code),),
        gap=gap,
        probe=SimpleNamespace(authoring_templates=()),
        model_calls=[],
        authoring_attempts=[],
        commands=[],
    )

    class FakeHardnessAgent:
        def __init__(self, _config: object) -> None:
            pass

        def run(self) -> object:
            return result

    monkeypatch.setattr("scripts.quals_benchmark.HardnessAgent", FakeHardnessAgent)
    outcome = run_adversarial_case(index=2, case=case, output_root=tmp_path)

    assert outcome.row["protocol_matches_expected"] is True
    assert outcome.row["pre_model_blocked"] is True
    assert outcome.row["model_call_count"] == 0


def test_quals_final_artifact_constructs_exact_native_completeness() -> None:
    source = build_quals_batch_artifact_source(
        (
            TypedAuthoringArtifactCase(
                case_id="spring2015-exactly-one-neighbor",
                input_module=(
                    "Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighbor"
                ),
                objective="prove_np_complete",
                source_declaration=(
                    "Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighbor.problem"
                ),
                target_declaration=(
                    "Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighbor.problem"
                ),
                route_atoms=("Some.forwardReduction",),
                membership_declaration="Some.nativeMembership",
                hub_declaration="Some.completeHub",
                completeness_declaration="Some.nativeCompleteness",
                candidate_modules=("Some.GeneratedMembership",),
            ),
            TypedAuthoringArtifactCase(
                case_id="uiuc2022-seeing-set",
                input_module="Benchmark.Hardness.Inputs.Quals.UIUC2022SeeingSet",
                objective="reduce_to",
                source_declaration="Some.SetCovering",
                target_declaration="Some.SeeingSet",
                route_atoms=("Some.generatedSeeingSetReduction",),
                candidate_modules=("Some.GeneratedReduction",),
            ),
        )
    )
    assert "Benchmark.Hardness.Quals.Final" in source
    assert "CompletenessTransport.alongPath" in source
    assert ".proveNPComplete" in source
    assert ".reduceTo" in source
    assert "NativeTMNPComplete" in source
    assert "assert_standard_axioms" in source
    assert "by_hardness_resolver" not in source


def test_wrong_endpoint_fixture_shares_codec_but_not_semantics() -> None:
    path = (
        ROOT
        / "Lean"
        / "Reference"
        / "Benchmark"
        / "Hardness"
        / "Inputs"
        / "Quals"
        / "Spring2015ExactlyOneNeighborWrongEndpoint.lean"
    )
    source = path.read_text(encoding="utf-8")
    assert "import Benchmark.Hardness.Inputs.Quals.Spring2015ExactlyOneNeighbor" in source
    assert "isYes := fun _ => False" in source
    assert "problem.representation" in source
    assert "native_membership_template" not in source


def test_n_c_capability_negative_modules_omit_the_positive_templates() -> None:
    quals = ROOT / "Lean" / "Reference" / "Benchmark" / "Hardness" / "Inputs" / "Quals"
    seeing_negative = (quals / "UIUC2022SeeingSetMissingReduction.lean").read_text()
    deletion_negative = (
        quals / "Fall2016NodeDeletionBipartiteMissingMembership.lean"
    ).read_text()
    most_neighbors_negative = (
        quals / "Fall2014MostNeighborsMissingMembership.lean"
    ).read_text()
    two_paths_negative = (
        quals / "UIUC2020TwoDisjointBoundedPathsMissingMembership.lean"
    ).read_text()

    assert "Domain.SetCoveringToSeeingSet" not in seeing_negative
    assert "program_reduction_template" not in seeing_negative
    assert "Domain.NodeDeletionBipartiteMembership" not in deletion_negative
    assert "native_membership_template" not in deletion_negative
    assert "Domain.MostNeighborsMembership" not in most_neighbors_negative
    assert "native_membership_template" not in most_neighbors_negative
    assert "Domain.TwoDisjointBoundedPathsMembership" not in two_paths_negative
    assert "native_membership_template" not in two_paths_negative


def test_quals_report_skeleton_separates_formalization_core_authoring_and_audit(
    tmp_path: Path,
) -> None:
    report = quals_report_skeleton(
        formalization_suite_file=FORMALIZATION,
        completeness_suite_file=COMPLETENESS,
        adversarial_suite_file=ADVERSARIAL,
        output_root=tmp_path,
    )
    assert report["formalization"] == {}
    assert report["milestone"] == "N-C"
    assert report["cases"] == []
    assert report["process_counts"] == {
        "formalization": 0,
        "setup_build": 0,
        "core_baseline": 0,
        "authoring_local": 0,
        "final_combined_lean": 0,
        "release_replay": 0,
    }


@pytest.mark.parametrize("jobs", [0, 5])
def test_quals_runner_rejects_parallelism_outside_one_to_four(
    tmp_path: Path, jobs: int
) -> None:
    with pytest.raises(ValueError, match="between 1 and 4"):
        run_full_suite(
            formalization_suite_file=FORMALIZATION,
            completeness_suite_file=COMPLETENESS,
            adversarial_suite_file=ADVERSARIAL,
            output_root=tmp_path / f"jobs-{jobs}",
            jobs=jobs,
            real=False,
            deepseek_config=None,
            canonical_report=None,
            lean_timeout_seconds=1800,
            run_label="test",
        )
