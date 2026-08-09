import pytest

from agent.hardness.artifact import (
    CertifiedPathArtifactCase,
    OpenTargetArtifactCase,
    build_certified_path_batch_artifact_source,
    build_open_target_batch_artifact_source,
    case_namespace,
)


def test_generic_batch_artifact_uses_real_inputs_and_one_axiom_gate() -> None:
    source = build_certified_path_batch_artifact_source(
        (
            CertifiedPathArtifactCase(
                case_id="direct-graph",
                input_module="Benchmark.Input.Graph",
                source_declaration="Benchmark.Input.Graph.source",
                target_declaration="Benchmark.Input.Graph.target",
                lean_term=(
                    "ComplexityReduction.Certificate.CertifiedPath.step "
                    "ComplexityReduction.Routes.Graph.route"
                ),
            ),
            CertifiedPathArtifactCase(
                case_id="wrapped-clause",
                input_module="Benchmark.Input.Clause",
                source_declaration="Benchmark.Input.Clause.wrapped",
                target_declaration="Benchmark.Input.Clause.target",
                lean_term=(
                    "ComplexityReduction.Certificate.CertifiedPath.step "
                    "ComplexityReduction.Routes.Clause.route"
                ),
            ),
        )
    )
    assert "CertifiedPath Benchmark.Input.Graph.source" in source
    assert "CertifiedPath Benchmark.Input.Clause.wrapped" in source
    assert source.count("assert_standard_axioms") == 1
    assert source.count("selectedPath") >= 6


def test_generic_batch_artifact_rejects_namespace_collisions() -> None:
    with pytest.raises(ValueError, match="colliding"):
        build_certified_path_batch_artifact_source(
            (
                CertifiedPathArtifactCase(
                    case_id="same-case",
                    input_module="Benchmark.Input",
                    source_declaration="Benchmark.Input.source",
                    target_declaration="Benchmark.Input.target",
                    lean_term="Term.one",
                ),
                CertifiedPathArtifactCase(
                    case_id="same_case",
                    input_module="Benchmark.Input",
                    source_declaration="Benchmark.Input.source",
                    target_declaration="Benchmark.Input.target",
                    lean_term="Term.two",
                ),
            )
        )


def test_case_namespace_remains_compatible_with_old_benchmark_entrypoint() -> None:
    assert case_namespace("three-sat-to-csp") == "CaseThreeSatToCsp"


def test_open_target_artifact_checks_path_membership_and_result_together() -> None:
    source = build_open_target_batch_artifact_source(
        (
            OpenTargetArtifactCase(
                case_id="membership-target",
                input_module="Benchmark.Input.Clause",
                source_declaration="Benchmark.Input.Clause.source",
                target_declaration="ComplexityReduction.Targets.clique",
                lean_term="ComplexityReduction.Certificate.CertifiedPath.refl",
                required_hardness="native_np",
                target_evidence_kind="native_membership",
                target_evidence_lean_term="ComplexityReduction.Evidence.cliqueNativeNP",
            ),
        )
    )
    assert ".reduceToKnownNP" in source
    assert "def targetMembership" in source
    assert "reduceToKnownNPPath" in source
    assert source.count("assert_standard_axioms") == 1
    assert "targetMembership" in source.split("assert_standard_axioms", 1)[1]


def test_open_target_artifact_projects_membership_from_selected_completeness() -> None:
    source = build_open_target_batch_artifact_source(
        (
            OpenTargetArtifactCase(
                case_id="complete-target",
                input_module="Benchmark.Input.Clause",
                source_declaration="Benchmark.Input.Clause.source",
                target_declaration="ComplexityReduction.Targets.threeSAT",
                lean_term="ComplexityReduction.Certificate.CertifiedPath.refl",
                required_hardness="native_np_complete",
                target_evidence_kind="native_completeness",
                target_evidence_lean_term="ComplexityReduction.Evidence.threeSATComplete",
            ),
        )
    )
    assert "def targetCompleteness" in source
    assert "NativeTMNPComplete.nativeMembership" in source
    audit = source.split("assert_standard_axioms", 1)[1]
    assert "targetCompleteness" in audit
    assert "targetMembership" in audit
    assert "selectedPath" in audit
    assert ".result" in audit


def test_open_target_artifact_audits_predicate_grounding_at_existing_source() -> None:
    source = build_open_target_batch_artifact_source(
        (
            OpenTargetArtifactCase(
                case_id="predicate-source",
                input_module="Benchmark.Input.Predicate",
                source_declaration="ComplexityReduction.Problems.CNF.problem",
                predicate_declaration="Benchmark.Input.Predicate.accepts",
                target_declaration="ComplexityReduction.Targets.threeSAT",
                lean_term="ComplexityReduction.Certificate.CertifiedPath.refl",
                required_hardness="native_np",
                target_evidence_kind="native_membership",
                target_evidence_lean_term="ComplexityReduction.Evidence.threeSATNativeNP",
            ),
        )
    )

    assert "Benchmark.Input.Predicate.accepts input" in source
    assert "ComplexityReduction.Problems.CNF.problem.accepts input" in source
    assert "CertifiedPath ComplexityReduction.Problems.CNF.problem" in source
    audit = source.split("assert_standard_axioms", 1)[1]
    assert "inputPredicateGrounding" in audit


@pytest.mark.parametrize(
    "evidence_kind",
    (
        "native_completeness_projection",
        "transported_native_completeness",
        "registered_native_membership",
        "registered_native_completeness",
    ),
)
def test_open_target_artifact_rejects_schema_compatible_unemittable_evidence(
    evidence_kind: str,
) -> None:
    with pytest.raises(ValueError, match="unsupported target evidence kind"):
        build_open_target_batch_artifact_source(
            (
                OpenTargetArtifactCase(
                    case_id="unemittable-target",
                    input_module="Benchmark.Input.Clause",
                    source_declaration="Benchmark.Input.Clause.source",
                    target_declaration="ComplexityReduction.Targets.dynamic",
                    lean_term="ComplexityReduction.Certificate.CertifiedPath.refl",
                    required_hardness="native_np",
                    target_evidence_kind=evidence_kind,
                    target_evidence_lean_term="ComplexityReduction.Evidence.dynamic",
                ),
            )
        )


def test_open_target_artifact_emits_transported_hardness_for_known_hardness() -> None:
    source = build_open_target_batch_artifact_source(
        (
            OpenTargetArtifactCase(
                case_id="transported-hardness-target",
                input_module="Benchmark.Input.Clause",
                source_declaration="Benchmark.Input.Clause.source",
                target_declaration="ComplexityReduction.Targets.dynamic",
                lean_term="ComplexityReduction.Certificate.CertifiedPath.refl",
                required_hardness="native_np_hard",
                target_evidence_kind="transported_native_hardness",
                target_evidence_lean_term="ComplexityReduction.Evidence.dynamicHardness",
            ),
        )
    )

    assert ".reduceTo " in source
    assert "def targetHardness" in source
    assert "NativeTMNPHard" in source
    assert "reduceToPath" in source
    audit = source.split("assert_standard_axioms", 1)[1]
    assert "targetHardness" in audit


def test_open_target_artifact_rejects_transported_hardness_for_known_np() -> None:
    with pytest.raises(ValueError, match="unsupported target evidence kind"):
        build_open_target_batch_artifact_source(
            (
                OpenTargetArtifactCase(
                    case_id="hardness-only-known-np",
                    input_module="Benchmark.Input.Clause",
                    source_declaration="Benchmark.Input.Clause.source",
                    target_declaration="ComplexityReduction.Targets.dynamic",
                    lean_term="ComplexityReduction.Certificate.CertifiedPath.refl",
                    required_hardness="native_np",
                    target_evidence_kind="transported_native_hardness",
                    target_evidence_lean_term="ComplexityReduction.Evidence.dynamicHardness",
                ),
            )
        )
