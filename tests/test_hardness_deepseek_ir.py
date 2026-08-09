from pathlib import Path

import pytest

from agent.hardness.benchmark import load_benchmark_manifest
from agent.hardness.deepseek_ir import (
    build_batch_artifact_source,
    build_batch_codegen_artifact_source,
    build_batch_probe_source,
    case_namespace,
)
from agent.hardness.models import RouteCandidate


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "Benchmark" / "Hardness" / "MANIFEST.json"


def ir_cases():
    manifest = load_benchmark_manifest(MANIFEST)
    return tuple(case for case in manifest.cases if case.suite_id == "ir-feasibility")


def route_for(case, *atoms: str) -> RouteCandidate:
    return RouteCandidate(
        target_declaration=case.target or "",
        membership_declaration=None,
        atoms=atoms,
        roles=tuple("sharedGadget" for _ in atoms),
        final_composition_edges=0,
        registry_fingerprint="registry-1",
    )


def test_batch_probe_contains_all_flat_and_ir_requests_once() -> None:
    cases = ir_cases()
    nonces = {case.id: f"nonce-{index}" for index, case in enumerate(cases)}

    source = build_batch_probe_source(cases, nonces=nonces)

    assert len(cases) == 12
    assert source.count("#hardness_probe_to_flat") == 6
    assert source.count("#hardness_probe_to_ir") == 6
    assert source.count("import ComplexityReduction.Agent.Hardness.Runtime") == 1
    for case in cases:
        assert f'"{nonces[case.id]}" {case.source} {case.target}' in source


def test_batch_artifact_explicitly_emits_paths_results_and_axiom_gate() -> None:
    cases = ir_cases()[:2]
    selections = (
        (cases[0], route_for(cases[0], "Edge.flat")),
        (cases[1], route_for(cases[1], "Edge.ingress", "Edge.shared")),
    )

    source = build_batch_artifact_source(selections)

    assert "CertifiedPath.step Edge.flat" in source
    assert "CertifiedPath.step Edge.ingress" in source
    assert "CertifiedPath.cons" in source
    assert "Edge.shared" in source
    assert source.count("TypedAutoReductionResult.reduceToPath") == 2
    assert "by_hardness_resolver" not in source
    assert "assert_standard_axioms" in source
    for case in cases:
        namespace = case_namespace(case.id)
        assert f"namespace {namespace}" in source
        assert f"{namespace}.selectedPath" in source
        assert f"{namespace}.result" in source


def test_batch_artifact_rejects_colliding_case_namespaces() -> None:
    first = ir_cases()[0]
    second = first.__class__(**{**first.__dict__, "id": first.id.replace("-", "_")})

    with pytest.raises(ValueError, match="colliding case namespaces"):
        build_batch_artifact_source(
            (
                (first, route_for(first, "Edge.one")),
                (second, route_for(second, "Edge.two")),
            )
        )


def test_codegen_artifact_embeds_model_written_terms_and_one_axiom_gate() -> None:
    cases = ir_cases()[:2]
    source = build_batch_codegen_artifact_source(
        (
            (
                cases[0],
                "ComplexityReduction.Certificate.CertifiedPath.step Edge.flat",
            ),
            (
                cases[1],
                "ComplexityReduction.Certificate.CertifiedPath.cons\n"
                "  (ComplexityReduction.Certificate.CertifiedPath.step Edge.ingress)\n"
                "  Edge.shared",
            ),
        )
    )

    assert "CertifiedPath.step Edge.flat" in source
    assert "CertifiedPath.step Edge.ingress" in source
    assert "Edge.shared" in source
    assert source.count("assert_standard_axioms") == 1
    assert source.count("TypedAutoReductionResult.reduceToPath") == 2
    assert "by_hardness_resolver" not in source
