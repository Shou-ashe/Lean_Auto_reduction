import json
from pathlib import Path

import pytest

from agent.hardness.np_hard_input import (
    NPHardInputError,
    build_np_hard_input_certificate_source,
    resolve_np_hard_input_reference,
)


ROOT = Path(__file__).resolve().parents[1]


@pytest.mark.parametrize(
    ("module", "term", "kind"),
    [
        (
            "ComplexityReduction.Certificate.NativeCookLevin",
            "canonical-three-sat-exact",
            "exact",
        ),
        (
            "Benchmark.Hardness.Inputs.Completeness.RegisteredThreeSAT",
            "canonical-three-sat",
            "alias",
        ),
        (
            "Benchmark.Hardness.Inputs.NPHardGeneralization.InputNormalization",
            "canonical-three-sat-wrapper",
            "wrapper",
        ),
    ],
)
def test_registered_inputs_resolve_deterministically(module: str, term: str, kind: str) -> None:
    reference = resolve_np_hard_input_reference(
        root=ROOT, input_module=module, requested_term=term
    )
    assert reference.normalization_kind == kind
    assert reference.canonical_problem == (
        "ComplexityReduction.Certificate.NativeCookLevin.canonicalThreeSAT"
    )
    source = build_np_hard_input_certificate_source(reference=reference, nonce="nonce")
    assert "#hardness_inspect_input" in source
    assert f"{reference.requested_declaration} = {reference.canonical_problem}" in source


def test_unknown_stable_id_and_module_substitution_fail_closed() -> None:
    with pytest.raises(NPHardInputError) as unknown:
        resolve_np_hard_input_reference(
            root=ROOT,
            input_module="Example.Module",
            requested_term="unregistered-problem-id",
        )
    assert unknown.value.code == "input_problem_not_found"
    with pytest.raises(NPHardInputError) as substituted:
        resolve_np_hard_input_reference(
            root=ROOT,
            input_module="Example.Other",
            requested_term="canonical-three-sat",
        )
    assert substituted.value.code == "input_problem_not_found"


def test_bare_encoding_registry_entry_uses_lean_discovered_unique_presentation() -> None:
    reference = resolve_np_hard_input_reference(
        root=ROOT,
        input_module="Benchmark.Hardness.Inputs.NPHardGeneralization.InputNormalization",
        requested_term="canonical-three-sat-bare-encoding",
    )
    assert reference.supported is True
    assert reference.normalization_kind == "encoding"
    assert reference.problem_declaration == (
        "ComplexityReduction.Certificate.NativeCookLevin.canonicalThreeSAT"
    )
    source = build_np_hard_input_certificate_source(reference=reference, nonce="nonce")
    assert "#hardness_inspect_input" in source
    assert (
        "bareThreeSATEncoding = "
        "ComplexityReduction.Certificate.NativeCookLevin.canonicalThreeSAT.representation"
    ) in source


def test_formal_g_e_report_satisfies_exit_conditions() -> None:
    report = json.loads(
        (ROOT / "Reports/NP_HARD_ENTRYPOINT_REPORT.json").read_text(
            encoding="utf-8"
        )
    )
    metrics = report["metrics"]
    assert report["passed"] is True
    assert metrics["normalization_case_count"] == 3
    assert metrics["normalization_verified_count"] == 3
    assert metrics["existing_route_count"] == 5
    assert metrics["existing_route_verified_count"] == 5
    assert metrics["existing_route_model_calls"] == 0
    assert metrics["missing_lawful_presentation_count"] == 1
    assert metrics["authoring_after_deterministic_blocker_count"] == 1
    assert {row["kind"] for row in report["normalization_cases"]} == {
        "exact", "alias", "wrapper"
    }
    assert all(
        row["identity"]["normalization_certificate"] == "lean-checked-artifact"
        for row in report["normalization_cases"]
    )
