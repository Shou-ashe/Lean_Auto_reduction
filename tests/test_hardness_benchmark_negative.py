from pathlib import Path

from agent.hardness.benchmark import load_benchmark_manifest


ROOT = Path(__file__).resolve().parents[1]


def test_current_negative_cases_have_exact_expected_failure_codes() -> None:
    manifest = load_benchmark_manifest(ROOT / "Gate" / "MANIFEST.json")
    cases = {case.id: case for case in manifest.cases}
    assert cases["no-route"].expected.final_failure_code == "no_registry_path"
    assert (
        cases["wrong-membership-endpoint"].expected.final_failure_code
        == "input_declaration_rejected"
    )
    assert (
        cases["backend-only-membership"].expected.final_failure_code
        == "input_declaration_rejected"
    )
    assert cases["wrong-membership-endpoint"].membership is not None
    assert cases["backend-only-membership"].membership is not None
    assert (
        cases["representation-mismatch-gap"].expected.final_failure_code
        == "missing_lawful_presentation"
    )
    assert cases["missing-primitive-gap"].expected.final_failure_code == "missing_primitive"
    assert (
        cases["missing-native-membership-gap"].expected.final_failure_code
        == "missing_native_membership"
    )
