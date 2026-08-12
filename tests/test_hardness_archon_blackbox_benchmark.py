from __future__ import annotations

from pathlib import Path

from agent.hardness.archon_blackbox_benchmark import (
    _verification_source,
    load_archon_benchmark_cases,
)


ROOT = Path(__file__).resolve().parents[1]


def test_blackbox_loader_matches_frozen_registry() -> None:
    cases = load_archon_benchmark_cases(root=ROOT)
    assert len(cases) == 78
    assert sum(case.kind == "capability" for case in cases) == 32
    assert sum(case.kind == "frontier" for case in cases) == 2
    assert sum(case.kind == "exact_edge" for case in cases) == 24
    assert sum(case.kind == "boolean_csp" for case in cases) == 20
    assert len({case.case_id for case in cases}) == 78


def test_blackbox_public_input_has_no_benchmark_solution_fields() -> None:
    case = load_archon_benchmark_cases(
        root=ROOT,
        selected_case_ids=("cdev-er-01-three-sat-seed",),
    )[0]
    public = case.public_input()
    serialized = repr(public).lower()
    assert set(public) == {
        "case_id",
        "kind",
        "split",
        "statement",
        "requirement",
        "formal_goal",
    }
    for forbidden in (
        "recommended",
        "oracle",
        "gold",
        "typed_dag",
        "diagnostic",
        "route",
        "dependency_body",
    ):
        assert forbidden not in serialized


def test_verifier_adds_axiom_gate_only_after_archon() -> None:
    case = load_archon_benchmark_cases(
        root=ROOT,
        selected_case_ids=("cdev-er-01-three-sat-seed",),
    )[0]
    namespace, source = _verification_source(case, "by\n  exact Classical.choice inferInstance")
    assert namespace.endswith("cdever01threesatseed")
    assert "import ComplexityReduction.AxiomGate" in source
    assert f"assert_standard_axioms {namespace}.result" in source
    assert "sorry" not in source
