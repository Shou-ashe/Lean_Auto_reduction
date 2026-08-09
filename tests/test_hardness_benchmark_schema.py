import json
from pathlib import Path

import pytest

from agent.hardness.benchmark import (
    BenchmarkManifestError,
    load_benchmark_manifest,
    load_benchmark_suite,
    select_benchmark_cases,
)


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "Benchmark" / "Hardness" / "MANIFEST.json"
INPUT_GROUNDING_SUITE = (
    ROOT / "Benchmark" / "Hardness" / "Suites" / "input_grounding_fixed_target.json"
)


def test_v2_manifest_and_suites_load_strictly() -> None:
    manifest = load_benchmark_manifest(MANIFEST)
    assert manifest.schema_version == "hardness_benchmark_v2"
    assert manifest.migration_ledger_file == (
        ROOT / "Benchmark" / "Hardness" / "MIGRATION_LEDGER.json"
    ).resolve()
    assert {suite.id for suite in manifest.suites} == {
        "smoke",
        "routes",
        "ir-feasibility",
        "cook-levin",
        "gaps",
        "authoring",
        "phase5-authoring",
        "model-authoring",
        "membership",
        "typed-authoring",
        "completeness",
        "negative",
        "security",
        "quals-completeness",
        "quals-adversarial",
    }
    assert len(manifest.cases) == 65
    assert len({case.id for case in manifest.cases}) == len(manifest.cases)
    assert all(case.input_kind == "presented_problem" for case in manifest.cases)
    assert all(case.effective_input_declaration == case.source for case in manifest.cases)


def test_input_grounding_suite_loads_strictly_without_entering_main_manifest() -> None:
    suite = load_benchmark_suite(INPUT_GROUNDING_SUITE)
    assert suite.id == "input-grounding-fixed-target"
    assert len(suite.cases) == 24
    assert sum(case.is_positive for case in suite.cases) == 18
    assert sum(not case.is_positive for case in suite.cases) == 6
    assert all(case.input_declaration == case.source for case in suite.cases)
    assert all(case.family_id is None for case in suite.cases)
    assert all(case.source_form_id is None for case in suite.cases)
    assert all(case.matched_pair_id is None for case in suite.cases)
    manifest = load_benchmark_manifest(MANIFEST)
    assert suite.id not in {item.id for item in manifest.suites}


def test_phase_gate_and_disabled_case_are_reported_separately() -> None:
    manifest = load_benchmark_manifest(MANIFEST)
    quals_phase_gate_ids = [
        "spring2015-exactly-one-neighbor",
        "uiuc2022-seeing-set",
        "fall2016-node-deletion-bipartite",
        "fall2014-most-neighbors",
        "uiuc2020-two-disjoint-bounded-paths",
        "spring2015-exactly-one-neighbor-missing-membership",
        "spring2015-exactly-one-neighbor-reversed-reduction",
        "spring2015-exactly-one-neighbor-wrong-endpoint",
        "uiuc2022-seeing-set-missing-reduction",
        "fall2016-node-deletion-bipartite-missing-membership",
        "fall2014-most-neighbors-missing-membership",
        "uiuc2020-two-disjoint-bounded-paths-missing-membership",
    ]
    selection = select_benchmark_cases(manifest, agent_phase=1)
    assert len(selection.runnable) == 20
    assert [(item.case.id, item.code) for item in selection.skipped] == [
        ("knapsack-native-cook-levin", "phase_gate"),
        ("knapsack-native-cook-levin-clique", "phase_gate"),
        ("missing-verifier-discipline", "phase_gate"),
        ("representation-mismatch-gap", "phase_gate"),
        ("missing-primitive-gap", "phase_gate"),
        ("missing-native-membership-gap", "phase_gate"),
        ("closed-family-template-authoring", "phase_gate"),
        ("closed-family-candidate-absent", "phase_gate"),
        ("lawful-presentation-template-authoring", "phase_gate"),
        ("lawful-presentation-candidate-absent", "phase_gate"),
        ("primitive-admission-template-authoring", "phase_gate"),
        ("primitive-admission-candidate-absent", "phase_gate"),
        ("program-indexed-reduction-authoring", "phase_gate"),
        ("program-indexed-candidate-absent", "phase_gate"),
        ("missing-direct-tm-authoring-blocker", "phase_gate"),
        ("program-indexed-retry-isolation", "phase_gate"),
        ("model-semantic-proof-authoring", "phase_gate"),
        ("exact-registered-native-membership", "phase_gate"),
        ("backend-only-prove-in-np-blocker", "phase_gate"),
        ("native-membership-deterministic-authoring", "phase_gate"),
        ("authoring-lawful-presentation", "phase_gate"),
        ("authoring-semantic-proof", "phase_gate"),
        ("authoring-single-edge-program", "phase_gate"),
        ("authoring-bounded-subset-membership", "phase_gate"),
        ("authoring-pair-list-membership", "phase_gate"),
        ("authoring-missing-direct-tm", "phase_gate"),
        ("authoring-unsupported-checker", "phase_gate"),
        ("authoring-wrong-endpoint-or-axiom", "phase_gate"),
        ("exact-registered-three-sat-completeness", "phase_gate"),
        ("three-sat-to-clique-transported-completeness", "phase_gate"),
        ("completeness-target-missing-membership", "phase_gate"),
        ("completeness-wrong-direction", "phase_gate"),
        ("backend-completeness-cannot-pass-native-gate", "phase_gate"),
    ] + [(case_id, "phase_gate") for case_id in quals_phase_gate_ids]
    phase_two = select_benchmark_cases(manifest, agent_phase=2)
    assert len(phase_two.runnable) == 23
    assert [item.case.id for item in phase_two.skipped] == [
        "representation-mismatch-gap",
        "missing-primitive-gap",
        "missing-native-membership-gap",
        "closed-family-template-authoring",
        "closed-family-candidate-absent",
        "lawful-presentation-template-authoring",
        "lawful-presentation-candidate-absent",
        "primitive-admission-template-authoring",
        "primitive-admission-candidate-absent",
        "program-indexed-reduction-authoring",
        "program-indexed-candidate-absent",
        "missing-direct-tm-authoring-blocker",
        "program-indexed-retry-isolation",
        "model-semantic-proof-authoring",
        "exact-registered-native-membership",
        "backend-only-prove-in-np-blocker",
        "native-membership-deterministic-authoring",
        "authoring-lawful-presentation",
        "authoring-semantic-proof",
        "authoring-single-edge-program",
        "authoring-bounded-subset-membership",
        "authoring-pair-list-membership",
        "authoring-missing-direct-tm",
        "authoring-unsupported-checker",
        "authoring-wrong-endpoint-or-axiom",
        "exact-registered-three-sat-completeness",
        "three-sat-to-clique-transported-completeness",
        "completeness-target-missing-membership",
        "completeness-wrong-direction",
        "backend-completeness-cannot-pass-native-gate",
    ] + quals_phase_gate_ids
    phase_three = select_benchmark_cases(manifest, agent_phase=3)
    assert len(phase_three.runnable) == 26
    assert [item.case.id for item in phase_three.skipped] == [
        "closed-family-template-authoring",
        "closed-family-candidate-absent",
        "lawful-presentation-template-authoring",
        "lawful-presentation-candidate-absent",
        "primitive-admission-template-authoring",
        "primitive-admission-candidate-absent",
        "program-indexed-reduction-authoring",
        "program-indexed-candidate-absent",
        "missing-direct-tm-authoring-blocker",
        "program-indexed-retry-isolation",
        "model-semantic-proof-authoring",
        "exact-registered-native-membership",
        "backend-only-prove-in-np-blocker",
        "native-membership-deterministic-authoring",
        "authoring-lawful-presentation",
        "authoring-semantic-proof",
        "authoring-single-edge-program",
        "authoring-bounded-subset-membership",
        "authoring-pair-list-membership",
        "authoring-missing-direct-tm",
        "authoring-unsupported-checker",
        "authoring-wrong-endpoint-or-axiom",
        "exact-registered-three-sat-completeness",
        "three-sat-to-clique-transported-completeness",
        "completeness-target-missing-membership",
        "completeness-wrong-direction",
        "backend-completeness-cannot-pass-native-gate",
    ] + quals_phase_gate_ids
    phase_four = select_benchmark_cases(manifest, agent_phase=4)
    assert len(phase_four.runnable) == 32
    assert [item.case.id for item in phase_four.skipped] == [
        "program-indexed-reduction-authoring",
        "program-indexed-candidate-absent",
        "missing-direct-tm-authoring-blocker",
        "program-indexed-retry-isolation",
        "model-semantic-proof-authoring",
        "exact-registered-native-membership",
        "backend-only-prove-in-np-blocker",
        "native-membership-deterministic-authoring",
        "authoring-lawful-presentation",
        "authoring-semantic-proof",
        "authoring-single-edge-program",
        "authoring-bounded-subset-membership",
        "authoring-pair-list-membership",
        "authoring-missing-direct-tm",
        "authoring-unsupported-checker",
        "authoring-wrong-endpoint-or-axiom",
        "exact-registered-three-sat-completeness",
        "three-sat-to-clique-transported-completeness",
        "completeness-target-missing-membership",
        "completeness-wrong-direction",
        "backend-completeness-cannot-pass-native-gate",
    ] + quals_phase_gate_ids
    phase_five = select_benchmark_cases(manifest, agent_phase=5)
    assert len(phase_five.runnable) == 36
    assert [item.case.id for item in phase_five.skipped] == [
        "model-semantic-proof-authoring",
        "exact-registered-native-membership",
        "backend-only-prove-in-np-blocker",
        "native-membership-deterministic-authoring",
        "authoring-lawful-presentation",
        "authoring-semantic-proof",
        "authoring-single-edge-program",
        "authoring-bounded-subset-membership",
        "authoring-pair-list-membership",
        "authoring-missing-direct-tm",
        "authoring-unsupported-checker",
        "authoring-wrong-endpoint-or-axiom",
        "exact-registered-three-sat-completeness",
        "three-sat-to-clique-transported-completeness",
        "completeness-target-missing-membership",
        "completeness-wrong-direction",
        "backend-completeness-cannot-pass-native-gate",
    ] + quals_phase_gate_ids
    phase_six = select_benchmark_cases(manifest, agent_phase=6)
    assert len(phase_six.runnable) == 44
    assert [item.case.id for item in phase_six.skipped] == [
        "model-semantic-proof-authoring",
        "authoring-lawful-presentation",
        "authoring-semantic-proof",
        "authoring-single-edge-program",
        "authoring-bounded-subset-membership",
        "authoring-pair-list-membership",
        "authoring-missing-direct-tm",
        "authoring-unsupported-checker",
        "authoring-wrong-endpoint-or-axiom",
    ] + quals_phase_gate_ids
    phase_seven = select_benchmark_cases(manifest, agent_phase=7)
    assert len(phase_seven.runnable) == 45
    assert [item.case.id for item in phase_seven.skipped] == [
        "authoring-lawful-presentation",
        "authoring-semantic-proof",
        "authoring-single-edge-program",
        "authoring-bounded-subset-membership",
        "authoring-pair-list-membership",
        "authoring-missing-direct-tm",
        "authoring-unsupported-checker",
        "authoring-wrong-endpoint-or-axiom",
    ] + quals_phase_gate_ids
    phase_thirteen = select_benchmark_cases(manifest, agent_phase=13)
    assert len(phase_thirteen.runnable) == 53
    assert [item.case.id for item in phase_thirteen.skipped] == quals_phase_gate_ids
    phase_fourteen = select_benchmark_cases(manifest, agent_phase=14)
    assert len(phase_fourteen.runnable) == 65
    assert phase_fourteen.skipped == ()


def test_resume_audit_selects_its_verified_authoring_prerequisite() -> None:
    manifest = load_benchmark_manifest(MANIFEST)
    selection = select_benchmark_cases(
        manifest,
        case_ids=["closed-family-candidate-absent"],
        agent_phase=4,
    )
    assert [case.id for case in selection.runnable] == [
        "closed-family-template-authoring",
        "closed-family-candidate-absent",
    ]
    absent = selection.runnable[-1]
    assert absent.resume_from_case == "closed-family-template-authoring"
    assert absent.remove_candidate_before_resume


def test_selecting_one_ir_case_expands_to_the_complete_matched_pair() -> None:
    manifest = load_benchmark_manifest(MANIFEST)
    selection = select_benchmark_cases(
        manifest, case_ids=["graph-to-role-graph-flat"], agent_phase=1
    )
    assert [case.id for case in selection.runnable] == [
        "graph-to-role-graph-flat",
        "graph-to-role-graph-ir",
    ]


def test_ir_feasibility_suite_has_three_real_families_and_six_matched_pairs() -> None:
    manifest = load_benchmark_manifest(MANIFEST)
    cases = [case for case in manifest.cases if case.suite_id == "ir-feasibility"]

    assert len(cases) == 12
    assert {case.family_id for case in cases} == {
        "graph-role-graph",
        "clause-csp",
        "incidence-eon",
    }
    assert len({case.matched_pair_id for case in cases}) == 6
    assert all(case.authoring_policy == {"enabled": False, "mode": "disabled"} for case in cases)


def test_selecting_new_incidence_case_expands_only_its_matched_peer() -> None:
    manifest = load_benchmark_manifest(MANIFEST)
    selection = select_benchmark_cases(
        manifest, case_ids=["modified-exact-cover-to-eon-ir"], agent_phase=1
    )

    assert [case.id for case in selection.runnable] == [
        "modified-exact-cover-to-eon-flat",
        "modified-exact-cover-to-eon-ir",
    ]


def test_fixed_targets_use_canonical_validated_declaration_handles() -> None:
    manifest = load_benchmark_manifest(MANIFEST)
    cases = {case.id: case for case in manifest.cases}
    assert cases["three-sat-explicit-suffix"].target == (
        "ComplexityReduction.Problems.Karp21.GraphAtoms.cliqueStructuredProblem"
    )
    assert cases["tagged-three-sat-normalization"].target == (
        "ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem"
    )
    assert cases["graph-coloring-route"].target == (
        "ComplexityReduction.Presentation.CliqueCover.structuredProblem"
    )
    assert cases["knapsack-native-cook-levin"].target == (
        "ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem"
    )
    assert cases["knapsack-native-cook-levin-clique"].target == (
        "ComplexityReduction.Problems.Karp21.GraphAtoms.cliqueStructuredProblem"
    )


def test_unknown_case_fails_closed() -> None:
    manifest = load_benchmark_manifest(MANIFEST)
    with pytest.raises(BenchmarkManifestError) as error:
        select_benchmark_cases(manifest, case_ids=["does-not-exist"])
    assert error.value.code == "unknown_case"


def test_duplicate_case_id_is_rejected(tmp_path: Path) -> None:
    repository = tmp_path / "repo"
    hardness = repository / "Benchmark" / "Hardness"
    suites = hardness / "Suites"
    input_file = (
        repository
        / "Lean"
        / "Reference"
        / "Benchmark"
        / "Hardness"
        / "Inputs"
        / "Smoke"
        / "Example.lean"
    )
    suites.mkdir(parents=True)
    input_file.parent.mkdir(parents=True)
    input_file.write_text("namespace Benchmark.Hardness.Inputs.Smoke.Example\nend Benchmark.Hardness.Inputs.Smoke.Example\n")
    case = {
        "id": "duplicate",
        "module": "Benchmark.Hardness.Inputs.Smoke.Example",
        "source": "Benchmark.Hardness.Inputs.Smoke.Example.source",
        "objective": "reduce_to_known_np",
        "target_policy": "open",
        "planner": "deterministic",
        "min_agent_phase": 1,
        "expected": {"final_status": "VERIFIED"},
        "tags": ["test"],
    }
    (suites / "one.json").write_text(
        json.dumps(
            {
                "schema_version": "hardness_benchmark_suite_v1",
                "suite_id": "one",
                "description": "one",
                "cases": [case],
            }
        )
    )
    (suites / "two.json").write_text(
        json.dumps(
            {
                "schema_version": "hardness_benchmark_suite_v1",
                "suite_id": "two",
                "description": "two",
                "cases": [case],
            }
        )
    )
    manifest = hardness / "MANIFEST.json"
    manifest.write_text(
        json.dumps(
            {
                "schema_version": "hardness_benchmark_v2",
                "benchmark_id": "duplicate-test",
                "suites": ["Suites/one.json", "Suites/two.json"],
            }
        )
    )
    with pytest.raises(BenchmarkManifestError) as error:
        load_benchmark_manifest(manifest)
    assert error.value.code == "duplicate_case_id"


def _write_ir_pair_manifest(
    tmp_path: Path, *, resource_mismatch: bool = False, omit_ir: bool = False
) -> Path:
    repository = tmp_path / "ir-repo"
    hardness = repository / "Benchmark" / "Hardness"
    suites = hardness / "Suites"
    input_file = (
        repository
        / "Lean"
        / "Reference"
        / "Benchmark"
        / "Hardness"
        / "Inputs"
        / "IRFeasibility"
        / "Example.lean"
    )
    suites.mkdir(parents=True)
    input_file.parent.mkdir(parents=True)
    input_file.write_text(
        "namespace Benchmark.Hardness.Inputs.IRFeasibility.Example\n"
        "end Benchmark.Hardness.Inputs.IRFeasibility.Example\n"
    )
    common = {
        "module": "Benchmark.Hardness.Inputs.IRFeasibility.Example",
        "source": "Benchmark.Hardness.Inputs.IRFeasibility.Example.source",
        "target": "Benchmark.Hardness.Inputs.IRFeasibility.Example.target",
        "objective": "reduce_to",
        "objective_direction": "source_to_target",
        "target_policy": "fixed",
        "planner": "deterministic",
        "execution_layer": "core_reuse",
        "verification_profile": "core",
        "evaluation_lane": "ir_feasibility",
        "matched_pair_id": "example-pair",
        "family_id": "example-family",
        "source_form_id": "source-form",
        "target_form_id": "target-form",
        "hub_ids": ["example-hub"],
        "authoring_policy": {"enabled": False, "mode": "disabled"},
        "expected": {"final_status": "VERIFIED"},
        "resources": {"lean_timeout_seconds": 30},
        "tags": ["test"],
    }
    flat = {
        **common,
        "id": "example-flat",
        "catalog_mode": "flat_api",
        "coverage": {
            "forbid_model_call": True,
            "required_resolution_class": "direct_or_final_facade",
        },
    }
    ir = {
        **common,
        "id": "example-ir",
        "catalog_mode": "ir_components",
        "coverage": {"forbid_model_call": True, "forbid_final_facade": True},
    }
    if resource_mismatch:
        ir["resources"] = {"lean_timeout_seconds": 31}
    (suites / "ir.json").write_text(
        json.dumps(
            {
                "schema_version": "hardness_benchmark_suite_v1",
                "suite_id": "ir-test",
                "description": "matched pair",
                "cases": [flat] if omit_ir else [flat, ir],
            }
        )
    )
    manifest = hardness / "MANIFEST.json"
    manifest.write_text(
        json.dumps(
            {
                "schema_version": "hardness_benchmark_v2",
                "benchmark_id": "ir-test",
                "suites": ["Suites/ir.json"],
            }
        )
    )
    return manifest


def test_ir_matched_pair_requires_equal_resource_controls(tmp_path: Path) -> None:
    manifest = _write_ir_pair_manifest(tmp_path, resource_mismatch=True)
    with pytest.raises(BenchmarkManifestError) as error:
        load_benchmark_manifest(manifest)
    assert error.value.code == "ir_matched_pair_mismatch"


def test_ir_matched_pair_requires_both_catalog_modes(tmp_path: Path) -> None:
    manifest = _write_ir_pair_manifest(tmp_path, omit_ir=True)
    with pytest.raises(BenchmarkManifestError) as error:
        load_benchmark_manifest(manifest)
    assert error.value.code == "invalid_ir_matched_pair"
