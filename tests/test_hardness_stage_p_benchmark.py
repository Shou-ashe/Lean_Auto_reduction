from __future__ import annotations

from pathlib import Path

from agent.hardness.benchmark import load_benchmark_suite
from agent.hardness.models import sha256_id
from agent.hardness.stage_p_benchmark import (
    build_stage_p_offline_aggregate_source,
    run_stage_p_offline_canonical,
    stage_p_offline_summary,
)
from agent.hardness.stage_p_contract import validate_stage_p_suites


ROOT = Path(__file__).resolve().parents[1]


def canonical_cases():
    positive = load_benchmark_suite(
        ROOT / "Gate/Suites/stage_p_open_world.json"
    )
    negative = load_benchmark_suite(
        ROOT / "Gate/Suites/stage_p_adversarial.json"
    )
    return validate_stage_p_suites(positive, negative)


def test_offline_canonical_is_24_of_24_with_dynamic_gap_and_publication_chain(
    tmp_path: Path,
) -> None:
    outcomes = run_stage_p_offline_canonical(
        canonical_cases(),
        output_root=tmp_path / "run",
        run_id="stage-p-offline-test",
        toolchain="leanprover/lean4:test",
        lake_manifest_sha256=sha256_id("lake-manifest"),
        input_source_sha256=sha256_id("stage-p-input"),
    )
    summary = stage_p_offline_summary(outcomes)
    assert summary["canonical_case_count"] == 24
    assert summary["protocol_expected_count"] == 24
    assert summary["positive_expected_count"] == 12
    assert summary["negative_expected_count"] == 12
    assert summary["simulated_model_case_count"] == 11
    assert summary["model_generated_case_count"] == 0
    assert summary["full_reduction_bundle_authored_count"] == 3
    assert summary["consumer_zero_authoring"]
    assert summary["all_model_bodies_required"]
    assert outcomes[6].row["gap_count"] == 4
    assert outcomes[6].row["fresh_core_resolve_count"] == 4
    assert outcomes[10].row["publications"][-1]["publication_role"] == "producer"
    assert outcomes[11].row["wave_barrier_satisfied"]
    assert all(outcome.row["protocol_matches_expected"] for outcome in outcomes)


def test_offline_aggregate_contains_every_authored_body_and_axiom_gate(
    tmp_path: Path,
) -> None:
    outcomes = run_stage_p_offline_canonical(
        canonical_cases(),
        output_root=tmp_path / "run",
        run_id="stage-p-offline-aggregate-test",
        toolchain="leanprover/lean4:test",
        lake_manifest_sha256=sha256_id("lake-manifest"),
        input_source_sha256=sha256_id("stage-p-input"),
    )
    source = build_stage_p_offline_aggregate_source(outcomes)
    declaration_count = sum(len(outcome.candidate_declarations) for outcome in outcomes)
    assert source.count("def capability") == declaration_count
    assert source.count("import Benchmark.Hardness.Inputs.StageP.ContractProbes") == 1
    assert "assert_standard_axioms" in source
    assert ".Gold." not in source
