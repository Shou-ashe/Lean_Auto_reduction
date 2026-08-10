from __future__ import annotations

from pathlib import Path

from agent.hardness.stage_p_contract import load_and_validate_stage_p_mutations
from agent.hardness.stage_p_mutations import OPERATIONS, run_stage_p_mutation_suite


ROOT = Path(__file__).resolve().parents[1]


def test_all_frozen_mutation_operators_are_implemented() -> None:
    rows = load_and_validate_stage_p_mutations(
        ROOT / "Gate/Suites/stage_p_mutations.json"
    )
    assert {row["mutation_operator"] for row in rows} == set(OPERATIONS)


def test_stage_p_mutation_suite_is_72_of_72(tmp_path: Path) -> None:
    rows = load_and_validate_stage_p_mutations(
        ROOT / "Gate/Suites/stage_p_mutations.json"
    )
    results = run_stage_p_mutation_suite(rows, workspace_root=tmp_path / "mutations")
    failures = [result.to_dict() for result in results if not result.passed]
    assert len(results) == 72
    assert not failures
