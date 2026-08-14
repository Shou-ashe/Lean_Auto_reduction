from __future__ import annotations

from pathlib import Path

import pytest

from agent.reduction.theorem_index import (
    build_probe_source,
    parse_probe_output,
    project_module_catalog,
)


ROOT = Path(__file__).resolve().parents[1]


def test_project_catalog_discovers_public_schaefer_theorem_without_benchmark_imports() -> None:
    modules = project_module_catalog(ROOT)
    assert "ComplexityReduction.Domain.BooleanCSP.Hardness.SchaeferHardness" in modules
    assert not any(module.startswith("Benchmark.") for module in modules)
    assert not any("Oracle" in module or ".Legacy." in module for module in modules)


def test_probe_source_uses_exact_input_but_no_suite_metadata() -> None:
    source = build_probe_source(
        input_module="Example.Input",
        problem_declaration="Example.Input.problem",
        modules=("Example.Rules",),
        nonce="abc123",
    )
    assert "#reduction_probe_np_hard_theorems \"abc123\" Example.Input.problem" in source
    for forbidden in ("case_id", "split", "oracle", "expected_public_status"):
        assert forbidden not in source.lower()


def test_parser_accepts_only_nonce_bound_typed_rows() -> None:
    output = "\n".join(
        (
            "REDUCTION_THEOREM_INDEX\treduction_theorem_index_v1\tnonce\tgoal\t"
            "Example.Input.problem\tNativeTMNPHard Example.Input.problem\t1\t1",
            "REDUCTION_THEOREM_INDEX\treduction_theorem_index_v1\tnonce\tcandidate\t"
            "Example.Rules.hard\tExample.Rules\t1\tP → NativeTMNPHard target\tP\t"
            "NativeTMNPHard Example.Input.problem\t2",
        )
    )
    candidates = parse_probe_output(stdout=output, stderr="", nonce="nonce")
    assert len(candidates) == 1
    assert candidates[0].declaration == "Example.Rules.hard"
    assert candidates[0].premises == ("P",)

    with pytest.raises(ValueError, match="no goal row"):
        parse_probe_output(stdout=output, stderr="", nonce="another")
