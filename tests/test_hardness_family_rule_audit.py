from pathlib import Path

from agent.hardness.family_rule_audit import audit_python_family_specific_rules


def cases() -> tuple[dict, ...]:
    return (
        {
            "id": "input-graph-direct-flat-api",
            "module": "Benchmark.Hardness.Inputs.InputGrounding.Graph",
            "source": "Benchmark.Hardness.Inputs.InputGrounding.Graph.direct",
            "target": "Benchmark.Hardness.Inputs.InputGrounding.Graph.target",
            "comparison_group_id": "input-graph-direct",
            "matched_pair_id": "input-graph-direct",
            "coverage": {
                "study_family": "graph",
                "logical_source": "graph",
            },
        },
    )


def test_family_rule_audit_separates_routing_rules_from_benchmark_contracts(
    tmp_path: Path,
) -> None:
    routing = tmp_path / "routing.py"
    routing.write_text(
        "def choose(family):\n"
        "    if family == 'graph':\n"
        "        return 'special route'\n",
        encoding="utf-8",
    )
    validation = tmp_path / "validation.py"
    validation.write_text(
        "EXPECTED_CASES = {'input-graph-direct'}\n",
        encoding="utf-8",
    )

    audit = audit_python_family_specific_rules(
        cases(),
        routing_source_paths=(routing,),
        benchmark_validation_paths=(validation,),
        display_root=tmp_path,
    )

    assert audit["python_family_specific_rule_count"] == 1
    assert audit["benchmark_contract_marker_count"] == 1
    assert audit["families"][0]["routing_evidence"][0]["path"] == "routing.py"
    assert audit["families"][0]["benchmark_contract_evidence"][0][
        "path"
    ] == "validation.py"


def test_family_rule_audit_reports_zero_for_generic_routing(tmp_path: Path) -> None:
    routing = tmp_path / "routing.py"
    routing.write_text(
        "def choose(entries):\n"
        "    return sorted(entries, key=lambda entry: entry.declaration)\n",
        encoding="utf-8",
    )

    audit = audit_python_family_specific_rules(
        cases(), routing_source_paths=(routing,), display_root=tmp_path
    )

    assert audit["python_family_specific_rule_count"] == 0
    assert audit["families"][0]["routing_evidence"] == []
