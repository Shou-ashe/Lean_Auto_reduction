import json
from pathlib import Path

import pytest

from agent.hardness.benchmark import BenchmarkManifestError, load_benchmark_manifest


def test_active_case_cannot_reference_oracle_module(tmp_path: Path) -> None:
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
        / "Oracles"
        / "Leak.lean"
    )
    suites.mkdir(parents=True)
    input_file.parent.mkdir(parents=True)
    input_file.write_text("namespace Benchmark.Hardness.Inputs.Oracles.Leak\nend Benchmark.Hardness.Inputs.Oracles.Leak\n")
    (suites / "security.json").write_text(
        json.dumps(
            {
                "schema_version": "hardness_benchmark_suite_v1",
                "suite_id": "security",
                "description": "oracle rejection",
                "cases": [
                    {
                        "id": "leak",
                        "module": "Benchmark.Hardness.Inputs.Oracles.Leak",
                        "source": "Benchmark.Hardness.Inputs.Oracles.Leak.source",
                        "objective": "reduce_to_known_np",
                        "target_policy": "open",
                        "planner": "deterministic",
                        "expected": {"final_status": "VERIFIED"},
                        "tags": ["security"],
                    }
                ],
            }
        )
    )
    manifest = hardness / "MANIFEST.json"
    manifest.write_text(
        json.dumps(
            {
                "schema_version": "hardness_benchmark_v2",
                "benchmark_id": "oracle-test",
                "suites": ["Suites/security.json"],
            }
        )
    )
    with pytest.raises(BenchmarkManifestError) as error:
        load_benchmark_manifest(manifest)
    assert error.value.code == "oracle_reference_forbidden"


def test_active_suite_files_do_not_reference_legacy_oracles() -> None:
    root = Path(__file__).resolve().parents[1]
    for suite in sorted(
        list((root / "Benchmark" / "Hardness" / "Suites").glob("*.json"))
        + list((root / "Gate" / "Suites").glob("*.json"))
    ):
        text = suite.read_text()
        assert "HiddenTargets" not in text
        assert "GoldProofs" not in text
        assert ".Legacy." not in text


def test_public_lean_inputs_are_oracle_free_and_sorry_free() -> None:
    root = Path(__file__).resolve().parents[1]
    inputs = root / "Lean" / "Reference" / "Benchmark" / "Hardness"
    for source in inputs.rglob("*.lean"):
        text = source.read_text()
        assert "Benchmark.Hardness.Legacy" not in text
        assert "HiddenTargets" not in text
        assert "GoldProofs" not in text
        for forbidden in ("sorry", "admit", "sorryAx", "axiom"):
            assert forbidden not in text.split()
