import json
from pathlib import Path

import pytest

from agent.hardness.benchmark import BenchmarkManifestError, load_benchmark_manifest


ROOT = Path(__file__).resolve().parents[1]
BENCHMARK = ROOT / "Benchmark"
HARDNESS = BENCHMARK / "Hardness"


def test_original_legacy_benchmark_paths_are_removed_from_active_root() -> None:
    for relative in (
        "MANIFEST.yaml",
        "Samples",
        "HiddenTargets",
        "GoldProofs",
        "V2Hardness",
    ):
        assert not (BENCHMARK / relative).exists()
    assert (HARDNESS / "Legacy" / "Opencode" / "MANIFEST.yaml").is_file()
    assert (HARDNESS / "Legacy" / "V2Hardness" / "MANIFEST.json").is_file()


def test_current_manifest_never_loads_legacy_files() -> None:
    manifest = json.loads((HARDNESS / "MANIFEST.json").read_text())
    assert all("Legacy" not in suite for suite in manifest["suites"])


def test_old_v2_schema_is_explicitly_rejected() -> None:
    old_manifest = HARDNESS / "Legacy" / "V2Hardness" / "MANIFEST.json"
    with pytest.raises(BenchmarkManifestError) as error:
        load_benchmark_manifest(old_manifest)
    assert error.value.code == "unsupported_legacy_benchmark"


def test_old_opencode_yaml_schema_is_explicitly_rejected() -> None:
    old_manifest = HARDNESS / "Legacy" / "Opencode" / "MANIFEST.yaml"
    with pytest.raises(BenchmarkManifestError) as error:
        load_benchmark_manifest(old_manifest)
    assert error.value.code == "unsupported_legacy_benchmark"
