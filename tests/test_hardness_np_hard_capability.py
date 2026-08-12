from __future__ import annotations

import hashlib
import json
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.model_client import DeepSeekConfig
from agent.hardness.np_hard_capability import (
    CAPABILITY_BENCHMARK_ID_V2,
    CAPABILITY_MANIFEST_SCHEMA_V2,
    CAPABILITY_SPLIT_COUNTS,
    FORMAL_PUBLIC_PROFILE,
    NPHardCapabilityError,
    _selected_cases,
    _validate_formal_profile,
    build_capability_isolated_workspace,
    load_capability_bundle,
    load_capability_oracle,
)


ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "Benchmark/Hardness/CAPABILITY_MANIFEST_V2.json"
MATRIX = (
    ROOT
    / "Benchmark/Hardness/Catalogs/np_hard_target_matrix_v2.json"
)
REGISTRY = ROOT / "agent/hardness/data/np_hard_input_registry.json"


def _write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def _formal_config(**changes: object) -> DeepSeekConfig:
    config = DeepSeekConfig(
        api_key="test-only-key",
        base_url="https://api.deepseek.com",
        model="deepseek-v4-flash",
        timeout_seconds=1_800,
        temperature=0.0,
        max_tokens=128_000,
        max_retries=0,
        reasoning_effort="max",
    )
    return replace(config, **changes)


def test_current_bundle_is_exactly_the_public_32_plus_2_contract() -> None:
    bundle = load_capability_bundle(MANIFEST, root=ROOT, verify_oracle=False)
    assert bundle.manifest.schema_version == CAPABILITY_MANIFEST_SCHEMA_V2
    assert bundle.manifest.benchmark_id == CAPABILITY_BENCHMARK_ID_V2
    assert bundle.manifest.target_matrix.path == MATRIX
    assert bundle.manifest.target_matrix.sha256 == "sha256:" + hashlib.sha256(
        MATRIX.read_bytes()
    ).hexdigest()
    assert REGISTRY.is_file()
    assert {
        split: len(bundle.suites[split].cases)
        for split in CAPABILITY_SPLIT_COUNTS
    } == CAPABILITY_SPLIT_COUNTS
    case_ids = [
        case.case_id
        for split in CAPABILITY_SPLIT_COUNTS
        for case in bundle.suites[split].cases
    ]
    assert len(case_ids) == len(set(case_ids)) == 34


def test_public_suites_are_answer_free() -> None:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    forbidden = {
        "answer",
        "expected",
        "expected_status",
        "gold",
        "hint",
        "oracle",
        "route",
        "solution",
    }
    for suite_ref in manifest["suites"].values():
        suite = json.loads((ROOT / suite_ref["file"]).read_text(encoding="utf-8"))
        assert all(forbidden.isdisjoint(case) for case in suite["cases"])


def test_current_oracle_has_32_scored_cases_and_ten_authoring_motifs() -> None:
    bundle = load_capability_bundle(MANIFEST, root=ROOT, verify_oracle=True)
    oracle = load_capability_oracle(bundle.manifest.oracle.path, bundle=bundle)
    assert len(oracle) == 34
    assert sum(case.scored for case in oracle.values()) == 32
    assert sum(
        case.required_authoring_motif is not None for case in oracle.values()
    ) == 10


def test_case_selection_is_explicit_and_lane_bounded() -> None:
    bundle = load_capability_bundle(MANIFEST, root=ROOT, verify_oracle=False)
    selected = _selected_cases(
        bundle,
        ("dev",),
        selected_case_ids=("cdev-er-01-three-sat-seed",),
    )
    assert [case.case_id for case in selected] == ["cdev-er-01-three-sat-seed"]
    with pytest.raises(NPHardCapabilityError) as raised:
        _selected_cases(
            bundle,
            ("dev",),
            selected_case_ids=("frontier-01-knapsack-unary-boundary",),
        )
    assert raised.value.code == "invalid_capability_split"


def test_formal_profile_requires_the_current_128k_max_model_contract() -> None:
    _validate_formal_profile(
        deepseek=_formal_config(), required_profile=FORMAL_PUBLIC_PROFILE
    )
    with pytest.raises(NPHardCapabilityError) as missing_key:
        _validate_formal_profile(
            deepseek=_formal_config(api_key=""),
            required_profile=FORMAL_PUBLIC_PROFILE,
        )
    assert missing_key.value.code == "model_provider_unavailable"
    with pytest.raises(NPHardCapabilityError) as wrong_budget:
        _validate_formal_profile(
            deepseek=_formal_config(max_tokens=16_000),
            required_profile=FORMAL_PUBLIC_PROFILE,
        )
    assert wrong_budget.value.code == "qualification_model_profile_mismatch"


def test_isolated_workspace_uses_migrated_runtime_data_without_gate(
    tmp_path: Path,
) -> None:
    source = tmp_path / "source"
    lean = source / "Lean"
    for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json"):
        path = lean / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("{}\n" if name.endswith(".json") else "test\n", encoding="utf-8")
    public = lean / "Reference/ComplexityReduction/Domain"
    public.mkdir(parents=True)
    (public / "Public.lean").write_text("def public := True\n", encoding="utf-8")
    _write_json(
        source / "agent/hardness/data/np_hard_input_registry.json",
        {"schema_version": "test-registry"},
    )
    matrix = source / "matrix.json"
    _write_json(matrix, {"schema_version": "test-matrix"})
    policy = source / "policy.json"
    _write_json(policy, {"schema_version": "test-policy"})

    destination = tmp_path / "isolated"
    report = build_capability_isolated_workspace(
        root=source,
        destination=destination,
        target_matrix_path=matrix,
        scope_policy_path=policy,
    )
    assert report["passed"] is True
    assert not (destination / "Gate").exists()
    assert json.loads(
        (destination / "agent/hardness/data/np_hard_input_registry.json").read_text()
    ) == {"schema_version": "test-registry"}
    assert json.loads(
        (
            destination
            / "Benchmark/Hardness/Catalogs/np_hard_target_matrix_v2.json"
        ).read_text()
    ) == {"schema_version": "test-matrix"}
