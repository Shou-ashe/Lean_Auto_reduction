from __future__ import annotations

from dataclasses import asdict, replace
import json
from pathlib import Path

import pytest

from agent.generative_reduction.boolean_csp_regression import (
    recursive_benchmark_budget,
)
from agent.generative_reduction.capability_gate_policy import (
    gadget_authoring_heldout_policy,
    gadget_authoring_policy,
    gadget_authoring_validation_policy,
)
from agent.generative_reduction.gadget_authoring_freeze import (
    DEFAULT_GADGET_AUTHORING_FREEZE_MANIFEST,
    GADGET_AUTHORING_FREEZE_COMPONENTS,
    GadgetAuthoringFreezeError,
    validate_gadget_authoring_freeze,
)
from agent.hardness.boolean_csp_np_hard_benchmark import load_suite


ROOT = Path(__file__).resolve().parents[1]
PUBLIC_SUITE_PATH = (
    ROOT
    / "Benchmark"
    / "Hardness"
    / "Suites"
    / "boolean_csp_np_hard_public_v1.json"
)
FREEZE_MANIFEST = ROOT / DEFAULT_GADGET_AUTHORING_FREEZE_MANIFEST
FROZEN_MODEL = {
    "base_url": "https://api.deepseek.com",
    "model": "deepseek-v4-flash",
    "timeout_seconds": 900,
    "temperature": 0.0,
    "max_tokens": 64000,
    "max_retries": 0,
    "reasoning_effort": "low",
    "api_key_configured": True,
}
FROZEN_RUNTIME = {
    "profile": "benchmark",
    "jobs": 4,
    "lean_timeout_seconds": 600,
}


def _suite_identity(suite) -> dict[str, object]:
    return {
        "suite_id": suite.suite_id,
        "suite_sha256": suite.sha256,
        "path": str(suite.path.relative_to(ROOT)),
    }


def _validate(*, policy, case_set_name: str, case_ids, manifest=FREEZE_MANIFEST):
    suite = load_suite(PUBLIC_SUITE_PATH)
    return validate_gadget_authoring_freeze(
        root=ROOT,
        manifest_path=manifest,
        policy=policy,
        case_set_name=case_set_name,
        selected_case_ids=case_ids,
        suite_identity=_suite_identity(suite),
        model_config=FROZEN_MODEL,
        runtime_config=FROZEN_RUNTIME,
        budget=asdict(recursive_benchmark_budget()),
    )


def test_staged_policies_partition_validation_and_heldout_exactly() -> None:
    suite = load_suite(PUBLIC_SUITE_PATH)
    validation_ids = tuple(
        case.case_id for case in suite.cases if case.split == "validation"
    )
    heldout_ids = tuple(
        case.case_id for case in suite.cases if case.split == "heldout"
    )

    validation = gadget_authoring_validation_policy()
    heldout = gadget_authoring_heldout_policy()
    validation.validate_case_ids(validation_ids)
    heldout.validate_case_ids(heldout_ids)
    assert validation.required_case_ids == validation_ids
    assert heldout.required_case_ids == heldout_ids
    assert validation.anchor_case_ids == heldout.anchor_case_ids == ()
    assert validation.name == heldout.name == "gadget-authoring"


def test_committed_freeze_validates_all_three_public_case_sets() -> None:
    suite = load_suite(PUBLIC_SUITE_PATH)
    cases = {
        "validation": tuple(
            case.case_id for case in suite.cases if case.split == "validation"
        ),
        "heldout": tuple(
            case.case_id for case in suite.cases if case.split == "heldout"
        ),
        "full": tuple(case.case_id for case in suite.cases),
    }
    policies = {
        "validation": gadget_authoring_validation_policy(),
        "heldout": gadget_authoring_heldout_policy(),
        "full": gadget_authoring_policy(),
    }

    for case_set_name in ("validation", "heldout", "full"):
        receipt = _validate(
            policy=policies[case_set_name],
            case_set_name=case_set_name,
            case_ids=cases[case_set_name],
        )
        assert receipt["integrity_passed"]
        assert receipt["verified_component_count"] == len(
            GADGET_AUTHORING_FREEZE_COMPONENTS
        )


def test_freeze_rejects_model_or_policy_drift() -> None:
    suite = load_suite(PUBLIC_SUITE_PATH)
    full_ids = tuple(case.case_id for case in suite.cases)

    with pytest.raises(GadgetAuthoringFreezeError, match="model_config_matches"):
        validate_gadget_authoring_freeze(
            root=ROOT,
            manifest_path=FREEZE_MANIFEST,
            policy=gadget_authoring_policy(),
            case_set_name="full",
            selected_case_ids=full_ids,
            suite_identity=_suite_identity(suite),
            model_config={**FROZEN_MODEL, "max_tokens": 15999},
            runtime_config=FROZEN_RUNTIME,
            budget=asdict(recursive_benchmark_budget()),
        )

    drifted_policy = replace(
        gadget_authoring_policy(), policy_version="gadget-authoring-policy-v999"
    )
    with pytest.raises(GadgetAuthoringFreezeError, match="policy_hash_matches"):
        _validate(
            policy=drifted_policy,
            case_set_name="full",
            case_ids=full_ids,
        )


def test_freeze_rejects_component_hash_tampering(tmp_path: Path) -> None:
    suite = load_suite(PUBLIC_SUITE_PATH)
    manifest = json.loads(FREEZE_MANIFEST.read_text(encoding="utf-8"))
    first_component = GADGET_AUTHORING_FREEZE_COMPONENTS[0]
    manifest["component_sha256"][first_component] = "sha256:" + "0" * 64
    tampered = tmp_path / "tampered-freeze.json"
    tampered.write_text(json.dumps(manifest), encoding="utf-8")

    with pytest.raises(GadgetAuthoringFreezeError, match="component_hashes_match"):
        _validate(
            policy=gadget_authoring_policy(),
            case_set_name="full",
            case_ids=tuple(case.case_id for case in suite.cases),
            manifest=tampered,
        )
