from __future__ import annotations

import json
from dataclasses import replace
from pathlib import Path

import pytest

from agent.hardness.lean_runner import sha256_file
from agent.hardness.model_client import ModelResponse
from agent.hardness.np_hard_input import (
    NPHardInputError,
    build_np_hard_input_certificate_source,
    certify_np_hard_input,
    resolve_np_hard_input_reference,
)
from agent.hardness.np_hard_orchestrator import (
    NPHardOrchestratorConfigV2,
    NPHardOrchestratorV2,
)


ROOT = Path(__file__).resolve().parents[1]
MODULE = "Benchmark.Hardness.Inputs.NPHardGeneralization.InputNormalizationOpenWorld"
PREFIX = MODULE + "."


class RecommendedBodyModel:
    def __init__(self) -> None:
        self.calls = 0

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        assert "untrusted Lean 4 author" in system
        self.calls += 1
        payload = json.loads(prompt)
        response = dict(payload["response_template"])
        response["replacement_body"] = payload["recommended_first_body"]
        return ModelResponse(
            called=True,
            ok=True,
            content=json.dumps(response),
            error=None,
            status_code=200,
            duration_seconds=0.0,
            usage={"fixture_tokens": 0},
            attempts=1,
            finish_reason="stop",
        )


@pytest.fixture(scope="module")
def unique_reference():
    return resolve_np_hard_input_reference(
        root=ROOT,
        input_module=MODULE,
        requested_term=PREFIX + "uniqueEncoding",
    )


def test_unregistered_exact_and_unique_encoding_resolve_from_lean_catalog(
    unique_reference,
) -> None:
    exact = resolve_np_hard_input_reference(
        root=ROOT,
        input_module="Benchmark.Hardness.Inputs.HCCrossModule.Entry",
        requested_term=(
            "Benchmark.Hardness.Inputs.HCCrossModule.Problem.heldOutTarget"
        ),
    )
    assert exact.normalization_kind == "exact"
    assert exact.stable_id is None
    assert exact.problem_declaration == exact.requested_declaration

    reference = unique_reference
    assert reference.normalization_kind == "encoding"
    assert reference.stable_id is None
    assert reference.canonical_problem == PREFIX + "uniqueProblem"
    assert reference.resolved_encoding == PREFIX + "uniqueEncoding"
    assert reference.normalization_observation.representation_match_count == 1
    source = build_np_hard_input_certificate_source(reference=reference, nonce="nonce")
    assert (
        f"{PREFIX}uniqueEncoding = {PREFIX}uniqueProblem.representation" in source
    )


def test_missing_and_ambiguous_presentations_block_without_model_calls() -> None:
    with pytest.raises(NPHardInputError) as missing:
        resolve_np_hard_input_reference(
            root=ROOT,
            input_module=MODULE,
            requested_term=PREFIX + "missingEncoding",
        )
    assert missing.value.code == "missing_lawful_presentation"

    with pytest.raises(NPHardInputError) as ambiguous:
        resolve_np_hard_input_reference(
            root=ROOT,
            input_module=MODULE,
            requested_term=PREFIX + "ambiguousEncoding",
        )
    assert ambiguous.value.code == "ambiguous_lawful_presentation"
    assert PREFIX + "ambiguousFirst" in ambiguous.value.message
    assert PREFIX + "ambiguousSecond" in ambiguous.value.message


def test_normalization_index_and_content_ids_are_deterministic(unique_reference) -> None:
    repeated = resolve_np_hard_input_reference(
        root=ROOT,
        input_module=MODULE,
        requested_term=PREFIX + "uniqueEncoding",
    )
    first = unique_reference.normalization_observation
    second = repeated.normalization_observation
    assert first.catalog_id == second.catalog_id
    assert first.observation_id == second.observation_id
    assert first.import_closure_sha256 == second.import_closure_sha256
    assert replace(first, nonce="f" * 32).observation_id == first.observation_id
    assert first.import_closure_sha256.startswith("sha256:")
    assert first.toolchain == "leanprover/lean4:v4.29.0"
    assert first.lake_manifest_sha256.startswith("sha256:")


def test_unique_encoding_certificate_is_compiled_and_records_trace(
    unique_reference, tmp_path
) -> None:
    identity, command = certify_np_hard_input(
        root=ROOT,
        reference=unique_reference,
        certificate_path=tmp_path / "InputNormalization.lean",
        toolchain=(ROOT / "Lean/lean-toolchain").read_text(encoding="utf-8").strip(),
        lake_manifest_sha256=sha256_file(ROOT / "Lean/lake-manifest.json"),
        timeout_seconds=600,
    )
    assert command.ok
    assert identity.requested_declaration == PREFIX + "uniqueEncoding"
    assert identity.canonical_problem == PREFIX + "uniqueProblem"
    assert identity.normalization_relation == (
        "encoding_defeq_canonical_representation"
    )
    assert identity.normalized_problem_node == identity.canonical_problem_node
    assert identity.normalization_catalog_id.startswith("sha256:")
    assert (tmp_path / "InputNormalizationObservation.json").is_file()


def test_old_identity_is_rejected_after_related_source_drift(
    unique_reference, tmp_path
) -> None:
    source_path = (
        ROOT
        / "Lean/Reference/Benchmark/Hardness/Inputs/NPHardGeneralization/"
        "InputNormalizationOpenWorld.lean"
    )
    original = source_path.read_text(encoding="utf-8")
    try:
        source_path.write_text(original + "\n-- H-D content drift probe\n", encoding="utf-8")
        with pytest.raises(NPHardInputError) as stale:
            certify_np_hard_input(
                root=ROOT,
                reference=unique_reference,
                certificate_path=tmp_path / "Stale.lean",
                toolchain=(ROOT / "Lean/lean-toolchain")
                .read_text(encoding="utf-8")
                .strip(),
                lake_manifest_sha256=sha256_file(ROOT / "Lean/lake-manifest.json"),
                timeout_seconds=600,
            )
        assert stale.value.code == "candidate_dependency_stale"
    finally:
        source_path.write_text(original, encoding="utf-8")


def test_nonexistent_and_wrong_module_ownership_fail_closed() -> None:
    with pytest.raises(NPHardInputError) as nonexistent:
        resolve_np_hard_input_reference(
            root=ROOT,
            input_module=MODULE,
            requested_term=PREFIX + "doesNotExist",
        )
    assert nonexistent.value.code == "input_problem_not_found"

    with pytest.raises(NPHardInputError) as wrong_module:
        resolve_np_hard_input_reference(
            root=ROOT,
            input_module=MODULE,
            requested_term=(
                "Benchmark.Hardness.Inputs.HCCrossModule.Problem.heldOutTarget"
            ),
        )
    assert wrong_module.value.code == "input_problem_not_found"


def test_bare_encoding_runs_through_production_orchestrator_at_canonical_endpoint(
    tmp_path,
) -> None:
    module = "Benchmark.Hardness.Inputs.HDCrossModuleEncoding"
    encoding = module + ".heldOutEncoding"
    canonical = "Benchmark.Hardness.Inputs.HCCrossModule.Problem.heldOutTarget"
    model = RecommendedBodyModel()
    result = NPHardOrchestratorV2(
        NPHardOrchestratorConfigV2(
            root=ROOT,
            input_module=module,
            problem_declaration=encoding,
            output_dir=tmp_path / "production",
            authoring_policy="model-required",
            runtime_prebuilt=False,
        ),
        model_client=model,
    ).run()
    payload = result.to_dict()
    identity = payload["input_identity"]
    assert result.status == "VERIFIED"
    assert result.model_calls == model.calls == 2
    assert identity["requested_declaration"] == encoding
    assert identity["resolved_encoding"] == encoding
    assert identity["canonical_problem"] == canonical
    assert identity["normalization_kind"] == "encoding"
    assert payload["artifact"]["endpoint"] == canonical
    assert payload["independent_replay"]["passed"] is True
    assert payload["axiom_audit"]["passed"] is True
    assert payload["deletion_audit"]["passed"] is True
