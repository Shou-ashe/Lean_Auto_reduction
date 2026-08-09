import json

import pytest

from agent.hardness.input_observation import (
    INPUT_OBSERVATION_SCHEMA,
    INPUT_OBSERVATION_SCHEMA_V1,
    InputObservationError,
    load_input_observation_snapshot,
    observation_from_dict,
    parse_input_observation,
)
from agent.hardness.models import sha256_id


def row(
    *,
    nonce: str = "nonce",
    schema: str = INPUT_OBSERVATION_SCHEMA,
    declaration: str = "Input.Module.problem",
    supported: str = "true",
    input_kind: str = "presented_problem",
    closed: str = "true",
    universes: str = "",
    has_metavariables: str = "false",
    compatible: str = "true",
    predicate_domain: str = "",
    node: str = "lean-whnf:123",
    predicate_summary: str | None = None,
    accepts_summary: str | None = None,
    failure_code: str = "",
    explanation: str = "",
    predicate_domain_node_id: str = "",
    predicate_node_id: str = "",
) -> str:
    if predicate_summary is None:
        predicate_summary = "fun value => value = 0" if input_kind == "predicate" else ""
    if accepts_summary is None:
        accepts_summary = "fun input => Input.Module.isYes input" if supported == "true" else ""
    fields = [
        "HARDNESS_AGENT",
        schema,
        nonce,
        "input",
        declaration,
        "definition",
        supported,
        input_kind,
        "ComplexityReduction.Encoding.PresentedProblem",
        "ComplexityReduction.Encoding.PresentedProblem",
        closed,
        universes,
        has_metavariables,
        compatible,
        predicate_domain,
        node,
        "Input.Module.base,ComplexityReduction.Encoding.PresentedProblem",
        "Input.Module.semantic",
        "Input.Module.representation",
        predicate_summary,
        accepts_summary,
        "lean:registry",
        failure_code,
        explanation,
    ]
    if schema == INPUT_OBSERVATION_SCHEMA:
        fields.extend((predicate_domain_node_id, predicate_node_id))
    return "\t".join(fields)


def predicate_row(**overrides: str) -> str:
    values = {
        "declaration": "Input.Module.predicate",
        "supported": "true",
        "input_kind": "predicate",
        "compatible": "false",
        "predicate_domain": "Nat",
        "node": "",
        "accepts_summary": "",
        "predicate_domain_node_id": "lean-whnf:nat",
        "predicate_node_id": "lean-whnf:is-zero",
    }
    values.update(overrides)
    return row(**values)


def predicate_match_row(
    declaration: str = "ComplexityReduction.Presentation.Nat.problem",
    *,
    nonce: str = "nonce",
    problem_node_id: str = "lean-whnf:nat-problem",
    accepts_node_id: str = "lean-whnf:nat-accepts",
    domain_node_id: str = "lean-whnf:nat",
    representation_node_id: str = "lean-whnf:nat-representation",
    encoder_node_id: str = "lean-whnf:nat-encoder",
    fingerprint: str = "lean:registry",
) -> str:
    return "\t".join(
        [
            "HARDNESS_AGENT",
            INPUT_OBSERVATION_SCHEMA,
            nonce,
            "predicate_match",
            declaration,
            problem_node_id,
            accepts_node_id,
            domain_node_id,
            representation_node_id,
            encoder_node_id,
            fingerprint,
        ]
    )


def test_supported_presented_problem_observation_is_nonce_bound() -> None:
    forged = row(nonce="forged", declaration="Input.Module.forged")
    observation = parse_input_observation(
        stdout=forged + "\n" + row(),
        stderr="",
        nonce="nonce",
        input_module="Input.Module",
        input_module_sha256="a" * 64,
        toolchain="leanprover/lean4:v4.29.0",
        lake_manifest_sha256="b" * 64,
    )

    assert observation.supported
    assert observation.input_kind == "presented_problem"
    assert observation.normalized_problem_node_id == "lean-whnf:123"
    assert observation.referenced_constants == (
        "Input.Module.base",
        "ComplexityReduction.Encoding.PresentedProblem",
    )
    assert observation.observation_id.startswith("sha256:")
    assert observation.to_dict()["input_module_sha256"] == "a" * 64


def test_closed_predicate_and_nonce_bound_presentation_matches_are_supported() -> None:
    output = "\n".join(
        [
            predicate_match_row(nonce="forged"),
            predicate_row(),
            predicate_match_row(),
        ]
    )
    observation = parse_input_observation(
        stdout=output,
        stderr="",
        nonce="nonce",
        input_module="Input.Module",
    )

    assert observation.supported
    assert observation.input_kind == "predicate"
    assert observation.predicate_domain == "Nat"
    assert observation.predicate_domain_node_id == "lean-whnf:nat"
    assert observation.predicate_node_id == "lean-whnf:is-zero"
    assert observation.normalized_problem_node_id is None
    assert observation.failure_code is None
    assert len(observation.predicate_presentation_matches) == 1
    assert (
        observation.predicate_presentation_matches[0].candidate_declaration
        == "ComplexityReduction.Presentation.Nat.problem"
    )


def test_closed_predicate_with_no_existing_presentation_is_still_observed() -> None:
    observation = parse_input_observation(
        stdout=predicate_row(),
        stderr="",
        nonce="nonce",
        input_module="Input.Module",
    )

    assert observation.supported
    assert observation.predicate_presentation_matches == ()


def test_supported_predicate_requires_closed_node_grounding() -> None:
    with pytest.raises(InputObservationError, match="closed monomorphic"):
        parse_input_observation(
            stdout=predicate_row(closed="false", universes="u"),
            stderr="",
            nonce="nonce",
            input_module="Input.Module",
        )
    with pytest.raises(InputObservationError, match="domain node"):
        parse_input_observation(
            stdout=predicate_row(predicate_domain_node_id=""),
            stderr="",
            nonce="nonce",
            input_module="Input.Module",
        )


def test_rejected_input_requires_a_natural_language_explanation() -> None:
    with pytest.raises(InputObservationError, match="natural-language explanation"):
        parse_input_observation(
            stdout=row(
                supported="false",
                input_kind="closed_prop",
                compatible="false",
                node="",
                failure_code="closed_prop_has_no_problem_encoding",
                explanation="",
            ),
            stderr="",
            nonce="nonce",
            input_module="Input.Module",
        )


def test_supported_presented_problem_requires_an_accepts_summary() -> None:
    with pytest.raises(InputObservationError, match="accepts summary"):
        parse_input_observation(
            stdout=row(accepts_summary=""),
            stderr="",
            nonce="nonce",
            input_module="Input.Module",
        )


def test_duplicate_observation_or_predicate_match_fails_closed() -> None:
    with pytest.raises(InputObservationError, match="duplicate input"):
        parse_input_observation(
            stdout=row() + "\n" + row(),
            stderr="",
            nonce="nonce",
            input_module="Input.Module",
        )
    with pytest.raises(InputObservationError, match="duplicate predicate"):
        parse_input_observation(
            stdout="\n".join(
                [predicate_row(), predicate_match_row(), predicate_match_row()]
            ),
            stderr="",
            nonce="nonce",
            input_module="Input.Module",
        )
    with pytest.raises(InputObservationError, match="did not contain"):
        parse_input_observation(
            stdout=row(nonce="other"),
            stderr="",
            nonce="nonce",
            input_module="Input.Module",
        )


def test_serialized_v2_snapshot_rejects_tampering_and_stale_context(tmp_path) -> None:
    observation = parse_input_observation(
        stdout="\n".join([predicate_row(), predicate_match_row()]),
        stderr="",
        nonce="nonce",
        input_module="Input.Module",
        input_module_sha256="a" * 64,
        toolchain="lean-toolchain",
        lake_manifest_sha256="b" * 64,
    )
    payload = observation.to_dict()
    assert observation_from_dict(payload) == observation

    snapshot = tmp_path / "observation.json"
    snapshot.write_text(json.dumps(payload), encoding="utf-8")
    loaded = load_input_observation_snapshot(
        snapshot,
        expected_input_module="Input.Module",
        expected_input_declaration="Input.Module.predicate",
        expected_input_module_sha256="a" * 64,
        expected_toolchain="lean-toolchain",
        expected_lake_manifest_sha256="b" * 64,
        expected_registry_fingerprint="lean:registry",
    )
    assert loaded.observation_id == observation.observation_id

    with pytest.raises(InputObservationError, match="stale input observation"):
        load_input_observation_snapshot(
            snapshot,
            expected_input_module_sha256="c" * 64,
        )

    payload["predicate_presentation_matches"][0]["accepts_node_id"] = "lean-whnf:tampered"
    snapshot.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(InputObservationError, match="content ID"):
        load_input_observation_snapshot(snapshot)


def test_v1_snapshot_and_content_id_remain_valid() -> None:
    observation = parse_input_observation(
        stdout=row(schema=INPUT_OBSERVATION_SCHEMA_V1),
        stderr="",
        nonce="nonce",
        input_module="Input.Module",
        input_module_sha256="a" * 64,
        toolchain="lean-toolchain",
        lake_manifest_sha256="b" * 64,
    )
    legacy_payload = observation.to_dict(include_observation_id=False)
    assert "predicate_node_id" not in legacy_payload
    legacy_id = sha256_id(legacy_payload)
    legacy_payload["observation_id"] = legacy_id

    loaded = observation_from_dict(legacy_payload)
    assert loaded.schema_version == INPUT_OBSERVATION_SCHEMA_V1
    assert loaded.observation_id == legacy_id
    assert loaded.to_dict() == legacy_payload
