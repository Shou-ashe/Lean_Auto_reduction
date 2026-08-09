import json

import pytest

from agent.hardness.connection_catalog import (
    CONNECTION_CATALOG_SCHEMA,
    ConnectionCatalogError,
    build_initial_connection_hints,
    connected_problem_match,
    connection_catalog_from_dict,
    connection_search_result,
    build_reduction_catalog,
    load_connection_catalog_snapshot,
    parse_connection_catalog,
    parse_connection_searches,
    search_connections,
)
from agent.hardness.input_observation import LeanInputObservation
from agent.hardness.problem_catalog import ProblemCatalog, ProblemCatalogEntry


def registry_row(*, nonce: str = "nonce", fingerprint: str = "lean:registry") -> str:
    return "\t".join(
        ["HARDNESS_AGENT", CONNECTION_CATALOG_SCHEMA, nonce, "registry", fingerprint]
    )


def connection_row(
    certificate: str,
    *,
    capability: str = "certified_reduction",
    relation: str = "existing_reduction",
    direction: str = "forward",
    term_kind: str = "certificate",
    projection: str | None = None,
    lean_term: str | None = None,
    source: str = "lean-whnf:source",
    target: str = "lean-whnf:target",
    fingerprint: str = "lean:registry",
) -> str:
    projection = projection or certificate
    lean_term = lean_term or certificate
    return "\t".join(
        [
            "HARDNESS_AGENT",
            CONNECTION_CATALOG_SCHEMA,
            "nonce",
            "connection",
            certificate,
            capability,
            relation,
            direction,
            term_kind,
            projection,
            lean_term,
            f"lean:{source}",
            f"lean:{target}",
            source,
            target,
            f"display {source}",
            f"display {target}",
            "ingress",
            fingerprint,
        ]
    )


def catalog_output() -> str:
    equiv = "ComplexityReduction.Routes.Example.problemEquiv"
    forward_projection = (
        "ComplexityReduction.Certificate.CertifiedEquiv.forwardReduction"
    )
    backward_projection = (
        "ComplexityReduction.Certificate.CertifiedEquiv.backwardReduction"
    )
    return "\n".join(
        [
            registry_row(),
            connection_row("ComplexityReduction.Routes.Example.direct"),
            connection_row(
                equiv,
                capability="certified_equiv",
                relation="certified_equiv_forward",
                term_kind="fixed_projection",
                projection=forward_projection,
                lean_term=f"{forward_projection} {equiv}",
            ),
            connection_row(
                equiv,
                capability="certified_equiv",
                relation="certified_equiv_backward",
                direction="backward",
                term_kind="fixed_projection",
                projection=backward_projection,
                lean_term=f"{backward_projection} {equiv}",
                source="lean-whnf:target",
                target="lean-whnf:source",
            ),
        ]
    )


def observation() -> LeanInputObservation:
    return LeanInputObservation(
        input_module="Input.Module",
        input_declaration="Input.Module.problem",
        declaration_kind="definition",
        supported=True,
        input_kind="presented_problem",
        elaborated_type="ComplexityReduction.Encoding.PresentedProblem",
        whnf_type="ComplexityReduction.Encoding.PresentedProblem",
        closed=True,
        universe_parameters=(),
        has_metavariables=False,
        presented_problem_compatible=True,
        predicate_domain=None,
        normalized_problem_node_id="lean-whnf:source",
        referenced_constants=(),
        semantic_summary="Input semantic",
        representation_summary="Input representation",
        predicate_summary=None,
        accepts_summary="fun input => input",
        registry_fingerprint="lean:registry",
        failure_code=None,
        explanation=None,
    )


def problem_catalog() -> tuple[ProblemCatalog, ProblemCatalogEntry]:
    candidate = ProblemCatalogEntry(
        declaration="ComplexityReduction.Presentation.Target.problem",
        declaration_kind="definition",
        display="target problem",
        problem_node_id="lean-whnf:target",
        semantic_summary="Target semantic",
        representation_summary="Target representation",
        encoder_bound_identity_summary="Target encoder identity",
        referenced_constants=(),
        registered=True,
        registry_fingerprint="lean:registry",
    )
    return (
        ProblemCatalog(registry_fingerprint="lean:registry", entries=(candidate,)),
        candidate,
    )


def test_catalog_exposes_only_lean_emitted_directions_and_fixed_projections() -> None:
    catalog = parse_connection_catalog(
        stdout=catalog_output(), stderr="", nonce="nonce"
    )
    assert len(catalog.entries) == 3
    equiv_entries = [
        entry for entry in catalog.entries if entry.capability_kind == "certified_equiv"
    ]
    assert {entry.direction for entry in equiv_entries} == {"forward", "backward"}
    backward = next(entry for entry in equiv_entries if entry.direction == "backward")
    assert backward.source_node_id == "lean-whnf:target"
    assert backward.target_node_id == "lean-whnf:source"
    assert backward.projection_declaration.endswith("backwardReduction")

    reduction_catalog = build_reduction_catalog(catalog)
    assert [entry.declaration for entry in reduction_catalog.entries] == [
        "ComplexityReduction.Routes.Example.direct"
    ]

    direct_reverse = search_connections(
        catalog,
        parse_connection_searches(
            {
                "searches": [
                    {
                        "capability_kinds": ["certified_reduction"],
                        "source_node_ids": ["lean-whnf:target"],
                        "target_node_ids": ["lean-whnf:source"],
                    }
                ]
            }
        ),
    )
    assert direct_reverse == ()


def test_search_is_bounded_and_initial_hints_do_not_reveal_declarations() -> None:
    catalog = parse_connection_catalog(
        stdout=catalog_output(), stderr="", nonce="nonce"
    )
    results = search_connections(
        catalog,
        parse_connection_searches(
            {
                "searches": [
                    {
                        "source_node_ids": ["lean-whnf:source"],
                        "relations": ["certified_equiv_forward"],
                    }
                ]
            }
        ),
    )
    assert len(results) == 1
    summary = connection_search_result(results[0])
    assert summary["validation_source"] == "lean_validated_fixed_projection"
    assert summary["source_node_id"] == "lean-whnf:source"

    hints = build_initial_connection_hints(
        catalog, input_node_id="lean-whnf:source"
    )
    assert not hints["contains_declaration_names"]
    serialized = json.dumps(hints)
    assert "problemEquiv" not in serialized
    assert "Example.direct" not in serialized


def test_connected_match_requires_retrieved_problem_and_connection() -> None:
    catalog = parse_connection_catalog(
        stdout=catalog_output(), stderr="", nonce="nonce"
    )
    problems, candidate = problem_catalog()
    connection = next(
        entry for entry in catalog.entries if entry.relation == "certified_equiv_forward"
    )
    match = connected_problem_match(
        observation=observation(),
        problem_catalog=problems,
        candidate=candidate,
        retrieved_problem_entries=(candidate,),
        connection_catalog=catalog,
        connection=connection,
        retrieved_connections=(connection,),
    )
    assert match.relation == "certified_equiv_forward"
    assert not match.exact_defeq
    assert match.connection_entry_id == connection.entry_id
    assert match.connection_lean_term == connection.lean_term
    assert match.supporting_declarations == (
        connection.certificate_declaration,
        connection.projection_declaration,
    )

    with pytest.raises(ConnectionCatalogError, match="not returned"):
        connected_problem_match(
            observation=observation(),
            problem_catalog=problems,
            candidate=candidate,
            retrieved_problem_entries=(candidate,),
            connection_catalog=catalog,
            connection=connection,
            retrieved_connections=(),
        )


def test_snapshot_rejects_tampering_staleness_and_nonfixed_projection(tmp_path) -> None:
    catalog = parse_connection_catalog(
        stdout=catalog_output(),
        stderr="",
        nonce="nonce",
        toolchain="lean-toolchain",
        lake_manifest_sha256="a" * 64,
    )
    payload = catalog.to_dict()
    assert connection_catalog_from_dict(payload) == catalog
    snapshot = tmp_path / "connections.json"
    snapshot.write_text(json.dumps(payload), encoding="utf-8")
    assert (
        load_connection_catalog_snapshot(
            snapshot,
            expected_registry_fingerprint="lean:registry",
            expected_toolchain="lean-toolchain",
            expected_lake_manifest_sha256="a" * 64,
        ).catalog_id
        == catalog.catalog_id
    )
    with pytest.raises(ConnectionCatalogError, match="stale connection catalog"):
        load_connection_catalog_snapshot(snapshot, expected_toolchain="other")

    forward_index = next(
        index
        for index, entry in enumerate(payload["entries"])
        if entry["relation"] == "certified_equiv_forward"
    )
    payload["entries"][forward_index]["projection_declaration"] = (
        "ComplexityReduction.Certificate.CertifiedEquiv.backwardReduction"
    )
    payload["entries"][forward_index].pop("entry_id")
    payload.pop("catalog_id")
    snapshot.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(ConnectionCatalogError, match="fixed projection"):
        load_connection_catalog_snapshot(snapshot)
