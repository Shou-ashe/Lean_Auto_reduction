import json
from dataclasses import replace

import pytest

from agent.hardness.input_observation import (
    LeanInputObservation,
    PredicatePresentationMatch,
)
from agent.hardness.models import sha256_id
from agent.hardness.problem_catalog import (
    PROBLEM_CATALOG_SCHEMA,
    PROBLEM_CATALOG_SCHEMA_V1,
    ProblemCatalogError,
    build_initial_problem_hints,
    exact_predicate_problem_match,
    exact_problem_match,
    load_problem_catalog_snapshot,
    parse_problem_catalog,
    parse_problem_searches,
    predicate_exact_candidates,
    predicate_presentation_groups,
    problem_catalog_from_dict,
    problem_search_result,
    search_problems,
)


def registry_row(
    *,
    nonce: str = "nonce",
    fingerprint: str = "lean:registry",
    schema: str = PROBLEM_CATALOG_SCHEMA,
) -> str:
    return "\t".join(["HARDNESS_AGENT", schema, nonce, "registry", fingerprint])


def problem_row(
    declaration: str,
    *,
    nonce: str = "nonce",
    schema: str = PROBLEM_CATALOG_SCHEMA,
    node: str = "lean-whnf:source",
    registered: str = "true",
    fingerprint: str = "lean:registry",
    semantic: str = "Graph semantic",
    representation: str = "Graph representation",
    accepts_summary: str = "fun input => graph input",
    accepts_node_id: str = "lean-whnf:graph-accepts",
    domain_summary: str = "Graph.Instance",
    domain_node_id: str = "lean-whnf:graph-domain",
    representation_node_id: str = "lean-whnf:graph-representation",
    encoder_node_id: str = "lean-whnf:graph-encoder",
) -> str:
    fields = [
        "HARDNESS_AGENT",
        schema,
        nonce,
        "problem",
        declaration,
        "definition",
        declaration,
        node,
        semantic,
        representation,
        f"encoder identity for {representation}",
        "ComplexityReduction.Encoding.PresentedProblem",
        registered,
        fingerprint,
    ]
    if schema == PROBLEM_CATALOG_SCHEMA:
        fields.extend(
            (
                accepts_summary,
                accepts_node_id,
                domain_summary,
                domain_node_id,
                representation_node_id,
                encoder_node_id,
            )
        )
    return "\t".join(fields)


def catalog_output(*, schema: str = PROBLEM_CATALOG_SCHEMA) -> str:
    return "\n".join(
        [
            registry_row(schema=schema),
            problem_row(
                "ComplexityReduction.Presentation.Graph.problem",
                schema=schema,
            ),
            problem_row(
                "ComplexityReduction.Routes.GraphAlias.sourceProblem",
                schema=schema,
                registered="false",
            ),
            problem_row(
                "ComplexityReduction.Presentation.Clause.problem",
                schema=schema,
                node="lean-whnf:clause",
                semantic="Clause semantic",
                representation="Clause representation",
                accepts_summary="fun input => clause input",
                accepts_node_id="lean-whnf:clause-accepts",
                domain_summary="Clause.Instance",
                domain_node_id="lean-whnf:clause-domain",
                representation_node_id="lean-whnf:clause-representation",
                encoder_node_id="lean-whnf:clause-encoder",
            ),
        ]
    )


def input_observation() -> LeanInputObservation:
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
        semantic_summary="Graph semantic",
        representation_summary="Graph representation",
        predicate_summary=None,
        accepts_summary="fun input => graph input",
        registry_fingerprint="lean:registry",
        failure_code=None,
        explanation=None,
    )


def predicate_observation(*declarations: str) -> LeanInputObservation:
    def match(declaration: str) -> PredicatePresentationMatch:
        if declaration.endswith("OtherCodec.problem"):
            representation_node_id = "lean-whnf:other-representation"
            encoder_node_id = "lean-whnf:other-encoder"
        else:
            representation_node_id = "lean-whnf:graph-representation"
            encoder_node_id = "lean-whnf:graph-encoder"
        return PredicatePresentationMatch(
            candidate_declaration=declaration,
            problem_node_id=(
                "lean-whnf:other-problem"
                if declaration.endswith("OtherCodec.problem")
                else "lean-whnf:source"
            ),
            accepts_node_id="lean-whnf:graph-accepts",
            domain_node_id="lean-whnf:graph-domain",
            representation_node_id=representation_node_id,
            encoder_bound_identity_node_id=encoder_node_id,
            registry_fingerprint="lean:registry",
        )

    return LeanInputObservation(
        input_module="Input.Module",
        input_declaration="Input.Module.graphPredicate",
        declaration_kind="definition",
        supported=True,
        input_kind="predicate",
        elaborated_type="Graph.Instance → Prop",
        whnf_type="Graph.Instance → Prop",
        closed=True,
        universe_parameters=(),
        has_metavariables=False,
        presented_problem_compatible=False,
        predicate_domain="Graph.Instance",
        normalized_problem_node_id=None,
        referenced_constants=(),
        semantic_summary="Graph semantic",
        representation_summary=None,
        predicate_summary="fun input => graph input",
        accepts_summary=None,
        registry_fingerprint="lean:registry",
        failure_code=None,
        explanation=None,
        predicate_domain_node_id="lean-whnf:observed-graph-domain",
        predicate_node_id="lean-whnf:observed-graph-accepts",
        predicate_presentation_matches=tuple(match(item) for item in declarations),
    )


def test_catalog_retains_multiple_public_names_for_one_lean_node() -> None:
    catalog = parse_problem_catalog(
        stdout=catalog_output(),
        stderr="",
        nonce="nonce",
        toolchain="lean-toolchain",
        lake_manifest_sha256="a" * 64,
    )

    exact = search_problems(
        catalog,
        parse_problem_searches({"searches": [{"node_ids": ["lean-whnf:source"]}]}),
    )
    assert [entry.declaration for entry in exact] == [
        "ComplexityReduction.Presentation.Graph.problem",
        "ComplexityReduction.Routes.GraphAlias.sourceProblem",
    ]
    assert all(
        problem_search_result(entry, input_node_id="lean-whnf:source")["exact_defeq"]
        for entry in exact
    )

    hints = build_initial_problem_hints(catalog, input_node_id="lean-whnf:source")
    assert hints["exact_candidate_count"] == 2
    assert not hints["contains_declaration_names"]
    serialized_hints = json.dumps(hints)
    assert "Graph.problem" not in serialized_hints
    assert "sourceProblem" not in serialized_hints


def test_search_supports_accepts_domain_and_representation_nodes() -> None:
    catalog = parse_problem_catalog(stdout=catalog_output(), stderr="", nonce="nonce")
    searches = parse_problem_searches(
        {
            "searches": [
                {
                    "accepts_node_ids": ["lean-whnf:graph-accepts"],
                    "domain_node_ids": ["lean-whnf:graph-domain"],
                    "representation_node_ids": [
                        "lean-whnf:graph-representation"
                    ],
                }
            ]
        }
    )
    results = search_problems(catalog, searches)
    assert len(results) == 2
    assert all(entry.accepts_node_id == "lean-whnf:graph-accepts" for entry in results)


def test_text_search_only_returns_candidates_and_never_claims_exactness() -> None:
    catalog = parse_problem_catalog(stdout=catalog_output(), stderr="", nonce="nonce")
    results = search_problems(
        catalog,
        parse_problem_searches({"searches": [{"terms": ["Clause"]}]}),
    )
    assert len(results) == 1
    summary = problem_search_result(results[0], input_node_id="lean-whnf:source")
    assert summary["declaration"].endswith("Clause.problem")
    assert not summary["exact_defeq"]
    assert not summary["accepts_exact_defeq"]
    assert summary["validation_source"] == "text_retrieval_only"


def test_exact_match_requires_a_retrieved_same_fingerprint_candidate() -> None:
    catalog = parse_problem_catalog(stdout=catalog_output(), stderr="", nonce="nonce")
    candidates = search_problems(
        catalog,
        parse_problem_searches(
            {"searches": [{"node_ids": ["lean-whnf:source"], "limit": 1}]}
        ),
    )
    candidate = candidates[0]
    match = exact_problem_match(
        observation=input_observation(),
        catalog=catalog,
        candidate=candidate,
        retrieved_entries=candidates,
    )
    assert match.relation == "exact_defeq"
    assert match.route_source_declaration == candidate.declaration
    assert match.route_source_node_id == candidate.problem_node_id

    with pytest.raises(ProblemCatalogError, match="not returned"):
        exact_problem_match(
            observation=input_observation(),
            catalog=catalog,
            candidate=candidate,
            retrieved_entries=(),
        )


def test_predicate_exactness_requires_match_row_and_all_catalog_nodes() -> None:
    catalog = parse_problem_catalog(stdout=catalog_output(), stderr="", nonce="nonce")
    graph_names = (
        "ComplexityReduction.Presentation.Graph.problem",
        "ComplexityReduction.Routes.GraphAlias.sourceProblem",
    )
    observation = predicate_observation(*graph_names)
    candidates = predicate_exact_candidates(observation, catalog)
    groups = predicate_presentation_groups(observation, catalog)

    assert [entry.declaration for entry in candidates] == list(graph_names)
    assert len(groups) == 1
    assert groups[0].representative.declaration == graph_names[0]
    assert groups[0].alias_declarations == graph_names
    assert problem_search_result(candidates[0], observation=observation)[
        "accepts_exact_defeq"
    ]

    stale_entry = replace(candidates[0], accepts_node_id="lean-whnf:stale")
    stale_result = problem_search_result(stale_entry, observation=observation)
    assert not stale_result["accepts_exact_defeq"]
    assert stale_result["validation_source"] == "text_retrieval_only"

    hints = build_initial_problem_hints(catalog, observation=observation)
    assert hints["exact_candidate_count"] == 2
    assert hints["predicate_presentation_group_count"] == 1
    assert not hints["predicate_codec_ambiguous"]


def test_exact_predicate_match_deduplicates_aliases_but_rejects_distinct_codecs() -> None:
    graph_names = (
        "ComplexityReduction.Presentation.Graph.problem",
        "ComplexityReduction.Routes.GraphAlias.sourceProblem",
    )
    catalog = parse_problem_catalog(stdout=catalog_output(), stderr="", nonce="nonce")
    observation = predicate_observation(*graph_names)
    candidates = predicate_exact_candidates(observation, catalog)
    match = exact_predicate_problem_match(
        observation=observation,
        catalog=catalog,
        candidate=candidates[1],
        retrieved_entries=candidates,
    )
    assert match.relation == "accepts_exact_defeq"
    assert match.accepts_exact_defeq
    assert not match.exact_defeq
    assert match.route_source_declaration == candidates[1].declaration
    assert match.route_source_node_id == "lean-whnf:source"

    other_name = "ComplexityReduction.Presentation.GraphOtherCodec.problem"
    ambiguous_output = "\n".join(
        [
            catalog_output(),
            problem_row(
                other_name,
                node="lean-whnf:other-problem",
                representation="Other graph representation",
                representation_node_id="lean-whnf:other-representation",
                encoder_node_id="lean-whnf:other-encoder",
            ),
        ]
    )
    ambiguous_catalog = parse_problem_catalog(
        stdout=ambiguous_output,
        stderr="",
        nonce="nonce",
    )
    ambiguous_observation = predicate_observation(*graph_names, other_name)
    ambiguous_candidates = predicate_exact_candidates(
        ambiguous_observation,
        ambiguous_catalog,
    )
    assert len(predicate_presentation_groups(ambiguous_observation, ambiguous_catalog)) == 2
    with pytest.raises(ProblemCatalogError, match="ambiguous"):
        exact_predicate_problem_match(
            observation=ambiguous_observation,
            catalog=ambiguous_catalog,
            candidate=ambiguous_candidates[0],
            retrieved_entries=ambiguous_candidates,
        )


def test_snapshot_rejects_tampering_staleness_and_forbidden_names(tmp_path) -> None:
    catalog = parse_problem_catalog(
        stdout=catalog_output(),
        stderr="",
        nonce="nonce",
        toolchain="lean-toolchain",
        lake_manifest_sha256="a" * 64,
    )
    payload = catalog.to_dict()
    assert problem_catalog_from_dict(payload) == catalog
    snapshot = tmp_path / "problem-catalog.json"
    snapshot.write_text(json.dumps(payload), encoding="utf-8")
    assert (
        load_problem_catalog_snapshot(
            snapshot,
            expected_registry_fingerprint="lean:registry",
            expected_toolchain="lean-toolchain",
            expected_lake_manifest_sha256="a" * 64,
        ).catalog_id
        == catalog.catalog_id
    )
    with pytest.raises(ProblemCatalogError, match="stale problem catalog"):
        load_problem_catalog_snapshot(snapshot, expected_toolchain="other")

    payload["entries"][0]["accepts_node_id"] = "lean-whnf:tampered"
    snapshot.write_text(json.dumps(payload), encoding="utf-8")
    with pytest.raises(ProblemCatalogError, match="content ID"):
        load_problem_catalog_snapshot(snapshot)

    forbidden = "\n".join(
        [
            registry_row(),
            problem_row("ComplexityReduction.Expected.Hidden.problem"),
        ]
    )
    with pytest.raises(ProblemCatalogError, match="forbidden declaration"):
        parse_problem_catalog(stdout=forbidden, stderr="", nonce="nonce")


def test_v1_catalog_snapshot_and_content_ids_remain_valid() -> None:
    catalog = parse_problem_catalog(
        stdout=catalog_output(schema=PROBLEM_CATALOG_SCHEMA_V1),
        stderr="",
        nonce="nonce",
        toolchain="lean-toolchain",
        lake_manifest_sha256="a" * 64,
    )
    legacy_payload = catalog.to_dict(include_catalog_id=False)
    assert "accepts_node_id" not in legacy_payload["entries"][0]
    assert legacy_payload["entries"][0]["entry_id"] == catalog.entries[0].entry_id
    legacy_id = sha256_id(legacy_payload)
    legacy_payload["catalog_id"] = legacy_id

    loaded = problem_catalog_from_dict(legacy_payload)
    assert loaded.schema_version == PROBLEM_CATALOG_SCHEMA_V1
    assert loaded.catalog_id == legacy_id
    assert loaded.to_dict() == legacy_payload
