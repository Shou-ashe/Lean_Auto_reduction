import json

import pytest

from agent.hardness.connection_catalog import ConnectionCatalog, ConnectionCatalogEntry
from agent.hardness.input_observation import (
    LeanInputObservation,
    PredicatePresentationMatch,
)
from agent.hardness.input_planner import (
    OBSERVED_INPUT_SYSTEM_PROMPT,
    InputPlanningError,
    ObservedInputPlanningSession,
    generate_lean_path_from_observed_input,
)
from agent.hardness.model_client import ModelResponse
from agent.hardness.models import TypedCatalog, TypedInventoryEntry
from agent.hardness.problem_catalog import ProblemCatalog, ProblemCatalogEntry


REGISTRY = "lean:registry"
INPUT = "Benchmark.Input.source"
TARGET = "Benchmark.Input.target"
PROBLEM = "ComplexityReduction.Presentation.Source.problem"
ROUTE = "ComplexityReduction.Routes.Example.route"
PREDICATE = "Benchmark.Input.sourcePredicate"
PREDICATE_NODE = "lean-whnf:source-predicate"
PREDICATE_DOMAIN_NODE = "lean-whnf:source-domain"


def observation(
    declaration: str,
    node: str,
    *,
    supported: bool = True,
    fingerprint: str = REGISTRY,
) -> LeanInputObservation:
    return LeanInputObservation(
        input_module="Benchmark.Input",
        input_declaration=declaration,
        declaration_kind="definition",
        supported=supported,
        input_kind="presented_problem" if supported else "closed_prop",
        elaborated_type=(
            "ComplexityReduction.Encoding.PresentedProblem" if supported else "Prop"
        ),
        whnf_type=(
            "ComplexityReduction.Encoding.PresentedProblem" if supported else "Prop"
        ),
        closed=True,
        universe_parameters=(),
        has_metavariables=False,
        presented_problem_compatible=supported,
        predicate_domain=None,
        normalized_problem_node_id=node if supported else None,
        referenced_constants=(),
        semantic_summary="semantic" if supported else None,
        representation_summary="representation" if supported else None,
        predicate_summary=None,
        accepts_summary="fun input => True" if supported else None,
        registry_fingerprint=fingerprint,
        failure_code=None if supported else "closed_prop_not_a_decision_problem",
        explanation=(
            None
            if supported
            else "这个声明只是一个封闭命题，没有实例类型、输入规模和合法编码。"
        ),
    )


def problem_entry(*, node: str = "lean-whnf:source") -> ProblemCatalogEntry:
    return ProblemCatalogEntry(
        declaration=PROBLEM,
        declaration_kind="definition",
        display="source problem",
        problem_node_id=node,
        semantic_summary="semantic",
        representation_summary="representation",
        encoder_bound_identity_summary="encoder identity",
        referenced_constants=(),
        registered=True,
        registry_fingerprint=REGISTRY,
    )


def predicate_problem_entry(
    *,
    declaration: str = PROBLEM,
    node: str = "lean-whnf:source",
    accepts_node: str = PREDICATE_NODE,
    domain_node: str = PREDICATE_DOMAIN_NODE,
    representation_node: str = "lean-whnf:source-representation",
    encoder_node: str = "lean-whnf:source-encoder",
    registered: bool = True,
) -> ProblemCatalogEntry:
    return ProblemCatalogEntry(
        declaration=declaration,
        declaration_kind="definition",
        display="predicate source problem",
        problem_node_id=node,
        semantic_summary="predicate semantics",
        accepts_summary="fun input => source predicate input",
        accepts_node_id=accepts_node,
        domain_summary="SourceInput",
        domain_node_id=domain_node,
        representation_summary="lawful source encoding",
        representation_node_id=representation_node,
        encoder_bound_identity_summary="source encoder identity",
        encoder_bound_identity_node_id=encoder_node,
        referenced_constants=(),
        registered=registered,
        registry_fingerprint=REGISTRY,
    )


def predicate_match(entry: ProblemCatalogEntry) -> PredicatePresentationMatch:
    return PredicatePresentationMatch(
        candidate_declaration=entry.declaration,
        problem_node_id=entry.problem_node_id,
        accepts_node_id=entry.accepts_node_id,
        domain_node_id=entry.domain_node_id,
        representation_node_id=entry.representation_node_id,
        encoder_bound_identity_node_id=entry.encoder_bound_identity_node_id,
        registry_fingerprint=REGISTRY,
    )


def predicate_observation(
    *,
    matches: tuple[PredicatePresentationMatch, ...] = (),
    predicate_node: str = PREDICATE_NODE,
    domain_node: str = PREDICATE_DOMAIN_NODE,
) -> LeanInputObservation:
    return LeanInputObservation(
        input_module="Benchmark.Input",
        input_declaration=PREDICATE,
        declaration_kind="definition",
        supported=True,
        input_kind="predicate",
        elaborated_type="SourceInput → Prop",
        whnf_type="SourceInput → Prop",
        closed=True,
        universe_parameters=(),
        has_metavariables=False,
        presented_problem_compatible=False,
        predicate_domain="SourceInput",
        normalized_problem_node_id=None,
        referenced_constants=(),
        semantic_summary=None,
        representation_summary=None,
        predicate_summary="fun input => source predicate input",
        accepts_summary=None,
        registry_fingerprint=REGISTRY,
        failure_code=None,
        explanation=None,
        predicate_domain_node_id=domain_node,
        predicate_node_id=predicate_node,
        predicate_presentation_matches=matches,
    )


def reduction_entry(
    *,
    source: str = "lean-whnf:source",
    target: str = "lean-whnf:target",
) -> TypedInventoryEntry:
    return TypedInventoryEntry(
        declaration=ROUTE,
        capability_kind="certified_reduction",
        component_role="sharedGadget",
        source_fingerprint=f"lean:{source}",
        target_fingerprint=f"lean:{target}",
        is_final_facade=False,
        discovery="registered",
        registry_fingerprint=REGISTRY,
        source_display="source",
        target_display="target",
        source_node_id=source,
        target_node_id=target,
    )


def catalogs(
    *,
    problem_node: str = "lean-whnf:source",
    reduction_source: str = "lean-whnf:source",
    reduction_target: str = "lean-whnf:target",
    connections: tuple[ConnectionCatalogEntry, ...] = (),
) -> tuple[ProblemCatalog, ConnectionCatalog, TypedCatalog]:
    problem = problem_entry(node=problem_node)
    return (
        ProblemCatalog(registry_fingerprint=REGISTRY, entries=(problem,)),
        ConnectionCatalog(registry_fingerprint=REGISTRY, entries=connections),
        TypedCatalog(
            mode="full",
            registry_fingerprint=REGISTRY,
            entries=(
                reduction_entry(
                    source=reduction_source,
                    target=reduction_target,
                ),
            ),
        ),
    )


def equiv_connection() -> ConnectionCatalogEntry:
    certificate = "ComplexityReduction.Routes.Example.inputEquiv"
    projection = "ComplexityReduction.Certificate.CertifiedEquiv.forwardReduction"
    return ConnectionCatalogEntry(
        certificate_declaration=certificate,
        capability_kind="certified_equiv",
        relation="certified_equiv_forward",
        direction="forward",
        term_kind="fixed_projection",
        projection_declaration=projection,
        lean_term=f"{projection} {certificate}",
        source_fingerprint="lean:input",
        target_fingerprint="lean:library",
        source_node_id="lean-whnf:input",
        target_node_id="lean-whnf:library",
        source_display="input",
        target_display="library problem",
        component_role="ingress",
        registry_fingerprint=REGISTRY,
    )


class FakeClient:
    def __init__(self, payloads: tuple[dict, ...]):
        self.payloads = payloads
        self.call_count = 0
        self.prompts: list[dict] = []

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        assert "write the complete Lean" in system
        assert "JSON" in system
        parsed = json.loads(prompt)
        self.prompts.append(parsed)
        assert "input_observation" in parsed
        assert "full_problem_catalog" not in parsed
        payload = self.payloads[self.call_count]
        self.call_count += 1
        return ModelResponse(
            called=True,
            ok=True,
            content=json.dumps(payload),
            error=None,
            status_code=200,
            duration_seconds=0.01,
            usage={"total_tokens": 10},
            attempts=1,
        )


def test_system_prompt_satisfies_deepseek_json_object_mode() -> None:
    assert "JSON" in OBSERVED_INPUT_SYSTEM_PROMPT


def test_session_uses_observed_source_node_and_records_real_input_in_plan() -> None:
    problem_catalog, connection_catalog, reduction_catalog = catalogs()
    session = ObservedInputPlanningSession(
        observation=observation(INPUT, "lean-whnf:source"),
        target_observation=observation(TARGET, "lean-whnf:target"),
        problem_catalog=problem_catalog,
        connection_catalog=connection_catalog,
        reduction_catalog=reduction_catalog,
    )
    initial_prompt = session.build_prompt()
    assert PROBLEM not in initial_prompt
    assert ROUTE not in initial_prompt
    initial_payload = json.loads(initial_prompt)
    assert initial_payload["connection_hints"]["deferred"] is True
    assert initial_payload["response_options"]["finish"]["field_rules"][
        "connection_entry_id"
    ]["when_exact_defeq"] is None
    assert any(
        "search_reductions" in rule and "search_connections" in rule
        for rule in initial_payload["workflow_rules"]
    )

    session.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": ["lean-whnf:source"]}],
        }
    )
    session.execute_query(
        {
            "action": "search_reductions",
            "searches": [
                {
                    "source_node_ids": ["lean-whnf:source"],
                    "target_node_ids": ["lean-whnf:target"],
                }
            ],
        }
    )
    term = f"ComplexityReduction.Certificate.CertifiedPath.step {ROUTE}"
    result = session.finish(
        {
            "action": "finish",
            "matched_problem": PROBLEM,
            "match_relation": "exact_defeq",
            "connection_entry_id": None,
            "reduction_declarations": [ROUTE],
            "target_declaration": TARGET,
            "lean_term": term,
            "explanation": "The exact input node has a direct existing route.",
        }
    )
    assert result.protocol_accepted
    assert result.plan is not None
    assert result.plan.source_declaration == INPUT
    assert result.plan.matched_problem_declaration == PROBLEM
    assert result.plan.problem_match["relation"] == "exact_defeq"
    assert result.plan.problem_catalog_id == problem_catalog.catalog_id
    assert result.plan.connection_catalog_id == connection_catalog.catalog_id
    assert result.plan.outputs[0].expected_type == (
        "ComplexityReduction.Certificate.CertifiedPath " f"{INPUT} {TARGET}"
    )
    assert result.plan.steps[0].action_kind == "reuse.exact_endpoint"


def test_exact_problem_match_requires_json_null_connection_id() -> None:
    problem_catalog, connection_catalog, reduction_catalog = catalogs()
    session = ObservedInputPlanningSession(
        observation=observation(INPUT, "lean-whnf:source"),
        target_observation=observation(TARGET, "lean-whnf:target"),
        problem_catalog=problem_catalog,
        connection_catalog=connection_catalog,
        reduction_catalog=reduction_catalog,
    )
    session.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": ["lean-whnf:source"]}],
        }
    )
    session.execute_query(
        {
            "action": "search_reductions",
            "searches": [
                {
                    "source_node_ids": ["lean-whnf:source"],
                    "target_node_ids": ["lean-whnf:target"],
                }
            ],
        }
    )
    with pytest.raises(InputPlanningError) as error:
        session.finish(
            {
                "action": "finish",
                "matched_problem": PROBLEM,
                "match_relation": "exact_defeq",
                "connection_entry_id": "null for exact_defeq",
                "reduction_declarations": [ROUTE],
                "target_declaration": TARGET,
                "lean_term": (
                    "ComplexityReduction.Certificate.CertifiedPath.step " + ROUTE
                ),
                "explanation": "Use the exact match and returned reduction.",
            }
        )
    assert error.value.failure_code == "unexpected_connection_for_exact_match"
    assert "JSON null" in error.value.explanation

    with pytest.raises(InputPlanningError) as error:
        session.finish(
            {
                "action": "finish",
                "matched_problem": PROBLEM,
                "match_relation": "exact_defeq",
                "connection_entry_id": None,
                "reduction_declarations": [ROUTE],
                "target_declaration": TARGET,
                "lean_term": ROUTE,
                "explanation": "Use the returned reduction as the path.",
            }
        )
    assert error.value.failure_code == "lean_term_missing_path_constructor"
    assert "CertifiedReduction" in error.value.explanation
    assert "CertifiedPath.step" in error.value.explanation


def test_nondefeq_match_uses_retrieved_fixed_projection_before_reductions() -> None:
    connection = equiv_connection()
    problem_catalog, connection_catalog, reduction_catalog = catalogs(
        problem_node="lean-whnf:library",
        reduction_source="lean-whnf:library",
        connections=(connection,),
    )
    session = ObservedInputPlanningSession(
        observation=observation(INPUT, "lean-whnf:input"),
        target_observation=observation(TARGET, "lean-whnf:target"),
        problem_catalog=problem_catalog,
        connection_catalog=connection_catalog,
        reduction_catalog=reduction_catalog,
    )
    session.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": ["lean-whnf:library"]}],
        }
    )
    session.execute_query(
        {
            "action": "search_connections",
            "searches": [
                {
                    "source_node_ids": ["lean-whnf:input"],
                    "target_node_ids": ["lean-whnf:library"],
                }
            ],
        }
    )
    session.execute_query(
        {
            "action": "search_reductions",
            "searches": [{"source_node_ids": ["lean-whnf:library"]}],
        }
    )
    term = (
        "ComplexityReduction.Certificate.CertifiedPath.cons "
        "(ComplexityReduction.Certificate.CertifiedPath.step "
        f"({connection.lean_term})) {ROUTE}"
    )
    result = session.finish(
        {
            "action": "finish",
            "matched_problem": PROBLEM,
            "match_relation": connection.relation,
            "connection_entry_id": connection.entry_id,
            "reduction_declarations": [ROUTE],
            "target_declaration": TARGET,
            "lean_term": term,
            "explanation": "Use the retrieved equivalence forward, then the route.",
        }
    )
    assert result.protocol_accepted
    assert result.problem_match is not None
    assert result.problem_match.connection_entry_id == connection.entry_id
    assert result.plan is not None
    assert result.plan.steps[0].action_kind == "reuse.certified_equiv.forward"
    assert result.plan.steps[0].parameters["executable_lean_term"] == connection.lean_term


def test_finish_rejects_unretrieved_problem_and_disconnected_route_in_plain_language() -> None:
    problem_catalog, connection_catalog, reduction_catalog = catalogs()
    session = ObservedInputPlanningSession(
        observation=observation(INPUT, "lean-whnf:source"),
        target_observation=observation(TARGET, "lean-whnf:target"),
        problem_catalog=problem_catalog,
        connection_catalog=connection_catalog,
        reduction_catalog=reduction_catalog,
    )
    with pytest.raises(InputPlanningError) as error:
        session.finish(
            {
                "matched_problem": PROBLEM,
                "match_relation": "exact_defeq",
                "connection_entry_id": None,
                "reduction_declarations": [],
                "target_declaration": TARGET,
                "lean_term": (
                    "ComplexityReduction.Certificate.CertifiedPath.refl " + INPUT
                ),
                "explanation": "No route needed.",
            }
        )
    assert error.value.failure_code == "problem_not_retrieved"
    assert "search_problems" in error.value.explanation

    session.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": ["lean-whnf:source"]}],
        }
    )
    with pytest.raises(InputPlanningError) as error:
        session.finish(
            {
                "matched_problem": PROBLEM,
                "match_relation": "exact_defeq",
                "connection_entry_id": None,
                "reduction_declarations": [],
                "target_declaration": TARGET,
                "lean_term": (
                    "ComplexityReduction.Certificate.CertifiedPath.refl " + INPUT
                ),
                "explanation": "No route needed.",
            }
        )
    assert error.value.failure_code == "reduction_path_does_not_reach_target"
    assert "没有到达固定目标" in error.value.explanation


def test_rejected_input_stops_before_model_call_with_original_natural_explanation() -> None:
    problem_catalog, connection_catalog, reduction_catalog = catalogs()
    client = FakeClient(())
    result = generate_lean_path_from_observed_input(
        observation=observation(INPUT, "", supported=False),
        target_observation=observation(TARGET, "lean-whnf:target"),
        problem_catalog=problem_catalog,
        connection_catalog=connection_catalog,
        reduction_catalog=reduction_catalog,
        client=client,  # type: ignore[arg-type]
    )
    assert not result.protocol_accepted
    assert result.failure_code == "closed_prop_not_a_decision_problem"
    assert "实例类型" in result.explanation
    assert client.call_count == 0


def test_model_loop_queries_catalogs_then_submits_its_own_lean_term() -> None:
    problem_catalog, connection_catalog, reduction_catalog = catalogs()
    term = f"ComplexityReduction.Certificate.CertifiedPath.step {ROUTE}"
    client = FakeClient(
        (
            {
                "action": "search_problems",
                "searches": [{"node_ids": ["lean-whnf:source"]}],
            },
            {
                "action": "search_reductions",
                "searches": [
                    {
                        "source_node_ids": ["lean-whnf:source"],
                        "target_node_ids": ["lean-whnf:target"],
                    }
                ],
            },
            {
                "action": "finish",
                "matched_problem": PROBLEM,
                "match_relation": "exact_defeq",
                "connection_entry_id": None,
                "reduction_declarations": [ROUTE],
                "target_declaration": TARGET,
                "lean_term": term,
                "explanation": "Use the exact problem and the retrieved route.",
            },
        )
    )
    result = generate_lean_path_from_observed_input(
        observation=observation(INPUT, "lean-whnf:source"),
        target_observation=observation(TARGET, "lean-whnf:target"),
        problem_catalog=problem_catalog,
        connection_catalog=connection_catalog,
        reduction_catalog=reduction_catalog,
        client=client,  # type: ignore[arg-type]
    )
    assert result.protocol_accepted
    assert result.lean_term == term
    assert len(result.model_responses) == 3
    assert result.plan is not None
    assert result.plan.metadata["query_rounds_used"] == 2


def test_prompt_preserves_an_empty_query_for_the_next_stateless_turn() -> None:
    problem_catalog, connection_catalog, reduction_catalog = catalogs(
        problem_node="lean-whnf:other",
        reduction_source="lean-whnf:other",
    )
    session = ObservedInputPlanningSession(
        observation=observation(INPUT, "lean-whnf:disconnected"),
        target_observation=observation(TARGET, "lean-whnf:target"),
        problem_catalog=problem_catalog,
        connection_catalog=connection_catalog,
        reduction_catalog=reduction_catalog,
    )
    session.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": ["lean-whnf:disconnected"], "limit": 8}],
        }
    )
    prompt = json.loads(session.build_prompt())
    assert prompt["retrieved"]["problems"] == []
    assert prompt["query_history"] == [
        {
            "action": "search_problems",
            "result_count": 0,
            "searches": [
                {
                    "limit": 8,
                    "namespace_prefixes": [],
                    "node_ids": ["lean-whnf:disconnected"],
                    "registered_only": False,
                    "representation_terms": [],
                    "semantic_terms": [],
                    "terms": [],
                }
            ],
        }
    ]


def test_model_receives_non_lean_protocol_feedback_and_can_correct_it() -> None:
    problem_catalog, connection_catalog, reduction_catalog = catalogs(
        reduction_source="lean-whnf:target",
        reduction_target="lean-whnf:source",
    )
    client = FakeClient(
        (
            {
                "action": "search_problems",
                "searches": [{"node_ids": ["lean-whnf:source"]}],
            },
            {
                "action": "stop",
                "failure_code": "no_existing_reduction_route",
                "matched_problem": PROBLEM,
                "match_relation": "exact_defeq",
                "connection_entry_id": None,
                "explanation": "No directed route was returned.",
            },
            {
                "action": "search_reductions",
                "searches": [{"source_node_ids": ["lean-whnf:source"]}],
            },
            {
                "action": "stop",
                "failure_code": "no_existing_reduction_route",
                "matched_problem": PROBLEM,
                "match_relation": "exact_defeq",
                "connection_entry_id": None,
                "explanation": "Only the opposite direction exists.",
            },
        )
    )
    result = generate_lean_path_from_observed_input(
        observation=observation(INPUT, "lean-whnf:source"),
        target_observation=observation(TARGET, "lean-whnf:target"),
        problem_catalog=problem_catalog,
        connection_catalog=connection_catalog,
        reduction_catalog=reduction_catalog,
        client=client,  # type: ignore[arg-type]
    )
    assert result.failure_code == "no_existing_reduction_route"
    assert len(result.model_responses) == 4
    assert client.prompts[2]["protocol_feedback"][-1]["failure_code"] == (
        "model_stop_not_auditable"
    )


def test_model_can_stop_after_auditable_search_finds_no_verified_problem_match() -> None:
    problem_catalog, connection_catalog, reduction_catalog = catalogs(
        problem_node="lean-whnf:other",
        reduction_source="lean-whnf:other",
    )
    client = FakeClient(
        (
            {
                "action": "search_problems",
                "searches": [{"node_ids": ["lean-whnf:disconnected"]}],
            },
            {
                "action": "search_connections",
                "searches": [{"source_node_ids": ["lean-whnf:disconnected"]}],
            },
            {
                "action": "stop",
                "failure_code": "no_lean_verified_problem_match",
                "explanation": "Both exact-node and outgoing-connection searches were empty.",
            },
        )
    )
    result = generate_lean_path_from_observed_input(
        observation=observation(INPUT, "lean-whnf:disconnected"),
        target_observation=observation(TARGET, "lean-whnf:target"),
        problem_catalog=problem_catalog,
        connection_catalog=connection_catalog,
        reduction_catalog=reduction_catalog,
        client=client,  # type: ignore[arg-type]
    )
    assert result.failure_code == "no_lean_verified_problem_match"
    assert "没有与其规范化 node 相同" in result.explanation
    assert result.lean_term is None
    assert len(result.model_responses) == 3


def test_no_route_stop_requires_search_and_is_rejected_when_a_route_exists() -> None:
    problem_catalog, connection_catalog, reverse_catalog = catalogs(
        reduction_source="lean-whnf:target",
        reduction_target="lean-whnf:source",
    )
    session = ObservedInputPlanningSession(
        observation=observation(INPUT, "lean-whnf:source"),
        target_observation=observation(TARGET, "lean-whnf:target"),
        problem_catalog=problem_catalog,
        connection_catalog=connection_catalog,
        reduction_catalog=reverse_catalog,
    )
    session.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": ["lean-whnf:source"]}],
        }
    )
    with pytest.raises(InputPlanningError) as error:
        session.stop(
            {
                "action": "stop",
                "failure_code": "no_existing_reduction_route",
                "matched_problem": PROBLEM,
                "match_relation": "exact_defeq",
                "connection_entry_id": None,
                "explanation": "No forward route was returned.",
            }
        )
    assert error.value.failure_code == "model_stop_not_auditable"

    session.execute_query(
        {
            "action": "search_reductions",
            "searches": [{"source_node_ids": ["lean-whnf:source"]}],
        }
    )
    stopped = session.stop(
        {
            "action": "stop",
            "failure_code": "no_existing_reduction_route",
            "matched_problem": PROBLEM,
            "match_relation": "exact_defeq",
            "connection_entry_id": None,
            "explanation": "Only the opposite direction exists in the catalog.",
        }
    )
    assert stopped.failure_code == "no_existing_reduction_route"
    assert "相反方向" in stopped.explanation

    _, _, forward_catalog = catalogs()
    contradicted = ObservedInputPlanningSession(
        observation=observation(INPUT, "lean-whnf:source"),
        target_observation=observation(TARGET, "lean-whnf:target"),
        problem_catalog=problem_catalog,
        connection_catalog=connection_catalog,
        reduction_catalog=forward_catalog,
    )
    contradicted.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": ["lean-whnf:source"]}],
        }
    )
    contradicted.execute_query(
        {
            "action": "search_reductions",
            "searches": [{"source_node_ids": ["lean-whnf:source"]}],
        }
    )
    with pytest.raises(InputPlanningError) as error:
        contradicted.stop(
            {
                "action": "stop",
                "failure_code": "no_existing_reduction_route",
                "matched_problem": PROBLEM,
                "match_relation": "exact_defeq",
                "connection_entry_id": None,
                "explanation": "No route exists.",
            }
        )
    assert error.value.failure_code == "model_stop_contradicted_by_catalog"


def test_predicate_match_uses_lean_accepts_evidence_and_presented_route_source() -> None:
    problem = predicate_problem_entry()
    source = predicate_observation(matches=(predicate_match(problem),))
    session = ObservedInputPlanningSession(
        observation=source,
        target_observation=observation(TARGET, "lean-whnf:target"),
        problem_catalog=ProblemCatalog(
            registry_fingerprint=REGISTRY,
            entries=(problem,),
        ),
        connection_catalog=ConnectionCatalog(
            registry_fingerprint=REGISTRY,
            entries=(),
        ),
        reduction_catalog=TypedCatalog(
            mode="full",
            registry_fingerprint=REGISTRY,
            entries=(reduction_entry(),),
        ),
    )
    initial = json.loads(session.build_prompt())
    assert initial["expected_lean_type"] == (
        "ComplexityReduction.Certificate.CertifiedPath "
        "<selected PresentedProblem returned by search_problems> "
        f"{TARGET}"
    )
    assert initial["problem_hints"]["match_mode"] == "predicate_accepts"
    assert initial["connection_hints"]["not_applicable"] is True

    searched = session.execute_query(
        {
            "action": "search_problems",
            "searches": [
                {
                    "accepts_node_ids": [PREDICATE_NODE],
                    "domain_node_ids": [PREDICATE_DOMAIN_NODE],
                }
            ],
        }
    )
    assert len(searched["results"]) == 1
    assert searched["results"][0]["exact_defeq"] is False
    assert searched["results"][0]["accepts_exact_defeq"] is True
    assert json.loads(session.build_prompt())["expected_lean_type"] == (
        "ComplexityReduction.Certificate.CertifiedPath " f"{PROBLEM} {TARGET}"
    )
    session.execute_query(
        {
            "action": "search_reductions",
            "searches": [
                {
                    "source_node_ids": [problem.problem_node_id],
                    "target_node_ids": ["lean-whnf:target"],
                }
            ],
        }
    )
    term = f"ComplexityReduction.Certificate.CertifiedPath.step {ROUTE}"
    result = session.finish(
        {
            "action": "finish",
            "matched_problem": PROBLEM,
            "match_relation": "accepts_exact_defeq",
            "connection_entry_id": None,
            "reduction_declarations": [ROUTE],
            "target_declaration": TARGET,
            "lean_term": term,
            "explanation": "Use the Lean-confirmed predicate presentation and route.",
        }
    )
    assert result.protocol_accepted
    assert result.problem_match is not None
    assert result.problem_match.accepts_exact_defeq is True
    assert result.problem_match.route_source_declaration == PROBLEM
    assert result.problem_match.route_source_node_id == problem.problem_node_id
    assert result.plan is not None
    assert result.plan.source_declaration == PROBLEM
    assert result.plan.source_declaration != PREDICATE
    assert result.plan.outputs[0].expected_type == (
        "ComplexityReduction.Certificate.CertifiedPath " f"{PROBLEM} {TARGET}"
    )
    assert result.plan.steps[0].action_kind == "select.existing_problem_presentation"
    assert PREDICATE not in result.plan.steps[0].parameters.values()
    with pytest.raises(InputPlanningError) as error:
        session.finish(
            {
                "action": "finish",
                "matched_problem": PROBLEM,
                "match_relation": "accepts_exact_defeq",
                "connection_entry_id": None,
                "reduction_declarations": [ROUTE],
                "target_declaration": TARGET,
                "lean_term": f"{term} {PREDICATE}",
                "explanation": "Incorrectly use the raw predicate as a path source.",
            }
        )
    assert error.value.failure_code == "predicate_used_as_path_source"


def test_predicate_search_deduplicates_aliases_but_rejects_distinct_codecs() -> None:
    alias = predicate_problem_entry(
        declaration="ComplexityReduction.Presentation.Source.alias",
        registered=False,
    )
    canonical = predicate_problem_entry()
    same_codec_observation = predicate_observation(
        matches=(predicate_match(alias), predicate_match(canonical))
    )
    session = ObservedInputPlanningSession(
        observation=same_codec_observation,
        target_observation=observation(TARGET, "lean-whnf:target"),
        problem_catalog=ProblemCatalog(
            registry_fingerprint=REGISTRY,
            entries=(alias, canonical),
        ),
        connection_catalog=ConnectionCatalog(
            registry_fingerprint=REGISTRY,
            entries=(),
        ),
        reduction_catalog=TypedCatalog(
            mode="full",
            registry_fingerprint=REGISTRY,
            entries=(reduction_entry(),),
        ),
    )
    result = session.execute_query(
        {
            "action": "search_problems",
            "searches": [
                {
                    "accepts_node_ids": [PREDICATE_NODE],
                    "domain_node_ids": [PREDICATE_DOMAIN_NODE],
                }
            ],
        }
    )
    assert [row["declaration"] for row in result["results"]] == [PROBLEM]

    incompatible = predicate_problem_entry(
        declaration="ComplexityReduction.Presentation.Source.binaryProblem",
        node="lean-whnf:binary-source",
        representation_node="lean-whnf:binary-representation",
        encoder_node="lean-whnf:binary-encoder",
    )
    ambiguous_observation = predicate_observation(
        matches=(predicate_match(canonical), predicate_match(incompatible))
    )
    ambiguous = ObservedInputPlanningSession(
        observation=ambiguous_observation,
        target_observation=observation(TARGET, "lean-whnf:target"),
        problem_catalog=ProblemCatalog(
            registry_fingerprint=REGISTRY,
            entries=(canonical, incompatible),
        ),
        connection_catalog=ConnectionCatalog(
            registry_fingerprint=REGISTRY,
            entries=(),
        ),
        reduction_catalog=TypedCatalog(
            mode="full",
            registry_fingerprint=REGISTRY,
            entries=(reduction_entry(),),
        ),
    )
    ambiguous.execute_query(
        {
            "action": "search_problems",
            "searches": [
                {
                    "accepts_node_ids": [PREDICATE_NODE],
                    "domain_node_ids": [PREDICATE_DOMAIN_NODE],
                }
            ],
        }
    )
    stopped = ambiguous.stop(
        {
            "action": "stop",
            "failure_code": "ambiguous_predicate_presentation",
            "explanation": "Two incompatible encoder identities were returned.",
        }
    )
    assert stopped.failure_code == "ambiguous_predicate_presentation"
    with pytest.raises(InputPlanningError) as error:
        ambiguous.finish(
            {
                "action": "finish",
                "matched_problem": PROBLEM,
                "match_relation": "accepts_exact_defeq",
                "connection_entry_id": None,
                "reduction_declarations": [],
                "target_declaration": TARGET,
                "lean_term": (
                    "ComplexityReduction.Certificate.CertifiedPath.refl " + PROBLEM
                ),
                "explanation": "Choose one codec by declaration order.",
            }
        )
    assert error.value.failure_code == "ambiguous_predicate_presentation"


@pytest.mark.parametrize(
    ("catalog_domain", "failure_code"),
    (
        (
            PREDICATE_DOMAIN_NODE,
            "predicate_accepts_not_definitionally_equal",
        ),
        (
            "lean-whnf:unrelated-domain",
            "predicate_has_no_lawful_presentation",
        ),
    ),
)
def test_predicate_negative_stops_require_predicate_and_domain_queries(
    catalog_domain: str,
    failure_code: str,
) -> None:
    problem = predicate_problem_entry(
        accepts_node="lean-whnf:different-accepts",
        domain_node=catalog_domain,
    )
    session = ObservedInputPlanningSession(
        observation=predicate_observation(),
        target_observation=observation(TARGET, "lean-whnf:target"),
        problem_catalog=ProblemCatalog(
            registry_fingerprint=REGISTRY,
            entries=(problem,),
        ),
        connection_catalog=ConnectionCatalog(
            registry_fingerprint=REGISTRY,
            entries=(),
        ),
        reduction_catalog=TypedCatalog(
            mode="full",
            registry_fingerprint=REGISTRY,
            entries=(reduction_entry(),),
        ),
    )
    with pytest.raises(InputPlanningError) as error:
        session.stop(
            {
                "action": "stop",
                "failure_code": failure_code,
                "explanation": "No Lean-confirmed presentation was returned.",
            }
        )
    assert error.value.failure_code == "model_stop_not_auditable"
    session.execute_query(
        {
            "action": "search_problems",
            "searches": [
                {
                    "accepts_node_ids": [PREDICATE_NODE],
                    "domain_node_ids": [PREDICATE_DOMAIN_NODE],
                },
                {"domain_node_ids": [PREDICATE_DOMAIN_NODE]},
            ],
        }
    )
    stopped = session.stop(
        {
            "action": "stop",
            "failure_code": failure_code,
            "explanation": "The accepts and domain searches establish the failure.",
        }
    )
    assert stopped.failure_code == failure_code
