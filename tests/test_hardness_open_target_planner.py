import json
from dataclasses import replace

import pytest

from agent.hardness.connection_catalog import ConnectionCatalog, ConnectionCatalogEntry
from agent.hardness.hardness_target_catalog import (
    HardnessTargetCatalog,
    HardnessTargetCatalogEntry,
    HardnessTargetEvidence,
)
from agent.hardness.input_observation import (
    LeanInputObservation,
    PredicatePresentationMatch,
)
from agent.hardness.input_planner import MAX_INPUT_PROTOCOL_FEEDBACK, InputPlanningError
from agent.hardness.model_client import ModelResponse
from agent.hardness.models import TypedCatalog, TypedInventoryEntry
from agent.hardness.open_target_planner import (
    MAX_KNOWN_HARDNESS_PROTOCOL_FEEDBACK,
    MAX_KNOWN_HARDNESS_RETRIEVED_REDUCTIONS,
    OPEN_TARGET_SYSTEM_PROMPT,
    OpenTargetPlanningSession,
    OpenTargetRequestPolicy,
    generate_lean_path_to_open_target,
)
from agent.hardness.open_target_simulation import SimulatedOpenTargetClient
from agent.hardness.problem_catalog import (
    ProblemCatalog,
    ProblemCatalogEntry,
    problem_search_result,
)


REGISTRY = "lean:stage-g"
INPUT = "Benchmark.Input.source"
PROBLEM = "ComplexityReduction.Problems.Source.problem"
TARGET = "ComplexityReduction.Problems.Target.problem"
EVIDENCE = "ComplexityReduction.Evidence.targetNativeNP"
ROUTE = "ComplexityReduction.Routes.SourceToTarget.route"
SOURCE_NODE = "lean-whnf:source"
TARGET_NODE = "lean-whnf:target"
MIDDLE_NODE = "lean-whnf:middle"
INPUT_NODE = "lean-whnf:input"
PREDICATE = "Benchmark.Input.sourcePredicate"
PREDICATE_NODE = "lean-whnf:source-predicate"
DOMAIN_NODE = "lean-whnf:source-domain"
REPRESENTATION_NODE = "lean-whnf:source-representation"
ENCODER_NODE = "lean-whnf:source-encoder"


def observation(*, fingerprint: str = REGISTRY) -> LeanInputObservation:
    return LeanInputObservation(
        input_module="Benchmark.Input",
        input_declaration=INPUT,
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
        normalized_problem_node_id=SOURCE_NODE,
        referenced_constants=(),
        semantic_summary="source semantic",
        representation_summary="source representation",
        predicate_summary=None,
        accepts_summary="fun input => True",
        registry_fingerprint=fingerprint,
        failure_code=None,
        explanation=None,
    )


def problem_catalog() -> ProblemCatalog:
    return ProblemCatalog(
        registry_fingerprint=REGISTRY,
        entries=(
            ProblemCatalogEntry(
                declaration=PROBLEM,
                declaration_kind="definition",
                display="source problem",
                problem_node_id=SOURCE_NODE,
                semantic_summary="source semantic",
                representation_summary="source representation",
                encoder_bound_identity_summary="source codec",
                referenced_constants=(),
                registered=True,
                registry_fingerprint=REGISTRY,
            ),
        ),
    )


def predicate_problem(
    *,
    declaration: str = PROBLEM,
    problem_node: str = SOURCE_NODE,
    accepts_node: str = PREDICATE_NODE,
    representation_node: str = REPRESENTATION_NODE,
    encoder_node: str = ENCODER_NODE,
) -> ProblemCatalogEntry:
    return ProblemCatalogEntry(
        declaration=declaration,
        declaration_kind="definition",
        display="source predicate presentation",
        problem_node_id=problem_node,
        semantic_summary="source predicate semantic",
        representation_summary="source predicate representation",
        encoder_bound_identity_summary="source predicate codec",
        referenced_constants=(),
        registered=True,
        registry_fingerprint=REGISTRY,
        accepts_summary="fun input => sourcePredicate input",
        accepts_node_id=accepts_node,
        domain_summary="Benchmark.Input.Source",
        domain_node_id=DOMAIN_NODE,
        representation_node_id=representation_node,
        encoder_bound_identity_node_id=encoder_node,
    )


def predicate_observation(
    *, matches: tuple[PredicatePresentationMatch, ...]
) -> LeanInputObservation:
    return LeanInputObservation(
        input_module="Benchmark.Input",
        input_declaration=PREDICATE,
        declaration_kind="definition",
        supported=True,
        input_kind="predicate",
        elaborated_type="Benchmark.Input.Source → Prop",
        whnf_type="Benchmark.Input.Source → Prop",
        closed=True,
        universe_parameters=(),
        has_metavariables=False,
        presented_problem_compatible=False,
        predicate_domain="Benchmark.Input.Source",
        normalized_problem_node_id=None,
        referenced_constants=(),
        semantic_summary=None,
        representation_summary=None,
        predicate_summary="fun input => sourcePredicate input",
        accepts_summary=None,
        registry_fingerprint=REGISTRY,
        failure_code=None,
        explanation=None,
        predicate_domain_node_id=DOMAIN_NODE,
        predicate_node_id=PREDICATE_NODE,
        predicate_presentation_matches=matches,
    )


def predicate_match(
    entry: ProblemCatalogEntry,
) -> PredicatePresentationMatch:
    return PredicatePresentationMatch(
        candidate_declaration=entry.declaration,
        problem_node_id=entry.problem_node_id,
        accepts_node_id=entry.accepts_node_id,
        domain_node_id=entry.domain_node_id,
        representation_node_id=entry.representation_node_id,
        encoder_bound_identity_node_id=entry.encoder_bound_identity_node_id,
        registry_fingerprint=REGISTRY,
    )


def predicate_session(
    *,
    entries: tuple[ProblemCatalogEntry, ...],
    matches: tuple[PredicatePresentationMatch, ...],
    targets: HardnessTargetCatalog | None = None,
    reductions: TypedCatalog | None = None,
) -> OpenTargetPlanningSession:
    return OpenTargetPlanningSession(
        observation=predicate_observation(matches=matches),
        problem_catalog=ProblemCatalog(
            registry_fingerprint=REGISTRY,
            entries=entries,
        ),
        connection_catalog=ConnectionCatalog(
            registry_fingerprint=REGISTRY,
            entries=(),
        ),
        reduction_catalog=reductions or reduction_catalog(),
        target_catalog=targets or target_catalog(),
        request_policy=policy(),
    )


def membership_evidence() -> HardnessTargetEvidence:
    return HardnessTargetEvidence(
        target_declaration=TARGET,
        target_node_id=TARGET_NODE,
        evidence_kind="native_membership",
        evidence_declaration=EVIDENCE,
        evidence_lean_term=EVIDENCE,
        membership_lean_term=EVIDENCE,
        satisfied_policies=("native_np",),
        validation_source="lean_registry_elaborated_type",
        provenance_declarations=(EVIDENCE,),
        registry_fingerprint=REGISTRY,
    )


def target_catalog(
    *, evidence: HardnessTargetEvidence | None = None
) -> HardnessTargetCatalog:
    selected = evidence or membership_evidence()
    return HardnessTargetCatalog(
        registry_fingerprint=REGISTRY,
        entries=(
            HardnessTargetCatalogEntry(
                target_declaration=TARGET,
                target_display="target problem",
                target_node_id=TARGET_NODE,
                target_namespace="ComplexityReduction.Problems.Target",
                registry_fingerprint=REGISTRY,
                evidences=(selected,),
            ),
        ),
    )


def reduction(
    *,
    source: str = SOURCE_NODE,
    target: str = TARGET_NODE,
    declaration: str = ROUTE,
) -> TypedInventoryEntry:
    return TypedInventoryEntry(
        declaration=declaration,
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


def direct_connection(
    *,
    source: str = SOURCE_NODE,
    target: str = TARGET_NODE,
    declaration: str = ROUTE,
) -> ConnectionCatalogEntry:
    return ConnectionCatalogEntry(
        certificate_declaration=declaration,
        capability_kind="certified_reduction",
        relation="existing_reduction",
        direction="forward",
        term_kind="certificate",
        projection_declaration=declaration,
        lean_term=declaration,
        source_fingerprint=f"lean:{source}",
        target_fingerprint=f"lean:{target}",
        source_node_id=source,
        target_node_id=target,
        source_display="source",
        target_display="target",
        component_role="sharedGadget",
        registry_fingerprint=REGISTRY,
    )


def reduction_catalog(
    *, source: str = SOURCE_NODE, target: str = TARGET_NODE
) -> TypedCatalog:
    return TypedCatalog(
        mode="full",
        registry_fingerprint=REGISTRY,
        entries=(reduction(source=source, target=target),),
    )


def policy(
    *,
    required: str = "native_np",
    allowed: tuple[str, ...] = ("native_membership",),
    maximum_route_atoms: int = 3,
    maximum_dependencies: int = 8,
    allow_reflexive_target: bool = True,
) -> OpenTargetRequestPolicy:
    return OpenTargetRequestPolicy(
        required_hardness=required,
        allowed_target_evidence=allowed,
        maximum_route_atoms=maximum_route_atoms,
        maximum_dependencies=maximum_dependencies,
        allow_reflexive_target=allow_reflexive_target,
    )


def session(
    *,
    targets: HardnessTargetCatalog | None = None,
    connections: ConnectionCatalog | None = None,
    reductions: TypedCatalog | None = None,
    request: OpenTargetRequestPolicy | None = None,
) -> OpenTargetPlanningSession:
    return OpenTargetPlanningSession(
        observation=observation(),
        problem_catalog=problem_catalog(),
        connection_catalog=connections
        or ConnectionCatalog(registry_fingerprint=REGISTRY, entries=()),
        reduction_catalog=reductions or reduction_catalog(),
        target_catalog=targets or target_catalog(),
        request_policy=request or policy(),
    )


def retrieve_positive(session: OpenTargetPlanningSession) -> None:
    session.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": [SOURCE_NODE], "limit": 8}],
        }
    )
    session.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"], "limit": 8}],
        }
    )
    session.execute_query(
        {
            "action": "search_reductions",
            "searches": [
                {
                    "source_node_ids": [SOURCE_NODE],
                    "target_node_ids": [TARGET_NODE],
                    "limit": 8,
                }
            ],
        }
    )


def test_system_prompt_requires_json_and_model_target_selection() -> None:
    assert "JSON" in OPEN_TARGET_SYSTEM_PROMPT
    assert "search_hardness_targets" in OPEN_TARGET_SYSTEM_PROMPT
    assert "terminal_guidance.mode is finish_now" in OPEN_TARGET_SYSTEM_PROMPT


def test_prompt_documents_problem_string_and_object_selectors() -> None:
    contracts = session().prompt_payload()["response_options"]["field_contracts"]
    problem_contract = contracts["matched_problem"]
    assert "entry_id/declaration string" in problem_contract
    assert "object" in problem_contract
    assert "same row" in problem_contract
    connection_contract = contracts["connection_entry_id"]
    assert "JSON null is recommended" in connection_contract
    assert "whitespace-only" in connection_contract


@pytest.mark.parametrize(
    "evidence_kind",
    (
        "registered_native_membership",
        "registered_native_completeness",
        "native_completeness_projection",
        "transported_native_completeness",
    ),
)
def test_open_target_policy_rejects_schema_compatible_unemittable_evidence(
    evidence_kind: str,
) -> None:
    with pytest.raises(ValueError, match="cannot emit"):
        policy(allowed=(evidence_kind,))


def test_known_np_policy_rejects_transported_hardness() -> None:
    with pytest.raises(ValueError, match="cannot emit"):
        policy(allowed=("transported_native_hardness",))


def test_known_hardness_policy_accepts_transported_hardness() -> None:
    request = OpenTargetRequestPolicy(
        required_hardness="native_np_hard",
        allowed_target_evidence=("transported_native_hardness",),
        minimum_route_atoms=5,
        maximum_route_atoms=6,
        maximum_dependencies=12,
        allow_reflexive_target=False,
        require_simple_path=True,
        objective="reduce_to_known_hardness",
    )

    assert request.allowed_target_evidence == ("transported_native_hardness",)
    assert request.minimum_route_atoms == 5
    assert request.require_simple_path is True


def test_known_hardness_session_has_a_scoped_long_route_retrieval_budget() -> None:
    known_np = session()
    known_hardness = session(
        request=OpenTargetRequestPolicy(
            required_hardness="native_np_hard",
            allowed_target_evidence=("transported_native_hardness",),
            minimum_route_atoms=5,
            maximum_route_atoms=6,
            maximum_dependencies=16,
            allow_reflexive_target=False,
            require_simple_path=True,
            objective="reduce_to_known_hardness",
        )
    )

    assert known_np.maximum_retrieved_reductions < (
        known_hardness.maximum_retrieved_reductions
    )
    assert (
        known_hardness.maximum_retrieved_reductions
        == MAX_KNOWN_HARDNESS_RETRIEVED_REDUCTIONS
    )


def test_known_hardness_session_has_a_scoped_protocol_feedback_budget() -> None:
    known_np = session()
    known_hardness = session(
        request=OpenTargetRequestPolicy(
            required_hardness="native_np_hard",
            allowed_target_evidence=("transported_native_hardness",),
            minimum_route_atoms=5,
            maximum_route_atoms=6,
            maximum_dependencies=16,
            allow_reflexive_target=False,
            require_simple_path=True,
            objective="reduce_to_known_hardness",
        )
    )

    assert known_np.maximum_protocol_feedback == MAX_INPUT_PROTOCOL_FEEDBACK
    assert (
        known_hardness.maximum_protocol_feedback
        == MAX_KNOWN_HARDNESS_PROTOCOL_FEEDBACK
    )
    assert (
        known_hardness.maximum_protocol_feedback
        > known_np.maximum_protocol_feedback
    )


def test_compact_retrieved_view_is_scoped_to_known_hardness() -> None:
    known_np_payload = session().prompt_payload()
    known_hardness_payload = session(
        request=OpenTargetRequestPolicy(
            required_hardness="native_np_hard",
            allowed_target_evidence=("transported_native_hardness",),
            minimum_route_atoms=5,
            maximum_route_atoms=6,
            maximum_dependencies=16,
            allow_reflexive_target=False,
            require_simple_path=True,
            objective="reduce_to_known_hardness",
        )
    ).prompt_payload()

    assert "retrieved_view" not in known_np_payload
    assert "frontier_guidance" not in known_np_payload
    assert "terminal_guidance" not in known_np_payload
    assert "terminal_guidance" not in known_hardness_payload
    assert known_hardness_payload["frontier_guidance"]["frontier_nodes"] == []
    assert known_hardness_payload["frontier_guidance"]["suggested_searches"] == []
    assert known_hardness_payload["retrieved_view"] == {
        "schema_version": "hardness_retrieved_compact_v1",
        "mode": "authorization_complete_compact",
        "complete_objects_retained_by_agent": True,
        "finish_selectors_hydrated_and_validated_by_agent": True,
        "selection_and_topology_fields_complete": True,
        "verbose_descriptions_omitted": True,
        "counts": {
            "problems": 0,
            "connections": 0,
            "hardness_targets": 0,
            "reductions": 0,
        },
    }


def _transported_hardness_evidence(
    *, provenance: tuple[str, ...] = ("ComplexityReduction.Evidence.transport",)
) -> HardnessTargetEvidence:
    return HardnessTargetEvidence(
        target_declaration=TARGET,
        target_node_id=TARGET_NODE,
        evidence_kind="transported_native_hardness",
        evidence_declaration="ComplexityReduction.Evidence.transportedHardness",
        evidence_lean_term="ComplexityReduction.Evidence.transportedHardness",
        membership_lean_term="",
        satisfied_policies=("native_np_hard",),
        validation_source="lean_registry_transported_hardness",
        provenance_declarations=provenance,
        registry_fingerprint=REGISTRY,
    )


def _known_hardness_policy(
    *, minimum: int = 2, maximum: int = 6, dependencies: int = 16
) -> OpenTargetRequestPolicy:
    return OpenTargetRequestPolicy(
        required_hardness="native_np_hard",
        allowed_target_evidence=("transported_native_hardness",),
        minimum_route_atoms=minimum,
        maximum_route_atoms=maximum,
        maximum_dependencies=dependencies,
        allow_reflexive_target=False,
        require_simple_path=True,
        objective="reduce_to_known_hardness",
    )


def test_known_hardness_frontier_guidance_prefers_incomplete_source_only_searches() -> None:
    first = reduction(source=SOURCE_NODE, target=MIDDLE_NODE, declaration="Route.first")
    second = reduction(source=MIDDLE_NODE, target=TARGET_NODE, declaration="Route.second")
    current = session(
        targets=target_catalog(evidence=_transported_hardness_evidence()),
        reductions=TypedCatalog(
            mode="full",
            registry_fingerprint=REGISTRY,
            entries=(first, second),
        ),
        request=_known_hardness_policy(),
    )
    current.search_problems(
        {"searches": [{"node_ids": [SOURCE_NODE], "limit": 8}]}
    )
    initial = current.prompt_payload()["frontier_guidance"]
    assert initial["suggested_searches"] == [
        {"source_node_ids": [SOURCE_NODE], "limit": 8}
    ]

    current.search_reductions(
        {
            "searches": [
                {
                    "source_node_ids": [SOURCE_NODE],
                    "target_node_ids": [TARGET_NODE],
                    "limit": 8,
                }
            ]
        }
    )
    after_filtered = current.prompt_payload()["frontier_guidance"]
    assert after_filtered["suggested_searches"] == [
        {"source_node_ids": [SOURCE_NODE], "limit": 8}
    ]

    current.search_reductions(
        {"searches": [{"source_node_ids": [SOURCE_NODE], "limit": 8}]}
    )
    after_source_only = current.prompt_payload()["frontier_guidance"]
    assert SOURCE_NODE in current.source_only_queried_reduction_source_node_ids
    assert SOURCE_NODE in current.fully_queried_reduction_source_node_ids
    assert after_source_only["suggested_searches"] == [
        {"source_node_ids": [MIDDLE_NODE], "limit": 8}
    ]


def test_known_hardness_rejects_an_exact_repeated_reduction_search() -> None:
    current = session(
        targets=target_catalog(evidence=_transported_hardness_evidence()),
        request=_known_hardness_policy(minimum=1),
    )
    query = {"searches": [{"source_node_ids": [SOURCE_NODE], "limit": 8}]}
    current.search_reductions(query)

    with pytest.raises(InputPlanningError) as error:
        current.search_reductions(query)

    assert error.value.failure_code == "repeated_reduction_search"
    assert current.query_rounds_used == 1


def test_known_hardness_terminal_guidance_stops_when_no_evidence_is_eligible() -> None:
    evidence = _transported_hardness_evidence(
        provenance=("Dependency.one", "Dependency.two", "Dependency.three")
    )
    current = session(
        targets=target_catalog(evidence=evidence),
        request=_known_hardness_policy(dependencies=1),
    )
    current.search_hardness_targets(
        {"searches": [{"required_policies": ["native_np_hard"], "limit": 8}]}
    )

    terminal = current.prompt_payload()["terminal_guidance"]

    assert terminal["mode"] == "stop_now"
    assert terminal["failure_code"] == "no_eligible_hardness_target"
    assert terminal["selector_fields_required"] == []


def test_known_hardness_terminal_guidance_stops_after_audited_no_route() -> None:
    current = session(
        targets=target_catalog(evidence=_transported_hardness_evidence()),
        reductions=TypedCatalog(
            mode="full", registry_fingerprint=REGISTRY, entries=()
        ),
        request=_known_hardness_policy(minimum=1),
    )
    current.search_problems(
        {"searches": [{"node_ids": [SOURCE_NODE], "limit": 8}]}
    )
    current.search_hardness_targets(
        {"searches": [{"required_policies": ["native_np_hard"], "limit": 8}]}
    )
    current.search_reductions(
        {"searches": [{"source_node_ids": [SOURCE_NODE], "limit": 8}]}
    )

    terminal = current.prompt_payload()["terminal_guidance"]

    assert terminal["mode"] == "stop_now"
    assert terminal["failure_code"] == "eligible_target_has_no_existing_route"
    assert terminal["selector_fields_required"] == [
        "matched_problem",
        "match_relation",
        "connection_entry_id",
    ]


def test_initial_prompt_contains_policy_but_no_target_or_evidence_declaration() -> None:
    current = session()
    prompt = current.build_prompt()
    assert TARGET not in prompt
    assert EVIDENCE not in prompt
    payload = json.loads(prompt)
    assert payload["request"]["required_hardness"] == "native_np"
    assert payload["hardness_target_hints"]["full_target_catalog_included"] is False
    assert payload["constraints"]["target_routes_are_not_included"] is True
    assert payload["lean_path_api"]["zero_edges"] == (
        "ComplexityReduction.Certificate.CertifiedPath.refl " + INPUT
    )


def test_predicate_prompt_queries_accepts_and_domain_without_using_raw_path_source() -> None:
    entry = predicate_problem()
    current = predicate_session(entries=(entry,), matches=(predicate_match(entry),))

    payload = current.prompt_payload()

    assert payload["problem_hints"]["match_mode"] == "predicate_accepts"
    assert payload["expected_lean_type_template"] == (
        "ComplexityReduction.Certificate.CertifiedPath "
        "<selected PresentedProblem returned by search_problems> "
        "<selected target declaration>"
    )
    assert payload["response_options"]["search_problems"]["searches"] == [
        {
            "accepts_node_ids": [PREDICATE_NODE],
            "domain_node_ids": [DOMAIN_NODE],
            "limit": 8,
        },
        {"domain_node_ids": [DOMAIN_NODE], "limit": 8},
    ]
    assert PREDICATE not in payload["lean_path_api"]["zero_edges"]


def test_predicate_open_target_uses_selected_presentation_as_plan_source() -> None:
    entry = predicate_problem()
    result = generate_lean_path_to_open_target(
        observation=predicate_observation(matches=(predicate_match(entry),)),
        problem_catalog=ProblemCatalog(
            registry_fingerprint=REGISTRY,
            entries=(entry,),
        ),
        connection_catalog=ConnectionCatalog(
            registry_fingerprint=REGISTRY,
            entries=(),
        ),
        reduction_catalog=reduction_catalog(),
        target_catalog=target_catalog(),
        request_policy=policy(),
        client=SimulatedOpenTargetClient(),  # type: ignore[arg-type]
    )

    assert result.protocol_accepted
    assert result.problem_match is not None
    assert result.problem_match.accepts_exact_defeq
    assert result.problem_match.relation == "accepts_exact_defeq"
    assert result.plan is not None
    assert result.plan.source_declaration == PROBLEM
    assert result.lean_term is not None
    assert PREDICATE not in result.lean_term
    assert len(result.model_responses) > 0


@pytest.mark.parametrize(
    ("entries", "matches", "failure_code"),
    (
        (
            (predicate_problem(accepts_node="lean-whnf:different-accepts"),),
            (),
            "predicate_accepts_not_definitionally_equal",
        ),
        ((), (), "predicate_has_no_lawful_presentation"),
    ),
)
def test_predicate_open_target_reports_grounding_blocker_after_model_query(
    entries: tuple[ProblemCatalogEntry, ...],
    matches: tuple[PredicatePresentationMatch, ...],
    failure_code: str,
) -> None:
    result = generate_lean_path_to_open_target(
        observation=predicate_observation(matches=matches),
        problem_catalog=ProblemCatalog(
            registry_fingerprint=REGISTRY,
            entries=entries,
        ),
        connection_catalog=ConnectionCatalog(
            registry_fingerprint=REGISTRY,
            entries=(),
        ),
        reduction_catalog=reduction_catalog(),
        target_catalog=target_catalog(),
        request_policy=policy(),
        client=SimulatedOpenTargetClient(),  # type: ignore[arg-type]
    )

    assert result.failure_code == failure_code
    assert len(result.model_responses) > 0


def test_predicate_open_target_rejects_multiple_encoder_identities() -> None:
    first = predicate_problem()
    second = predicate_problem(
        declaration="ComplexityReduction.Problems.Source.alternate",
        problem_node="lean-whnf:alternate-source",
        representation_node="lean-whnf:alternate-representation",
        encoder_node="lean-whnf:alternate-encoder",
    )
    result = generate_lean_path_to_open_target(
        observation=predicate_observation(
            matches=(predicate_match(first), predicate_match(second))
        ),
        problem_catalog=ProblemCatalog(
            registry_fingerprint=REGISTRY,
            entries=(first, second),
        ),
        connection_catalog=ConnectionCatalog(
            registry_fingerprint=REGISTRY,
            entries=(),
        ),
        reduction_catalog=reduction_catalog(),
        target_catalog=target_catalog(),
        request_policy=policy(),
        client=SimulatedOpenTargetClient(),  # type: ignore[arg-type]
    )

    assert result.failure_code == "ambiguous_predicate_presentation"
    assert len(result.model_responses) > 0


def test_target_search_exposes_evidence_specific_policy_route_decision() -> None:
    dependency_limited = session(request=policy(maximum_dependencies=1))
    response = dependency_limited.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"]}],
        }
    )
    evidence = response["results"][0]["evidences"][0]
    assert evidence["request_eligible"] is True
    assert evidence["policy_route_allowed"] is False
    assert evidence["shortest_policy_route_atom_count"] is None
    assert response["results"][0]["policy_route_allowed"] is False
    assert ROUTE not in json.dumps(response, sort_keys=True)

    atom_limited = session(request=policy(maximum_route_atoms=0))
    response = atom_limited.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"]}],
        }
    )
    assert response["results"][0]["evidences"][0][
        "policy_route_allowed"
    ] is False


def test_target_search_policy_route_honors_reflexive_flag() -> None:
    reflexive_declaration = "ComplexityReduction.Problems.Reflexive.problem"
    reflexive_evidence_declaration = (
        "ComplexityReduction.Evidence.reflexiveNativeNP"
    )
    reflexive_evidence = HardnessTargetEvidence(
        target_declaration=reflexive_declaration,
        target_node_id=SOURCE_NODE,
        evidence_kind="native_membership",
        evidence_declaration=reflexive_evidence_declaration,
        evidence_lean_term=reflexive_evidence_declaration,
        membership_lean_term=reflexive_evidence_declaration,
        satisfied_policies=("native_np",),
        validation_source="lean_registry_elaborated_type",
        provenance_declarations=(reflexive_evidence_declaration,),
        registry_fingerprint=REGISTRY,
    )
    targets = HardnessTargetCatalog(
        registry_fingerprint=REGISTRY,
        entries=(
            HardnessTargetCatalogEntry(
                target_declaration=reflexive_declaration,
                target_display="reflexive problem",
                target_node_id=SOURCE_NODE,
                target_namespace="ComplexityReduction.Problems.Reflexive",
                registry_fingerprint=REGISTRY,
                evidences=(reflexive_evidence,),
            ),
        ),
    )
    forbidden = session(
        targets=targets,
        reductions=TypedCatalog(mode="full", registry_fingerprint=REGISTRY, entries=()),
        request=policy(allow_reflexive_target=False),
    )
    forbidden_result = forbidden.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"]}],
        }
    )
    forbidden_evidence = forbidden_result["results"][0]["evidences"][0]
    assert forbidden_evidence["policy_route_allowed"] is False

    allowed = session(
        targets=targets,
        reductions=TypedCatalog(mode="full", registry_fingerprint=REGISTRY, entries=()),
        request=policy(allow_reflexive_target=True),
    )
    allowed_result = allowed.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"]}],
        }
    )
    allowed_evidence = allowed_result["results"][0]["evidences"][0]
    assert allowed_evidence["policy_route_allowed"] is True
    assert allowed_evidence["shortest_policy_route_atom_count"] == 0


def test_target_search_policy_route_counts_input_connection_atoms_and_dependencies() -> None:
    certificate = "ComplexityReduction.Routes.Input.inputEquiv"
    projection = "ComplexityReduction.Certificate.CertifiedEquiv.forwardReduction"
    connection = ConnectionCatalogEntry(
        certificate_declaration=certificate,
        capability_kind="certified_equiv",
        relation="certified_equiv_forward",
        direction="forward",
        term_kind="fixed_projection",
        projection_declaration=projection,
        lean_term=f"{projection} {certificate}",
        source_fingerprint="lean:input",
        target_fingerprint="lean:source",
        source_node_id=INPUT_NODE,
        target_node_id=SOURCE_NODE,
        source_display="input",
        target_display="source problem",
        component_role="ingress",
        registry_fingerprint=REGISTRY,
    )

    def connected_session(request: OpenTargetRequestPolicy) -> OpenTargetPlanningSession:
        connected_observation = replace(
            observation(),
            normalized_problem_node_id=INPUT_NODE,
        )
        return OpenTargetPlanningSession(
            observation=connected_observation,
            problem_catalog=problem_catalog(),
            connection_catalog=ConnectionCatalog(
                registry_fingerprint=REGISTRY,
                entries=(connection,),
            ),
            reduction_catalog=reduction_catalog(),
            target_catalog=target_catalog(),
            request_policy=request,
        )

    dependency_limited = connected_session(
        policy(maximum_route_atoms=2, maximum_dependencies=3)
    )
    response = dependency_limited.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"]}],
        }
    )
    evidence = response["results"][0]["evidences"][0]
    assert evidence["request_eligible"] is True
    assert evidence["policy_route_allowed"] is False

    allowed = connected_session(
        policy(maximum_route_atoms=2, maximum_dependencies=4)
    )
    response = allowed.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"]}],
        }
    )
    evidence = response["results"][0]["evidences"][0]
    assert evidence["policy_route_allowed"] is True
    assert evidence["shortest_policy_route_atom_count"] == 2


def test_finish_records_exact_model_selected_target_and_evidence_in_plan() -> None:
    current = session()
    retrieve_positive(current)
    entry = next(iter(current.retrieved_hardness_targets.values()))
    evidence = membership_evidence()
    term = f"ComplexityReduction.Certificate.CertifiedPath.step {ROUTE}"
    result = current.finish(
        {
            "action": "finish",
            "matched_problem": PROBLEM,
            "match_relation": "exact_defeq",
            "connection_entry_id": None,
            "target_entry_id": entry.target_entry_id,
            "target_evidence_id": evidence.evidence_id,
            "target_declaration": TARGET,
            "reduction_declarations": [ROUTE],
            "lean_term": term,
            "explanation": "Select the returned Native NP target and direct route.",
        }
    )
    assert result.protocol_accepted
    assert result.lean_term == term
    assert result.plan is not None
    assert result.plan.objective == "reduce_to_known_np"
    assert result.plan.target_declaration == TARGET
    assert result.plan.target_evidence["evidence_id"] == evidence.evidence_id
    assert result.plan.target_evidence["selection_policy"] == "model_open_target"
    assert result.plan.target_evidence["policy_satisfied"] is True


def test_finish_accepts_retrieved_problem_entry_id_and_canonicalizes_plan() -> None:
    current = session()
    retrieve_positive(current)
    problem = next(iter(current.retrieved_problems.values()))
    target = next(iter(current.retrieved_hardness_targets.values()))
    evidence = membership_evidence()
    term = f"ComplexityReduction.Certificate.CertifiedPath.step {ROUTE}"

    result = current.finish(
        {
            "action": "finish",
            "matched_problem": problem.entry_id,
            "match_relation": "exact_defeq",
            "connection_entry_id": None,
            "target_entry_id": target.target_entry_id,
            "target_evidence_id": evidence.evidence_id,
            "target_declaration": TARGET,
            "reduction_declarations": [ROUTE],
            "lean_term": term,
            "explanation": "Select the retrieved problem by its stable entry ID.",
        }
    )

    assert result.protocol_accepted
    assert result.problem_match is not None
    assert result.problem_match.candidate_declaration == PROBLEM
    assert result.plan is not None
    assert result.plan.matched_problem_declaration == PROBLEM
    assert result.plan.steps[0].parameters["problem_declaration"] == PROBLEM


def test_finish_accepts_retrieved_problem_result_object() -> None:
    current = session()
    retrieve_positive(current)
    problem = next(iter(current.retrieved_problems.values()))
    target = next(iter(current.retrieved_hardness_targets.values()))
    evidence = membership_evidence()
    matched_problem = problem_search_result(problem, input_node_id=SOURCE_NODE)
    matched_problem["problem_node_id"] = "untrusted-echoed-node"
    matched_problem["exact_defeq"] = False

    result = current.finish(
        {
            "action": "finish",
            "matched_problem": matched_problem,
            "match_relation": "exact_defeq",
            "connection_entry_id": None,
            "target_entry_id": target.target_entry_id,
            "target_evidence_id": evidence.evidence_id,
            "target_declaration": TARGET,
            "reduction_declarations": [ROUTE],
            "lean_term": (
                f"ComplexityReduction.Certificate.CertifiedPath.step {ROUTE}"
            ),
            "explanation": "Echo the retrieved problem result object.",
        }
    )

    assert result.protocol_accepted
    assert result.problem_match is not None
    assert result.problem_match.candidate_node_id == SOURCE_NODE
    assert result.plan is not None
    assert result.plan.matched_problem_declaration == PROBLEM


@pytest.mark.parametrize("connection_entry_id", ("", "  \t  "))
def test_finish_normalizes_blank_connection_id_to_absent(
    connection_entry_id: str,
) -> None:
    current = session()
    retrieve_positive(current)
    target = next(iter(current.retrieved_hardness_targets.values()))
    evidence = membership_evidence()

    result = current.finish(
        {
            "action": "finish",
            "matched_problem": PROBLEM,
            "match_relation": "exact_defeq",
            "connection_entry_id": connection_entry_id,
            "target_entry_id": target.target_entry_id,
            "target_evidence_id": evidence.evidence_id,
            "target_declaration": TARGET,
            "reduction_declarations": [ROUTE],
            "lean_term": (
                f"ComplexityReduction.Certificate.CertifiedPath.step {ROUTE}"
            ),
            "explanation": "A blank connection selector means no adapter connection.",
        }
    )

    assert result.protocol_accepted
    assert result.selected_connection is None


def test_finish_still_rejects_nonempty_connection_for_exact_match() -> None:
    current = session()
    retrieve_positive(current)
    target = next(iter(current.retrieved_hardness_targets.values()))
    with pytest.raises(InputPlanningError) as error:
        current.finish(
            {
                "action": "finish",
                "matched_problem": PROBLEM,
                "match_relation": "exact_defeq",
                "connection_entry_id": "sha256:not-an-absent-connection",
                "target_entry_id": target.target_entry_id,
                "target_evidence_id": membership_evidence().evidence_id,
                "target_declaration": TARGET,
                "reduction_declarations": [ROUTE],
                "lean_term": (
                    f"ComplexityReduction.Certificate.CertifiedPath.step {ROUTE}"
                ),
                "explanation": "A non-empty adapter is invalid for an exact match.",
            }
        )
    assert error.value.failure_code == "unexpected_connection_for_exact_match"


def test_finish_rejects_unretrieved_target_and_policy_mismatch() -> None:
    current = session()
    current.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": [SOURCE_NODE]}],
        }
    )
    with pytest.raises(InputPlanningError) as error:
        current.finish(
            {
                "matched_problem": PROBLEM,
                "match_relation": "exact_defeq",
                "connection_entry_id": None,
                "target_entry_id": "sha256:not-retrieved",
                "target_evidence_id": "sha256:not-retrieved",
                "target_declaration": TARGET,
                "reduction_declarations": [],
                "lean_term": "ComplexityReduction.Certificate.CertifiedPath.refl",
                "explanation": "Invented target.",
            }
        )
    assert error.value.failure_code == "hardness_target_not_retrieved"

    mismatched = session(
        request=policy(required="native_np_complete", allowed=("native_membership",))
    )
    mismatched.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"], "limit": 8}],
        }
    )
    entry = next(iter(mismatched.retrieved_hardness_targets.values()))
    with pytest.raises(InputPlanningError) as error:
        mismatched._selected_target(
            target_entry_id=entry.target_entry_id,
            target_evidence_id=membership_evidence().evidence_id,
            target_declaration=TARGET,
        )
    assert error.value.failure_code == "target_evidence_policy_mismatch"


def test_finish_rejects_route_that_does_not_reach_selected_target() -> None:
    wrong = reduction_catalog(target="lean-whnf:other")
    current = session(reductions=wrong)
    current.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": [SOURCE_NODE]}],
        }
    )
    current.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"]}],
        }
    )
    current.execute_query(
        {
            "action": "search_reductions",
            "searches": [{"source_node_ids": [SOURCE_NODE]}],
        }
    )
    entry = next(iter(current.retrieved_hardness_targets.values()))
    with pytest.raises(InputPlanningError) as error:
        current.finish(
            {
                "matched_problem": PROBLEM,
                "match_relation": "exact_defeq",
                "connection_entry_id": None,
                "target_entry_id": entry.target_entry_id,
                "target_evidence_id": membership_evidence().evidence_id,
                "target_declaration": TARGET,
                "reduction_declarations": [ROUTE],
                "lean_term": (
                    "ComplexityReduction.Certificate.CertifiedPath.step " + ROUTE
                ),
                "explanation": "Wrong endpoint.",
            }
        )
    assert error.value.failure_code == "reduction_path_does_not_reach_selected_target"


def test_no_eligible_target_and_no_route_are_distinct_auditable_stops() -> None:
    no_eligible = session(request=policy(maximum_dependencies=0))
    no_eligible.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"]}],
        }
    )
    stopped = no_eligible.stop(
        {
            "action": "stop",
            "failure_code": "no_eligible_hardness_target",
            "explanation": "Every returned evidence exceeds the dependency limit.",
        }
    )
    assert stopped.failure_code == "no_eligible_hardness_target"
    assert "没有任何证据" in stopped.explanation

    reverse_only = session(
        reductions=reduction_catalog(source=TARGET_NODE, target=SOURCE_NODE)
    )
    reverse_only.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": [SOURCE_NODE]}],
        }
    )
    reverse_only.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"]}],
        }
    )
    reverse_only.execute_query(
        {
            "action": "search_reductions",
            "searches": [{"source_node_ids": [SOURCE_NODE]}],
        }
    )
    stopped = reverse_only.stop(
        {
            "action": "stop",
            "failure_code": "eligible_target_has_no_existing_route",
            "matched_problem": PROBLEM,
            "match_relation": "exact_defeq",
            "connection_entry_id": None,
            "explanation": "Only a target-to-source path exists.",
        }
    )
    assert stopped.failure_code == "eligible_target_has_no_existing_route"
    assert "相反方向" in stopped.explanation


def test_no_route_stop_accepts_retrieved_problem_entry_id() -> None:
    current = session(
        reductions=reduction_catalog(source=TARGET_NODE, target=SOURCE_NODE)
    )
    current.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": [SOURCE_NODE]}],
        }
    )
    current.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"]}],
        }
    )
    current.execute_query(
        {
            "action": "search_reductions",
            "searches": [{"source_node_ids": [SOURCE_NODE]}],
        }
    )
    problem = next(iter(current.retrieved_problems.values()))

    stopped = current.stop(
        {
            "action": "stop",
            "failure_code": "eligible_target_has_no_existing_route",
            "matched_problem": problem.entry_id,
            "match_relation": "exact_defeq",
            "connection_entry_id": None,
            "explanation": "Only the reverse direction is registered.",
        }
    )

    assert stopped.failure_code == "eligible_target_has_no_existing_route"
    assert stopped.problem_match is not None
    assert stopped.problem_match.candidate_declaration == PROBLEM


def test_no_route_stop_accepts_retrieved_problem_result_object() -> None:
    current = session(
        reductions=reduction_catalog(source=TARGET_NODE, target=SOURCE_NODE)
    )
    problem_response = current.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": [SOURCE_NODE]}],
        }
    )
    current.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"]}],
        }
    )
    current.execute_query(
        {
            "action": "search_reductions",
            "searches": [{"source_node_ids": [SOURCE_NODE]}],
        }
    )

    stopped = current.stop(
        {
            "action": "stop",
            "failure_code": "eligible_target_has_no_existing_route",
            "matched_problem": problem_response["results"][0],
            "match_relation": "exact_defeq",
            "connection_entry_id": None,
            "explanation": "The returned problem has no forward target route.",
        }
    )

    assert stopped.failure_code == "eligible_target_has_no_existing_route"
    assert stopped.problem_match is not None
    assert stopped.problem_match.candidate_declaration == PROBLEM


@pytest.mark.parametrize("connection_entry_id", ("", "  \n  "))
def test_no_route_stop_normalizes_blank_connection_id_to_absent(
    connection_entry_id: str,
) -> None:
    current = session(
        reductions=reduction_catalog(source=TARGET_NODE, target=SOURCE_NODE)
    )
    current.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": [SOURCE_NODE]}],
        }
    )
    current.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"]}],
        }
    )
    current.execute_query(
        {
            "action": "search_reductions",
            "searches": [{"source_node_ids": [SOURCE_NODE]}],
        }
    )

    stopped = current.stop(
        {
            "action": "stop",
            "failure_code": "eligible_target_has_no_existing_route",
            "matched_problem": PROBLEM,
            "match_relation": "exact_defeq",
            "connection_entry_id": connection_entry_id,
            "explanation": "No adapter connection is required for the exact match.",
        }
    )

    assert stopped.failure_code == "eligible_target_has_no_existing_route"
    assert stopped.selected_connection is None


def test_no_route_stop_accepts_complete_source_frontier_from_connections() -> None:
    declaration = "ComplexityReduction.Routes.SourceToMiddle.route"
    source_edge = reduction(
        source=SOURCE_NODE,
        target=MIDDLE_NODE,
        declaration=declaration,
    )
    current = session(
        connections=ConnectionCatalog(
            registry_fingerprint=REGISTRY,
            entries=(
                direct_connection(
                    source=SOURCE_NODE,
                    target=MIDDLE_NODE,
                    declaration=declaration,
                ),
            ),
        ),
        reductions=TypedCatalog(
            mode="full",
            registry_fingerprint=REGISTRY,
            entries=(source_edge,),
        ),
    )
    current.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": [SOURCE_NODE]}],
        }
    )
    current.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"]}],
        }
    )
    response = current.execute_query(
        {
            "action": "search_connections",
            "searches": [{"source_node_ids": [SOURCE_NODE], "limit": 8}],
        }
    )
    assert len(response["results"]) == 1

    stopped = current.stop(
        {
            "action": "stop",
            "failure_code": "eligible_target_has_no_existing_route",
            "matched_problem": PROBLEM,
            "match_relation": "exact_defeq",
            "connection_entry_id": "",
            "explanation": "The complete source frontier cannot reach a target.",
        }
    )

    assert stopped.failure_code == "eligible_target_has_no_existing_route"
    assert stopped.selected_connection is None


def test_no_route_stop_rejects_incomplete_source_frontier_from_connections() -> None:
    first_declaration = "ComplexityReduction.Routes.SourceToMiddle.first"
    second_declaration = "ComplexityReduction.Routes.SourceToOther.second"
    other_node = "lean-whnf:other"
    current = session(
        connections=ConnectionCatalog(
            registry_fingerprint=REGISTRY,
            entries=(
                direct_connection(
                    source=SOURCE_NODE,
                    target=MIDDLE_NODE,
                    declaration=first_declaration,
                ),
                direct_connection(
                    source=SOURCE_NODE,
                    target=other_node,
                    declaration=second_declaration,
                ),
            ),
        ),
        reductions=TypedCatalog(
            mode="full",
            registry_fingerprint=REGISTRY,
            entries=(
                reduction(
                    source=SOURCE_NODE,
                    target=MIDDLE_NODE,
                    declaration=first_declaration,
                ),
                reduction(
                    source=SOURCE_NODE,
                    target=other_node,
                    declaration=second_declaration,
                ),
            ),
        ),
    )
    current.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": [SOURCE_NODE]}],
        }
    )
    current.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"]}],
        }
    )
    response = current.execute_query(
        {
            "action": "search_connections",
            "searches": [{"source_node_ids": [SOURCE_NODE], "limit": 1}],
        }
    )
    assert len(response["results"]) == 1

    with pytest.raises(InputPlanningError) as error:
        current.stop(
            {
                "action": "stop",
                "failure_code": "eligible_target_has_no_existing_route",
                "matched_problem": PROBLEM,
                "match_relation": "exact_defeq",
                "connection_entry_id": None,
                "explanation": "A truncated source frontier is not an absence proof.",
            }
        )
    assert error.value.failure_code == "model_stop_not_auditable"
    assert "完整" in error.value.explanation


def test_problem_selector_rejects_unretrieved_and_ambiguous_values() -> None:
    current = session()
    current.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": [SOURCE_NODE]}],
        }
    )

    with pytest.raises(InputPlanningError) as error:
        current._selected_problem("sha256:not-retrieved")
    assert error.value.failure_code == "problem_not_retrieved"

    original = next(iter(current.retrieved_problems.values()))
    other = replace(
        original,
        declaration="ComplexityReduction.Problems.Other.problem",
        display="other problem",
    )
    current.retrieved_problems[other.entry_id] = other
    with pytest.raises(InputPlanningError) as error:
        current._selected_problem(
            {"entry_id": original.entry_id, "declaration": other.declaration}
        )
    assert error.value.failure_code == "problem_not_retrieved"

    with pytest.raises(InputPlanningError) as error:
        current._selected_problem(
            {"entry_id": "sha256:not-retrieved", "declaration": PROBLEM}
        )
    assert error.value.failure_code == "problem_not_retrieved"

    duplicate = replace(original, display="ambiguous duplicate")
    current.retrieved_problems[duplicate.entry_id] = duplicate
    with pytest.raises(InputPlanningError) as error:
        current._selected_problem(PROBLEM)
    assert error.value.failure_code == "problem_not_retrieved"

    assert current._selected_problem(original.entry_id) == original
    assert current._selected_problem(duplicate.entry_id) == duplicate


def test_no_route_stop_is_rejected_when_any_eligible_target_is_reachable() -> None:
    current = session()
    current.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": [SOURCE_NODE]}],
        }
    )
    current.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"]}],
        }
    )
    current.execute_query(
        {
            "action": "search_reductions",
            "searches": [{"source_node_ids": [SOURCE_NODE]}],
        }
    )
    with pytest.raises(InputPlanningError) as error:
        current.stop(
            {
                "action": "stop",
                "failure_code": "eligible_target_has_no_existing_route",
                "matched_problem": PROBLEM,
                "match_relation": "exact_defeq",
                "connection_entry_id": None,
                "explanation": "Incorrect absence claim.",
            }
        )
    assert error.value.failure_code == "model_stop_contradicted_by_catalog"


def test_no_route_stop_requires_query_for_the_requested_policy() -> None:
    complete_declaration = "ComplexityReduction.Evidence.targetNativeComplete"
    completeness = HardnessTargetEvidence(
        target_declaration=TARGET,
        target_node_id=TARGET_NODE,
        evidence_kind="native_completeness",
        evidence_declaration=complete_declaration,
        evidence_lean_term=complete_declaration,
        membership_lean_term=(
            "ComplexityReduction.Certificate.NativeTMNPComplete.nativeMembership "
            + complete_declaration
        ),
        satisfied_policies=("native_np", "native_np_hard", "native_np_complete"),
        validation_source="lean_registry_elaborated_type",
        provenance_declarations=(complete_declaration,),
        registry_fingerprint=REGISTRY,
    )
    current = session(
        targets=target_catalog(evidence=completeness),
        reductions=reduction_catalog(source=TARGET_NODE, target=SOURCE_NODE),
        request=policy(allowed=("native_completeness",)),
    )
    current.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": [SOURCE_NODE]}],
        }
    )
    current.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np_hard"]}],
        }
    )
    current.execute_query(
        {
            "action": "search_reductions",
            "searches": [{"source_node_ids": [SOURCE_NODE]}],
        }
    )
    with pytest.raises(InputPlanningError) as error:
        current.stop(
            {
                "action": "stop",
                "failure_code": "eligible_target_has_no_existing_route",
                "matched_problem": PROBLEM,
                "match_relation": "exact_defeq",
                "connection_entry_id": None,
                "explanation": "A different policy query is not enough.",
            }
        )
    assert error.value.failure_code == "model_stop_not_auditable"
    assert "本请求" in error.value.explanation


def test_no_route_stop_requires_visible_request_eligible_evidence() -> None:
    current = session(
        reductions=reduction_catalog(source=TARGET_NODE, target=SOURCE_NODE)
    )
    current.execute_query(
        {
            "action": "search_problems",
            "searches": [{"node_ids": [SOURCE_NODE]}],
        }
    )
    response = current.execute_query(
        {
            "action": "search_hardness_targets",
            "searches": [
                {
                    "required_policies": ["native_np"],
                    "terms": ["definitely-unmatched-query-token"],
                }
            ],
        }
    )
    assert response["results"] == []
    current.execute_query(
        {
            "action": "search_reductions",
            "searches": [{"source_node_ids": [SOURCE_NODE]}],
        }
    )
    with pytest.raises(InputPlanningError) as error:
        current.stop(
            {
                "action": "stop",
                "failure_code": "eligible_target_has_no_existing_route",
                "matched_problem": PROBLEM,
                "match_relation": "exact_defeq",
                "connection_entry_id": None,
                "explanation": "No target evidence was actually visible.",
            }
        )
    assert error.value.failure_code == "model_stop_not_auditable"
    assert "可见" in error.value.explanation


class FakeClient:
    def __init__(self, payloads: tuple[dict, ...]):
        self.payloads = payloads
        self.calls = 0

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        assert "JSON" in system
        assert "search_hardness_targets" in system
        json.loads(prompt)
        payload = self.payloads[self.calls]
        self.calls += 1
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


def test_known_hardness_model_can_correct_after_three_protocol_feedbacks() -> None:
    node_a = "lean-whnf:long-a"
    node_b = "lean-whnf:long-b"
    node_c = "lean-whnf:long-c"
    node_d = "lean-whnf:long-d"
    route_1 = "ComplexityReduction.Routes.Long.routeOne"
    route_2 = "ComplexityReduction.Routes.Long.routeTwo"
    route_3 = "ComplexityReduction.Routes.Long.routeThree"
    short_route_4 = "ComplexityReduction.Routes.Long.shortRouteFour"
    long_route_4 = "ComplexityReduction.Routes.Long.longRouteFour"
    long_route_5 = "ComplexityReduction.Routes.Long.longRouteFive"
    short_route = (route_1, route_2, route_3, short_route_4)
    long_route = (route_1, route_2, route_3, long_route_4, long_route_5)
    reductions = TypedCatalog(
        mode="full",
        registry_fingerprint=REGISTRY,
        entries=(
            reduction(source=SOURCE_NODE, target=node_a, declaration=route_1),
            reduction(source=node_a, target=node_b, declaration=route_2),
            reduction(source=node_b, target=node_c, declaration=route_3),
            reduction(
                source=node_c,
                target=TARGET_NODE,
                declaration=short_route_4,
            ),
            reduction(source=node_c, target=node_d, declaration=long_route_4),
            reduction(source=node_d, target=TARGET_NODE, declaration=long_route_5),
        ),
    )
    evidence_declaration = (
        "ComplexityReduction.Evidence.targetTransportedNativeHardness"
    )
    evidence = HardnessTargetEvidence(
        target_declaration=TARGET,
        target_node_id=TARGET_NODE,
        evidence_kind="transported_native_hardness",
        evidence_declaration=evidence_declaration,
        evidence_lean_term=evidence_declaration,
        membership_lean_term="",
        satisfied_policies=("native_np_hard",),
        validation_source="lean_registry_transported_hardness",
        provenance_declarations=(evidence_declaration,),
        registry_fingerprint=REGISTRY,
    )
    targets = target_catalog(evidence=evidence)
    target_entry = targets.entries[0]

    def path_term(route: tuple[str, ...]) -> str:
        term = f"ComplexityReduction.Certificate.CertifiedPath.step {route[0]}"
        for declaration in route[1:]:
            term = (
                "ComplexityReduction.Certificate.CertifiedPath.cons "
                f"({term}) {declaration}"
            )
        return term

    def finish_payload(route: tuple[str, ...]) -> dict:
        return {
            "action": "finish",
            "matched_problem": PROBLEM,
            "match_relation": "exact_defeq",
            "connection_entry_id": None,
            "target_entry_id": target_entry.target_entry_id,
            "target_evidence_id": evidence.evidence_id,
            "target_declaration": TARGET,
            "reduction_declarations": list(route),
            "lean_term": path_term(route),
            "explanation": "Use only the retrieved directed reduction edges.",
        }

    client = FakeClient(
        (
            {
                "action": "search_problems",
                "searches": [{"node_ids": [SOURCE_NODE]}],
            },
            {
                "action": "search_hardness_targets",
                "searches": [{"required_policies": ["native_np_hard"]}],
            },
            {
                "action": "search_reductions",
                "searches": [
                    {
                        "source_node_ids": [
                            SOURCE_NODE,
                            node_a,
                            node_b,
                            node_c,
                            node_d,
                        ]
                    }
                ],
            },
            {
                "action": "search_reductions",
                "searches": [{"terms": ["route"]}] * 5,
            },
            finish_payload(short_route),
            finish_payload(short_route),
            finish_payload(long_route),
        )
    )
    result = generate_lean_path_to_open_target(
        observation=observation(),
        problem_catalog=problem_catalog(),
        connection_catalog=ConnectionCatalog(
            registry_fingerprint=REGISTRY,
            entries=(),
        ),
        reduction_catalog=reductions,
        target_catalog=targets,
        request_policy=OpenTargetRequestPolicy(
            required_hardness="native_np_hard",
            allowed_target_evidence=("transported_native_hardness",),
            minimum_route_atoms=5,
            maximum_route_atoms=6,
            maximum_dependencies=16,
            allow_reflexive_target=False,
            require_simple_path=True,
            objective="reduce_to_known_hardness",
        ),
        client=client,  # type: ignore[arg-type]
    )

    assert result.protocol_accepted
    assert result.reduction_declarations == long_route
    assert client.calls == 7
    feedback = [
        row for row in result.query_trace if row.get("action") == "protocol_feedback"
    ]
    assert [row["failure_code"] for row in feedback] == [
        "invalid_reduction_search",
        "selected_path_too_short",
        "selected_path_too_short",
    ]
    short_explanation = feedback[-1]["explanation"]
    assert "实际提交了 4 条归约边" in short_explanation
    assert "至少需要 5 条" in short_explanation
    assert "不是路径 endpoint/node 的数量" in short_explanation
    final_prompt = json.loads(result.model_prompts[-1])
    assert len(final_prompt["protocol_feedback"]) == 3
    assert final_prompt["retrieved_view"]["mode"] == (
        "authorization_complete_compact"
    )
    assert final_prompt["terminal_guidance"] == {
        "mode": "finish_now",
        "available_route_atom_counts": [5],
        "route_and_target_remain_model_selected": True,
        "instruction": (
            "A compliant route is fully retrieved. Return finish now; do not issue "
            "another search or re-derive the full graph."
        ),
    }
    assert "source" not in final_prompt["retrieved"]["reductions"][0]


def test_model_loop_selects_target_only_after_bounded_target_search() -> None:
    targets = target_catalog()
    entry = targets.entries[0]
    evidence = entry.evidences[0]
    term = f"ComplexityReduction.Certificate.CertifiedPath.step {ROUTE}"
    client = FakeClient(
        (
            {
                "action": "search_problems",
                "searches": [{"node_ids": [SOURCE_NODE]}],
            },
            {
                "action": "search_hardness_targets",
                "searches": [{"required_policies": ["native_np"]}],
            },
            {
                "action": "search_reductions",
                "searches": [
                    {
                        "source_node_ids": [SOURCE_NODE],
                        "target_node_ids": [TARGET_NODE],
                    }
                ],
            },
            {
                "action": "finish",
                "matched_problem": PROBLEM,
                "match_relation": "exact_defeq",
                "connection_entry_id": None,
                "target_entry_id": entry.target_entry_id,
                "target_evidence_id": evidence.evidence_id,
                "target_declaration": TARGET,
                "reduction_declarations": [ROUTE],
                "lean_term": term,
                "explanation": "Use the returned target and route.",
            },
        )
    )
    result = generate_lean_path_to_open_target(
        observation=observation(),
        problem_catalog=problem_catalog(),
        connection_catalog=ConnectionCatalog(
            registry_fingerprint=REGISTRY, entries=()
        ),
        reduction_catalog=reduction_catalog(),
        target_catalog=targets,
        request_policy=policy(),
        client=client,  # type: ignore[arg-type]
    )
    assert result.protocol_accepted
    assert result.plan is not None
    assert result.plan.target_declaration == TARGET
    assert len(result.model_responses) == 4


def test_catalog_fingerprint_mismatch_stops_before_model_call() -> None:
    stale_targets = HardnessTargetCatalog(
        registry_fingerprint="lean:stale",
        entries=target_catalog().entries,
    )
    client = FakeClient(())
    result = generate_lean_path_to_open_target(
        observation=observation(),
        problem_catalog=problem_catalog(),
        connection_catalog=ConnectionCatalog(
            registry_fingerprint=REGISTRY, entries=()
        ),
        reduction_catalog=reduction_catalog(),
        target_catalog=stale_targets,
        request_policy=policy(),
        client=client,  # type: ignore[arg-type]
    )
    assert result.failure_code == "stale_catalog_fingerprint"
    assert client.calls == 0


def test_prompt_only_simulation_completes_positive_and_reverse_only_cases() -> None:
    positive_client = SimulatedOpenTargetClient()
    positive = generate_lean_path_to_open_target(
        observation=observation(),
        problem_catalog=problem_catalog(),
        connection_catalog=ConnectionCatalog(
            registry_fingerprint=REGISTRY, entries=()
        ),
        reduction_catalog=reduction_catalog(),
        target_catalog=target_catalog(),
        request_policy=policy(),
        client=positive_client,  # type: ignore[arg-type]
    )
    assert positive.protocol_accepted
    assert positive.plan is not None
    assert positive.plan.target_declaration == TARGET

    reverse_client = SimulatedOpenTargetClient()
    reverse = generate_lean_path_to_open_target(
        observation=observation(),
        problem_catalog=problem_catalog(),
        connection_catalog=ConnectionCatalog(
            registry_fingerprint=REGISTRY, entries=()
        ),
        reduction_catalog=reduction_catalog(source=TARGET_NODE, target=SOURCE_NODE),
        target_catalog=target_catalog(),
        request_policy=policy(),
        client=reverse_client,  # type: ignore[arg-type]
    )
    assert reverse.failure_code == "eligible_target_has_no_existing_route"


def test_prompt_only_simulation_expands_outgoing_frontier_after_empty_target_lookup() -> None:
    first = "ComplexityReduction.Routes.SourceToMiddle.route"
    second = "ComplexityReduction.Routes.MiddleToTarget.route"
    reductions = TypedCatalog(
        mode="full",
        registry_fingerprint=REGISTRY,
        entries=(
            reduction(source=SOURCE_NODE, target=MIDDLE_NODE, declaration=first),
            reduction(source=MIDDLE_NODE, target=TARGET_NODE, declaration=second),
        ),
    )
    client = SimulatedOpenTargetClient()
    result = generate_lean_path_to_open_target(
        observation=observation(),
        problem_catalog=problem_catalog(),
        connection_catalog=ConnectionCatalog(
            registry_fingerprint=REGISTRY, entries=()
        ),
        reduction_catalog=reductions,
        target_catalog=target_catalog(),
        request_policy=policy(maximum_route_atoms=2),
        client=client,  # type: ignore[arg-type]
    )
    assert result.protocol_accepted
    assert result.reduction_declarations == (first, second)

    searches = [
        row["searches"][0]
        for row in result.query_trace
        if row.get("action") == "search_reductions" and "searches" in row
    ]
    assert searches[0]["source_node_ids"] == [SOURCE_NODE]
    assert searches[0]["target_node_ids"] == [TARGET_NODE]
    assert searches[1]["source_node_ids"] == [SOURCE_NODE]
    assert searches[1]["target_node_ids"] == []
    assert searches[2]["source_node_ids"] == [MIDDLE_NODE]
    assert searches[2]["target_node_ids"] == []


def test_prompt_only_simulation_skips_reflexive_target_forbidden_by_policy() -> None:
    reflexive_target = "ComplexityReduction.Problems.AReflexive.problem"
    reflexive_evidence_declaration = (
        "ComplexityReduction.Evidence.aReflexiveNativeNP"
    )
    reflexive_evidence = HardnessTargetEvidence(
        target_declaration=reflexive_target,
        target_node_id=SOURCE_NODE,
        evidence_kind="native_membership",
        evidence_declaration=reflexive_evidence_declaration,
        evidence_lean_term=reflexive_evidence_declaration,
        membership_lean_term=reflexive_evidence_declaration,
        satisfied_policies=("native_np",),
        validation_source="lean_registry_elaborated_type",
        provenance_declarations=(reflexive_evidence_declaration,),
        registry_fingerprint=REGISTRY,
    )
    targets = HardnessTargetCatalog(
        registry_fingerprint=REGISTRY,
        entries=(
            HardnessTargetCatalogEntry(
                target_declaration=reflexive_target,
                target_display="reflexive problem",
                target_node_id=SOURCE_NODE,
                target_namespace="ComplexityReduction.Problems.AReflexive",
                registry_fingerprint=REGISTRY,
                evidences=(reflexive_evidence,),
            ),
            target_catalog().entries[0],
        ),
    )
    client = SimulatedOpenTargetClient()
    result = generate_lean_path_to_open_target(
        observation=observation(),
        problem_catalog=problem_catalog(),
        connection_catalog=ConnectionCatalog(
            registry_fingerprint=REGISTRY, entries=()
        ),
        reduction_catalog=reduction_catalog(),
        target_catalog=targets,
        request_policy=policy(allow_reflexive_target=False),
        client=client,  # type: ignore[arg-type]
    )
    assert result.protocol_accepted
    assert result.plan is not None
    assert result.plan.target_declaration == TARGET


def test_prompt_only_simulation_applies_reflexive_constructor_to_input() -> None:
    reflexive_target = "ComplexityReduction.Problems.Reflexive.problem"
    evidence_declaration = "ComplexityReduction.Evidence.reflexiveNativeNP"
    evidence = HardnessTargetEvidence(
        target_declaration=reflexive_target,
        target_node_id=SOURCE_NODE,
        evidence_kind="native_membership",
        evidence_declaration=evidence_declaration,
        evidence_lean_term=evidence_declaration,
        membership_lean_term=evidence_declaration,
        satisfied_policies=("native_np",),
        validation_source="lean_registry_elaborated_type",
        provenance_declarations=(evidence_declaration,),
        registry_fingerprint=REGISTRY,
    )
    targets = HardnessTargetCatalog(
        registry_fingerprint=REGISTRY,
        entries=(
            HardnessTargetCatalogEntry(
                target_declaration=reflexive_target,
                target_display="reflexive problem",
                target_node_id=SOURCE_NODE,
                target_namespace="ComplexityReduction.Problems.Reflexive",
                registry_fingerprint=REGISTRY,
                evidences=(evidence,),
            ),
        ),
    )
    result = generate_lean_path_to_open_target(
        observation=observation(),
        problem_catalog=problem_catalog(),
        connection_catalog=ConnectionCatalog(
            registry_fingerprint=REGISTRY, entries=()
        ),
        reduction_catalog=TypedCatalog(
            mode="full", registry_fingerprint=REGISTRY, entries=()
        ),
        target_catalog=targets,
        request_policy=policy(allow_reflexive_target=True),
        client=SimulatedOpenTargetClient(),  # type: ignore[arg-type]
    )
    assert result.protocol_accepted
    assert result.lean_term == (
        "ComplexityReduction.Certificate.CertifiedPath.refl " + INPUT
    )
