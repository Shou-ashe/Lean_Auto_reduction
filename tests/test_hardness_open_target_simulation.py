import json
from typing import Any

import pytest

from agent.hardness.connection_catalog import ConnectionCatalog
from agent.hardness.hardness_target_catalog import (
    HardnessTargetCatalog,
    HardnessTargetCatalogEntry,
    HardnessTargetEvidence,
)
from agent.hardness.input_observation import (
    LeanInputObservation,
    PredicatePresentationMatch,
)
from agent.hardness.models import TypedCatalog, TypedInventoryEntry
from agent.hardness.open_target_planner import (
    OpenTargetRequestPolicy,
    generate_lean_path_to_open_target,
)
from agent.hardness.open_target_simulation import SimulatedOpenTargetClient
from agent.hardness.problem_catalog import ProblemCatalog, ProblemCatalogEntry


SYSTEM = "Return JSON and use search_hardness_targets."
PREDICATE = "lean-whnf:predicate"
DOMAIN = "lean-whnf:domain"
PROBLEM_NODE = "lean-whnf:problem"
PREDICATE_DECLARATION = "Benchmark.Input.predicate"
PROBLEM_DECLARATION = "ComplexityReduction.Problems.Source.problem"


def _predicate_lookup_history() -> list[dict[str, Any]]:
    return [
        {
            "action": "search_problems",
            "searches": [
                {
                    "accepts_node_ids": [PREDICATE],
                    "domain_node_ids": [DOMAIN],
                    "limit": 8,
                },
                {"domain_node_ids": [DOMAIN], "limit": 8},
            ],
            "result_count": 0,
        }
    ]


def _payload(
    *,
    problems: list[dict[str, Any]] | None = None,
    history: list[dict[str, Any]] | None = None,
    targets: list[dict[str, Any]] | None = None,
) -> dict[str, Any]:
    return {
        "task": "predicate open target",
        "request": {
            "required_hardness": "native_np",
            "maximum_route_atoms": 3,
            "maximum_dependencies": 8,
            "allow_reflexive_target": True,
        },
        "input_observation": {
            "input_declaration": PREDICATE_DECLARATION,
            "input_kind": "predicate",
            "normalized_problem_node_id": "",
            "predicate_node_id": PREDICATE,
            "predicate_domain_node_id": DOMAIN,
        },
        "query_history": history or [],
        "retrieved": {
            "problems": problems or [],
            "connections": [],
            "hardness_targets": targets or [],
            "reductions": [],
        },
        "constraints": {"target_routes_are_not_included": True},
    }


def _complete(payload: dict[str, Any]) -> dict[str, Any]:
    response = SimulatedOpenTargetClient().complete_json(
        system=SYSTEM,
        prompt=json.dumps(payload),
    )
    assert response.content is not None
    return json.loads(response.content)


def _problem(
    declaration: str = PROBLEM_DECLARATION,
    *,
    exact: bool,
    codec: str = "codec-a",
    registered: bool = True,
) -> dict[str, Any]:
    return {
        "entry_id": f"entry:{declaration}",
        "declaration": declaration,
        "problem_node_id": PROBLEM_NODE,
        "domain_node_id": DOMAIN,
        "accepts_exact_defeq": exact,
        "codec_group_id": codec,
        "encoder_bound_identity_node_id": f"lean-whnf:{codec}",
        "registered": registered,
    }


def test_predicate_simulation_queries_accepts_and_carrier_together() -> None:
    result = _complete(_payload())

    assert result == {
        "action": "search_problems",
        "searches": [
            {
                "accepts_node_ids": [PREDICATE],
                "domain_node_ids": [DOMAIN],
                "limit": 8,
            },
            {"domain_node_ids": [DOMAIN], "limit": 8},
        ],
    }


def test_simulation_distinguishes_transport_provenance_from_input_route() -> None:
    payload = _payload()
    payload["constraints"] = {
        "target_routes_are_not_included": False,
        "target_evidence_transport_provenance_may_be_included": True,
        "input_route_is_not_preselected": True,
    }

    assert _complete(payload)["action"] == "search_problems"

    payload["constraints"]["input_route_is_not_preselected"] = False
    with pytest.raises(ValueError, match="route isolation"):
        _complete(payload)


@pytest.mark.parametrize(
    ("problems", "failure_code"),
    (
        (
            [_problem(exact=False)],
            "predicate_accepts_not_definitionally_equal",
        ),
        ([], "predicate_has_no_lawful_presentation"),
        (
            [
                _problem(exact=True, codec="codec-a"),
                _problem(
                    "ComplexityReduction.Problems.Other.problem",
                    exact=True,
                    codec="codec-b",
                ),
            ],
            "ambiguous_predicate_presentation",
        ),
    ),
)
def test_predicate_simulation_classifies_grounding_failures(
    problems: list[dict[str, Any]], failure_code: str
) -> None:
    result = _complete(
        _payload(problems=problems, history=_predicate_lookup_history())
    )

    assert result["action"] == "stop"
    assert result["failure_code"] == failure_code


def test_predicate_simulation_uses_selected_problem_as_route_and_refl_source() -> None:
    alias = _problem(
        "ComplexityReduction.Problems.Source.alias",
        exact=True,
        registered=False,
    )
    selected = _problem(exact=True, registered=True)
    history = [
        *_predicate_lookup_history(),
        {
            "action": "search_hardness_targets",
            "searches": [{"required_policies": ["native_np"], "limit": 8}],
            "result_count": 1,
        },
    ]
    target = {
        "target_entry_id": "target-entry",
        "target_declaration": "ComplexityReduction.Problems.Target.problem",
        "target_node_id": PROBLEM_NODE,
        "evidences": [
            {
                "evidence_id": "target-evidence",
                "request_eligible": True,
                "policy_route_allowed": True,
                "shortest_policy_route_atom_count": 0,
                "provenance_declarations": [],
            }
        ],
    }

    result = _complete(
        _payload(problems=[alias, selected], history=history, targets=[target])
    )

    assert result["action"] == "finish"
    assert result["matched_problem"] == PROBLEM_DECLARATION
    assert result["match_relation"] == "accepts_exact_defeq"
    assert result["connection_entry_id"] is None
    assert result["lean_term"] == (
        "ComplexityReduction.Certificate.CertifiedPath.refl "
        + PROBLEM_DECLARATION
    )
    assert PREDICATE_DECLARATION not in result["lean_term"]


def test_predicate_simulation_integrates_with_open_target_planner() -> None:
    registry = "lean:registry"
    representation_node = "lean-whnf:representation"
    encoder_node = "lean-whnf:encoder"
    target_node = "lean-whnf:target"
    route = "ComplexityReduction.Routes.SourceToTarget.route"
    presentation_match = PredicatePresentationMatch(
        candidate_declaration=PROBLEM_DECLARATION,
        problem_node_id=PROBLEM_NODE,
        accepts_node_id=PREDICATE,
        domain_node_id=DOMAIN,
        representation_node_id=representation_node,
        encoder_bound_identity_node_id=encoder_node,
        registry_fingerprint=registry,
    )
    observation = LeanInputObservation(
        input_module="Benchmark.Input",
        input_declaration=PREDICATE_DECLARATION,
        declaration_kind="definition",
        supported=True,
        input_kind="predicate",
        elaborated_type="Input → Prop",
        whnf_type="Input → Prop",
        closed=True,
        universe_parameters=(),
        has_metavariables=False,
        presented_problem_compatible=False,
        predicate_domain="Input",
        normalized_problem_node_id=None,
        referenced_constants=(),
        semantic_summary="source semantics",
        representation_summary=None,
        predicate_summary="fun input => accepts input",
        accepts_summary=None,
        registry_fingerprint=registry,
        failure_code=None,
        explanation=None,
        predicate_domain_node_id=DOMAIN,
        predicate_node_id=PREDICATE,
        predicate_presentation_matches=(presentation_match,),
    )
    problems = ProblemCatalog(
        registry_fingerprint=registry,
        entries=(
            ProblemCatalogEntry(
                declaration=PROBLEM_DECLARATION,
                declaration_kind="definition",
                display="source problem",
                problem_node_id=PROBLEM_NODE,
                semantic_summary="source semantics",
                representation_summary="source representation",
                encoder_bound_identity_summary="source codec",
                referenced_constants=(),
                registered=True,
                registry_fingerprint=registry,
                accepts_summary="fun input => accepts input",
                accepts_node_id=PREDICATE,
                domain_summary="Input",
                domain_node_id=DOMAIN,
                representation_node_id=representation_node,
                encoder_bound_identity_node_id=encoder_node,
            ),
        ),
    )
    target_declaration = "ComplexityReduction.Problems.Target.problem"
    evidence_declaration = "ComplexityReduction.Evidence.targetNativeNP"
    evidence = HardnessTargetEvidence(
        target_declaration=target_declaration,
        target_node_id=target_node,
        evidence_kind="native_membership",
        evidence_declaration=evidence_declaration,
        evidence_lean_term=evidence_declaration,
        membership_lean_term=evidence_declaration,
        satisfied_policies=("native_np",),
        validation_source="lean_registry_elaborated_type",
        provenance_declarations=(evidence_declaration,),
        registry_fingerprint=registry,
    )
    targets = HardnessTargetCatalog(
        registry_fingerprint=registry,
        entries=(
            HardnessTargetCatalogEntry(
                target_declaration=target_declaration,
                target_display="target problem",
                target_node_id=target_node,
                target_namespace="ComplexityReduction.Problems.Target",
                registry_fingerprint=registry,
                evidences=(evidence,),
            ),
        ),
    )
    reductions = TypedCatalog(
        mode="full",
        registry_fingerprint=registry,
        entries=(
            TypedInventoryEntry(
                declaration=route,
                capability_kind="certified_reduction",
                component_role="sharedGadget",
                source_fingerprint="lean:source",
                target_fingerprint="lean:target",
                is_final_facade=False,
                discovery="registered",
                registry_fingerprint=registry,
                source_display="source",
                target_display="target",
                source_node_id=PROBLEM_NODE,
                target_node_id=target_node,
            ),
        ),
    )

    result = generate_lean_path_to_open_target(
        observation=observation,
        problem_catalog=problems,
        connection_catalog=ConnectionCatalog(
            registry_fingerprint=registry,
            entries=(),
        ),
        reduction_catalog=reductions,
        target_catalog=targets,
        request_policy=OpenTargetRequestPolicy(
            required_hardness="native_np",
            allowed_target_evidence=("native_membership",),
            maximum_route_atoms=3,
            maximum_dependencies=8,
            allow_reflexive_target=False,
        ),
        client=SimulatedOpenTargetClient(),  # type: ignore[arg-type]
    )

    assert result.protocol_accepted
    assert result.problem_match is not None
    assert result.problem_match.accepts_exact_defeq
    assert result.plan is not None
    assert result.plan.source_declaration == PROBLEM_DECLARATION
    assert result.lean_term == (
        "ComplexityReduction.Certificate.CertifiedPath.step " + route
    )
    assert len(result.model_responses) == 4
