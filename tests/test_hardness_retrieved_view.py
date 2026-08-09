import json

from agent.hardness.retrieved_view import (
    COMPACT_RETRIEVED_VIEW_MODE,
    compact_retrieved_payload,
    compact_retrieved_view_errors,
    compact_retrieved_view_metadata,
    retrieved_prompt_metrics,
)


def full_retrieved_payload() -> dict:
    verbose = "Lean-validated verbose display " * 400
    return {
        "problems": [
            {
                "entry_id": "sha256:problem",
                "declaration": "ComplexityReduction.Problems.Source.problem",
                "namespace": "ComplexityReduction.Problems.Source",
                "display": verbose,
                "problem_node_id": "lean-whnf:source",
                "semantic_summary": verbose,
                "accepts_summary": verbose,
                "accepts_node_id": "lean-whnf:accepts",
                "domain_summary": verbose,
                "domain_node_id": "lean-whnf:domain",
                "representation_summary": verbose,
                "representation_node_id": "lean-whnf:representation",
                "encoder_bound_identity_summary": verbose,
                "encoder_bound_identity_node_id": "lean-whnf:encoder",
                "codec_group_id": "sha256:codec",
                "registered": True,
                "exact_defeq": False,
                "accepts_exact_defeq": True,
                "validation_source": "lean_nonce_bound_predicate_match_catalog_nodes",
            }
        ],
        "connections": [
            {
                "entry_id": "sha256:connection",
                "certificate_declaration": "ComplexityReduction.Connection.source",
                "namespace": "ComplexityReduction.Connection",
                "capability_kind": "certified_reduction",
                "relation": "existing_reduction",
                "direction": "forward",
                "projection_declaration": "ComplexityReduction.Connection.source",
                "lean_term": "ComplexityReduction.Connection.source",
                "source_fingerprint": "lean:source",
                "target_fingerprint": "lean:target",
                "source_node_id": "lean-whnf:input",
                "target_node_id": "lean-whnf:source",
                "source_display": verbose,
                "target_display": verbose,
                "component_role": "ingress",
                "validation_source": "lean_validated_fixed_projection",
            }
        ],
        "hardness_targets": [
            {
                "target_entry_id": "sha256:target",
                "target_declaration": "ComplexityReduction.Problems.Target.problem",
                "target_display": verbose,
                "target_namespace": "ComplexityReduction.Problems.Target",
                "target_node_id": "lean-whnf:target",
                "satisfied_policies": ["native_np_hard"],
                "request_eligible_evidence_count": 1,
                "reachable_from_input": True,
                "shortest_route_length_from_input": 5,
                "within_route_atom_limit": True,
                "policy_route_allowed": True,
                "shortest_policy_route_atom_count": 5,
                "route_declarations_included": True,
                "registry_fingerprint": "lean:registry",
                "validation_source": "lean_validated_hardness_target_catalog",
                "evidences": [
                    {
                        "schema_version": "hardness_target_evidence_v1",
                        "evidence_id": "sha256:evidence",
                        "evidence_kind": "transported_native_hardness",
                        "evidence_declaration": (
                            "ComplexityReduction.Certificate.NativeTMNPHard."
                            "ofCompleteAlongPath"
                        ),
                        "evidence_lean_term": verbose,
                        "membership_lean_term": "",
                        "satisfied_policies": ["native_np_hard"],
                        "allowed_evidence_kind": True,
                        "request_eligible": True,
                        "policy_route_allowed": True,
                        "shortest_policy_route_atom_count": 5,
                        "target_evidence_dependency_count": 2,
                        "provenance_declarations": [
                            "ComplexityReduction.Certificate.NativeTMNPHard."
                            "ofCompleteAlongPath",
                            "ComplexityReduction.Routes.SourceToTarget.route",
                        ],
                        "target_declaration": (
                            "ComplexityReduction.Problems.Target.problem"
                        ),
                        "target_node_id": "lean-whnf:target",
                        "registry_fingerprint": "lean:registry",
                        "validation_source": "lean_registry_path_composition",
                    }
                ],
            }
        ],
        "reductions": [
            {
                "declaration": "ComplexityReduction.Routes.SourceToTarget.route",
                "namespace": "ComplexityReduction.Routes.SourceToTarget",
                "role": "sharedGadget",
                "source": verbose,
                "target": verbose,
                "source_fingerprint": "lean:source",
                "target_fingerprint": "lean:target",
                "source_node_id": "lean-whnf:source",
                "target_node_id": "lean-whnf:target",
            }
        ],
    }


def test_compact_retrieved_view_is_authorization_complete_and_much_smaller() -> None:
    full = full_retrieved_payload()
    compact = compact_retrieved_payload(full)
    payload = {
        "request": {"objective": "reduce_to_known_hardness"},
        "retrieved": compact,
        "retrieved_view": compact_retrieved_view_metadata(compact),
    }

    assert compact_retrieved_view_errors(payload) == ()
    assert payload["retrieved_view"]["mode"] == COMPACT_RETRIEVED_VIEW_MODE
    assert "semantic_summary" not in compact["problems"][0]
    assert "source" not in compact["reductions"][0]
    assert "evidence_lean_term" not in compact["hardness_targets"][0][
        "evidences"
    ][0]
    assert compact["hardness_targets"][0]["evidences"][0][
        "provenance_declarations"
    ]
    full_size = len(json.dumps(full, ensure_ascii=False, separators=(",", ":")))
    compact_size = len(
        json.dumps(compact, ensure_ascii=False, separators=(",", ":"))
    )
    assert compact_size < full_size * 0.5

    metrics = retrieved_prompt_metrics(payload)
    assert metrics["retrieved_view_mode"] == COMPACT_RETRIEVED_VIEW_MODE
    assert metrics["compact_view_errors"] == []
    assert metrics["retrieved_counts"] == {
        "problems": 1,
        "connections": 1,
        "hardness_targets": 1,
        "reductions": 1,
    }


def test_compact_retrieved_view_audit_rejects_lost_authorization_fields() -> None:
    compact = compact_retrieved_payload(full_retrieved_payload())
    del compact["reductions"][0]["target_node_id"]
    payload = {
        "request": {"objective": "reduce_to_known_hardness"},
        "retrieved": compact,
        "retrieved_view": compact_retrieved_view_metadata(compact),
    }

    errors = compact_retrieved_view_errors(payload)
    assert any("target_node_id" in error for error in errors)
