import json

from agent.hardness.model_client import ModelResponse
from agent.hardness.models import TypedCatalog, TypedInventoryEntry
from agent.hardness.plan import PLAN_OUTPUT_SCHEMA, PLAN_SCHEMA, PLAN_STEP_SCHEMA
from agent.hardness.planner import (
    build_deepseek_lean_prompt,
    build_deepseek_route_prompt,
    choose_route_with_deepseek,
    generate_lean_path_with_deepseek,
)


def entry(declaration: str, *, role: str, source: str, target: str) -> TypedInventoryEntry:
    return TypedInventoryEntry(
        declaration=declaration,
        capability_kind="certified_reduction",
        component_role=role,
        source_fingerprint=f"lean:{source}",
        target_fingerprint=f"lean:{target}",
        is_final_facade=role == "finalComposition",
        discovery="registered",
        registry_fingerprint="registry-1",
        source_display=source,
        target_display=target,
        source_node_id=f"node:{source}",
        target_node_id=f"node:{target}",
    )


def catalog(mode: str = "ir_components") -> TypedCatalog:
    return TypedCatalog(
        mode=mode,
        registry_fingerprint="registry-1",
        entries=(
            entry("Edge.ingress", role="ingress", source="Source", target="Hub"),
            entry("Edge.shared", role="sharedGadget", source="Hub", target="Target"),
        ),
    )


class FakeClient:
    def __init__(self, payload: object | tuple[object, ...], *, ok: bool = True):
        self.payloads = payload if isinstance(payload, tuple) else (payload,)
        self.ok = ok
        self.call_count = 0

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        assert (
            "Never invent declarations" in system
            or "navigate a compiled Lean theorem index" in system
        )
        parsed_prompt = json.loads(prompt)
        assert parsed_prompt["catalog_id"].startswith("sha256:")
        if "navigate a compiled Lean theorem index" in system:
            assert "library_architecture" in parsed_prompt
            assert "catalog_entries" not in parsed_prompt
        if self.call_count >= len(self.payloads):
            raise AssertionError("FakeClient received more calls than fixtures")
        payload = self.payloads[self.call_count]
        self.call_count += 1
        return ModelResponse(
            called=True,
            ok=self.ok,
            content=json.dumps(payload) if self.ok else "",
            error=None if self.ok else "request failed",
            status_code=200 if self.ok else 500,
            duration_seconds=0.1,
            usage={"total_tokens": 42},
            attempts=1,
        )


def search_edges() -> dict:
    return {
        "action": "search",
        "searches": [{"namespace_prefixes": ["Edge"], "limit": 8}],
        "reason": "inspect the small Edge namespace",
    }


def choose(client: FakeClient, *, selected_catalog: TypedCatalog | None = None):
    return choose_route_with_deepseek(
        catalog=selected_catalog or catalog(),
        source_declaration="Input.source",
        source_display="Source",
        target_declaration="Input.target",
        target_display="Target",
        client=client,  # type: ignore[arg-type]
    )


def test_deepseek_planner_accepts_only_allowlisted_ordered_atoms() -> None:
    result = choose(
        FakeClient(
            {"atoms": ["Edge.ingress", "Edge.shared"], "reason": "via shared hub"}
        )
    )

    assert result.protocol_accepted is True
    assert result.route is not None
    assert result.route.atoms == ("Edge.ingress", "Edge.shared")
    assert result.route.roles == ("ingress", "sharedGadget")
    assert result.decision.mode == "deepseek"
    assert result.decision.model_called is True
    assert result.decision.model_ok is True


def test_deepseek_planner_rejects_declarations_outside_catalog() -> None:
    result = choose(FakeClient({"atoms": ["Edge.invented"]}))

    assert result.route is None
    assert result.protocol_accepted is False
    assert result.decision.model_ok is False
    assert result.decision.model_error == (
        "DeepSeek selected a declaration outside the catalog allowlist"
    )


def test_flat_catalog_requires_one_selected_declaration() -> None:
    flat = TypedCatalog(
        mode="flat_api",
        registry_fingerprint="registry-1",
        entries=(
            entry("Edge.final", role="finalComposition", source="Source", target="Target"),
            entry("Edge.direct", role="unannotated", source="Source", target="Target"),
        ),
    )
    result = choose(
        FakeClient({"atoms": ["Edge.final", "Edge.direct"]}),
        selected_catalog=flat,
    )

    assert result.route is None
    assert result.decision.model_error == (
        "flat_api route selection requires exactly one declaration"
    )


def test_deepseek_prompt_contains_catalog_endpoints_but_no_proof_body() -> None:
    prompt = json.loads(
        build_deepseek_route_prompt(
            catalog=catalog(),
            source_declaration="Input.source",
            source_display="Source",
            target_declaration="Input.target",
            target_display="Target",
        )
    )

    assert prompt["request"]["source_declaration"] == "Input.source"
    assert prompt["catalog_entries"][0]["declaration"] == "Edge.ingress"
    assert "proof" not in prompt
    assert "lean_source" not in prompt


def test_deepseek_accepts_native_open_plan_under_the_active_profile() -> None:
    selected_catalog = catalog()
    expected_type = (
        "ComplexityReduction.Certificate.CertifiedPath "
        "Input.source Input.target"
    )
    result = generate_lean_path_with_deepseek(
        catalog=selected_catalog,
        source_declaration="Input.source",
        source_display="Source",
        target_declaration="Input.target",
        target_display="Target",
        client=FakeClient(
            (
                search_edges(),
                {
                    "action": "finish",
                    "plan": {
                    "schema_version": PLAN_SCHEMA,
                    "objective": "reduce_to",
                    "source_declaration": "Input.source",
                    "target_declaration": "Input.target",
                    "registry_fingerprint": selected_catalog.registry_fingerprint,
                    "catalog_id": selected_catalog.catalog_id,
                    "steps": [
                        {
                            "schema_version": PLAN_STEP_SCHEMA,
                            "step_id": "s1",
                            "action_kind": "reuse.certified_reduction",
                            "capability_kind": "certified_reduction",
                            "declaration": "Edge.ingress",
                            "role": "ingress",
                        },
                        {
                            "schema_version": PLAN_STEP_SCHEMA,
                            "step_id": "s2",
                            "action_kind": "reuse.certified_reduction",
                            "capability_kind": "certified_reduction",
                            "declaration": "Edge.shared",
                            "depends_on": ["s1"],
                            "role": "sharedGadget",
                        },
                    ],
                    "outputs": [
                        {
                            "schema_version": PLAN_OUTPUT_SCHEMA,
                            "output_id": "selected_path",
                            "output_kind": "lean.term",
                            "producer_steps": ["s1", "s2"],
                            "expected_type": expected_type,
                            "lean_code": (
                                "ComplexityReduction.Certificate.CertifiedPath.cons "
                                "(ComplexityReduction.Certificate.CertifiedPath.step "
                                "Edge.ingress) Edge.shared"
                            ),
                        }
                    ],
                    },
                    "reason": "compose the existing ingress and shared gadget",
                },
            )
        ),  # type: ignore[arg-type]
    )

    assert result.protocol_accepted is True
    assert result.declarations == ("Edge.ingress", "Edge.shared")
    assert result.plan is not None
    assert result.decision.selected_route_id == result.plan.plan_id
    assert len(result.model_responses) == 2
    assert result.retrieved_declarations == ("Edge.ingress", "Edge.shared")
    assert result.lean_term is not None
    assert "CertifiedPath.cons" in result.lean_term


def test_deepseek_small_codegen_payload_is_adapted_to_plan() -> None:
    result = generate_lean_path_with_deepseek(
        catalog=catalog(),
        source_declaration="Input.source",
        source_display="Source",
        target_declaration="Input.target",
        target_display="Target",
        client=FakeClient(
            (
                search_edges(),
                {
                    "action": "finish",
                    "declarations": ["Edge.ingress", "Edge.shared"],
                    "lean_term": (
                        "ComplexityReduction.Certificate.CertifiedPath.cons "
                        "(ComplexityReduction.Certificate.CertifiedPath.step "
                        "Edge.ingress) Edge.shared"
                    ),
                    "reason": "compose the existing ingress and shared gadget",
                },
            )
        ),  # type: ignore[arg-type]
    )

    assert result.protocol_accepted is True
    assert result.declarations == ("Edge.ingress", "Edge.shared")
    assert result.plan is not None
    assert result.plan.metadata["adapted_from"] == (
        "existing_reduction_codegen_response_v1"
    )
    assert result.lean_term is not None
    assert "CertifiedPath.cons" in result.lean_term


def test_deepseek_accepts_one_extra_action_wrapper() -> None:
    selected_catalog = catalog(mode="flat_api")
    selected_catalog = TypedCatalog(
        mode="flat_api",
        registry_fingerprint=selected_catalog.registry_fingerprint,
        entries=(
            entry("Edge.final", role="finalComposition", source="Source", target="Target"),
        ),
    )
    result = generate_lean_path_with_deepseek(
        catalog=selected_catalog,
        source_declaration="Input.source",
        source_display="Source",
        target_declaration="Input.target",
        target_display="Target",
        client=FakeClient(
            (
                {
                    "action": "search",
                    "searches": [{"namespace_prefixes": ["Edge"]}],
                },
                {
                    "search": {
                        "searches": [{"namespace_prefixes": ["Edge"]}],
                        "reason": "double-check the same narrow namespace",
                    }
                },
                {
                    "finish": {
                        "plan": {
                            "schema_version": PLAN_SCHEMA,
                            "objective": "reduce_to",
                            "source_declaration": "Input.source",
                            "target_declaration": "Input.target",
                            "registry_fingerprint": selected_catalog.registry_fingerprint,
                            "catalog_id": selected_catalog.catalog_id,
                            "steps": [
                                {
                                    "schema_version": PLAN_STEP_SCHEMA,
                                    "step_id": "s1",
                                    "action_kind": "reuse.certified_reduction",
                                    "capability_kind": "certified_reduction",
                                    "declaration": "Edge.final",
                                    "role": "finalComposition",
                                }
                            ],
                            "outputs": [
                                {
                                    "schema_version": PLAN_OUTPUT_SCHEMA,
                                    "output_id": "selected_path",
                                    "output_kind": "lean.term",
                                    "producer_steps": ["s1"],
                                    "expected_type": (
                                        "ComplexityReduction.Certificate.CertifiedPath "
                                        "Input.source Input.target"
                                    ),
                                    "lean_code": (
                                        "ComplexityReduction.Certificate.CertifiedPath.step "
                                        "Edge.final"
                                    ),
                                }
                            ],
                        }
                    }
                },
            )
        ),  # type: ignore[arg-type]
    )

    assert result.protocol_accepted is True
    assert result.declarations == ("Edge.final",)


def test_deepseek_lean_codegen_rejects_placeholders_before_final_lean_run() -> None:
    result = generate_lean_path_with_deepseek(
        catalog=catalog(),
        source_declaration="Input.source",
        source_display="Source",
        target_declaration="Input.target",
        target_display="Target",
        client=FakeClient(
            (
                search_edges(),
                {
                    "action": "finish",
                    "declarations": ["Edge.ingress"],
                    "lean_term": "by sorry",
                },
            )
        ),  # type: ignore[arg-type]
    )

    assert result.protocol_accepted is False
    assert result.lean_term is None
    assert result.decision.model_error == (
        "DeepSeek Lean term contains a forbidden command or placeholder"
    )


def test_deepseek_lean_prompt_requests_a_term_of_the_exact_endpoint_type() -> None:
    prompt = json.loads(
        build_deepseek_lean_prompt(
            catalog=catalog(),
            source_declaration="Input.source",
            source_display="Source",
            target_declaration="Input.target",
            target_display="Target",
        )
    )

    assert prompt["expected_type"].endswith("Input.source Input.target")
    assert (
        prompt["constraints"][
            "return_ordered_declarations_and_one_term"
        ]
        is True
    )
    assert prompt["execution_profile"]["profile_id"].endswith("_v1")
    assert "do not output" in prompt["execution_profile"]["internal_record"]
    assert "plan_protocol" not in prompt
    assert prompt["retrieved_entries"] == []
    assert "catalog_entries" not in prompt
    architecture = prompt["library_architecture"]
    assert architecture["full_namespace_topology_included"] is False
    assert "namespaces" not in architecture
    assert architecture["catalog_summary"] == {
        "namespace_count": 1,
        "reduction_declaration_count": 2,
        "role_counts": {"ingress": 1, "sharedGadget": 1},
    }
    assert len(json.dumps(architecture, ensure_ascii=False)) < 3000
    assert "inspect_architecture" in prompt["response_options"]
    finish = prompt["response_options"]["finish"]
    assert finish["declarations"]
    assert finish["lean_term"].startswith("Lean expression")


def test_deepseek_lean_prompt_allows_finish_after_search_results_exist() -> None:
    selected_catalog = catalog()
    prompt = json.loads(
        build_deepseek_lean_prompt(
            catalog=selected_catalog,
            source_declaration="Input.source",
            source_display="Source",
            target_declaration="Input.target",
            target_display="Target",
            retrieved_entries=(selected_catalog.entries[0],),
            round_index=2,
            maximum_rounds=4,
            search_rounds_used=1,
        )
    )

    state = prompt["retrieval_state"]
    assert state["must_search_before_finish"] is False
    assert state["may_finish_if_the_retrieved_path_is_complete"] is False
    assert state["query_rounds_remaining"] == 3


def test_deepseek_lean_prompt_exposes_only_retrieved_connectivity() -> None:
    selected_catalog = catalog()
    prompt = json.loads(
        build_deepseek_lean_prompt(
            catalog=selected_catalog,
            source_declaration="Input.source",
            source_display="Source",
            source_node_id="node:Source",
            target_declaration="Input.target",
            target_display="Target",
            target_node_id="node:Target",
            retrieved_entries=selected_catalog.entries,
            round_index=3,
            maximum_rounds=4,
        )
    )

    assert prompt["request"]["source_node_id"] == "node:Source"
    assert prompt["request"]["target_node_id"] == "node:Target"
    assert prompt["retrieved_connectivity"]["complete_paths"] == [
        ["Edge.ingress", "Edge.shared"]
    ]
    assert "catalog_entries" not in prompt


def test_deepseek_node_search_builds_a_complete_path_incrementally() -> None:
    selected_catalog = catalog()
    expected_type = (
        "ComplexityReduction.Certificate.CertifiedPath "
        "Input.source Input.target"
    )
    result = generate_lean_path_with_deepseek(
        catalog=selected_catalog,
        source_declaration="Input.source",
        source_display="Source",
        source_node_id="node:Source",
        target_declaration="Input.target",
        target_display="Target",
        target_node_id="node:Target",
        client=FakeClient(
            (
                {
                    "action": "search",
                    "searches": [{"source_node_ids": ["node:Source"]}],
                },
                {
                    "action": "search",
                    "searches": [{"source_node_ids": ["node:Hub"]}],
                },
                {
                    "action": "finish",
                    "plan": {
                        "schema_version": PLAN_SCHEMA,
                        "objective": "reduce_to",
                        "source_declaration": "Input.source",
                        "target_declaration": "Input.target",
                        "registry_fingerprint": selected_catalog.registry_fingerprint,
                        "catalog_id": selected_catalog.catalog_id,
                        "steps": [
                            {
                                "schema_version": PLAN_STEP_SCHEMA,
                                "step_id": "s1",
                                "action_kind": "reuse.certified_reduction",
                                "capability_kind": "certified_reduction",
                                "declaration": "Edge.ingress",
                                "role": "ingress",
                            },
                            {
                                "schema_version": PLAN_STEP_SCHEMA,
                                "step_id": "s2",
                                "action_kind": "reuse.certified_reduction",
                                "capability_kind": "certified_reduction",
                                "declaration": "Edge.shared",
                                "depends_on": ["s1"],
                                "role": "sharedGadget",
                            },
                        ],
                        "outputs": [
                            {
                                "schema_version": PLAN_OUTPUT_SCHEMA,
                                "output_id": "selected_path",
                                "output_kind": "lean.term",
                                "producer_steps": ["s1", "s2"],
                                "expected_type": expected_type,
                                "lean_code": (
                                    "ComplexityReduction.Certificate.CertifiedPath.cons "
                                    "(ComplexityReduction.Certificate.CertifiedPath.step "
                                    "Edge.ingress) Edge.shared"
                                ),
                            }
                        ],
                    },
                },
            )
        ),  # type: ignore[arg-type]
    )

    assert result.protocol_accepted is True
    assert len(result.model_responses) == 3
    assert result.declarations == ("Edge.ingress", "Edge.shared")
    assert [row["new_declarations"] for row in result.retrieval_trace] == [
        ["Edge.ingress"],
        ["Edge.shared"],
    ]


def test_model_can_inspect_architecture_before_retrieving_theorems() -> None:
    result = generate_lean_path_with_deepseek(
        catalog=catalog(),
        source_declaration="Input.source",
        source_display="Source",
        source_node_id="node:Source",
        target_declaration="Input.target",
        target_display="Target",
        target_node_id="node:Target",
        maximum_retrieval_rounds=2,
        client=FakeClient(
            (
                {
                    "action": "inspect_architecture",
                    "queries": [{"namespace_prefixes": ["Edge"]}],
                },
                search_edges(),
                {
                    "action": "finish",
                    "declarations": ["Edge.ingress", "Edge.shared"],
                    "lean_term": (
                        "ComplexityReduction.Certificate.CertifiedPath.cons "
                        "(ComplexityReduction.Certificate.CertifiedPath.step "
                        "Edge.ingress) Edge.shared"
                    ),
                },
            )
        ),  # type: ignore[arg-type]
    )

    assert result.protocol_accepted is True
    assert len(result.model_responses) == 3
    assert result.retrieval_trace[0]["status"] == (
        "architecture_inspection_completed"
    )
    assert result.retrieval_trace[0]["contains_declaration_names"] is False
    assert result.retrieval_trace[1]["status"] == "search_completed"


def test_last_allowed_search_still_gets_a_finish_turn() -> None:
    result = generate_lean_path_with_deepseek(
        catalog=catalog(),
        source_declaration="Input.source",
        source_display="Source",
        source_node_id="node:Source",
        target_declaration="Input.target",
        target_display="Target",
        target_node_id="node:Target",
        maximum_retrieval_rounds=2,
        client=FakeClient(
            (
                {
                    "action": "search",
                    "searches": [{"source_node_ids": ["node:Source"]}],
                },
                {
                    "action": "search",
                    "searches": [{"source_node_ids": ["node:Hub"]}],
                },
                {
                    "action": "finish",
                    "declarations": ["Edge.ingress", "Edge.shared"],
                    "lean_term": (
                        "ComplexityReduction.Certificate.CertifiedPath.cons "
                        "(ComplexityReduction.Certificate.CertifiedPath.step "
                        "Edge.ingress) Edge.shared"
                    ),
                },
            )
        ),  # type: ignore[arg-type]
    )

    assert result.protocol_accepted is True
    assert len(result.model_responses) == 3


def test_invalid_search_shape_is_reported_to_the_model_for_repair() -> None:
    result = generate_lean_path_with_deepseek(
        catalog=catalog(),
        source_declaration="Input.source",
        source_display="Source",
        source_node_id="node:Source",
        target_declaration="Input.target",
        target_display="Target",
        target_node_id="node:Target",
        client=FakeClient(
            (
                {
                    "action": "search",
                    "searches": [
                        {
                            "namespace_prefixes": [
                                "A",
                                "B",
                                "C",
                                "D",
                                "E",
                                "F",
                                "G",
                            ]
                        }
                    ],
                },
                search_edges(),
                {
                    "action": "finish",
                    "declarations": ["Edge.ingress", "Edge.shared"],
                    "lean_term": (
                        "ComplexityReduction.Certificate.CertifiedPath.cons "
                        "(ComplexityReduction.Certificate.CertifiedPath.step "
                        "Edge.ingress) Edge.shared"
                    ),
                },
            )
        ),  # type: ignore[arg-type]
    )

    assert result.protocol_accepted is True
    assert len(result.model_responses) == 3
    assert result.retrieval_trace[0]["status"] == "rejected_model_action"
    repaired_prompt = json.loads(result.model_prompts[1])
    assert "at most 6 items" in repaired_prompt["protocol_feedback"][0][
        "validation_error"
    ]


def test_composite_plan_declaration_field_is_safely_normalized() -> None:
    selected_catalog = catalog()
    lean_term = (
        "ComplexityReduction.Certificate.CertifiedPath.cons "
        "(ComplexityReduction.Certificate.CertifiedPath.step Edge.ingress) "
        "Edge.shared"
    )
    result = generate_lean_path_with_deepseek(
        catalog=selected_catalog,
        source_declaration="Input.source",
        source_display="Source",
        source_node_id="node:Source",
        target_declaration="Input.target",
        target_display="Target",
        target_node_id="node:Target",
        client=FakeClient(
            (
                search_edges(),
                {
                    "action": "finish",
                    "plan": {
                        "schema_version": PLAN_SCHEMA,
                        "objective": "reduce_to",
                        "source_declaration": "Input.source",
                        "target_declaration": "Input.target",
                        "registry_fingerprint": selected_catalog.registry_fingerprint,
                        "catalog_id": selected_catalog.catalog_id,
                        "steps": [
                            {
                                "schema_version": PLAN_STEP_SCHEMA,
                                "step_id": "s1",
                                "action_kind": "reuse.certified_reduction",
                                "declaration": lean_term,
                            }
                        ],
                        "outputs": [
                            {
                                "schema_version": PLAN_OUTPUT_SCHEMA,
                                "output_id": "selected_path",
                                "output_kind": "lean.term",
                                "producer_steps": ["s1"],
                                "expected_type": (
                                    "ComplexityReduction.Certificate.CertifiedPath "
                                    "Input.source Input.target"
                                ),
                                "lean_code": lean_term,
                            }
                        ],
                    },
                },
            )
        ),  # type: ignore[arg-type]
    )

    assert result.protocol_accepted is True
    assert result.declarations == ("Edge.ingress", "Edge.shared")
    assert result.plan is not None
    assert result.plan.metadata["adapted_from"] == (
        "normalized_model_plan_declaration_field"
    )


def test_redundant_step_wrapper_on_later_edge_is_normalized() -> None:
    model_term = (
        "ComplexityReduction.Certificate.CertifiedPath.cons "
        "(ComplexityReduction.Certificate.CertifiedPath.step Edge.ingress) "
        "(ComplexityReduction.Certificate.CertifiedPath.step Edge.shared)"
    )
    result = generate_lean_path_with_deepseek(
        catalog=catalog(),
        source_declaration="Input.source",
        source_display="Source",
        source_node_id="node:Source",
        target_declaration="Input.target",
        target_display="Target",
        target_node_id="node:Target",
        client=FakeClient(
            (
                search_edges(),
                {
                    "action": "finish",
                    "declarations": ["Edge.ingress", "Edge.shared"],
                    "lean_term": model_term,
                },
            )
        ),  # type: ignore[arg-type]
    )

    assert result.protocol_accepted is True
    assert result.model_lean_term == model_term
    assert result.lean_term_normalized is True
    assert result.lean_term == (
        "ComplexityReduction.Certificate.CertifiedPath.cons "
        "(ComplexityReduction.Certificate.CertifiedPath.step Edge.ingress) "
        "Edge.shared"
    )
