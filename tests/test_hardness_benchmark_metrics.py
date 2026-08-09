from agent.hardness.benchmark import summarize_benchmark_results


def test_positive_negative_axiom_replay_and_authoring_rates_are_separate() -> None:
    results = [
        {
            "id": "authored",
            "objective": "reduce_to",
            "expected_status": "VERIFIED",
            "actual_status": "VERIFIED",
            "passed": True,
            "requires_authoring": True,
            "new_certified_reduction": True,
            "axiom_clean": True,
            "deterministic_replay": True,
        },
        {
            "id": "blocked",
            "objective": "reduce_to",
            "expected_status": "BLOCKED",
            "actual_status": "BLOCKED",
            "passed": True,
            "requires_authoring": True,
            "new_certified_reduction": False,
        },
    ]
    metrics = summarize_benchmark_results(results=results)["metrics"]
    assert metrics == {
        "case_outcome_accuracy": 1.0,
        "positive_final_verified_rate": 1.0,
        "negative_block_accuracy": 1.0,
        "full_reduction_authored_rate": 1.0,
        "native_membership_rate": None,
        "native_completeness_rate": None,
        "axiom_clean_rate": 1.0,
        "deterministic_replay_rate": 1.0,
        "matched_pair_both_verified_rate": None,
    }


def test_empty_lane_rate_is_null_not_a_false_success() -> None:
    metrics = summarize_benchmark_results(results=[])["metrics"]
    assert all(value is None for value in metrics.values())


def test_capability_lane_rates_do_not_dilute_reduction_authoring() -> None:
    results = [
        {
            "id": "membership",
            "objective": "prove_in_np",
            "expected_status": "VERIFIED",
            "actual_status": "VERIFIED",
            "passed": True,
            "requires_authoring": True,
            "new_certified_reduction": False,
            "axiom_clean": True,
            "deterministic_replay": True,
        },
        {
            "id": "complete",
            "objective": "prove_np_complete",
            "expected_status": "VERIFIED",
            "actual_status": "VERIFIED",
            "passed": True,
            "requires_authoring": False,
            "new_certified_reduction": False,
            "axiom_clean": True,
            "deterministic_replay": True,
        },
    ]
    metrics = summarize_benchmark_results(results=results)["metrics"]
    assert metrics["full_reduction_authored_rate"] is None
    assert metrics["native_membership_rate"] == 1.0
    assert metrics["native_completeness_rate"] == 1.0


def test_existing_fixture_and_model_synthesis_lanes_are_never_mixed() -> None:
    results = [
        {
            "id": "route",
            "evaluation_lane": "existing_route",
            "objective": "reduce_to",
            "expected_status": "VERIFIED",
            "actual_status": "VERIFIED",
            "passed": True,
            "requires_authoring": False,
            "model_call_count": 0,
        },
        {
            "id": "fixture",
            "evaluation_lane": "deterministic_fixture",
            "objective": "reduce_to",
            "expected_status": "VERIFIED",
            "actual_status": "VERIFIED",
            "passed": True,
            "requires_authoring": True,
            "new_certified_reduction": True,
            "model_call_count": 0,
        },
        {
            "id": "model",
            "evaluation_lane": "model_synthesis",
            "objective": "reduce_to",
            "expected_status": "VERIFIED",
            "actual_status": "BLOCKED",
            "passed": False,
            "requires_authoring": True,
            "model_call_count": 3,
        },
    ]
    lanes = summarize_benchmark_results(results=results)["evaluation_lanes"]
    assert lanes["existing_route"]["outcome_accuracy"] == 1.0
    assert lanes["deterministic_fixture"]["outcome_accuracy"] == 1.0
    assert lanes["model_synthesis"]["outcome_accuracy"] == 0.0
    assert lanes["model_synthesis"]["model_call_count"] == 3
    assert lanes["model_synthesis"]["capability_closure_rate"] == 0.0


def test_ir_metrics_pair_outcomes_and_deduplicate_catalog_and_selected_atoms() -> None:
    flat_catalog = [
        {
            "entry_id": f"flat-{index}",
            "declaration": f"Facade.{index}",
            "component_role": "finalComposition",
            "is_final_facade": True,
        }
        for index in range(4)
    ]
    ir_catalog = [
        {
            "entry_id": entry_id,
            "declaration": declaration,
            "component_role": role,
            "is_final_facade": False,
        }
        for entry_id, declaration, role in (
            ("ir-a", "Edge.ingressA", "ingress"),
            ("ir-b", "Edge.ingressB", "ingress"),
            ("ir-shared", "Edge.shared", "sharedGadget"),
        )
    ]

    def row(
        pair: str,
        mode: str,
        atoms: list[str],
        roles: list[str],
    ) -> dict[str, object]:
        return {
            "id": f"{pair}-{mode}",
            "evaluation_lane": "ir_feasibility",
            "matched_pair_id": pair,
            "family_id": "graph-family",
            "catalog_mode": mode,
            "expected_status": "VERIFIED",
            "actual_status": "VERIFIED",
            "passed": True,
            "route_atoms": atoms,
            "route_roles": roles,
            "route_atom_count": len(atoms),
            "catalog_id": f"catalog-{mode}",
            "catalog_entries": flat_catalog if mode == "flat_api" else ir_catalog,
        }

    results = [
        row("pair-a", "flat_api", ["Facade.a"], ["finalComposition"]),
        row(
            "pair-a",
            "ir_components",
            ["Edge.ingressA", "Edge.shared"],
            ["ingress", "sharedGadget"],
        ),
        row("pair-b", "flat_api", ["Facade.b"], ["finalComposition"]),
        row(
            "pair-b",
            "ir_components",
            ["Edge.ingressB", "Edge.shared"],
            ["ingress", "sharedGadget"],
        ),
    ]
    summary = summarize_benchmark_results(results=results)
    study = summary["ir_feasibility"]
    assert study["matched_pair_both_verified_rate"] == 1.0
    assert summary["metrics"]["matched_pair_both_verified_rate"] == 1.0
    aggregate = study["aggregate"]
    assert aggregate["agent_interface_compression_ratio"] == 0.25
    assert aggregate["ir_component_reuse_factor"] == 0.666667
    assert aggregate["average_route_atom_overhead"] == 1.0
    assert aggregate["selected_semantic_atomic_compression_ratio"] is None
    flat = aggregate["modes"]["flat_api"]
    ir = aggregate["modes"]["ir_components"]
    assert flat["selected_final_facade_count"] == 2
    assert flat["selected_semantic_atomic_interface_count"] == 0
    assert ir["selected_semantic_atomic_interfaces"] == [
        "Edge.ingressA",
        "Edge.ingressB",
        "Edge.shared",
    ]
    assert ir["reused_semantic_atomic_interfaces"] == ["Edge.shared"]
    assert study["families"][0]["family_id"] == "graph-family"
