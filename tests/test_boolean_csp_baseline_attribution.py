from __future__ import annotations

from agent.generative_reduction.boolean_csp_regression import (
    BASELINE_POLICY_NAME,
    DEFAULT_REPORT_NAME,
    _baseline_attribution,
    _boolean_csp_plugin_inventory,
    _repair_prompts_have_matching_base_hash,
)


def test_baseline_attribution_separates_reuse_and_final_used_plugin_work() -> None:
    report = _baseline_attribution(
        (
            {
                "case_id": "anchor",
                "proof_status": "VERIFIED",
                "solution_classification": "VERIFIED_REUSE",
                "contribution_receipts": (),
                "proof_tree": (),
                "selected_proof_route": ("Example.anchor",),
                "model_calls": (),
            },
            {
                "case_id": "authored",
                "proof_status": "VERIFIED",
                "solution_classification": "VERIFIED_AUXILIARY_GENERATION",
                "contribution_receipts": (
                    {
                        "capability_declaration": "Example.generated",
                        "contribution_class": "DETERMINISTIC_GENERATED_CAPABILITY",
                        "final_artifact_used": True,
                    },
                    {
                        "capability_declaration": "Example.abandoned",
                        "contribution_class": "MODEL_GENERATED_CAPABILITY",
                        "final_artifact_used": False,
                    },
                ),
                "proof_tree": (
                    {
                        "provider": "plugin",
                        "solver": "boolean-csp-explicit-finite-gadget",
                        "declaration": "Example.generated",
                    },
                ),
                "selected_proof_route": (),
                "model_calls": ({"called": True},),
            },
        )
    )

    assert report["case_count"] == 2
    assert report["exact_reuse_case_ids"] == ["anchor"]
    assert report["contribution_class_case_counts"] == {
        "DETERMINISTIC_GENERATED_CAPABILITY": 1,
        "THEOREM_REUSE": 1,
    }
    assert report["finite_plugin_case_counts"] == {
        "boolean-csp-explicit-finite-gadget": 1
    }
    assert report["nonreuse_without_real_model_call_case_ids"] == []


def test_deterministic_baseline_inventory_records_all_runtime_finite_plugins() -> None:
    inventory = _boolean_csp_plugin_inventory()

    assert BASELINE_POLICY_NAME == "deterministic-baseline"
    assert "DETERMINISTIC_BASELINE" in DEFAULT_REPORT_NAME
    assert inventory["disabled_finite_synthesis_plugins"] == []
    assert inventory["installed_finite_synthesis_plugins"] == [
        "boolean-csp-direct-tm-compiler",
        "boolean-csp-semantic-compiler",
        "boolean-csp-explicit-finite-gadget",
        "boolean-csp-canonical-database",
    ]
    assert inventory["runtime_finite_synthesis_plugins"] == inventory[
        "installed_finite_synthesis_plugins"
    ]


def test_repair_base_hash_audit_accepts_transport_failure_after_bound_prompt() -> None:
    initial_hash = "sha256:initial-payload"
    rows = (
        {
            "typed_capability_plans": (
                {
                    "schema_version": "boolean_csp_gadget_authoring_receipt_v1",
                    "design_id": "design-1",
                    "kind": "initial",
                    "model_attempt": {
                        "requested_base_sha256": None,
                        "returned_base_sha256": None,
                        "response_payload_sha256": initial_hash,
                    },
                },
                {
                    "schema_version": "boolean_csp_gadget_authoring_receipt_v1",
                    "design_id": "design-1",
                    "kind": "repair",
                    "model_attempt": {
                        "requested_base_sha256": initial_hash,
                        "returned_base_sha256": None,
                        "response_payload_sha256": "sha256:empty-transport-payload",
                    },
                },
            ),
            "repair_lineage": (
                {
                    "kind": "repair",
                    "protocol": "structured-gadget-authoring",
                    "requested_base_sha256": initial_hash,
                    "returned_base_sha256": None,
                },
            ),
        },
    )

    assert _repair_prompts_have_matching_base_hash(rows)

    rows[0]["typed_capability_plans"][1]["model_attempt"][
        "requested_base_sha256"
    ] = "sha256:wrong"
    assert not _repair_prompts_have_matching_base_hash(rows)
