import copy

import pytest

from agent.hardness.models import TypedCatalog, TypedInventoryEntry
from agent.hardness.plan import (
    PLAN_OUTPUT_SCHEMA,
    PLAN_SCHEMA,
    PLAN_STEP_SCHEMA,
    PlanValidationError,
    parse_hardness_plan,
)
from agent.hardness.plan_profiles import validate_existing_reduction_profile


def reduction_entry(
    declaration: str, *, role: str, source: str, target: str
) -> TypedInventoryEntry:
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
    )


def reduction_catalog() -> TypedCatalog:
    return TypedCatalog(
        mode="ir_components",
        registry_fingerprint="registry-1",
        entries=(
            reduction_entry(
                "Edge.ingress", role="ingress", source="Source", target="Hub"
            ),
            reduction_entry(
                "Edge.shared", role="sharedGadget", source="Hub", target="Target"
            ),
        ),
    )


def open_plan_payload() -> dict:
    return {
        "schema_version": PLAN_SCHEMA,
        "objective": "establish_np_completeness",
        "source_declaration": "Input.problem",
        "target_declaration": "Target.problem",
        "steps": [
            {
                "schema_version": PLAN_STEP_SCHEMA,
                "step_id": "equiv",
                "action_kind": "reuse.certified_equiv",
                "declaration": "Equiv.inputToCanonical",
                "output_handles": ["canonical_problem"],
            },
            {
                "schema_version": PLAN_STEP_SCHEMA,
                "step_id": "family",
                "action_kind": "instantiate.family",
                "declaration": "Family.canonicalHardness",
                "argument_declarations": ["Input.parameter"],
                "depends_on": ["equiv"],
                "input_handles": ["canonical_problem"],
                "output_handles": ["hardness_evidence"],
            },
            {
                "schema_version": PLAN_STEP_SCHEMA,
                "step_id": "membership",
                "action_kind": "evidence.native_membership",
                "declaration": "Input.inNP",
                "output_handles": ["membership_evidence"],
            },
            {
                "schema_version": PLAN_STEP_SCHEMA,
                "step_id": "assemble",
                "action_kind": "author.local_lemma",
                "depends_on": ["family", "membership"],
                "input_handles": ["hardness_evidence", "membership_evidence"],
                "parameters": {"lemma_shape": "np_complete"},
            },
        ],
        "outputs": [
            {
                "schema_version": PLAN_OUTPUT_SCHEMA,
                "output_id": "completed_theorem",
                "output_kind": "lean.declaration",
                "producer_steps": ["assemble"],
                "declaration_name": "Generated.inputNPComplete",
                "metadata": {"backend": "lean4"},
            }
        ],
    }


def existing_reduction_payload() -> tuple[TypedCatalog, dict]:
    catalog = reduction_catalog()
    expected_type = (
        "ComplexityReduction.Certificate.CertifiedPath "
        "Input.source Input.target"
    )
    payload = {
        "schema_version": PLAN_SCHEMA,
        "objective": "reduce_to",
        "source_declaration": "Input.source",
        "target_declaration": "Input.target",
        "registry_fingerprint": catalog.registry_fingerprint,
        "catalog_id": catalog.catalog_id,
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
    }
    return catalog, payload


def test_core_plan_parser_accepts_non_reduction_objective_and_open_actions() -> None:
    plan = parse_hardness_plan(open_plan_payload())

    assert plan.objective == "establish_np_completeness"
    assert [step.action_kind for step in plan.steps] == [
        "reuse.certified_equiv",
        "instantiate.family",
        "evidence.native_membership",
        "author.local_lemma",
    ]
    assert plan.outputs[0].output_kind == "lean.declaration"


def test_current_existing_reduction_profile_is_a_separate_narrow_projection() -> None:
    catalog, payload = existing_reduction_payload()
    plan = parse_hardness_plan(payload)

    view = validate_existing_reduction_profile(
        plan,
        catalog=catalog,
        source_declaration="Input.source",
        target_declaration="Input.target",
        maximum_steps=8,
        require_single_step=False,
    )

    assert view.declarations == ("Edge.ingress", "Edge.shared")
    assert view.roles == ("ingress", "sharedGadget")


def test_current_profile_rejects_actions_that_remain_valid_in_core_plan() -> None:
    catalog, payload = existing_reduction_payload()
    payload["steps"][0]["action_kind"] = "reuse.certified_equiv"
    plan = parse_hardness_plan(payload)

    with pytest.raises(
        PlanValidationError,
        match="accepts only reuse.certified_reduction",
    ):
        validate_existing_reduction_profile(
            plan,
            catalog=catalog,
            source_declaration="Input.source",
            target_declaration="Input.target",
            maximum_steps=8,
            require_single_step=False,
        )


def test_current_profile_rejects_backend_outputs_outside_its_contract() -> None:
    catalog, payload = existing_reduction_payload()
    payload["outputs"].append(
        {
            "schema_version": PLAN_OUTPUT_SCHEMA,
            "output_id": "audit_note",
            "output_kind": "report.note",
            "producer_steps": ["s2"],
        }
    )
    plan = parse_hardness_plan(payload)

    with pytest.raises(PlanValidationError, match="exactly one selected_path"):
        validate_existing_reduction_profile(
            plan,
            catalog=catalog,
            source_declaration="Input.source",
            target_declaration="Input.target",
            maximum_steps=8,
            require_single_step=False,
        )


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        (lambda raw: raw["steps"][0].update(depends_on=["missing"]), "unknown dependencies"),
        (
            lambda raw: raw["outputs"][0].update(producer_steps=["missing"]),
            "unknown producers",
        ),
    ],
)
def test_plan_graph_rejects_unknown_references(mutation, message: str) -> None:
    payload = open_plan_payload()
    mutation(payload)

    with pytest.raises(PlanValidationError, match=message):
        parse_hardness_plan(payload)


def test_plan_graph_rejects_dependency_cycles() -> None:
    payload = open_plan_payload()
    payload["steps"][0]["depends_on"] = ["assemble"]

    with pytest.raises(PlanValidationError, match="contains a cycle"):
        parse_hardness_plan(payload)


def test_unknown_fields_are_preserved_as_extensions_at_every_level() -> None:
    payload = open_plan_payload()
    payload["vendor_plan_hint"] = {"priority": 2}
    payload["extensions"] = {"org.example.trace": "trace-1"}
    payload["steps"][0]["vendor_step_cost"] = 17
    payload["steps"][0]["extensions"] = {"org.example.memo": True}
    payload["outputs"][0]["vendor_output_format"] = "declaration"

    plan = parse_hardness_plan(payload)
    serialized = plan.to_dict()

    assert plan.extensions == {
        "org.example.trace": "trace-1",
        "vendor_plan_hint": {"priority": 2},
    }
    assert plan.steps[0].extensions == {
        "org.example.memo": True,
        "vendor_step_cost": 17,
    }
    assert plan.outputs[0].extensions == {
        "vendor_output_format": "declaration"
    }
    assert parse_hardness_plan(serialized).to_dict() == serialized


def test_plan_id_is_stable_and_bound_to_normalized_content() -> None:
    first = parse_hardness_plan(open_plan_payload())
    reordered = copy.deepcopy(open_plan_payload())
    reordered = dict(reversed(list(reordered.items())))
    second = parse_hardness_plan(reordered)

    assert first.plan_id == second.plan_id
    assert first.plan_id.startswith("sha256:")

    changed = open_plan_payload()
    changed["metadata"] = {"planner": "different"}
    assert parse_hardness_plan(changed).plan_id != first.plan_id


def test_supplied_plan_id_and_nested_schema_versions_fail_closed() -> None:
    plan = parse_hardness_plan(open_plan_payload())
    serialized = plan.to_dict()
    serialized["plan_id"] = "sha256:" + "0" * 64

    with pytest.raises(PlanValidationError, match="does not match"):
        parse_hardness_plan(serialized)

    wrong_step_schema = open_plan_payload()
    wrong_step_schema["steps"][0]["schema_version"] = "future_step_v9"
    with pytest.raises(
        PlanValidationError, match=r"unsupported plan.steps\[0\] schema"
    ):
        parse_hardness_plan(wrong_step_schema)
