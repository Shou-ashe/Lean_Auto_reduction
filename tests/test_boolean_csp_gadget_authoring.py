from __future__ import annotations

from dataclasses import asdict
import json
from pathlib import Path

import pytest

from agent.generative_reduction.budgets import BudgetTracker, SearchBudget
from agent.generative_reduction.boolean_csp_regression import (
    _adaptive_gadget_token_audit,
    _repair_prompts_have_matching_base_hash,
)
from agent.generative_reduction.capability_gate_policy import gadget_authoring_policy
from agent.generative_reduction.boolean_csp_gadget_authoring import (
    BooleanCSPGadgetAuthoringBrief,
    BooleanCSPGadgetContext,
    BooleanCSPGadgetPlanV1,
    BooleanCSPGadgetProtocolError,
    GADGET_PLAN_SCHEMA,
    GADGET_RENDERER_VERSION,
    GADGET_SEMANTIC_CHECKER_VERSION,
    NAE3_CORE,
    check_explicit_gadget_plan,
    render_boolean_csp_gadget_plan,
)
from agent.generative_reduction.lean_bridge import run_lean_file
from agent.generative_reduction.model.gadget_authoring import (
    propose_gadget_plan_repair,
    propose_initial_gadget_plan,
)
from agent.generative_reduction.reconstruction import (
    build_authored_capability_source,
)
from agent.generative_reduction.job import GeneralJobStore
from agent.generative_reduction.models import (
    ActionDisposition,
    CandidateAction,
    ConstructionContract,
    ExactClosureResult,
    GoalKind,
    ModelPolicy,
    ProviderKind,
    RootGoal,
    SubstepPlan,
)
from agent.generative_reduction.premise_registry import PremiseSolverRegistry
from agent.generative_reduction.proof_state import ProofState
from agent.generative_reduction.recursive_runtime import RecursiveSearchRuntime
from agent.hardness.model_client import DeepSeekConfig, ModelResponse


ROOT = Path(__file__).resolve().parents[1]
GADGET = "ComplexityReduction.Domain.BooleanCSP.Hardness.Gadget"
FINITE_GADGET_MODULE = (
    "ComplexityReduction.Agent.GenerativeReduction.Plugins."
    "BooleanCSPFiniteGadget"
)


def _context(
    *,
    case_id: str = "q-b02-positive-nae4",
    module: str = (
        "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case02PositiveNAE4"
    ),
) -> BooleanCSPGadgetContext:
    exact_goal = (
        f"(symbol : {NAE3_CORE}.Symbol) → {GADGET} {module}.gamma "
        f"({NAE3_CORE}.relationOf symbol)"
    )
    return BooleanCSPGadgetContext.create(
        case_id=case_id,
        input_module=module,
        exact_goal=exact_goal,
        policy_sha256="sha256:test-policy",
        max_variable_count=12,
        max_constraint_count=24,
    )


def _nae3_from_nae4_payload() -> dict[str, object]:
    return {
        "schema": GADGET_PLAN_SCHEMA,
        "source_core": "nae3",
        "gadgets": [
            {
                "source_symbol": "source-0",
                "variable_count": 3,
                "outputs": [0, 1, 2],
                "constraints": [
                    {"target_symbol": "target-0", "vars": [0, 1, 2, 2]}
                ],
            }
        ],
        "mathematical_rationale": (
            "Repeating the third coordinate makes NAE4 equivalent to NAE3."
        ),
    }


def _false_positive_nae4_payload() -> dict[str, object]:
    payload = _nae3_from_nae4_payload()
    payload["gadgets"][0]["variable_count"] = 4
    payload["gadgets"][0]["constraints"] = [
        {"target_symbol": "target-0", "vars": [0, 1, 2, 3]}
    ]
    payload["mathematical_rationale"] = (
        "This intentionally leaves one auxiliary variable free."
    )
    return payload


def _false_negative_nae4_payload() -> dict[str, object]:
    payload = _nae3_from_nae4_payload()
    payload["gadgets"][0]["constraints"] = [
        {"target_symbol": "target-0", "vars": [0, 1, 0, 1]}
    ]
    payload["mathematical_rationale"] = (
        "This intentionally ignores the third source coordinate."
    )
    return payload


def test_public_truth_table_context_is_complete_and_answer_free() -> None:
    context = _context()
    payload = context.prompt_dict()

    assert context.source_core == "nae3"
    assert len(payload["source"]["symbols"][0]["rows"]) == 8
    assert len(payload["target"]["symbols"][0]["rows"]) == 16
    assert payload["source"]["symbols"][0]["rows"][0]["holds"] is False
    assert payload["source"]["symbols"][0]["rows"][1]["holds"] is True
    assert payload["target"]["symbols"][0]["rows"][15]["holds"] is False
    assert "formula" not in json.dumps(payload)


@pytest.mark.parametrize(
    ("case_id", "module", "arities"),
    [
        (
            "ga-dev-random-hard4",
            "Benchmark.Hardness.Inputs.BooleanCSPNPHard."
            "GadgetAuthoringDevRandomHard4",
            (4,),
        ),
        (
            "ga-dev-dual-exactly-five7",
            "Benchmark.Hardness.Inputs.BooleanCSPNPHard."
            "GadgetAuthoringDevDualExactlyFive7",
            (7,),
        ),
        (
            "ga-dev-mixed-nand2-or3",
            "Benchmark.Hardness.Inputs.BooleanCSPNPHard."
            "GadgetAuthoringDevMixedNAND2OR3",
            (2, 3),
        ),
    ],
)
def test_development_fixture_truth_tables_are_complete_and_answer_free(
    case_id: str, module: str, arities: tuple[int, ...]
) -> None:
    context = _context(case_id=case_id, module=module)
    payload = context.prompt_dict()

    assert tuple(item["arity"] for item in payload["target"]["symbols"]) == arities
    assert tuple(
        len(item["rows"]) for item in payload["target"]["symbols"]
    ) == tuple(1 << arity for arity in arities)
    assert payload["case_id"] == case_id
    assert "solution" not in json.dumps(payload).lower()


def test_schema_accepts_repeated_variables_auxiliaries_and_nonprefix_outputs() -> None:
    module = "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case05OR2EvenParity3"
    context = _context(case_id="q-b05-or2-even-parity3", module=module)
    payload = {
        "schema": GADGET_PLAN_SCHEMA,
        "source_core": "nae3",
        "gadgets": [
            {
                "source_symbol": "source-0",
                "variable_count": 6,
                "outputs": [2, 4, 1],
                "constraints": [
                    {"target_symbol": "target-0", "vars": [2, 2]},
                    {"target_symbol": "target-1", "vars": [4, 1, 5]},
                ],
            }
        ],
        "mathematical_rationale": "Schema-only multi-relation fixture.",
    }

    plan = BooleanCSPGadgetPlanV1.from_mapping(payload, context)

    assert plan.maximum_variable_count == 6
    assert plan.constraint_count == 2
    assert plan.gadgets[0].outputs == (2, 4, 1)


@pytest.mark.parametrize(
    ("mutation", "message"),
    [
        (lambda payload: payload["gadgets"][0].update(outputs=[0, 0, 2]), "injective"),
        (lambda payload: payload["gadgets"][0].update(outputs=[0, 1]), "source arity"),
        (
            lambda payload: payload["gadgets"][0]["constraints"][0].update(
                vars=[0, 1, 2]
            ),
            "arity mismatch",
        ),
        (
            lambda payload: payload["gadgets"][0]["constraints"][0].update(
                vars=[0, 1, 2, 3]
            ),
            "out of range",
        ),
    ],
)
def test_schema_rejects_invalid_model_payloads(mutation, message: str) -> None:
    context = _context()
    payload = _nae3_from_nae4_payload()
    mutation(payload)

    with pytest.raises(BooleanCSPGadgetProtocolError, match=message):
        BooleanCSPGadgetPlanV1.from_mapping(payload, context)


def test_finite_semantic_checker_accepts_correct_plan_without_auxiliaries() -> None:
    context = _context()
    plan = BooleanCSPGadgetPlanV1.from_mapping(
        _nae3_from_nae4_payload(), context
    )

    receipt = check_explicit_gadget_plan(plan=plan, context=context)

    assert receipt.success
    assert receipt.counterexample is None
    assert receipt.source_rows_checked == 8
    assert receipt.auxiliary_assignments_checked == 8
    assert receipt.semantic_payload_sha256 == plan.semantic_payload_sha256
    assert receipt.checker_input_sha256.startswith("sha256:")
    assert receipt.checker_version == GADGET_SEMANTIC_CHECKER_VERSION


def test_finite_semantic_checker_returns_stable_false_positive() -> None:
    context = _context()
    plan = BooleanCSPGadgetPlanV1.from_mapping(
        _false_positive_nae4_payload(), context
    )

    first = check_explicit_gadget_plan(plan=plan, context=context)
    second = check_explicit_gadget_plan(plan=plan, context=context)

    assert first.to_dict() == second.to_dict()
    assert not first.success
    assert first.source_rows_checked == 1
    assert first.auxiliary_assignments_checked == 2
    assert first.counterexample is not None
    assert first.counterexample.source_row_index == 0
    assert first.counterexample.source_tuple == (False, False, False)
    assert first.counterexample.expected_relation_holds is False
    assert first.counterexample.formula_has_extension is True
    assert first.counterexample.direction == "false-positive"


def test_finite_semantic_checker_returns_stable_false_negative() -> None:
    context = _context()
    plan = BooleanCSPGadgetPlanV1.from_mapping(
        _false_negative_nae4_payload(), context
    )

    receipt = check_explicit_gadget_plan(plan=plan, context=context)

    assert not receipt.success
    assert receipt.source_rows_checked == 2
    assert receipt.auxiliary_assignments_checked == 2
    assert receipt.counterexample is not None
    assert receipt.counterexample.source_row_index == 1
    assert receipt.counterexample.source_tuple == (False, False, True)
    assert receipt.counterexample.expected_relation_holds is True
    assert receipt.counterexample.formula_has_extension is False
    assert receipt.counterexample.direction == "false-negative"


def test_finite_semantic_checker_counts_multiple_auxiliary_assignments() -> None:
    context = _context()
    payload = _nae3_from_nae4_payload()
    payload["gadgets"][0]["variable_count"] = 5
    plan = BooleanCSPGadgetPlanV1.from_mapping(payload, context)

    receipt = check_explicit_gadget_plan(plan=plan, context=context)

    assert receipt.success
    assert receipt.source_rows_checked == 8
    assert receipt.auxiliary_assignments_checked == 14


def test_finite_semantic_checker_evaluates_multiple_target_relations() -> None:
    module = "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case05OR2EvenParity3"
    context = _context(case_id="q-b05-or2-even-parity3", module=module)
    payload = {
        "schema": GADGET_PLAN_SCHEMA,
        "source_core": "nae3",
        "gadgets": [
            {
                "source_symbol": "source-0",
                "variable_count": 3,
                "outputs": [0, 1, 2],
                "constraints": [
                    {"target_symbol": "target-1", "vars": [0, 1, 2]},
                    {"target_symbol": "target-0", "vars": [0, 1]},
                ],
            }
        ],
        "mathematical_rationale": "Intentional multi-relation counterexample.",
    }
    plan = BooleanCSPGadgetPlanV1.from_mapping(payload, context)

    receipt = check_explicit_gadget_plan(plan=plan, context=context)

    assert not receipt.success
    assert receipt.counterexample is not None
    assert receipt.counterexample.source_row_index == 1
    assert receipt.counterexample.direction == "false-negative"


def test_canonical_hash_excludes_rationale_and_renderer_is_byte_stable() -> None:
    context = _context()
    first_payload = _nae3_from_nae4_payload()
    second_payload = _nae3_from_nae4_payload()
    second_payload["mathematical_rationale"] = "A different audit explanation."
    first = BooleanCSPGadgetPlanV1.from_mapping(first_payload, context)
    second = BooleanCSPGadgetPlanV1.from_mapping(second_payload, context)

    first_render = render_boolean_csp_gadget_plan(
        plan=first, context=context, declaration_name="generatedGadget"
    )
    second_render = render_boolean_csp_gadget_plan(
        plan=second, context=context, declaration_name="generatedGadget"
    )

    assert first.semantic_payload_sha256 == second.semantic_payload_sha256
    assert first_render.implementation == second_render.implementation
    assert first_render.renderer_version == GADGET_RENDERER_VERSION
    assert first_render.model_constraint_count == 1
    assert first_render.rendered_constraint_count == 1
    assert first_render.renderer_added_semantic_atom_count == 0
    assert (
        first_render.semantic_payload_sha256_before
        == first_render.semantic_payload_sha256_after
    )
    for forbidden_helper in (
        "gadgetOfCandidates",
        "gadgetOfPlannedSearch",
        "CanonicalDatabase.gadget",
        "templates",
    ):
        assert forbidden_helper not in first_render.implementation


class _FakeModel:
    def __init__(self, responses: list[object]):
        self.responses = responses
        self.prompts: list[dict[str, object]] = []
        self.profile_calls: list[dict[str, object]] = []

    def complete_json(self, *, system: str, prompt: str) -> ModelResponse:
        parsed_prompt = json.loads(prompt)
        self.prompts.append(parsed_prompt)
        response = self.responses.pop(0)
        if callable(response):
            response = response(parsed_prompt)
        if isinstance(response, ModelResponse):
            return response
        content = json.dumps(response)
        return ModelResponse(
            called=True,
            ok=True,
            content=content,
            error=None,
            status_code=200,
            duration_seconds=0.01,
            usage={"prompt_tokens": 10, "completion_tokens": 10},
            attempts=1,
        )

    def complete_json_with_profile(
        self,
        *,
        system: str,
        prompt: str,
        max_tokens: int,
        reasoning_effort: str | None,
    ) -> ModelResponse:
        self.profile_calls.append(
            {
                "max_tokens": max_tokens,
                "reasoning_effort": reasoning_effort,
            }
        )
        return self.complete_json(system=system, prompt=prompt)


def _brief(
    context: BooleanCSPGadgetContext,
    *,
    prior_failure: dict[str, object] | None = None,
) -> BooleanCSPGadgetAuthoringBrief:
    return BooleanCSPGadgetAuthoringBrief.create(
        context=context,
        forbidden_declarations=("Forbidden.answer",),
        allowed_neutral_declaration_signatures=(
            FINITE_GADGET_MODULE + ".Spec",
            FINITE_GADGET_MODULE + ".Spec.Correct",
            FINITE_GADGET_MODULE + ".Spec.toGadget",
        ),
        prior_failure=prior_failure,
    )


def _length_exhausted_response(*, completion_tokens: int) -> ModelResponse:
    return ModelResponse(
        called=True,
        ok=False,
        content="",
        error="empty assistant content (finish_reason=length)",
        status_code=200,
        duration_seconds=0.01,
        usage={
            "prompt_tokens": 100,
            "completion_tokens": completion_tokens,
            "total_tokens": completion_tokens + 100,
        },
        attempts=1,
        finish_reason="length",
    )


def _structured_runtime_fixture(tmp_path: Path, *, suffix: str):
    context = _context()
    root_goal = RootGoal(
        input_module=context.input_module,
        problem_declaration=context.input_module + ".problem",
        exact_type=context.exact_goal,
        endpoint_fingerprint=f"structured-gadget-{suffix}",
    )
    state = ProofState.initial(root_goal, import_closure_fingerprint="test-env")
    goal = state.select_open_goal()
    contract = ConstructionContract(
        contract_id=f"contract-structured-gadget-{suffix}",
        goal_key=goal.key,
        exact_expected_lean_type=goal.exact_type,
        frozen_source_handle=NAE3_CORE,
        frozen_target_handle=context.input_module + ".gamma",
        available_inputs=(),
        reusable_declarations=(),
        already_closed_fragments=(),
        residual_obligations=(),
        semantic_requirements=("explicit pp gadget",),
        complexity_requirements=(),
        composition_requirements=("preserve exact endpoints",),
        allowed_construction_modes=("direct-authoring",),
        forbidden_declarations=(),
        forbidden_edits=("source and target endpoints",),
        validation_commands=(("lake", "env", "lean", "<generated-file>"),),
    )
    action = CandidateAction(
        action_id=f"structured-gadget-{suffix}-action",
        provider=ProviderKind.SYNTHESIS,
        disposition=ActionDisposition.SYNTHESIS_REQUIRED,
        goal_key=goal.key,
        estimated_cost=1.0,
        contract_id=contract.contract_id,
        metadata={"construction_mode": "direct-authoring"},
    )
    substep = SubstepPlan(
        goal_key=goal.key,
        exact_closure_result=ExactClosureResult(goal_key=goal.key, closed=False),
        ranked_proof_guidance=(),
        reusable_fragments=(),
        residual_obligations=(),
        construction_contract=contract,
        candidate_actions=(action,),
        recommended_action_id=action.action_id,
        cache_key=f"structured-gadget-{suffix}-cache",
        plan_fingerprint=f"structured-gadget-{suffix}-plan",
    )
    policy = gadget_authoring_policy()
    model_calls = []
    events: list[tuple[str, dict[str, object]]] = []
    runtime = RecursiveSearchRuntime(
        root=ROOT,
        store=GeneralJobStore(tmp_path / "job"),
        input_module=context.input_module,
        modules=(context.input_module,),
        plugin_imports=(FINITE_GADGET_MODULE,),
        forbidden_declarations=policy.forbidden_declarations,
        tracker=BudgetTracker(SearchBudget()),
        solver_registry=PremiseSolverRegistry(),
        model_policy=ModelPolicy.REQUIRED,
        deepseek=DeepSeekConfig(
            api_key="fake-key",
            max_retries=0,
            max_tokens=64_000,
            reasoning_effort="low",
        ),
        lean_timeout_seconds=120,
        commands=[],
        model_calls=model_calls,
        event_sink=lambda name, details: events.append((name, dict(details))),
        gate_policy=policy,
        capability_gate_case_id="q-b02-positive-nae4",
    )
    return context, state, goal, substep, action, runtime, model_calls, events


def test_dedicated_initial_and_stateful_repair_protocols() -> None:
    context = _context()
    invalid = _nae3_from_nae4_payload()
    invalid["gadgets"][0]["outputs"] = [0, 0, 2]

    def repaired(prompt: dict[str, object]) -> dict[str, object]:
        return {
            "base_sha256": prompt["base_sha256"],
            "plan": _nae3_from_nae4_payload(),
            "changed_reason": "Made output coordinates injective.",
        }

    model = _FakeModel([invalid, repaired])
    initial, initial_record = propose_initial_gadget_plan(
        model=model, brief=_brief(context)
    )
    assert initial.plan is None
    assert initial.error_code == "gadget_plan_schema_invalid"
    assert initial_record.purpose == "gadget-authoring-initial"
    repair, repair_record = propose_gadget_plan_repair(
        model=model,
        brief=_brief(
            context,
            prior_failure={
                "failure_class": "schema",
                "error_code": initial.error_code,
                "message": initial.error,
            },
        ),
        previous_attempt=initial,
    )

    assert repair.plan is not None
    assert repair.requested_base_sha256 == initial.response_payload_sha256
    assert repair.returned_base_sha256 == initial.response_payload_sha256
    assert repair_record.purpose == "gadget-authoring-repair"
    assert repair_record.ok
    initial_brief = model.prompts[0]["generator_brief"]
    assert initial_brief["answer_free"] is True
    assert initial_brief["required_output_schema"]["candidate_lists_allowed"] is False
    assert "candidates" not in initial_brief


def test_fake_model_plan_materializes_to_verified_lean_spec(tmp_path: Path) -> None:
    context = _context()
    model = _FakeModel([_nae3_from_nae4_payload()])
    attempt, record = propose_initial_gadget_plan(model=model, brief=_brief(context))
    assert record.ok and attempt.plan is not None
    semantic_check = check_explicit_gadget_plan(
        plan=attempt.plan, context=context
    )
    assert semantic_check.success
    rendered = render_boolean_csp_gadget_plan(
        plan=attempt.plan,
        context=context,
        declaration_name="generatedGadget",
    )
    source, declaration = build_authored_capability_source(
        input_module=context.input_module,
        exact_type=context.exact_goal,
        namespace="BooleanCSPStructuredGadgetSmoke",
        declaration_name="generatedGadget",
        implementation=rendered.implementation,
        extra_imports=(FINITE_GADGET_MODULE,),
    )
    path = tmp_path / "StructuredGadgetSmoke.lean"
    path.write_text(source, encoding="utf-8")

    command = run_lean_file(root=ROOT, path=path, timeout_seconds=120)

    assert command.ok, command.stderr or command.stdout
    assert declaration == "BooleanCSPStructuredGadgetSmoke.generatedGadget"


def test_required_gate_runtime_uses_structured_generator_and_registers_capability(
    tmp_path: Path,
) -> None:
    context = _context()
    root_goal = RootGoal(
        input_module=context.input_module,
        problem_declaration=context.input_module + ".problem",
        exact_type=context.exact_goal,
        endpoint_fingerprint="structured-gadget-test",
    )
    state = ProofState.initial(root_goal, import_closure_fingerprint="test-env")
    goal = state.select_open_goal()
    assert goal.kind in {GoalKind.DATA, GoalKind.PROPOSITION, GoalKind.UNKNOWN}
    contract = ConstructionContract(
        contract_id="contract-structured-gadget",
        goal_key=goal.key,
        exact_expected_lean_type=goal.exact_type,
        frozen_source_handle=NAE3_CORE,
        frozen_target_handle=context.input_module + ".gamma",
        available_inputs=(),
        reusable_declarations=(),
        already_closed_fragments=(),
        residual_obligations=(),
        semantic_requirements=("explicit pp gadget",),
        complexity_requirements=(),
        composition_requirements=("preserve exact endpoints",),
        allowed_construction_modes=("direct-authoring",),
        forbidden_declarations=(),
        forbidden_edits=("source and target endpoints",),
        validation_commands=(("lake", "env", "lean", "<generated-file>"),),
    )
    action = CandidateAction(
        action_id="structured-gadget-action",
        provider=ProviderKind.SYNTHESIS,
        disposition=ActionDisposition.SYNTHESIS_REQUIRED,
        goal_key=goal.key,
        estimated_cost=1.0,
        contract_id=contract.contract_id,
        metadata={"construction_mode": "direct-authoring"},
    )
    substep = SubstepPlan(
        goal_key=goal.key,
        exact_closure_result=ExactClosureResult(goal_key=goal.key, closed=False),
        ranked_proof_guidance=(),
        reusable_fragments=(),
        residual_obligations=(),
        construction_contract=contract,
        candidate_actions=(action,),
        recommended_action_id=action.action_id,
        cache_key="structured-gadget-cache",
        plan_fingerprint="structured-gadget-plan",
    )
    policy = gadget_authoring_policy()
    model_calls = []
    runtime = RecursiveSearchRuntime(
        root=ROOT,
        store=GeneralJobStore(tmp_path / "job"),
        input_module=context.input_module,
        modules=(context.input_module,),
        plugin_imports=(FINITE_GADGET_MODULE,),
        forbidden_declarations=policy.forbidden_declarations,
        tracker=BudgetTracker(SearchBudget()),
        solver_registry=PremiseSolverRegistry(),
        model_policy=ModelPolicy.REQUIRED,
        deepseek=DeepSeekConfig(
            api_key="fake-key", max_retries=0, max_tokens=64_000
        ),
        lean_timeout_seconds=120,
        commands=[],
        model_calls=model_calls,
        gate_policy=policy,
        capability_gate_case_id="q-b02-positive-nae4",
    )
    invalid = _nae3_from_nae4_payload()
    invalid["gadgets"][0]["outputs"] = [0, 0, 2]

    def semantic_repair(prompt: dict[str, object]) -> dict[str, object]:
        return {
            "base_sha256": prompt["base_sha256"],
            "plan": _false_positive_nae4_payload(),
            "changed_reason": "Made outputs injective but left an unsound auxiliary.",
        }

    def correct_repair(prompt: dict[str, object]) -> dict[str, object]:
        return {
            "base_sha256": prompt["base_sha256"],
            "plan": _nae3_from_nae4_payload(),
            "changed_reason": "Removed the false-positive auxiliary assignment.",
        }

    fake_model = _FakeModel([invalid, semantic_repair, correct_repair])
    runtime._client = fake_model

    completed = runtime._execute_synthesis(state, goal, substep, action)

    assert completed.root_fragment is not None
    assert len(completed.generated_capabilities) == 1
    assert completed.generated_capabilities[0].provenance == (
        "model-structured-gadget-plan-v2"
    )
    assert [call.purpose for call in model_calls] == [
        "gadget-authoring-initial",
        "gadget-authoring-repair",
        "gadget-authoring-repair",
    ]
    contribution = runtime.contribution_receipts()[0]
    assert contribution.contribution_class.value == "MODEL_GENERATED_CAPABILITY"
    receipts = runtime.typed_plan_receipts()
    assert len(receipts) == 3
    assert {receipt["status"] for receipt in receipts} == {
        "schema-failed",
        "semantic-failed",
        "lean-verified",
    }
    verified = next(receipt for receipt in receipts if receipt["status"] == "lean-verified")
    semantic_failed = next(
        receipt for receipt in receipts if receipt["status"] == "semantic-failed"
    )
    repaired_receipts = [
        receipt for receipt in receipts if receipt["kind"] == "repair"
    ]
    initial_receipt = next(receipt for receipt in receipts if receipt["kind"] == "initial")
    assert repaired_receipts[0]["model_attempt"]["requested_base_sha256"] == (
        initial_receipt["model_attempt"]["response_payload_sha256"]
    )
    assert repaired_receipts[1]["model_attempt"]["requested_base_sha256"] == (
        repaired_receipts[0]["model_attempt"]["response_payload_sha256"]
    )
    assert all(
        receipt["model_attempt"]["returned_base_sha256"]
        == receipt["model_attempt"]["requested_base_sha256"]
        for receipt in repaired_receipts
    )
    assert semantic_failed["semantic_checker"]["success"] is False
    assert semantic_failed["semantic_checker"]["counterexample"]["direction"] == (
        "false-positive"
    )
    assert "renderer" not in semantic_failed
    assert "generated_file" not in semantic_failed
    assert verified["answer_free"] is True
    assert verified["semantic_checker"]["success"] is True
    assert verified["renderer"]["renderer_added_semantic_atom_count"] == 0
    authorship = contribution.authorship_evidence
    assert authorship is not None
    assert authorship.origin == "model"
    assert authorship.semantic_payload_schema == GADGET_PLAN_SCHEMA
    assert authorship.semantic_payload_sha256 == verified["gadget_plan"][
        "semantic_payload_sha256"
    ]
    assert authorship.model_response_sha256 == verified["model_attempt"][
        "model_response_sha256"
    ]
    assert authorship.renderer_name == verified["renderer"]["renderer_name"]
    assert authorship.renderer_version == verified["renderer"]["renderer_version"]
    assert authorship.renderer_added_semantic_atom_count == 0
    assert authorship.variable_count == verified["gadget_plan"][
        "maximum_variable_count"
    ]
    assert authorship.constraint_count == verified["gadget_plan"][
        "constraint_count"
    ]
    assert authorship.output_mapping == tuple(
        variable
        for gadget in verified["gadget_plan"]["gadgets"]
        for variable in gadget["outputs"]
    )
    assert authorship.relation_symbols_used == tuple(
        dict.fromkeys(
            constraint["target_symbol"]
            for gadget in verified["gadget_plan"]["gadgets"]
            for constraint in gadget["constraints"]
        )
    )
    assert authorship.repair_payload_hashes == tuple(
        receipt["model_attempt"]["response_payload_sha256"]
        for receipt in sorted(repaired_receipts, key=lambda item: item["attempt"])
    )
    assert runtime.tracker.usage.generated_lean_checks == 1
    third_brief = fake_model.prompts[2]["generator_brief"]
    assert third_brief["prior_failure"]["failure_class"] == "semantic"
    assert third_brief["prior_failure"]["semantic_checker"]["counterexample"][
        "direction"
    ] == "false-positive"
    assert [item["max_tokens"] for item in fake_model.profile_calls] == [
        16_000,
        16_000,
        16_000,
    ]


def test_length_exhaustion_escalates_same_prompt_from_16k_to_64k(
    tmp_path: Path,
) -> None:
    (
        _,
        state,
        goal,
        substep,
        action,
        runtime,
        model_calls,
        _,
    ) = _structured_runtime_fixture(tmp_path, suffix="adaptive-success")
    fake_model = _FakeModel(
        [
            _length_exhausted_response(completion_tokens=16_000),
            _nae3_from_nae4_payload(),
        ]
    )
    runtime._client = fake_model

    completed = runtime._execute_synthesis(state, goal, substep, action)

    assert completed.root_fragment is not None
    assert [item["max_tokens"] for item in fake_model.profile_calls] == [
        16_000,
        64_000,
    ]
    assert fake_model.prompts[0] == fake_model.prompts[1]
    assert [call.finish_reason for call in model_calls] == ["length", None]
    assert model_calls[0].request_payload_sha256 == (
        model_calls[1].request_payload_sha256
    )
    assert model_calls[1].escalation_of_response_sha256 == (
        "sha256:" + model_calls[0].response_sha256
    )
    assert [call.transport_attempt for call in model_calls] == [1, 2]
    receipts = runtime.typed_plan_receipts()
    assert [receipt["status"] for receipt in receipts] == [
        "transport-escalated",
        "lean-verified",
    ]
    assert receipts[1]["token_escalation"] == {
        "trigger_finish_reason": "length",
        "from_token_profile": "gadget-authoring-base-16k-v1",
        "from_requested_max_tokens": 16_000,
        "from_model_response_sha256": receipts[0]["model_attempt"][
            "model_response_sha256"
        ],
        "to_token_profile": "gadget-authoring-escalated-64k-v1",
        "to_requested_max_tokens": 64_000,
        "same_request_payload_sha256": True,
        "same_requested_base_sha256": True,
    }
    assert runtime.tracker.usage.authoring_calls == 2
    assert runtime.tracker.usage.model_calls == 2
    assert runtime.tracker.usage.generated_lean_checks == 1
    audit = _adaptive_gadget_token_audit(
        (
            {
                "case_id": "q-b02-positive-nae4",
                "model_calls": [asdict(call) for call in model_calls],
                "typed_capability_plans": list(receipts),
            },
        ),
        gadget_authoring_policy(),
    )
    assert not audit["violations"]
    assert audit["successful_escalation_count"] == 1


def test_two_length_exhaustions_are_typed_as_search_nonconvergence(
    tmp_path: Path,
) -> None:
    (
        _,
        state,
        goal,
        substep,
        action,
        runtime,
        model_calls,
        _,
    ) = _structured_runtime_fixture(tmp_path, suffix="adaptive-nonconvergent")
    fake_model = _FakeModel(
        [
            _length_exhausted_response(completion_tokens=16_000),
            _length_exhausted_response(completion_tokens=64_000),
        ]
    )
    runtime._client = fake_model

    completed = runtime._execute_synthesis(state, goal, substep, action)

    assert completed.root_fragment is None
    assert [call.finish_reason for call in model_calls] == ["length", "length"]
    assert [receipt["status"] for receipt in runtime.typed_plan_receipts()] == [
        "transport-escalated",
        "transport-escalation-exhausted",
    ]
    terminal = runtime.typed_plan_receipts()[-1]
    assert terminal["failure"]["failure_class"] == "search-nonconvergent"
    assert terminal["failure"]["error_code"] == (
        "gadget_authoring_search_nonconvergent"
    )


def test_semantic_repair_length_exhaustion_has_distinct_terminal_status(
    tmp_path: Path,
) -> None:
    (
        _,
        state,
        goal,
        substep,
        action,
        runtime,
        model_calls,
        _,
    ) = _structured_runtime_fixture(tmp_path, suffix="semantic-repair-length")
    fake_model = _FakeModel(
        [
            _false_positive_nae4_payload(),
            _length_exhausted_response(completion_tokens=16_000),
            _length_exhausted_response(completion_tokens=64_000),
        ]
    )
    runtime._client = fake_model

    completed = runtime._execute_synthesis(state, goal, substep, action)

    assert completed.root_fragment is None
    assert [call.purpose for call in model_calls] == [
        "gadget-authoring-initial",
        "gadget-authoring-repair",
        "gadget-authoring-repair",
    ]
    assert fake_model.prompts[1] == fake_model.prompts[2]
    assert [receipt["status"] for receipt in runtime.typed_plan_receipts()] == [
        "semantic-failed",
        "transport-escalated",
        "semantic-repair-escalation-exhausted",
    ]
    terminal = runtime.typed_plan_receipts()[-1]
    assert terminal["failure"]["failure_class"] == "semantic-repair"
    assert terminal["failure"]["error_code"] == (
        "gadget_semantic_repair_nonconvergent"
    )
    row = {
        "case_id": "q-b02-positive-nae4",
        "model_calls": [asdict(call) for call in model_calls],
        "typed_capability_plans": list(runtime.typed_plan_receipts()),
        "repair_lineage": list(runtime.repair_lineage_receipts()),
    }
    assert _repair_prompts_have_matching_base_hash((row,))
    audit = _adaptive_gadget_token_audit((row,), gadget_authoring_policy())
    assert not audit["violations"]
    assert audit["semantic_repair_nonconvergence_count"] == 1


def test_transport_failure_skips_repair_and_duplicate_context_skips_model(
    tmp_path: Path,
) -> None:
    context = _context()
    root_goal = RootGoal(
        input_module=context.input_module,
        problem_declaration=context.input_module + ".problem",
        exact_type=context.exact_goal,
        endpoint_fingerprint="structured-gadget-transport-test",
    )
    state = ProofState.initial(root_goal, import_closure_fingerprint="test-env")
    goal = state.select_open_goal()
    contract = ConstructionContract(
        contract_id="contract-structured-gadget-transport",
        goal_key=goal.key,
        exact_expected_lean_type=goal.exact_type,
        frozen_source_handle=NAE3_CORE,
        frozen_target_handle=context.input_module + ".gamma",
        available_inputs=(),
        reusable_declarations=(),
        already_closed_fragments=(),
        residual_obligations=(),
        semantic_requirements=("explicit pp gadget",),
        complexity_requirements=(),
        composition_requirements=("preserve exact endpoints",),
        allowed_construction_modes=("direct-authoring",),
        forbidden_declarations=(),
        forbidden_edits=("source and target endpoints",),
        validation_commands=(("lake", "env", "lean", "<generated-file>"),),
    )
    action = CandidateAction(
        action_id="structured-gadget-transport-action",
        provider=ProviderKind.SYNTHESIS,
        disposition=ActionDisposition.SYNTHESIS_REQUIRED,
        goal_key=goal.key,
        estimated_cost=1.0,
        contract_id=contract.contract_id,
        metadata={"construction_mode": "direct-authoring"},
    )
    substep = SubstepPlan(
        goal_key=goal.key,
        exact_closure_result=ExactClosureResult(goal_key=goal.key, closed=False),
        ranked_proof_guidance=(),
        reusable_fragments=(),
        residual_obligations=(),
        construction_contract=contract,
        candidate_actions=(action,),
        recommended_action_id=action.action_id,
        cache_key="structured-gadget-transport-cache",
        plan_fingerprint="structured-gadget-transport-plan",
    )
    policy = gadget_authoring_policy()
    model_calls = []
    events: list[tuple[str, dict[str, object]]] = []
    runtime = RecursiveSearchRuntime(
        root=ROOT,
        store=GeneralJobStore(tmp_path / "job"),
        input_module=context.input_module,
        modules=(context.input_module,),
        plugin_imports=(FINITE_GADGET_MODULE,),
        forbidden_declarations=policy.forbidden_declarations,
        tracker=BudgetTracker(SearchBudget()),
        solver_registry=PremiseSolverRegistry(),
        model_policy=ModelPolicy.REQUIRED,
        deepseek=DeepSeekConfig(
            api_key="fake-key", max_retries=0, max_tokens=64_000
        ),
        lean_timeout_seconds=120,
        commands=[],
        model_calls=model_calls,
        event_sink=lambda name, details: events.append((name, dict(details))),
        gate_policy=policy,
        capability_gate_case_id="q-b02-positive-nae4",
    )
    fake_model = _FakeModel(
        [
            ModelResponse(
                called=True,
                ok=False,
                content="",
                error="network timeout",
                status_code=None,
                duration_seconds=0.01,
                usage={},
                attempts=1,
            )
        ]
    )
    runtime._client = fake_model

    first = runtime._execute_synthesis(state, goal, substep, action)
    second = runtime._execute_synthesis(state, goal, substep, action)

    assert first.root_fragment is None
    assert second.root_fragment is None
    assert len(fake_model.prompts) == 1
    assert [call.purpose for call in model_calls] == ["gadget-authoring-initial"]
    assert [receipt["status"] for receipt in runtime.typed_plan_receipts()] == [
        "transport-failed"
    ]
    lineage = runtime.repair_lineage_receipts()
    assert len(lineage) == 1
    assert lineage[0]["failure_class"] == "transport"
    assert lineage[0]["status"] == "transport-failed"
    response_event = next(
        details for name, details in events if name == "GADGET_AUTHORING_MODEL_RESPONSE"
    )
    assert response_event["http_status"] is None
    assert response_event["network_attempts"] == 1
    assert response_event["error"] == "network timeout"
    assert any(
        name == "GADGET_AUTHORING_CONTEXT_DUPLICATE_REJECTED"
        for name, _ in events
    )
