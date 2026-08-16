"""Typed deterministic generators for reusable reduction capabilities.

The compilers in this module are deliberately target driven.  They parse the
exact Lean type, construct an auditable capability-specific DAG, emit a frozen
GeneratorBrief, and materialize only lower-level public primitives.  The
resulting source is still checked independently by the generic Lean runtime.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
import re
import textwrap
from typing import Mapping

from .finite_synthesis import FiniteCandidateWitness, FiniteCapabilityStage
from .model.authoring import fixed_declaration_header
from .models import (
    CapabilityKind,
    CapabilityPlan,
    ContributionClass,
    ContributionReceipt,
    DirectTMCapabilityPlan,
    GeneratorBrief,
    GeneratorResult,
    GeneratorStatus,
    OpenGoal,
    SemanticCapabilityPlan,
    SemanticDirectionPlan,
    TypedProgramNode,
    stable_sha256,
)


HARDNESS = "ComplexityReduction.Domain.BooleanCSP.Hardness"
PRESENTATION = "ComplexityReduction.Presentation.FiniteDomainCSPTable"
TM = "ComplexityReduction.TMPolyTimeMap"
CSP_FORMULA = "ComplexityReduction.CSP.Formula"
SAT_ASSIGNMENT = "ComplexityReduction.SAT.Assignment"


@dataclass(frozen=True)
class InterpretApplication:
    head: str
    source_language: str
    target_language: str
    interpretation_term: str
    formula_term: str | None
    source_span: tuple[int, int]


_INTERPRET_START = re.compile(
    r"\(\s*@(?P<head>[A-Za-z_][A-Za-z0-9_'.]*\.Hardness\.interpret)\b"
)


def _split_top_level(value: str) -> tuple[str, ...]:
    tokens: list[str] = []
    start: int | None = None
    stack: list[str] = []
    matching = {")": "(", "]": "[", "}": "{"}
    for index, character in enumerate(value):
        if character in "([{":
            stack.append(character)
        elif character in matching:
            if stack and stack[-1] == matching[character]:
                stack.pop()
        if character.isspace() and not stack:
            if start is not None:
                tokens.append(value[start:index])
                start = None
        elif start is None:
            start = index
    if start is not None:
        tokens.append(value[start:])
    return tuple(token for token in tokens if token)


def parse_interpret_application(exact_type: str) -> InterpretApplication | None:
    """Extract the explicit parameters of one pretty-printed `@interpret` call."""

    match = _INTERPRET_START.search(exact_type)
    if match is None:
        return None
    outer_start = match.start()
    depth = 0
    end: int | None = None
    for index in range(outer_start, len(exact_type)):
        character = exact_type[index]
        if character == "(":
            depth += 1
        elif character == ")":
            depth -= 1
            if depth == 0:
                end = index + 1
                break
    if end is None:
        return None
    tokens = _split_top_level(exact_type[outer_start + 1 : end - 1].strip())
    if len(tokens) < 4 or not tokens[0].startswith("@"):
        return None
    head = tokens[0][1:]
    if head != match.group("head"):
        return None
    return InterpretApplication(
        head=head,
        source_language=tokens[1],
        target_language=tokens[2],
        interpretation_term=tokens[3],
        formula_term=(tokens[4] if len(tokens) >= 5 else None),
        source_span=(outer_start, end),
    )


def is_direct_tm_interpret_goal(goal: OpenGoal) -> bool:
    compact = " ".join(goal.exact_type.split())
    return "ComplexityReduction.TMPolyTimeMap" in compact and (
        parse_interpret_application(goal.exact_type) is not None
    )


def is_semantic_interpret_goal(goal: OpenGoal) -> bool:
    compact = " ".join(goal.exact_type.split())
    return (
        "Satisfiable" in compact
        and (" Iff " in f" {compact} " or "↔" in compact)
        and parse_interpret_application(goal.exact_type) is not None
    )


def _primitive_id(declaration: str) -> str:
    return "primitive-" + stable_sha256(declaration).removeprefix("sha256:")[:20]


def _brief(
    *,
    plan: CapabilityPlan,
    declaration_name: str,
    exact_type: str,
    design: Mapping[str, object],
    hints: tuple[Mapping[str, object], ...],
    helper_contracts: tuple[Mapping[str, object], ...],
    primitives: tuple[str, ...],
) -> GeneratorBrief:
    return GeneratorBrief.create(
        plan=plan,
        exact_declaration_name=declaration_name,
        exact_declaration_type=exact_type,
        fixed_declaration_envelope={
            "header": fixed_declaration_header(
                declaration=declaration_name, exact_type=exact_type
            ),
            "model_may_edit_header": "false",
            "owner": "recursive-runtime",
        },
        selected_design=design,
        ordered_proof_hints=hints,
        helper_contracts=helper_contracts,
        allowed_identifier_manifest=primitives,
        forbidden_declarations=plan.forbidden_closure_ids,
        expected_residuals=tuple(
            str(item.get("exact_type") or "") for item in plan.residual_goal_dag
        ),
    )


def _stage(
    *,
    capability_kind: CapabilityKind,
    parent_plan: CapabilityPlan,
    goal_id: str,
    stage_id: str,
    declaration_name: str,
    exact_type: str,
    proof_body: str,
    route: str,
    primitive_declarations: tuple[str, ...],
    dependency_stage_ids: tuple[str, ...] = (),
    dependency_declarations: tuple[str, ...] = (),
    imports: tuple[str, ...] = (),
) -> FiniteCapabilityStage:
    proof_body = textwrap.dedent(proof_body).strip()
    stage_plan = CapabilityPlan.create(
        capability_kind=capability_kind,
        goal_id=f"{goal_id}:{stage_id}",
        exact_goal=exact_type,
        selected_route=route,
        selected_design_id=f"design-{stage_id}",
        construction_basis_ids=tuple(
            _primitive_id(item) for item in primitive_declarations
        ),
        forbidden_closure_ids=parent_plan.forbidden_closure_ids,
        proof_outline=(route,),
        helper_specs=(
            {
                "helper_name": declaration_name,
                "stage_id": stage_id,
                "exact_type": exact_type,
                "dependencies": dependency_stage_ids,
            },
        ),
        budget_allocation={
            "generation": 1,
            "lean_check": 1,
            "repair_reserve": 1,
        },
        context_requirements=parent_plan.context_requirements,
    )
    identifiers = tuple(
        dict.fromkeys((*primitive_declarations, *dependency_declarations))
    )
    brief = _brief(
        plan=stage_plan,
        declaration_name=declaration_name,
        exact_type=exact_type,
        design={
            "design_id": stage_plan.selected_design_id,
            "design_kind": "capability-dag-stage",
            "stage_id": stage_id,
            "parent_plan_id": parent_plan.plan_id,
        },
        hints=(
            {
                "hint_id": stage_id,
                "hint_kind": "materialize-capability-stage",
                "primitive_declarations": primitive_declarations,
                "dependency_stage_ids": dependency_stage_ids,
            },
        ),
        helper_contracts=stage_plan.helper_specs,
        primitives=identifiers,
    )
    rendered_body = "\n".join(
        "  " + line if line else "" for line in proof_body.splitlines()
    )
    implementation = (
        fixed_declaration_header(
            declaration=declaration_name, exact_type=exact_type
        )
        + "\n"
        + rendered_body
    )
    result = GeneratorResult.create(
        brief=brief,
        status=GeneratorStatus.PROPOSED,
        implementation_body=proof_body,
        planner_hints_followed=(stage_id,),
    )
    return FiniteCapabilityStage(
        stage_id=stage_id,
        declaration_name=declaration_name,
        exact_type=exact_type,
        implementation=implementation,
        imports=imports,
        dependency_stage_ids=dependency_stage_ids,
        check_receipt={
            "parent_plan_id": parent_plan.plan_id,
            "route": route,
            "primitive_declarations": primitive_declarations,
        },
        capability_plan=stage_plan,
        generator_brief=brief,
        generator_result=result,
    )


def compile_direct_tm_candidate(
    goal: OpenGoal, *, declaration_name: str
) -> FiniteCandidateWitness | None:
    application = parse_interpret_application(goal.exact_type)
    if application is None or not is_direct_tm_interpret_goal(goal):
        return None
    source = application.source_language
    target = application.target_language
    interpretation = application.interpretation_term
    input_type = f"{PRESENTATION}.encodedType {source}"
    output_type = f"{PRESENTATION}.encodedType {target}"
    code_type = f"{PRESENTATION}.formulaCodeEncodedType"
    digest = stable_sha256(
        {
            "goal": goal.exact_type,
            "declaration": declaration_name,
            "compiler": "boolean-csp-direct-tm-v1",
        }
    ).removeprefix("sha256:")[:12]
    formula_helper = f"direct_tm_formula_code_{digest}"
    code_helper = f"direct_tm_interpret_code_{digest}"
    endpoint_helper = f"direct_tm_endpoint_{digest}"

    formula_node = TypedProgramNode.create(
        operation="encoding-equivalence",
        input_encoded_type=input_type,
        output_encoded_type=code_type,
        function_term=f"fun formula => {PRESENTATION}.formulaCode {source} formula",
        primitive_declaration=f"{TM}.of_encodingEquiv",
        generated_helper_name=formula_helper,
        status="generator-required",
    )
    code_node = TypedProgramNode.create(
        operation="composition",
        input_encoded_type=input_type,
        output_encoded_type=code_type,
        function_term=(
            f"fun formula => {HARDNESS}.interpretCode {interpretation} "
            f"({PRESENTATION}.formulaCode {source} formula)"
        ),
        primitive_declaration=f"{TM}.comp",
        dependency_node_ids=(formula_node.node_id,),
        generated_helper_name=code_helper,
        status="generator-required",
    )
    endpoint_goal = (
        f"∀ input, {HARDNESS}.interpretCode {interpretation} "
        f"({PRESENTATION}.formulaCode {source} input) = "
        f"{PRESENTATION}.formulaCode {target} "
        f"(@{HARDNESS}.interpret {source} {target} {interpretation} input)"
    )
    endpoint_node = TypedProgramNode.create(
        operation="endpoint-equality",
        input_encoded_type=input_type,
        output_encoded_type=output_type,
        function_term=f"@{HARDNESS}.interpret {source} {target} {interpretation}",
        primitive_declaration=f"{HARDNESS}.interpretCode_eq_formulaCode",
        dependency_node_ids=(code_node.node_id,),
        endpoint_equality=endpoint_goal,
        generated_helper_name=endpoint_helper,
        status="generator-required",
    )
    final_node = TypedProgramNode.create(
        operation="formula-code-output-transport",
        input_encoded_type=input_type,
        output_encoded_type=output_type,
        function_term=f"@{HARDNESS}.interpret {source} {target} {interpretation}",
        primitive_declaration=f"{PRESENTATION}.formula_tmPolyTime_of_code",
        dependency_node_ids=(code_node.node_id, endpoint_node.node_id),
        generated_helper_name=declaration_name,
        status="deterministic-compiler",
    )
    typed_plan = DirectTMCapabilityPlan.create(
        exact_goal=goal.exact_type,
        source_language=source,
        target_language=target,
        interpretation_term=interpretation,
        nodes=(formula_node, code_node, endpoint_node, final_node),
        final_node_id=final_node.node_id,
        missing_node_ids=(
            formula_node.node_id,
            code_node.node_id,
            endpoint_node.node_id,
        ),
        endpoint_goal=endpoint_goal,
        normalization_receipt={
            "parser": "explicit-interpret-application-v1",
            "interpret_head": application.head,
            "source_span": application.source_span,
            "acyclic": True,
            "target_specific": True,
        },
    )
    primitives = tuple(
        dict.fromkeys(
            node.primitive_declaration
            for node in typed_plan.nodes
            if node.primitive_declaration is not None
        )
    ) + (f"{HARDNESS}.interpretCode_tmPolyTime",)
    helper_specs = tuple(
        {
            "helper_name": node.generated_helper_name,
            "node_id": node.node_id,
            "operation": node.operation,
            "exact_type": node.endpoint_equality
            or f"{TM} {node.input_encoded_type} {node.output_encoded_type} ({node.function_term})",
            "dependencies": node.dependency_node_ids,
        }
        for node in typed_plan.nodes[:-1]
    )
    capability_plan = CapabilityPlan.create(
        capability_kind=CapabilityKind.DIRECT_TM,
        goal_id=goal.goal_id,
        exact_goal=goal.exact_type,
        selected_route="typed-program-dag/deterministic-tm-compiler",
        selected_design_id="design-" + typed_plan.plan_id,
        construction_basis_ids=tuple(_primitive_id(item) for item in primitives),
        forbidden_closure_ids=(f"{HARDNESS}.interpretation_tmPolyTime",),
        proof_outline=tuple(node.operation for node in typed_plan.nodes),
        helper_specs=helper_specs,
        residual_goal_dag=tuple(
            {
                "goal_id": node.node_id,
                "exact_type": spec["exact_type"],
                "dependencies": node.dependency_node_ids,
            }
            for node, spec in zip(typed_plan.nodes[:-1], helper_specs, strict=True)
        ),
        budget_allocation={
            "planner": 1,
            "node_generation": 3,
            "lean_checks": 1,
            "repair_reserve": 1,
            "final_verification_reserve": 1,
        },
        context_requirements=(
            "formula-code encoding primitive",
            "code-level interpretation TM primitive",
            "endpoint code equality",
        ),
    )
    hints = tuple(
        {
            "hint_id": node.node_id,
            "hint_kind": (
                "prove-endpoint-equality"
                if node.operation == "endpoint-equality"
                else "apply-candidate"
            ),
            "primitive_declaration": node.primitive_declaration,
            "dependency_node_ids": node.dependency_node_ids,
        }
        for node in typed_plan.nodes
    )
    brief = _brief(
        plan=capability_plan,
        declaration_name=declaration_name,
        exact_type=goal.exact_type,
        design={
            "design_id": capability_plan.selected_design_id,
            "design_kind": "typed-program-dag",
            "typed_plan_id": typed_plan.plan_id,
        },
        hints=hints,
        helper_contracts=helper_specs,
        primitives=primitives,
    )

    compiler_imports = (
        "ComplexityReduction.Domain.BooleanCSP.Hardness.InterpretCompiler",
    )
    formula_type = (
        f"{TM} ({input_type}) {code_type} "
        f"(fun formula => {PRESENTATION}.formulaCode {source} formula)"
    )
    formula_proof = f"""exact {TM}.of_encodingEquiv
  ({input_type})
  {code_type}
  (fun formula => {PRESENTATION}.formulaCode {source} formula)
  (Equiv.refl _)
  (by
    intro formula
    change {code_type}.encode
        ({PRESENTATION}.formulaCode {source} formula) =
      List.map id
        ({code_type}.encode
          ({PRESENTATION}.formulaCode {source} formula))
    rw [List.map_id])"""
    code_stage_type = (
        f"{TM} ({input_type}) {code_type} "
        f"(fun formula => {HARDNESS}.interpretCode {interpretation} "
        f"({PRESENTATION}.formulaCode {source} formula))"
    )
    code_proof = f"""have hComp := {TM}.comp
  ({HARDNESS}.interpretCode_tmPolyTime {interpretation})
  {formula_helper}
simpa [Function.comp] using hComp"""
    endpoint_proof = (
        f"exact {HARDNESS}.interpretCode_eq_formulaCode {interpretation}"
    )
    formula_stage = _stage(
        capability_kind=CapabilityKind.DIRECT_TM,
        parent_plan=capability_plan,
        goal_id=goal.goal_id,
        stage_id=formula_node.node_id,
        declaration_name=formula_helper,
        exact_type=formula_type,
        proof_body=formula_proof,
        route="encoding-equivalence",
        primitive_declarations=(f"{TM}.of_encodingEquiv",),
        imports=compiler_imports,
    )
    code_stage = _stage(
        capability_kind=CapabilityKind.DIRECT_TM,
        parent_plan=capability_plan,
        goal_id=goal.goal_id,
        stage_id=code_node.node_id,
        declaration_name=code_helper,
        exact_type=code_stage_type,
        proof_body=code_proof,
        route="composition",
        primitive_declarations=(
            f"{TM}.comp",
            f"{HARDNESS}.interpretCode_tmPolyTime",
        ),
        dependency_stage_ids=(formula_node.node_id,),
        dependency_declarations=(formula_helper,),
        imports=compiler_imports,
    )
    endpoint_stage = _stage(
        capability_kind=CapabilityKind.DIRECT_TM,
        parent_plan=capability_plan,
        goal_id=goal.goal_id,
        stage_id=endpoint_node.node_id,
        declaration_name=endpoint_helper,
        exact_type=endpoint_goal,
        proof_body=endpoint_proof,
        route="endpoint-equality",
        primitive_declarations=(f"{HARDNESS}.interpretCode_eq_formulaCode",),
        dependency_stage_ids=(code_node.node_id,),
        dependency_declarations=(code_helper,),
        imports=compiler_imports,
    )
    proof_body = (
        f"exact {PRESENTATION}.formula_tmPolyTime_of_code "
        f"{code_helper} {endpoint_helper}"
    )
    implementation = (
        fixed_declaration_header(
            declaration=declaration_name, exact_type=goal.exact_type
        )
        + "\n  "
        + proof_body
    )
    generator_result = GeneratorResult.create(
        brief=brief,
        status=GeneratorStatus.PROPOSED,
        implementation_body=proof_body,
        planner_hints_followed=tuple(node.node_id for node in typed_plan.nodes),
    )
    contribution = ContributionReceipt(
        capability_declaration=declaration_name,
        contribution_class=ContributionClass.DETERMINISTIC_GENERATED_CAPABILITY,
        capability_kind=CapabilityKind.DIRECT_TM,
        plan_id=capability_plan.plan_id,
        brief_id=brief.brief_id,
        generator_result_id=generator_result.result_id,
        primitive_candidates_used=tuple(_primitive_id(item) for item in primitives),
        planner_advice_ids=tuple(node.node_id for node in typed_plan.nodes),
        generated_helpers=(formula_helper, code_helper, endpoint_helper),
        generated_data_objects=(typed_plan.plan_id,),
        deterministic_solver_steps=tuple(node.operation for node in typed_plan.nodes),
    )
    return FiniteCandidateWitness(
        witness_id="direct-tm-compiler-" + typed_plan.plan_fingerprint[-20:],
        implementation=implementation,
        imports=compiler_imports,
        executable_status="typed-program-dag-complete",
        check_receipt={
            "typed_plan_id": typed_plan.plan_id,
            "node_count": len(typed_plan.nodes),
            "missing_node_count_before_generation": len(typed_plan.missing_node_ids),
            "endpoint_equality_generated": True,
            "forbidden_closure_used": False,
            "proof_authority": "pending-independent-lean-verification",
        },
        candidate_class="typed-compiler",
        authoritative_typed_compiler=True,
        capability_plan=capability_plan,
        generator_brief=brief,
        generator_result=generator_result,
        contribution_receipt=contribution,
        typed_plan_receipt=asdict(typed_plan),
        stages=(formula_stage, code_stage, endpoint_stage),
    )


def compile_semantic_candidate(
    goal: OpenGoal, *, declaration_name: str
) -> FiniteCandidateWitness | None:
    application = parse_interpret_application(goal.exact_type)
    if application is None or not is_semantic_interpret_goal(goal):
        return None
    source = application.source_language
    target = application.target_language
    interpretation = application.interpretation_term
    digest = stable_sha256(
        {
            "goal": goal.exact_type,
            "declaration": declaration_name,
            "compiler": "boolean-csp-semantic-helper-dag-v1",
        }
    ).removeprefix("sha256:")[:12]
    reverse_helper = f"semantic_reverse_{digest}"
    forward_helper = f"semantic_forward_{digest}"
    interpret_formula = (
        f"@{HARDNESS}.interpret {source} {target} {interpretation} formula"
    )
    reverse_type = f"""∀ (formula : {CSP_FORMULA} {source})
    {{targetAssignment : {SAT_ASSIGNMENT}}},
    {CSP_FORMULA}.Satisfies ({interpret_formula}) targetAssignment →
      {CSP_FORMULA}.Satisfies formula targetAssignment"""
    forward_assignment = (
        f"@{HARDNESS}.forwardAssignment {source} {target} {interpretation} "
        "formula sourceAssignment sourceSatisfies"
    )
    forward_type = f"""∀ (formula : {CSP_FORMULA} {source})
    {{sourceAssignment : {SAT_ASSIGNMENT}}}
    (sourceSatisfies : {CSP_FORMULA}.Satisfies formula sourceAssignment),
    {CSP_FORMULA}.Satisfies ({interpret_formula})
      ({forward_assignment})"""
    reverse_primitives = (
        f"{HARDNESS}.instantiate_satisfies_reverse",
        "List.mem_flatMap",
    )
    forward_primitives = (
        f"{HARDNESS}.instantiate_satisfies_forward",
        f"{HARDNESS}.forwardAssignment",
        f"{HARDNESS}.forwardAssignment_source",
        f"{HARDNESS}.forwardAssignment_fresh",
        f"{HARDNESS}.constraint_vars_le_formula_maxVar",
        "List.mem_flatMap",
    )
    reverse_plan = SemanticDirectionPlan.create(
        direction="reverse",
        exact_helper_type=reverse_type,
        witness_schema={
            "assignment": "reuse target assignment on source variables",
            "quantifier": "universal constraint membership",
        },
        invariant_specs=(
            {
                "name": "instantiated-block-membership",
                "exact_requirement": "each source constraint block is in interpret flatMap",
            },
        ),
        primitive_declarations=reverse_primitives,
        proof_outline=(
            "introduce source constraint",
            "apply one-gadget reverse primitive",
            "lift block membership through flatMap",
        ),
    )
    forward_plan = SemanticDirectionPlan.create(
        direction="forward",
        exact_helper_type=forward_type,
        witness_schema={
            "assignment": f"{HARDNESS}.forwardAssignment",
            "source_region": "preserve variables at or below Formula.maxVar",
            "fresh_region": "use selected gadget witness",
        },
        invariant_specs=(
            {
                "name": "source-agreement",
                "primitive": f"{HARDNESS}.forwardAssignment_source",
            },
            {
                "name": "fresh-witness-agreement",
                "primitive": f"{HARDNESS}.forwardAssignment_fresh",
            },
            {
                "name": "source-vars-bounded",
                "primitive": f"{HARDNESS}.constraint_vars_le_formula_maxVar",
            },
        ),
        primitive_declarations=forward_primitives,
        proof_outline=(
            "decompose target flatMap membership",
            "apply one-gadget forward primitive",
            "prove source/fresh assignment invariants",
            "discharge selected block membership",
        ),
    )
    residual_dag = (
        {
            "goal_id": reverse_plan.direction_id,
            "direction": "reverse",
            "exact_type": reverse_type,
            "dependencies": (),
            "preserve_on_sibling_failure": True,
        },
        {
            "goal_id": forward_plan.direction_id,
            "direction": "forward",
            "exact_type": forward_type,
            "dependencies": (),
            "preserve_on_sibling_failure": True,
        },
        {
            "goal_id": "semantic-final-assembly",
            "direction": "iff-assembly",
            "exact_type": goal.exact_type,
            "dependencies": (
                reverse_plan.direction_id,
                forward_plan.direction_id,
            ),
        },
    )
    typed_plan = SemanticCapabilityPlan.create(
        exact_goal=goal.exact_type,
        source_language=source,
        target_language=target,
        interpretation_term=interpretation,
        forward=forward_plan,
        reverse=reverse_plan,
        final_helper_type=goal.exact_type,
        residual_goal_dag=residual_dag,
    )
    primitives = tuple(dict.fromkeys((*reverse_primitives, *forward_primitives)))
    capability_plan = CapabilityPlan.create(
        capability_kind=CapabilityKind.SEMANTIC,
        goal_id=goal.goal_id,
        exact_goal=goal.exact_type,
        selected_route="semantic-direction-helper-dag/final-iff-assembly",
        selected_design_id="design-" + typed_plan.plan_id,
        construction_basis_ids=tuple(_primitive_id(item) for item in primitives),
        forbidden_closure_ids=(
            f"{HARDNESS}.interpret_satisfiable_iff",
            f"{HARDNESS}.interpret_satisfies_forward",
            f"{HARDNESS}.interpret_satisfies_reverse",
        ),
        proof_outline=(
            "generate reverse direction helper",
            "generate forward witness and invariant helper",
            "assemble satisfiable iff from generated directions",
        ),
        helper_specs=(
            {
                "helper_name": reverse_helper,
                "direction_id": reverse_plan.direction_id,
                "exact_type": reverse_type,
                "dependencies": (),
            },
            {
                "helper_name": forward_helper,
                "direction_id": forward_plan.direction_id,
                "exact_type": forward_type,
                "dependencies": (),
            },
        ),
        witness_schema=forward_plan.witness_schema,
        residual_goal_dag=residual_dag,
        budget_allocation={
            "planner": 1,
            "reverse_generation": 1,
            "forward_generation": 1,
            "final_assembly": 1,
            "lean_checks": 1,
            "repair_reserve_per_direction": 1,
        },
        context_requirements=(
            "one-gadget forward/reverse primitives",
            "forward assignment definition and invariants",
            "flatMap membership constructors",
        ),
    )
    hints = (
        {
            "hint_id": reverse_plan.direction_id,
            "hint_kind": "split-structurally",
            "primitive_declarations": reverse_primitives,
        },
        {
            "hint_id": forward_plan.direction_id,
            "hint_kind": "construct-witness",
            "primitive_declarations": forward_primitives,
        },
        {
            "hint_id": "semantic-final-assembly",
            "hint_kind": "split-structurally",
            "generated_helper_ids": (
                reverse_plan.direction_id,
                forward_plan.direction_id,
            ),
        },
    )
    helper_contracts = tuple(capability_plan.helper_specs)
    brief = _brief(
        plan=capability_plan,
        declaration_name=declaration_name,
        exact_type=goal.exact_type,
        design={
            "design_id": capability_plan.selected_design_id,
            "design_kind": "semantic-helper-dag",
            "typed_plan_id": typed_plan.plan_id,
        },
        hints=hints,
        helper_contracts=helper_contracts,
        primitives=primitives,
    )

    compiler_imports = (
        "ComplexityReduction.Domain.BooleanCSP.Hardness.PPDefinability",
    )
    reverse_proof = f"""intro formula targetAssignment targetSatisfies
intro constraint constraintMember
apply {HARDNESS}.instantiate_satisfies_reverse
  {interpretation} ({CSP_FORMULA}.maxVar formula) constraint
intro instantiatedConstraint instantiatedMember
exact targetSatisfies instantiatedConstraint
  (List.mem_flatMap.mpr
    ⟨constraint, constraintMember, instantiatedMember⟩)"""
    forward_proof = f"""intro formula sourceAssignment sourceSatisfies
intro instantiatedConstraint instantiatedMember
rcases List.mem_flatMap.mp instantiatedMember with
  ⟨constraint, constraintMember, inBlock⟩
apply {HARDNESS}.instantiate_satisfies_forward
  {interpretation} ({CSP_FORMULA}.maxVar formula)
  (sourceSatisfies := sourceSatisfies constraint constraintMember)
  (target := {forward_assignment})
· intro var below
  exact {HARDNESS}.forwardAssignment_source
    {interpretation} formula below
· intro index
  exact {HARDNESS}.constraint_vars_le_formula_maxVar
    constraintMember index
· intro gadgetVariable
  exact {HARDNESS}.forwardAssignment_fresh
    {interpretation} formula constraintMember gadgetVariable
exact inBlock"""
    reverse_stage = _stage(
        capability_kind=CapabilityKind.SEMANTIC,
        parent_plan=capability_plan,
        goal_id=goal.goal_id,
        stage_id=reverse_plan.direction_id,
        declaration_name=reverse_helper,
        exact_type=reverse_type,
        proof_body=reverse_proof,
        route="semantic-reverse-direction",
        primitive_declarations=reverse_primitives,
        imports=compiler_imports,
    )
    forward_stage = _stage(
        capability_kind=CapabilityKind.SEMANTIC,
        parent_plan=capability_plan,
        goal_id=goal.goal_id,
        stage_id=forward_plan.direction_id,
        declaration_name=forward_helper,
        exact_type=forward_type,
        proof_body=forward_proof,
        route="semantic-forward-witness-and-invariants",
        primitive_declarations=forward_primitives,
        imports=compiler_imports,
    )
    proof_body = f"""intro formula
constructor
· rintro ⟨targetAssignment, targetSatisfies⟩
  exact ⟨targetAssignment,
    {reverse_helper} formula targetSatisfies⟩
· rintro ⟨sourceAssignment, sourceSatisfies⟩
  exact ⟨{forward_assignment},
    {forward_helper} formula sourceSatisfies⟩"""
    rendered_body = "\n".join("  " + line if line else "" for line in proof_body.splitlines())
    implementation = (
        fixed_declaration_header(
            declaration=declaration_name, exact_type=goal.exact_type
        )
        + "\n"
        + rendered_body
    )
    generator_result = GeneratorResult.create(
        brief=brief,
        status=GeneratorStatus.PROPOSED,
        implementation_body=proof_body,
        planner_hints_followed=(
            reverse_plan.direction_id,
            forward_plan.direction_id,
            "semantic-final-assembly",
        ),
    )
    contribution = ContributionReceipt(
        capability_declaration=declaration_name,
        contribution_class=ContributionClass.DETERMINISTIC_GENERATED_CAPABILITY,
        capability_kind=CapabilityKind.SEMANTIC,
        plan_id=capability_plan.plan_id,
        brief_id=brief.brief_id,
        generator_result_id=generator_result.result_id,
        primitive_candidates_used=tuple(_primitive_id(item) for item in primitives),
        planner_advice_ids=(
            reverse_plan.direction_id,
            forward_plan.direction_id,
            "semantic-final-assembly",
        ),
        generated_helpers=(reverse_helper, forward_helper),
        generated_data_objects=(typed_plan.plan_id,),
        deterministic_solver_steps=(
            "reverse-direction-helper",
            "forward-witness-and-invariants",
            "final-iff-assembly",
        ),
    )
    return FiniteCandidateWitness(
        witness_id="semantic-compiler-" + typed_plan.plan_fingerprint[-20:],
        implementation=implementation,
        imports=compiler_imports,
        executable_status="semantic-direction-dag-complete",
        check_receipt={
            "typed_plan_id": typed_plan.plan_id,
            "direction_count": 2,
            "forward_witness_generated": True,
            "direction_helpers_preserved_independently": True,
            "forbidden_closure_used": False,
            "proof_authority": "pending-independent-lean-verification",
        },
        candidate_class="typed-compiler",
        authoritative_typed_compiler=True,
        capability_plan=capability_plan,
        generator_brief=brief,
        generator_result=generator_result,
        contribution_receipt=contribution,
        typed_plan_receipt=asdict(typed_plan),
        stages=(reverse_stage, forward_stage),
    )


__all__ = [
    "InterpretApplication",
    "compile_direct_tm_candidate",
    "compile_semantic_candidate",
    "is_direct_tm_interpret_goal",
    "is_semantic_interpret_goal",
    "parse_interpret_application",
]
