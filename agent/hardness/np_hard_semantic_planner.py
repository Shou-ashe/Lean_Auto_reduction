"""Shared, checked semantic proof planning for staged NP-hard authoring."""

from __future__ import annotations

import json
import re
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import Any, Mapping, Protocol

from .lean_diagnostic_coach import coach_lean_diagnostic_text
from .lean_runner import run_command
from .model_client import ModelResponse, extract_json_object
from .models import CommandResult, sha256_id
from .np_hard_authoring import (
    NPHardAuthoringContractError,
    NPHardAuthoringTaskV2,
    NPHardSemanticPlanV1,
)
from .np_hard_production import semantic_planner_reasoning_profile


SEMANTIC_PLAN_NODE_ID = "semantic-plan"
SEMANTIC_PLAN_MAX_ATTEMPTS = 2
SEMANTIC_PLAN_CONSTRUCTION_NODE_IDS = (
    "clause-constraint",
    "complement-constraint",
    "clause-gadget",
    "reference-executable",
    "reduction-executable",
)

_NAE3_SCAFFOLD_MODULE = (
    "ComplexityReduction.Agent.Hardness.BooleanCSPReductionScaffold"
)
_NAE4_SCAFFOLD_MODULE = (
    "ComplexityReduction.Agent.Hardness.BooleanCSPNAE4ReductionScaffold"
)
_NAE5_SCAFFOLD_MODULE = (
    "ComplexityReduction.Agent.Hardness.BooleanCSPNAE5ReductionScaffold"
)


@dataclass(frozen=True)
class SemanticPlanFamilyProfileV1:
    """Family-specific public interface of one Boolean-CSP reference scaffold."""

    scaffold_module: str
    scaffold_file: str
    constraint_constructor: str
    clause_constraint_constructor: str
    satisfies_lemma: str
    main_constraint_lemma: str
    complement_lemmas: tuple[str, ...]
    default_complement_lemma: str
    target_assignment: str
    literal_value_lemma: str
    source_assignment: str
    literal_recovery_lemma: str
    constraint_code_tm: str
    payload_tm: str
    ingress_executable: str
    ingress_correct: str
    repeat_tm_note: str


_BOOLEAN_CSP_FAMILY_PROFILES: tuple[SemanticPlanFamilyProfileV1, ...] = (
    SemanticPlanFamilyProfileV1(
        scaffold_module=_NAE3_SCAFFOLD_MODULE,
        scaffold_file="BooleanCSPReductionScaffold.lean",
        constraint_constructor="ternaryConstraint",
        clause_constraint_constructor="ternaryConstraint",
        satisfies_lemma="ternaryConstraint_satisfies_iff",
        main_constraint_lemma="ternaryConstraint_satisfies_iff",
        complement_lemmas=(
            "ternaryConstraint_repeat_satisfies_iff",
            "ternaryConstraint_repeat_first_satisfies_iff",
            "ternaryConstraint_repeat_second_satisfies_iff",
        ),
        default_complement_lemma="ternaryConstraint_repeat_satisfies_iff",
        target_assignment="literalAssignment",
        literal_value_lemma="literalAssignment_literalKey",
        source_assignment="positiveKeyAssignment",
        literal_recovery_lemma="literal_eval_positiveKeyAssignment_of_complement",
        constraint_code_tm="ternaryConstraintCode_tmPolyTime",
        payload_tm="constraintPayload_tmPolyTime",
        ingress_executable="threeSATToNAEThreeSATIngress.executable",
        ingress_correct="threeSATToNAEThreeSATIngress.executableCorrect",
        repeat_tm_note="ternaryConstraintCode_tmPolyTime",
    ),
    SemanticPlanFamilyProfileV1(
        scaffold_module=_NAE4_SCAFFOLD_MODULE,
        scaffold_file="BooleanCSPNAE4ReductionScaffold.lean",
        constraint_constructor="quaternaryConstraint",
        clause_constraint_constructor="clauseConstraint",
        satisfies_lemma="quaternaryConstraint_satisfies_iff",
        main_constraint_lemma="clauseConstraint_satisfies_iff",
        complement_lemmas=("quaternaryConstraint_repeat_satisfies_iff",),
        default_complement_lemma="quaternaryConstraint_repeat_satisfies_iff",
        target_assignment="literalAssignment",
        literal_value_lemma="literalAssignment_literalKey",
        source_assignment="positiveKeyAssignment",
        literal_recovery_lemma="literal_eval_positiveKeyAssignment_of_complement",
        constraint_code_tm="quaternaryConstraintCode_tmPolyTime",
        payload_tm="constraintPayload_tmPolyTime",
        ingress_executable="threeSATToNAEThreeSATIngress.executable",
        ingress_correct="threeSATToNAEThreeSATIngress.executableCorrect",
        repeat_tm_note="quaternaryConstraintCode_tmPolyTime",
    ),
    SemanticPlanFamilyProfileV1(
        scaffold_module=_NAE5_SCAFFOLD_MODULE,
        scaffold_file="BooleanCSPNAE5ReductionScaffold.lean",
        constraint_constructor="pentaryConstraint",
        clause_constraint_constructor="clauseConstraint",
        satisfies_lemma="pentaryConstraint_satisfies_iff",
        main_constraint_lemma="clauseConstraint_satisfies_iff",
        complement_lemmas=("pentaryConstraint_repeat_satisfies_iff",),
        default_complement_lemma="pentaryConstraint_repeat_satisfies_iff",
        target_assignment="literalAssignment",
        literal_value_lemma="literalAssignment_literalKey",
        source_assignment="positiveKeyAssignment",
        literal_recovery_lemma="literal_eval_positiveKeyAssignment_of_complement",
        constraint_code_tm="pentaryConstraintCode_tmPolyTime",
        payload_tm="constraintPayload_tmPolyTime",
        ingress_executable="threeSATToNAEThreeSATIngress.executable",
        ingress_correct="threeSATToNAEThreeSATIngress.executableCorrect",
        repeat_tm_note="pentaryConstraintCode_tmPolyTime",
    ),
)

_BOOLEAN_CSP_FAMILY_PROFILES_BY_MODULE = {
    profile.scaffold_module: profile for profile in _BOOLEAN_CSP_FAMILY_PROFILES
}


def _family_profile(task: NPHardAuthoringTaskV2) -> SemanticPlanFamilyProfileV1:
    for module in task.allowed_imports:
        profile = _BOOLEAN_CSP_FAMILY_PROFILES_BY_MODULE.get(module)
        if profile is not None:
            return profile
    return _BOOLEAN_CSP_FAMILY_PROFILES[0]
SEMANTIC_PLAN_FORWARD_OBLIGATION_COUNT = 5
SEMANTIC_PLAN_FORBIDDEN_REFERENCES = (
    "TMPolyTimeMap",
    "formulaCode",
    "constraintCode",
    "Primitive",
    "PolyProg",
    "directTM",
    "DirectTM",
    "direct_tm",
)
SEMANTIC_PLAN_SYSTEM_PROMPT = """\
Return exactly one JSON object for a shared Lean semantic proof plan.  Do not
return a Lean proof or markdown.  Every declaration-valued field must copy one
exact declaration from the supplied catalog.  The ten ordered obligations are
Lean proposition types: entries 1-5 are forward, entries 6-10 are reverse.
Use formula_satisfaction_by_membership for both block methods; do not manually
decompose a fixed-length constraint list.  Your response's eight top-level
keys must be exactly schema_version, dependency_fingerprint,
formula_structure, forward, reverse, language_conversion,
ordered_obligations, and final_bridge.  The final_bridge fields are frozen by
the output template: copy them unchanged.  Never echo planner_context,
declaration_catalog, accepted_construction_bodies, exact_goals, or the
surrounding request.
"""


class SemanticPlannerModelClient(Protocol):
    def complete_json(self, *, system: str, prompt: str) -> ModelResponse: ...


@dataclass(frozen=True)
class SemanticPlanDependencySnapshot:
    fingerprint: str
    construction_bodies: tuple[tuple[str, str], ...]
    public_dependencies: tuple[tuple[str, str], ...]


@dataclass(frozen=True)
class SemanticPlanCheckResult:
    ok: bool
    commands: tuple[CommandResult, ...]
    diagnostic: str | None = None
    construction_mismatch_node_id: str | None = None


@dataclass(frozen=True)
class SemanticPlannerRunResult:
    plan: NPHardSemanticPlanV1 | None
    model_calls: int
    ledger: tuple[Mapping[str, Any], ...]
    commands: tuple[CommandResult, ...]
    failure_code: str | None = None
    failure_message: str | None = None
    construction_mismatch_node_id: str | None = None


def semantic_plan_required(task: NPHardAuthoringTaskV2) -> bool:
    ids = {node.node_id for node in task.gap_nodes}
    return set(SEMANTIC_PLAN_CONSTRUCTION_NODE_IDS).issubset(ids) and {
        "reference-semantic-forward",
        "reference-semantic-reverse",
    }.issubset(ids)


def _node(task: NPHardAuthoringTaskV2, node_id: str):
    matches = [node for node in task.gap_nodes if node.node_id == node_id]
    if len(matches) != 1:
        raise NPHardAuthoringContractError(
            "invalid_semantic_plan_schema", f"missing semantic-plan node {node_id}"
        )
    return matches[0]


def semantic_plan_dependency_snapshot(
    *, task: NPHardAuthoringTaskV2, accepted_bodies: Mapping[str, str]
) -> SemanticPlanDependencySnapshot:
    bodies: list[tuple[str, str]] = []
    for node_id in SEMANTIC_PLAN_CONSTRUCTION_NODE_IDS:
        declaration = _node(task, node_id).declaration
        body = accepted_bodies.get(declaration)
        if body is None:
            raise NPHardAuthoringContractError(
                "candidate_dependency_stale",
                f"semantic plan lacks accepted construction body {node_id}",
            )
        bodies.append((node_id, sha256_id(body)))
    semantic_primitives = set(dict(task.allowed_primitive_layers)["semantic"])
    primitive_types = dict(task.allowed_primitive_exact_types)
    public = tuple(
        sorted(
            (name, sha256_id(primitive_types[name]))
            for name in semantic_primitives
            if name in primitive_types
        )
    )
    payload = {
        "task_request_id": task.request_id,
        "construction_bodies": dict(bodies),
        "public_semantic_declarations": dict(public),
        "target_problem": task.target_problem.to_dict(),
        "reference_forward_type": _node(
            task, "reference-semantic-forward"
        ).exact_type,
        "reference_reverse_type": _node(
            task, "reference-semantic-reverse"
        ).exact_type,
    }
    return SemanticPlanDependencySnapshot(
        fingerprint=sha256_id(payload),
        construction_bodies=tuple(bodies),
        public_dependencies=public,
    )


def _declaration_catalog(task: NPHardAuthoringTaskV2) -> dict[str, str]:
    layers = dict(task.allowed_primitive_layers)
    exact_types = dict(task.allowed_primitive_exact_types)
    permitted = (*layers["construction"], *layers["semantic"])
    return {
        name: exact_types[name]
        for name in permitted
        if name in exact_types
        and not any(token in name for token in SEMANTIC_PLAN_FORBIDDEN_REFERENCES)
    }


def _source_snippets(root: Path, task: NPHardAuthoringTaskV2) -> dict[str, str]:
    profile = _family_profile(task)
    wanted = (
        task.target_problem.module.rsplit(".", 1)[-1] + ".lean",
        "Common.lean",
        profile.scaffold_file,
        "Formula.lean",
        "NAEThreeSAT.lean",
        "BooleanCSP.lean",
    )
    output: dict[str, str] = {}
    declaration_re = re.compile(
        r"(?m)^\s*(?:@\[[^\]]+\]\s*)?(?:noncomputable\s+)?"
        r"(?:def|abbrev|theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
    )
    catalog_names = {name.rsplit(".", 1)[-1] for name in _declaration_catalog(task)}
    catalog_names.update(
        {
            "gamma",
            "problem",
            "singletonGamma",
            "Satisfies",
            "Satisfiable",
            "satisfies_flatMap",
            "satisfies_flatMap_intro",
            "satisfies_flatMap_elim",
        }
    )
    for relative in task.public_source_files:
        if not relative.endswith(wanted):
            continue
        source = (root / relative).read_text(encoding="utf-8")
        matches = list(declaration_re.finditer(source))
        blocks: list[str] = []
        for index, match in enumerate(matches):
            name = match.group(1)
            if name not in catalog_names:
                continue
            end = matches[index + 1].start() if index + 1 < len(matches) else len(source)
            block = source[match.start() : end]
            if any(token in block for token in SEMANTIC_PLAN_FORBIDDEN_REFERENCES):
                continue
            blocks.append(block[:5_000])
        if blocks:
            output[relative] = "\n".join(blocks)[:16_000]
    return output


def build_semantic_planner_prompt(
    *,
    root: Path,
    task: NPHardAuthoringTaskV2,
    accepted_bodies: Mapping[str, str],
    diagnostic: str | None = None,
) -> tuple[str, SemanticPlanDependencySnapshot]:
    snapshot = semantic_plan_dependency_snapshot(
        task=task, accepted_bodies=accepted_bodies
    )
    accepted = {
        _node(task, node_id).declaration: accepted_bodies[
            _node(task, node_id).declaration
        ]
        for node_id in SEMANTIC_PLAN_CONSTRUCTION_NODE_IDS
    }
    target_gamma = task.target_problem.module + ".gamma"
    profile = _family_profile(task)
    scaffold = profile.scaffold_module
    payload = {
        "output_contract": {
            "top_level_keys_exactly": [
                "schema_version",
                "dependency_fingerprint",
                "formula_structure",
                "forward",
                "reverse",
                "language_conversion",
                "ordered_obligations",
                "final_bridge",
            ],
            "return_only_output_template_object": True,
            "do_not_echo_planner_context": True,
        },
        "output_template": {
            "schema_version": "hardness_np_hard_semantic_plan_v1",
            "dependency_fingerprint": snapshot.fingerprint,
            "formula_structure": {
                "reference_constructor": "List.flatMap",
                "block_declaration": _node(task, "clause-gadget").declaration,
                "introduction_lemma": "ComplexityReduction.CSP.Formula.satisfies_flatMap_intro",
                "elimination_lemma": "ComplexityReduction.CSP.Formula.satisfies_flatMap_elim",
            },
            "forward": {
                "target_assignment": scaffold + "." + profile.target_assignment,
                "literal_value_lemma": scaffold
                + "."
                + profile.literal_value_lemma,
                "main_constraint_lemma": scaffold
                + "."
                + profile.main_constraint_lemma,
                "complement_constraint_lemma": scaffold
                + "."
                + profile.default_complement_lemma,
                "block_proof_method": "formula_satisfaction_by_membership",
            },
            "reverse": {
                "source_assignment": scaffold + "." + profile.source_assignment,
                "block_extraction_method": "formula_satisfaction_by_membership",
                "main_constraint_lemma": scaffold
                + "."
                + profile.main_constraint_lemma,
                "complement_constraint_lemma": scaffold
                + "."
                + profile.default_complement_lemma,
                "literal_recovery_lemma": scaffold
                + "."
                + profile.literal_recovery_lemma,
            },
            "language_conversion": {
                "method": "unfold_and_simpa",
                "definitions": [
                    target_gamma,
                    "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common.singletonGamma",
                    scaffold + ".gamma",
                ],
            },
            "ordered_obligations": [
                "exact forward Lean proposition 1",
                "exact forward Lean proposition 2",
                "exact forward Lean proposition 3",
                "exact forward Lean proposition 4",
                "exact forward Lean proposition 5",
                "exact reverse Lean proposition 1",
                "exact reverse Lean proposition 2",
                "exact reverse Lean proposition 3",
                "exact reverse Lean proposition 4",
                "exact reverse Lean proposition 5",
            ],
            "final_bridge": {
                "source_bridge_theorem": scaffold
                + "."
                + profile.ingress_correct,
                "reference_formula_builder": scaffold
                + "."
                + profile.ingress_executable,
                "application_form": "apply_bridge_at_input_then_project",
                "program_run_declaration": _node(
                    task, "program-run-coherence"
                ).declaration,
                "synthesized_executable_declaration": _node(
                    task, "reduction-executable"
                ).declaration,
                "reference_executable_declaration": _node(
                    task, "reference-executable"
                ).declaration,
                "reference_forward_declaration": _node(
                    task, "reference-semantic-forward"
                ).declaration,
                "reference_reverse_declaration": _node(
                    task, "reference-semantic-reverse"
                ).declaration,
                "semantic_forward_declaration": _node(
                    task, "semantic-forward"
                ).declaration,
                "semantic_reverse_declaration": _node(
                    task, "semantic-reverse"
                ).declaration,
            },
        },
        "planner_context": {
            "accepted_construction_bodies": accepted,
            "declaration_catalog": _declaration_catalog(task),
            "semantic_source_snippets": _source_snippets(root, task),
            "exact_goals": {
                "forward": _node(task, "reference-semantic-forward").exact_type,
                "reverse": _node(task, "reference-semantic-reverse").exact_type,
            },
            "public_endpoint_definitions": {
                "problem": task.target_problem.term,
                "gamma": target_gamma,
                "accepts": task.target_problem.term + ".accepts",
            },
            "fixed_methods": {
                "reference_constructor": "List.flatMap",
                "block_proof_method": "formula_satisfaction_by_membership",
                "block_extraction_method": "formula_satisfaction_by_membership",
                "language_conversion_method": "unfold_and_simpa",
            },
            "ordered_obligation_contract": {
                "count": 10,
                "forward_entries": [1, 2, 3, 4, 5],
                "reverse_entries": [6, 7, 8, 9, 10],
                "required_form": "exact Lean proposition types",
            },
            "lean_diagnostic": (
                coach_lean_diagnostic_text(diagnostic, max_coached_chars=8_000)
                if diagnostic
                else None
            ),
        },
    }
    serialized = json.dumps(payload, ensure_ascii=True, indent=2, sort_keys=True)
    for forbidden in SEMANTIC_PLAN_FORBIDDEN_REFERENCES:
        if forbidden in serialized:
            raise NPHardAuthoringContractError(
                "semantic_plan_forbidden_layer",
                f"semantic planner prompt leaked excluded interface {forbidden}",
            )
    return serialized, snapshot


def validate_semantic_plan(
    *,
    plan: NPHardSemanticPlanV1,
    task: NPHardAuthoringTaskV2,
    snapshot: SemanticPlanDependencySnapshot,
) -> None:
    plan.validate_shape()
    if plan.dependency_fingerprint != snapshot.fingerprint:
        raise NPHardAuthoringContractError(
            "candidate_dependency_stale", "semantic plan dependency fingerprint is stale"
        )
    catalog = _declaration_catalog(task)
    theorem_names = (
        plan.formula_structure.introduction_lemma,
        plan.formula_structure.elimination_lemma,
        plan.forward.literal_value_lemma,
        plan.forward.main_constraint_lemma,
        plan.forward.complement_constraint_lemma,
        plan.reverse.main_constraint_lemma,
        plan.reverse.complement_constraint_lemma,
        plan.reverse.literal_recovery_lemma,
        plan.final_bridge.source_bridge_theorem,
        plan.final_bridge.reference_formula_builder,
    )
    missing = [name for name in theorem_names if name not in catalog]
    if missing:
        raise NPHardAuthoringContractError(
            "semantic_plan_unknown_declaration",
            f"semantic plan cites declarations outside permitted layers: {missing!r}",
        )
    if plan.formula_structure.reference_constructor != "List.flatMap":
        raise NPHardAuthoringContractError(
            "invalid_semantic_plan_schema", "unsupported reference constructor"
        )
    if plan.formula_structure.block_declaration != _node(
        task, "clause-gadget"
    ).declaration:
        raise NPHardAuthoringContractError(
            "candidate_dependency_stale", "semantic plan changed the block declaration"
        )
    profile = _family_profile(task)
    scaffold = profile.scaffold_module
    exact_fields = {
        plan.forward.target_assignment: scaffold
        + "."
        + profile.target_assignment,
        plan.forward.literal_value_lemma: scaffold
        + "."
        + profile.literal_value_lemma,
        plan.forward.main_constraint_lemma: scaffold
        + "."
        + profile.main_constraint_lemma,
        plan.reverse.source_assignment: scaffold
        + "."
        + profile.source_assignment,
        plan.reverse.main_constraint_lemma: scaffold
        + "."
        + profile.main_constraint_lemma,
        plan.reverse.literal_recovery_lemma: scaffold
        + "."
        + profile.literal_recovery_lemma,
        plan.final_bridge.source_bridge_theorem: scaffold
        + "."
        + profile.ingress_correct,
        plan.final_bridge.reference_formula_builder: scaffold
        + "."
        + profile.ingress_executable,
        plan.final_bridge.application_form: "apply_bridge_at_input_then_project",
    }
    if any(observed != expected for observed, expected in exact_fields.items()):
        raise NPHardAuthoringContractError(
            "invalid_semantic_plan_schema", "semantic plan changed a fixed semantic interface"
        )
    expected_generated_declarations = {
        plan.final_bridge.program_run_declaration: _node(
            task, "program-run-coherence"
        ).declaration,
        plan.final_bridge.synthesized_executable_declaration: _node(
            task, "reduction-executable"
        ).declaration,
        plan.final_bridge.reference_executable_declaration: _node(
            task, "reference-executable"
        ).declaration,
        plan.final_bridge.reference_forward_declaration: _node(
            task, "reference-semantic-forward"
        ).declaration,
        plan.final_bridge.reference_reverse_declaration: _node(
            task, "reference-semantic-reverse"
        ).declaration,
        plan.final_bridge.semantic_forward_declaration: _node(
            task, "semantic-forward"
        ).declaration,
        plan.final_bridge.semantic_reverse_declaration: _node(
            task, "semantic-reverse"
        ).declaration,
    }
    if any(
        observed != expected
        for observed, expected in expected_generated_declarations.items()
    ):
        raise NPHardAuthoringContractError(
            "candidate_dependency_stale",
            "semantic plan final bridge does not bind the exact DAG node declarations",
        )
    repeat_lemmas = {
        scaffold + "." + lemma for lemma in profile.complement_lemmas
    }
    if {
        plan.forward.complement_constraint_lemma,
        plan.reverse.complement_constraint_lemma,
    } - repeat_lemmas:
        raise NPHardAuthoringContractError(
            "invalid_semantic_plan_schema", "semantic plan selected an unsupported repeat lemma"
        )
    if plan.forward.complement_constraint_lemma != plan.reverse.complement_constraint_lemma:
        raise NPHardAuthoringContractError(
            "invalid_semantic_plan_schema", "forward/reverse disagree on complement layout"
        )
    if (
        plan.forward.block_proof_method != "formula_satisfaction_by_membership"
        or plan.reverse.block_extraction_method
        != "formula_satisfaction_by_membership"
        or plan.language_conversion.method != "unfold_and_simpa"
    ):
        raise NPHardAuthoringContractError(
            "invalid_semantic_plan_schema", "semantic plan selected an unsupported method"
        )
    expected_definitions = {
        task.target_problem.module + ".gamma",
        "Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common.singletonGamma",
        scaffold + ".gamma",
    }
    if set(plan.language_conversion.definitions) != expected_definitions:
        raise NPHardAuthoringContractError(
            "invalid_semantic_plan_schema", "semantic plan language definitions drifted"
        )
    declaration_re = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+")
    for obligation in plan.ordered_obligations:
        if not declaration_re.search(obligation) or any(
            token in obligation for token in SEMANTIC_PLAN_FORBIDDEN_REFERENCES
        ):
            raise NPHardAuthoringContractError(
                "invalid_semantic_plan_schema",
                "ordered obligation is not an exact permitted Lean proposition",
            )


def parse_semantic_plan(
    *,
    content: str,
    task: NPHardAuthoringTaskV2,
    snapshot: SemanticPlanDependencySnapshot,
) -> NPHardSemanticPlanV1:
    value = extract_json_object(content)
    if not isinstance(value, Mapping):
        raise NPHardAuthoringContractError(
            "invalid_semantic_plan_schema", "planner did not return one JSON object"
        )
    plan = NPHardSemanticPlanV1.from_dict(value)
    validate_semantic_plan(plan=plan, task=task, snapshot=snapshot)
    return plan


def _construction_source(
    *, task: NPHardAuthoringTaskV2, accepted_bodies: Mapping[str, str]
) -> str:
    imports = "\n".join(f"import {name}" for name in task.allowed_imports)
    declarations: list[str] = []
    for node_id in SEMANTIC_PLAN_CONSTRUCTION_NODE_IDS:
        node = _node(task, node_id)
        short = node.declaration.removeprefix(task.candidate_module + ".")
        body = accepted_bodies[node.declaration]
        declarations.append(
            f"noncomputable def {short} :\n    {node.exact_type} :=\n"
            + "\n".join(f"  {line}" for line in body.rstrip().splitlines())
        )
    return f"""{imports}

namespace {task.candidate_module}
open ComplexityReduction
open ComplexityReduction.CSP
open {task.target_problem.module}

{chr(10).join(declarations)}
"""


def _check_source(
    *,
    task: NPHardAuthoringTaskV2,
    accepted_bodies: Mapping[str, str],
    plan: NPHardSemanticPlanV1,
    check_ordered_obligations: bool = True,
) -> str:
    clause = _node(task, "clause-constraint").declaration.rsplit(".", 1)[-1]
    complement = _node(task, "complement-constraint").declaration.rsplit(".", 1)[-1]
    gadget = _node(task, "clause-gadget").declaration.rsplit(".", 1)[-1]
    reference = _node(task, "reference-executable").declaration.rsplit(".", 1)[-1]
    reduction = _node(task, "reduction-executable").declaration.rsplit(".", 1)[-1]
    scaffold = _family_profile(task).scaffold_module
    target_gamma = task.target_problem.module + ".gamma"
    source = _construction_source(task=task, accepted_bodies=accepted_bodies)
    obligation_checks = (
        "\n".join(
            f"#check ({obligation})" for obligation in plan.ordered_obligations
        )
        if check_ordered_obligations
        else ""
    )
    return source + f"""

example (formula : ComplexityReduction.NAEThreeSAT.Formula) :
    {reference} formula = List.flatMap {gadget} formula := by
  rfl

example (input : {task.source_problem.term}.Instance) :
    {reduction} input =
      {reference} ({scaffold}.threeSATToNAEThreeSATIngress.executable input) := by
  rfl

example (clauseValue : ComplexityReduction.NAEThreeSAT.Clause)
    (assignment : ComplexityReduction.SAT.Assignment) :
    ComplexityReduction.CSP.Constraint.Satisfies
        ({clause} clauseValue) assignment ↔
      ¬ (assignment ({scaffold}.literalKey clauseValue.first) =
          assignment ({scaffold}.literalKey clauseValue.second) ∧
        assignment ({scaffold}.literalKey clauseValue.second) =
          assignment ({scaffold}.literalKey clauseValue.third)) := by
  unfold {clause}
  exact {plan.forward.main_constraint_lemma} _ _ _ assignment

example (literal : ComplexityReduction.SAT.Literal)
    (assignment : ComplexityReduction.SAT.Assignment) :
    ComplexityReduction.CSP.Constraint.Satisfies
        ({complement} literal) assignment ↔
      assignment ({scaffold}.literalKey ({scaffold}.complementLiteral literal)) =
        !assignment ({scaffold}.literalKey literal) := by
  unfold {complement}
  exact {plan.forward.complement_constraint_lemma} _ _ assignment

example (formula : ComplexityReduction.NAEThreeSAT.Formula)
    (assignment : ComplexityReduction.SAT.Assignment)
    (hBlocks : ∀ clauseValue ∈ formula,
      ComplexityReduction.CSP.Formula.Satisfies
        ({gadget} clauseValue) assignment) :
    ComplexityReduction.CSP.Formula.Satisfies
      ({reference} formula) assignment := by
  change ComplexityReduction.CSP.Formula.Satisfies
    (List.flatMap {gadget} formula) assignment
  exact {plan.formula_structure.introduction_lemma} hBlocks

example (formula : ComplexityReduction.NAEThreeSAT.Formula)
    (assignment : ComplexityReduction.SAT.Assignment)
    (hFormula : ComplexityReduction.CSP.Formula.Satisfies
      ({reference} formula) assignment)
    (clauseValue : ComplexityReduction.NAEThreeSAT.Clause)
    (hMember : clauseValue ∈ formula) :
    ComplexityReduction.CSP.Formula.Satisfies
      ({gadget} clauseValue) assignment := by
  have hFlat : ComplexityReduction.CSP.Formula.Satisfies
      (List.flatMap {gadget} formula) assignment := by
    change ComplexityReduction.CSP.Formula.Satisfies ({reference} formula) assignment
    exact hFormula
  exact {plan.formula_structure.elimination_lemma} hFlat clauseValue hMember

example (clauseValue : ComplexityReduction.NAEThreeSAT.Clause)
    (assignment : ComplexityReduction.SAT.Assignment)
    (hBlock : ComplexityReduction.CSP.Formula.Satisfies
      ({gadget} clauseValue) assignment) :
    ComplexityReduction.CSP.Constraint.Satisfies
      ({clause} clauseValue) assignment := by
  exact hBlock ({clause} clauseValue) (by simp [{gadget}])

example (clauseValue : ComplexityReduction.NAEThreeSAT.Clause)
    (assignment : ComplexityReduction.SAT.Assignment)
    (hBlock : ComplexityReduction.CSP.Formula.Satisfies
      ({gadget} clauseValue) assignment) :
    ComplexityReduction.CSP.Constraint.Satisfies
      ({complement} clauseValue.first) assignment := by
  exact hBlock ({complement} clauseValue.first) (by simp [{gadget}])

example (literal : ComplexityReduction.SAT.Literal)
    (assignment : ComplexityReduction.SAT.Assignment)
    (hConstraint : ComplexityReduction.CSP.Constraint.Satisfies
      ({complement} literal) assignment) :
    literal.eval ({plan.reverse.source_assignment} assignment) =
      assignment ({scaffold}.literalKey literal) := by
  apply {plan.reverse.literal_recovery_lemma} assignment literal
  exact ({plan.reverse.complement_constraint_lemma} _ _ assignment).1 (by
    simpa [{complement}] using hConstraint)

example (formula : ComplexityReduction.CSP.Formula {target_gamma}) :
    {task.target_problem.term}.accepts formula ↔
      ComplexityReduction.CSP.Formula.Satisfiable
        (show ComplexityReduction.CSP.Formula {scaffold}.gamma from formula) := by
  simpa [{task.target_problem.term}, {", ".join(plan.language_conversion.definitions)}] using
    (ComplexityReduction.Domain.BooleanCSP.cspOf_accepts {target_gamma} formula)

example (input : {task.source_problem.term}.Instance)
    (hInput : {task.source_problem.term}.accepts input) :
    ComplexityReduction.NAEThreeSAT.Formula.Satisfiable
        ({plan.final_bridge.reference_formula_builder} input) :=
  ({plan.final_bridge.source_bridge_theorem} input).1 hInput

{obligation_checks}

end {task.candidate_module}
"""


def check_semantic_plan_locally(
    *,
    root: Path,
    output_dir: Path,
    task: NPHardAuthoringTaskV2,
    accepted_bodies: Mapping[str, str],
    plan: NPHardSemanticPlanV1,
    timeout_seconds: int,
    check_ordered_obligations: bool = True,
) -> SemanticPlanCheckResult:
    output_dir.mkdir(parents=True, exist_ok=True)
    source_path = output_dir / "SemanticPlanCheck.lean"
    source_path.write_text(
        _check_source(
            task=task,
            accepted_bodies=accepted_bodies,
            plan=plan,
            check_ordered_obligations=check_ordered_obligations,
        ),
        encoding="utf-8",
    )
    command = run_command(
        ["lake", "env", "lean", str(source_path)],
        cwd=root / "Lean",
        timeout_seconds=timeout_seconds,
    )
    if command.ok:
        return SemanticPlanCheckResult(ok=True, commands=(command,))
    diagnostic = (command.stderr or command.stdout or "semantic plan check failed")[:8_000]
    return SemanticPlanCheckResult(
        ok=False, commands=(command,), diagnostic=diagnostic
    )


def _construction_node_for_diagnostic(
    *, source_path: Path, diagnostic: str
) -> str | None:
    match = re.search(r":(\d+):(\d+): error:", diagnostic)
    if match is None:
        return None
    line_number = int(match.group(1))
    lines = source_path.read_text(encoding="utf-8").splitlines()
    prefix = "\n".join(lines[max(0, line_number - 14) : line_number])
    if "referenceExecutable formula = List.flatMap" in prefix:
        return "reference-executable"
    if "threeSATToNAEThreeSATIngress.executable input" in prefix:
        return "reduction-executable"
    if "clauseConstraint" in prefix and "hBlock" not in prefix:
        return "clause-constraint"
    if "complementConstraint" in prefix and "hBlock" not in prefix:
        return "complement-constraint"
    if "hBlock" in prefix or "hFormula" in prefix:
        return "clause-gadget"
    if "literal_recovery" in prefix or "positiveKeyAssignment" in prefix:
        return "complement-constraint"
    return None


def classify_semantic_construction_mismatch(
    *,
    root: Path,
    output_dir: Path,
    task: NPHardAuthoringTaskV2,
    accepted_bodies: Mapping[str, str],
    plan: NPHardSemanticPlanV1,
    timeout_seconds: int,
) -> tuple[str | None, tuple[CommandResult, ...]]:
    """Prove a checked plan failed because construction, not obligations, drifted."""

    scaffold = "ComplexityReduction.Agent.Hardness.BooleanCSPReductionScaffold"
    repeat_lemmas = (
        scaffold + ".ternaryConstraint_repeat_satisfies_iff",
        scaffold + ".ternaryConstraint_repeat_first_satisfies_iff",
        scaffold + ".ternaryConstraint_repeat_second_satisfies_iff",
    )
    commands: list[CommandResult] = []
    first_failure: tuple[Path, str] | None = None
    for index, lemma in enumerate(repeat_lemmas, start=1):
        candidate = replace(
            plan,
            forward=replace(plan.forward, complement_constraint_lemma=lemma),
            reverse=replace(plan.reverse, complement_constraint_lemma=lemma),
        )
        check_dir = output_dir / f"construction-probe-{index:02d}"
        result = check_semantic_plan_locally(
            root=root,
            output_dir=check_dir,
            task=task,
            accepted_bodies=accepted_bodies,
            plan=candidate,
            timeout_seconds=timeout_seconds,
            check_ordered_obligations=False,
        )
        commands.extend(result.commands)
        if result.ok:
            return None, tuple(commands)
        if first_failure is None:
            first_failure = (
                check_dir / "SemanticPlanCheck.lean",
                result.diagnostic or "",
            )
    if first_failure is None:
        return None, tuple(commands)
    source_path, diagnostic = first_failure
    return (
        _construction_node_for_diagnostic(
            source_path=source_path, diagnostic=diagnostic
        )
        or "clause-constraint",
        tuple(commands),
    )


def split_semantic_plan_for_node(
    plan: NPHardSemanticPlanV1, *, capability: str
) -> dict[str, Any]:
    shared = {
        "formula_structure": {
            "reference_constructor": plan.formula_structure.reference_constructor,
            "block_declaration": plan.formula_structure.block_declaration,
            "introduction_lemma": plan.formula_structure.introduction_lemma,
            "elimination_lemma": plan.formula_structure.elimination_lemma,
        },
        "language_conversion": {
            "method": plan.language_conversion.method,
            "definitions": list(plan.language_conversion.definitions),
        },
    }
    if capability == "reference_semantic_forward":
        return {
            **shared,
            "forward": {
                **plan.forward.__dict__,
                "ordered_obligations": list(
                    plan.ordered_obligations[:SEMANTIC_PLAN_FORWARD_OBLIGATION_COUNT]
                ),
            },
        }
    if capability == "reference_semantic_reverse":
        return {
            **shared,
            "reverse": {
                **plan.reverse.__dict__,
                "ordered_obligations": list(
                    plan.ordered_obligations[SEMANTIC_PLAN_FORWARD_OBLIGATION_COUNT:]
                ),
            },
        }
    if capability in {
        "semantic_forward",
        "semantic_forward_implication",
        "semantic_reverse",
        "semantic_reverse_implication",
        "semantic_iff",
        "semantic_iff_implication",
    }:
        return {
            **shared,
            "final_bridge": asdict(plan.final_bridge),
        }
    return {}


def run_semantic_planner(
    *,
    root: Path,
    output_dir: Path,
    task: NPHardAuthoringTaskV2,
    accepted_bodies: Mapping[str, str],
    model: SemanticPlannerModelClient,
    timeout_seconds: int,
) -> SemanticPlannerRunResult:
    diagnostic: str | None = None
    ledger: list[Mapping[str, Any]] = []
    commands: list[CommandResult] = []
    last_checked_plan: NPHardSemanticPlanV1 | None = None
    profile = semantic_planner_reasoning_profile(model=model)
    for attempt in range(1, SEMANTIC_PLAN_MAX_ATTEMPTS + 1):
        prompt, snapshot = build_semantic_planner_prompt(
            root=root,
            task=task,
            accepted_bodies=accepted_bodies,
            diagnostic=diagnostic,
        )
        method = getattr(model, "complete_json_with_profile", None)
        if callable(method):
            response = method(
                system=SEMANTIC_PLAN_SYSTEM_PROMPT,
                prompt=prompt,
                max_tokens=profile["effective_max_tokens"],
                reasoning_effort=profile["effective_reasoning_effort"],
            )
        else:
            response = model.complete_json(
                system=SEMANTIC_PLAN_SYSTEM_PROMPT, prompt=prompt
            )
        output_dir.mkdir(parents=True, exist_ok=True)
        prompt_path = output_dir / f"attempt-{attempt:02d}-prompt.json"
        response_path = output_dir / f"attempt-{attempt:02d}-response.json"
        prompt_path.write_text(prompt, encoding="utf-8")
        response_path.write_text(
            json.dumps(
                {
                    "called": response.called,
                    "ok": response.ok,
                    "status_code": response.status_code,
                    "duration_seconds": response.duration_seconds,
                    "usage": response.usage,
                    "attempts": response.attempts,
                    "finish_reason": response.finish_reason,
                    "content": response.content,
                    "error": response.error,
                    "reasoning_profile": profile,
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        record: dict[str, Any] = {
            "node_id": SEMANTIC_PLAN_NODE_ID,
            "attempt": attempt,
            "prompt_sha256": sha256_id(prompt),
            "prompt_file": str(prompt_path),
            "response_sha256": sha256_id(response.content),
            "response_file": str(response_path),
            "called": response.called,
            "ok": response.ok,
            "status_code": response.status_code,
            "duration_seconds": response.duration_seconds,
            "usage": response.usage,
            "provider_attempts": response.attempts,
            "finish_reason": response.finish_reason,
            "error": response.error,
            "node_reasoning_profile": profile,
        }
        ledger.append(record)
        if not response.called or not response.ok:
            diagnostic = response.error or "semantic planner request failed"
            continue
        try:
            plan = parse_semantic_plan(
                content=response.content, task=task, snapshot=snapshot
            )
        except (NPHardAuthoringContractError, ValueError) as error:
            diagnostic = str(error)
            continue
        check = check_semantic_plan_locally(
            root=root,
            output_dir=output_dir / f"attempt-{attempt:02d}-lean",
            task=task,
            accepted_bodies=accepted_bodies,
            plan=plan,
            timeout_seconds=timeout_seconds,
        )
        commands.extend(check.commands)
        if not check.ok:
            last_checked_plan = plan
            diagnostic = check.diagnostic
            continue
        plan_path = output_dir / "plan.json"
        plan_path.write_text(
            json.dumps(plan.to_dict(), indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        record["semantic_plan_sha256"] = sha256_id(plan.to_dict())
        record["semantic_plan_file"] = str(plan_path)
        return SemanticPlannerRunResult(
            plan=plan,
            model_calls=len(ledger),
            ledger=tuple(ledger),
            commands=tuple(commands),
        )
    mismatch_node_id: str | None = None
    if last_checked_plan is not None:
        mismatch_node_id, mismatch_commands = classify_semantic_construction_mismatch(
            root=root,
            output_dir=output_dir / "construction-classification",
            task=task,
            accepted_bodies=accepted_bodies,
            plan=last_checked_plan,
            timeout_seconds=timeout_seconds,
        )
        commands.extend(mismatch_commands)
    return SemanticPlannerRunResult(
        plan=None,
        model_calls=len(ledger),
        ledger=tuple(ledger),
        commands=tuple(commands),
        failure_code=(
            "semantic_plan_construction_mismatch"
            if mismatch_node_id is not None
            else "semantic_plan_failed"
        ),
        failure_message=diagnostic or "semantic planner exhausted its two attempts",
        construction_mismatch_node_id=mismatch_node_id,
    )
