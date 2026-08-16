"""Optional finite-reflection capabilities for Boolean CSP premises."""

from __future__ import annotations

from dataclasses import asdict
import re
from typing import Mapping, Sequence

from ..capability_compilers import (
    compile_direct_tm_candidate,
    compile_semantic_candidate,
    is_direct_tm_interpret_goal,
    is_semantic_interpret_goal,
)
from ..finite_synthesis import (
    FiniteCandidateWitness,
    FiniteSupportReceipt,
)
from ..model.authoring import fixed_declaration_header
from ..models import (
    CapabilityKind,
    CapabilityPlan,
    ContributionClass,
    ContributionReceipt,
    GadgetCapabilityPlan,
    GeneratorBrief,
    GeneratorResult,
    GeneratorStatus,
    PremiseKind,
    TheoremPremise,
    stable_sha256,
)
from ..premise_registry import PremiseSolution, PremiseSolverRegistry
from .registry import Plugin


def _is_decision_equality(text: str) -> bool:
    return (
        ("Decidable.decide" in text or "@decide" in text)
        and ("Bool.true" in text or "Bool.false" in text)
    )


def _is_negative_goal(text: str) -> bool:
    normalized = " ".join(text.split())
    return normalized.startswith(("¬", "Not ", "Not(")) or normalized.endswith(
        ("→ False", "-> False")
    )


class BooleanCSPFiniteReflectionSolver:
    name = "boolean-csp-finite-reflection"

    def supports(self, premise: TheoremPremise, local_context: Sequence[str]) -> float:
        if premise.kind != PremiseKind.PROPOSITION:
            return 0.0
        text = premise.exact_type
        if _is_decision_equality(text):
            return 1.0
        if ".Nonempty" in text:
            return 1.0
        if "IsSchaeferTractable" in text and _is_negative_goal(text):
            return 1.0
        if "PreservesComplement" in text:
            return 1.0
        return 0.0

    def propose(
        self, premise: TheoremPremise, local_context: Sequence[str]
    ) -> PremiseSolution | None:
        text = premise.exact_type
        if _is_decision_equality(text):
            return PremiseSolution(
                solver=self.name + ":decision-equality",
                proof_lines=("  · decide",),
                proof_term="by decide",
                confidence=1.0,
            )
        if ".Nonempty" in text:
            return PremiseSolution(
                solver=self.name + ":relations-nonempty",
                proof_lines=(
                    "  · apply ComplexityReduction.Agent.Reduction.Reflection."
                    "gammaRelationsNonempty_of_decide_eq_true",
                    "    decide",
                ),
                proof_term=None,
                confidence=1.0,
            )
        if "IsSchaeferTractable" in text and _is_negative_goal(text):
            return PremiseSolution(
                solver=self.name + ":hard-side",
                proof_lines=(
                    "  · apply ComplexityReduction.Agent.Reduction.Reflection."
                    "gammaNotSchaeferTractable_of_decide_eq_false",
                    "    decide",
                ),
                proof_term=None,
                confidence=1.0,
            )
        if "PreservesComplement" in text:
            negative = _is_negative_goal(text)
            theorem = (
                "gammaNotPreservesComplement_of_decide_eq_false"
                if negative
                else "gammaPreservesComplement_of_decide_eq_true"
            )
            return PremiseSolution(
                solver=self.name + (":not-complement" if negative else ":complement"),
                proof_lines=(
                    "  · apply ComplexityReduction.Agent.Reduction.Reflection." + theorem,
                    "    decide",
                ),
                proof_term=None,
                confidence=1.0,
            )
        return None


_HARDNESS = "ComplexityReduction.Domain.BooleanCSP.Hardness."
_INTERPRETATION = _HARDNESS + "LanguageInterpretation"
_GADGET = _HARDNESS + "Gadget"
_ONE_IN_THREE = _HARDNESS + "oneInThreeCore"
_NAE3 = _HARDNESS + "nae3Core"
_EXACTLY_TWO3 = _HARDNESS + "exactlyTwo3Core"
_THREE_SAT_LIKE = _HARDNESS + "threeSATLikeCore"
_FINITE_GADGET = (
    "ComplexityReduction.Agent.GenerativeReduction.Plugins."
    "BooleanCSPFiniteGadget."
)
_STANDARD = "ComplexityReduction.CSP.StandardRelations."


def _lean_nat_list(values: Sequence[int]) -> str:
    return "[" + ", ".join(str(value) for value in values) + "]"


def _lean_template_list(templates: Sequence[Sequence[Sequence[int]]]) -> str:
    return "[" + ", ".join(
        "[" + ", ".join(_lean_nat_list(mapping) for mapping in template) + "]"
        for template in templates
    ) + "]"


def _dual_cardinality_template(arity: int) -> tuple[tuple[int, ...], ...]:
    """Express one-in-three from an exactly-(arity-1)-of-arity relation.

    The construction is relation-table generic: one atom pins ``t=true`` and
    ``f=false``; three atoms define complements of the output coordinates;
    the final atom requires exactly two complements.  It uses no benchmark or
    declaration name and is valid for every arity at least four.
    """

    if arity < 4:
        raise ValueError("dual-cardinality seed requires arity at least four")
    true_variable = 3
    false_variable = 4
    complements = (5, 6, 7)
    return (
        (*([true_variable] * (arity - 1)), false_variable),
        (0, complements[0], *([true_variable] * (arity - 2))),
        (1, complements[1], *([true_variable] * (arity - 2))),
        (2, complements[2], *([true_variable] * (arity - 2))),
        (*complements, *([true_variable] * (arity - 3))),
    )


_DUAL_CARDINALITY_SEEDS = tuple(
    (arity, _dual_cardinality_template(arity)) for arity in range(4, 7)
)


def _expanded_gadget_templates(
    *, variable_bound: int, constraint_bound: int, round_index: int
) -> tuple[tuple[tuple[int, ...], ...], ...]:
    """Generate grammar expansions without inspecting a benchmark or relation name."""

    if round_index <= 0:
        return ()
    expansions: list[tuple[tuple[int, ...], ...]] = []
    expansions.extend(template for _, template in _DUAL_CARDINALITY_SEEDS)
    auxiliary_variables = range(3, max(4, variable_bound))
    for auxiliary in auxiliary_variables:
        expansions.extend(
            (
                ((0, 1, 2, auxiliary), (0, auxiliary)),
                ((0, auxiliary, 2), (1, auxiliary)),
                ((auxiliary, 1, 2), (0, auxiliary)),
                ((0, 1, auxiliary), (2, auxiliary)),
            )
        )
    # Add bounded chains and pairwise constraints as the CEGIS history grows.
    # `plannedMappedVariable` safely truncates/extends mappings for any target
    # relation arity, so these are grammar shapes rather than case templates.
    chain_length = min(constraint_bound, 2 + round_index)
    if chain_length >= 2:
        chain = tuple(
            (index % variable_bound, (index + 1) % variable_bound, (index + 2) % variable_bound)
            for index in range(chain_length)
        )
        expansions.append(chain)
    pairwise = tuple(
        (left, right, right)
        for left in range(min(variable_bound, 5))
        for right in range(left + 1, min(variable_bound, 5))
    )
    if pairwise:
        expansions.append(pairwise[:constraint_bound])
    unique: list[tuple[tuple[int, ...], ...]] = []
    for template in expansions:
        normalized = template[:constraint_bound]
        if normalized and normalized not in unique:
            unique.append(normalized)
    return tuple(unique)


def _selected_template_expression(
    *, variable_bound: int, constraint_bound: int, round_index: int
) -> tuple[str, int]:
    expanded = _expanded_gadget_templates(
        variable_bound=variable_bound,
        constraint_bound=constraint_bound,
        round_index=round_index,
    )
    if not expanded:
        return _FINITE_GADGET + "templates", 0
    return (
        f"({_FINITE_GADGET}templates ++ {_lean_template_list(expanded)})",
        len(expanded),
    )


def _compact(value: str) -> str:
    return " ".join(value.split())


_POINTWISE_GADGET_GOAL = re.compile(
    rf"^\(symbol : (?P<source>\S+)\.Symbol\) → "
    rf"{re.escape(_GADGET)} (?P<target>\S+) "
    rf"\((?P=source)\.relationOf symbol\)$"
)
_INTERPRETATION_GOAL = re.compile(
    rf"^{re.escape(_INTERPRETATION)} (?P<source>\S+) (?P<target>\S+)$"
)


def _gadget_endpoints(exact_type: str) -> tuple[str, str, bool] | None:
    compact = _compact(exact_type)
    pointwise = _POINTWISE_GADGET_GOAL.fullmatch(compact)
    if pointwise is not None:
        return pointwise.group("source"), pointwise.group("target"), True
    interpretation = _INTERPRETATION_GOAL.fullmatch(compact)
    if interpretation is not None:
        return (
            interpretation.group("source"),
            interpretation.group("target"),
            False,
        )
    return None


class BooleanCSPExplicitFiniteGadgetPlugin:
    """Planner-parameterized finite pp search over any reified finite Gamma."""

    name = "boolean-csp-explicit-finite-gadget"
    candidate_class = "finite-enumeration"
    authoritative_typed_compiler = False

    def supports(self, goal) -> FiniteSupportReceipt:
        supported_shape = _gadget_endpoints(goal.exact_type) is not None
        return FiniteSupportReceipt.create(
            plugin=self.name,
            goal=goal,
            supported=supported_shape,
            confidence=0.995 if supported_shape else 0.0,
            reason=(
                "source and target are finite by Gamma; symbols are reified with Fintype"
                if supported_shape
                else "goal is outside the generic Boolean-CSP gadget interface"
            ),
            witness_grammar=(
                "planner-selected variable/constraint bounds, arbitrary target symbols, "
                "projection/permutation/repetition/auxiliary variables, full truth table"
            ),
        )

    @staticmethod
    def _gadget_body(
        *,
        pointwise: bool,
        variable_bound: int,
        source_language: str,
        target_language: str,
        selected_templates: str,
    ) -> tuple[str, ...]:
        prefix: list[str] = ["classical"]
        if not pointwise:
            prefix.append("refine { gadgetOf := ?_ }")
        prefix.extend(
            (
                "intro symbol",
                "apply Classical.choice",
                "fin_cases symbol <;>",
                "  first",
                f"  | exact ⟨{_FINITE_GADGET}gadgetOfPlannedSearch _",
                "      [()] _",
                f"      {variable_bound} (by decide) (by decide)",
                f"      {selected_templates}",
                f"      (by simp [{source_language}, {target_language}] <;> decide)⟩",
                f"  | exact ⟨{_FINITE_GADGET}gadgetOfPlannedSearch _",
                "      [false, true] _",
                f"      {variable_bound} (by decide) (by decide)",
                f"      {selected_templates}",
                f"      (by simp [{source_language}, {target_language}] <;> decide)⟩",
                f"  | exact ⟨{_FINITE_GADGET}gadgetOfPlannedSearch _",
                "      (Finset.univ.toList) _",
                f"      {variable_bound} (by decide) (by decide)",
                f"      {selected_templates}",
                f"      (by simp [{source_language}, {target_language}] <;> decide)⟩",
            )
        )
        return tuple(prefix)

    def _build_candidate(
        self,
        goal,
        *,
        declaration_name: str,
        enumeration_limit: int,
        receipt: FiniteSupportReceipt,
        source_language: str,
        target_language: str,
        pointwise: bool,
        counterexamples: Sequence[Mapping[str, object]],
        round_index: int,
        variable_bound: int,
        constraint_bound: int,
        selected_templates: str,
        expanded_template_count: int,
        grammar_variant: str,
    ) -> FiniteCandidateWitness:
        counterexample_count = len(tuple(counterexamples))
        proof_lines = self._gadget_body(
            pointwise=pointwise,
            variable_bound=variable_bound,
            source_language=source_language,
            target_language=target_language,
            selected_templates=selected_templates,
        )
        rendered = "\n".join("  " + line if line else "" for line in proof_lines)
        implementation = (
            fixed_declaration_header(
                declaration=declaration_name, exact_type=goal.exact_type
            )
            + "\n"
            + rendered
        )
        seed_patterns = (
            {"name": "projection-and-repetition", "maximum_constraints": 3},
            {"name": "auxiliary-chain", "maximum_constraints": 4},
            {"name": "constant-parity-clause", "maximum_constraints": 5},
            {"name": "dual-cardinality-complement-pinning", "maximum_constraints": 5},
            {"name": "seven-atom-cardinality", "maximum_constraints": 7},
        )
        typed_plan = GadgetCapabilityPlan.create(
            source_relation_receipt={
                "exact_goal": goal.exact_type,
                "source_language": source_language,
                "symbol_reification": "Fintype/fin_cases",
                "relation_selected_after_source-symbol-case-split": True,
            },
            target_gamma_receipt={
                "symbol_enumeration": "Finset.univ.toList",
                "target_language": target_language,
                "finite_by_construction": True,
                "benchmark_identifier_used": False,
            },
            design_kind=(
                "finite-enumeration" if round_index == 0 else "cegis-finite-spec"
            ),
            variable_bound=variable_bound,
            constraint_bound=constraint_bound,
            witness_grammar={
                "target_symbol": "all reified symbols",
                "argument_mapping": (
                    "projection, permutation, repeated variables, auxiliary variables"
                ),
                "formula": "bounded conjunction",
            },
            output_schema={
                "mapping": "first source-arity variables",
                "injectivity": "FiniteGadget.firstOutputs_injective",
            },
            symmetry_breaking=(
                "fixed output prefix",
                "planner seed order before expanded grammar",
            ),
            seed_patterns=seed_patterns,
            selected_primitive_ids=(
                stable_sha256(_FINITE_GADGET + "gadgetOfPlannedSearch"),
                stable_sha256(_FINITE_GADGET + "plannedSpecs"),
            ),
            counterexample_policy={
                "retain_all": True,
                "replan_on_truth_table_counterexample": True,
                "round": round_index + 1,
                "observed_counterexample_count": counterexample_count,
                "bound_expanded": round_index > 0 or variable_bound > 6,
            },
            enumeration_order=(
                "seed patterns",
                "target symbols",
                "argument mappings",
                "complete truth-table check",
            ),
            fallback_designs=(
                {"design_kind": "cegis-finite-spec"},
                {"design_kind": "symbolic-formula"},
            ),
        )
        primitives = (
            _FINITE_GADGET + "gadgetOfPlannedSearch",
            _FINITE_GADGET + "plannedSpecs",
            "Finset.univ.toList",
        )
        capability_plan = CapabilityPlan.create(
            capability_kind=CapabilityKind.GADGET,
            goal_id=goal.goal_id,
            exact_goal=goal.exact_type,
            selected_route="planner-bounded-finite-enumeration",
            selected_design_id="design-" + typed_plan.plan_id,
            construction_basis_ids=typed_plan.selected_primitive_ids,
            proof_outline=(
                "reify arbitrary finite source/target symbols",
                "materialize planner-selected bounded grammar",
                "Lean-decide complete truth table",
                "lift Spec.Correct to Gadget",
            ),
            witness_schema=typed_plan.witness_grammar,
            residual_goal_dag=(
                {
                    "goal_id": "finite-spec-correct",
                    "exact_type": "BooleanCSPFiniteGadget.Spec.Correct generatedSpec",
                    "dependencies": (),
                },
            ),
            budget_allocation={
                "planner": 1,
                "enumeration": enumeration_limit,
                "counterexample_rounds": 8,
                "lean_checks": 1,
            },
            fallback_plans=typed_plan.fallback_designs,
            context_requirements=(
                "finite source symbol carrier",
                "finite target symbol carrier",
                "decidable relation truth tables",
            ),
        )
        brief = GeneratorBrief.create(
            plan=capability_plan,
            exact_declaration_name=declaration_name,
            exact_declaration_type=goal.exact_type,
            fixed_declaration_envelope={
                "header": fixed_declaration_header(
                    declaration=declaration_name, exact_type=goal.exact_type
                ),
                "model_may_edit_header": "false",
            },
            selected_design={
                "design_id": capability_plan.selected_design_id,
                "design_kind": typed_plan.design_kind,
                "typed_plan_id": typed_plan.plan_id,
                "grammar_variant": grammar_variant,
            },
            ordered_proof_hints=(
                {
                    "hint_id": typed_plan.plan_id,
                    "hint_kind": "construct-witness",
                    "primitive": _FINITE_GADGET + "gadgetOfPlannedSearch",
                },
            ),
            witness_contract=typed_plan.witness_grammar,
            allowed_identifier_manifest=primitives,
            prior_counterexamples=counterexamples,
        )
        generator_result = GeneratorResult.create(
            brief=brief,
            status=GeneratorStatus.PROPOSED,
            implementation_body="\n".join(proof_lines),
            planner_hints_followed=(typed_plan.plan_id,),
        )
        contribution = ContributionReceipt(
            capability_declaration=declaration_name,
            contribution_class=ContributionClass.DETERMINISTIC_GENERATED_CAPABILITY,
            capability_kind=CapabilityKind.GADGET,
            plan_id=capability_plan.plan_id,
            brief_id=brief.brief_id,
            generator_result_id=generator_result.result_id,
            primitive_candidates_used=typed_plan.selected_primitive_ids,
            planner_advice_ids=(typed_plan.plan_id,),
            generated_data_objects=("planner-selected-finite-spec",),
            deterministic_solver_steps=(
                "Fintype symbol enumeration",
                "bounded pp grammar enumeration",
                "complete truth-table decision",
                "Spec.toGadget materialization",
            ),
        )
        return FiniteCandidateWitness(
            witness_id=(
                "explicit-finite-"
                + receipt.receipt_hash.removeprefix("sha256:")[:16]
                + f"-round-{round_index + 1}-v{variable_bound}-c{constraint_bound}"
                + f"-{grammar_variant}"
            ),
            implementation=implementation,
            imports=(
                "ComplexityReduction.Agent.GenerativeReduction.Plugins."
                "BooleanCSPFiniteGadget",
            ),
            executable_status="complete-finite-truth-table-check-pending",
            check_receipt={
                "support_receipt": receipt.receipt_hash,
                "pointwise": pointwise,
                "target_symbol_enumeration": "Finset.univ.toList",
                "variable_bound": variable_bound,
                "constraint_bound": constraint_bound,
                "expanded_template_count": expanded_template_count,
                "grammar_variant": grammar_variant,
                "cegis_round": round_index + 1,
                "bound_expanded": round_index > 0 or variable_bound > 6,
                "typed_plan_id": typed_plan.plan_id,
                "counterexample_count": counterexample_count,
                "executable_semantics": "Lean-decide-complete-truth-table",
                "proof_authority": "pending-independent-lean-verification",
                "counterexample_probe_schema": "finite-truth-table-counterexample-v1",
                "counterexample_probe_term": (
                    f"{_FINITE_GADGET}firstPlannedCounterexample? "
                    f"{source_language} {target_language} {variable_bound} "
                    "(by decide) "
                    "(by intro symbol; fin_cases symbol <;> decide) "
                    f"{selected_templates}"
                ),
            },
            capability_plan=capability_plan,
            generator_brief=brief,
            generator_result=generator_result,
            contribution_receipt=contribution,
            typed_plan_receipt=asdict(typed_plan),
        )

    def enumerate(
        self,
        goal,
        *,
        declaration_name: str,
        limit: int,
        counterexamples: Sequence[Mapping[str, object]] = (),
    ) -> Sequence[FiniteCandidateWitness]:
        if limit <= 0:
            return ()
        receipt = self.supports(goal)
        if not receipt.supported:
            return ()
        endpoints = _gadget_endpoints(goal.exact_type)
        if endpoints is None:
            return ()
        source_language, target_language, pointwise = endpoints
        counterexample_count = len(tuple(counterexamples))
        round_index = counterexample_count
        variable_bound = min(12, 6 + 2 * counterexample_count)
        constraint_bound = min(12, 7 + counterexample_count)
        selected_templates, expanded_template_count = _selected_template_expression(
            variable_bound=variable_bound,
            constraint_bound=constraint_bound,
            round_index=round_index,
        )
        specifications: list[tuple[str, int, int, str, int]] = [
            (
                "planner-base-grammar",
                variable_bound,
                constraint_bound,
                selected_templates,
                expanded_template_count,
            )
        ]
        if round_index == 0:
            for arity, template in _DUAL_CARDINALITY_SEEDS:
                if len(specifications) >= limit:
                    break
                specifications.append(
                    (
                        f"dual-cardinality-arity-{arity}",
                        8,
                        5,
                        _lean_template_list((template,)),
                        1,
                    )
                )
        return tuple(
            self._build_candidate(
                goal,
                declaration_name=declaration_name,
                enumeration_limit=limit,
                receipt=receipt,
                source_language=source_language,
                target_language=target_language,
                pointwise=pointwise,
                counterexamples=counterexamples,
                round_index=round_index,
                variable_bound=candidate_variable_bound,
                constraint_bound=candidate_constraint_bound,
                selected_templates=candidate_templates,
                expanded_template_count=candidate_expanded_count,
                grammar_variant=grammar_variant,
            )
            for (
                grammar_variant,
                candidate_variable_bound,
                candidate_constraint_bound,
                candidate_templates,
                candidate_expanded_count,
            ) in specifications[:limit]
        )


class BooleanCSPDirectTMCompilerPlugin:
    """Materialize a target-specific direct-TM program DAG."""

    name = "boolean-csp-direct-tm-compiler"
    candidate_class = "typed-compiler"
    authoritative_typed_compiler = True

    def supports(self, goal) -> FiniteSupportReceipt:
        supported = is_direct_tm_interpret_goal(goal)
        return FiniteSupportReceipt.create(
            plugin=self.name,
            goal=goal,
            supported=supported,
            confidence=1.0 if supported else 0.0,
            reason=(
                "exact goal is a parsed TMPolyTimeMap over a LanguageInterpretation"
                if supported
                else "goal is not a direct-TM interpretation capability"
            ),
            witness_grammar="typed program DAG + primitive registry + endpoint equality",
        )

    def enumerate(
        self,
        goal,
        *,
        declaration_name: str,
        limit: int,
        counterexamples: Sequence[Mapping[str, object]] = (),
    ) -> Sequence[FiniteCandidateWitness]:
        del counterexamples
        if limit <= 0:
            return ()
        candidate = compile_direct_tm_candidate(
            goal, declaration_name=declaration_name
        )
        return (candidate,) if candidate is not None else ()


class BooleanCSPSemanticCompilerPlugin:
    """Materialize forward/reverse helpers and assemble the semantic iff."""

    name = "boolean-csp-semantic-compiler"
    candidate_class = "typed-compiler"
    authoritative_typed_compiler = True

    def supports(self, goal) -> FiniteSupportReceipt:
        supported = is_semantic_interpret_goal(goal)
        return FiniteSupportReceipt.create(
            plugin=self.name,
            goal=goal,
            supported=supported,
            confidence=1.0 if supported else 0.0,
            reason=(
                "exact goal is a parsed satisfiability iff for a LanguageInterpretation"
                if supported
                else "goal is not a semantic interpretation capability"
            ),
            witness_grammar="reverse helper + forward witness/invariants + final Iff assembler",
        )

    def enumerate(
        self,
        goal,
        *,
        declaration_name: str,
        limit: int,
        counterexamples: Sequence[Mapping[str, object]] = (),
    ) -> Sequence[FiniteCandidateWitness]:
        del counterexamples
        if limit <= 0:
            return ()
        candidate = compile_semantic_candidate(
            goal, declaration_name=declaration_name
        )
        return (candidate,) if candidate is not None else ()


class BooleanCSPCanonicalDatabaseFinitePlugin:
    """Materialize canonical finite-database gadgets with Lean certificates.

    The adapter recognizes only the stable public Boolean-CSP interface.  It
    never receives a benchmark ID or an oracle row; the concrete language is
    inferred by Lean from the exact goal and all finite class checks are proved
    through the public reflection theorems.
    """

    name = "boolean-csp-canonical-database"
    candidate_class = "finite-enumeration"
    authoritative_typed_compiler = False

    @staticmethod
    def _core(goal_text: str) -> str | None:
        if _ONE_IN_THREE in goal_text:
            return "one-in-three"
        if _NAE3 in goal_text:
            return "nae3"
        return None

    def supports(self, goal) -> FiniteSupportReceipt:
        text = _compact(goal.exact_type)
        core = self._core(text)
        supported_shape = (
            _INTERPRETATION in text
            or (_GADGET in text and ".Symbol" in text and "→" in text)
        )
        supported = core is not None and supported_shape
        return FiniteSupportReceipt.create(
            plugin=self.name,
            goal=goal,
            supported=supported,
            confidence=0.98 if supported else 0.0,
            reason=(
                "exact goal is a hard-core language interpretation or its pointwise gadget"
                if supported
                else "goal is outside the canonical Boolean-CSP finite-gadget interface"
            ),
            witness_grammar=(
                "canonical-database formula + coordinate outputs + reflected finite class checks"
            ),
        )

    @staticmethod
    def _gadget_body(*, core: str, pointwise: bool) -> list[str]:
        prefix: list[str] = []
        if not pointwise:
            prefix.extend(("  refine { gadgetOf := ?_ }", "  intro symbol"))
        else:
            prefix.append("  intro symbol")
        prefix.extend(("  cases symbol", "  apply " + _HARDNESS + "CanonicalDatabase.gadget"))
        reflection = "ComplexityReduction.Agent.Reduction.Reflection."
        canonical = _HARDNESS + "CanonicalHardCores."
        if core == "one-in-three":
            prefix.extend(
                (
                    "  · exact " + canonical + "exactlyOne_separates",
                    "  · apply " + canonical + "exactlyOne_closed_of_notSchaeferTractable",
                    "    · exact " + reflection
                    + "gammaRelationsNonempty_of_decide_eq_true _ (by decide)",
                    "    · exact " + reflection
                    + "gammaNotSchaeferTractable_of_decide_eq_false _ (by decide)",
                    "    · exact " + reflection
                    + "gammaNotPreservesComplement_of_decide_eq_false _ (by decide)",
                )
            )
        else:
            prefix.extend(
                (
                    "  · exact " + canonical + "nae_separates",
                    "  · apply " + canonical + "nae_closed_of_notSchaeferTractable",
                    "    · exact " + reflection
                    + "gammaRelationsNonempty_of_decide_eq_true _ (by decide)",
                    "    · exact " + reflection
                    + "gammaNotSchaeferTractable_of_decide_eq_false _ (by decide)",
                    "    · exact " + reflection
                    + "gammaPreservesComplement_of_decide_eq_true _ (by decide)",
                )
            )
        return prefix

    def enumerate(
        self,
        goal,
        *,
        declaration_name: str,
        limit: int,
        counterexamples: Sequence[Mapping[str, object]] = (),
    ) -> Sequence[FiniteCandidateWitness]:
        if limit <= 0:
            return ()
        receipt = self.supports(goal)
        if not receipt.supported:
            return ()
        text = _compact(goal.exact_type)
        core = self._core(text)
        if core is None:
            return ()
        pointwise = _INTERPRETATION not in text
        implementation = "\n".join(
            (
                f"noncomputable def {declaration_name} : {goal.exact_type.strip()} := by",
                *self._gadget_body(core=core, pointwise=pointwise),
            )
        )
        witness_id = "finite-" + receipt.receipt_hash.removeprefix("sha256:")[:20]
        return (
            FiniteCandidateWitness(
                witness_id=witness_id,
                implementation=implementation,
                imports=(
                    "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores",
                    "ComplexityReduction.Agent.Reduction.Reflection",
                ),
                executable_status="accepted-by-typed-finite-interface",
                check_receipt={
                    "support_receipt": receipt.receipt_hash,
                    "core": core,
                    "pointwise": pointwise,
                    "counterexample_count": len(tuple(counterexamples)),
                    "proof_authority": "pending-independent-lean-verification",
                },
            ),
        )


def _register(registry: PremiseSolverRegistry) -> None:
    registry.register(BooleanCSPFiniteReflectionSolver())


PLUGIN = Plugin(
    name="boolean_csp",
    register=_register,
    public_capabilities=(
        "finite relation nonemptiness reflection",
        "finite tractability-side reflection",
        "finite complement-closure reflection",
        "proof-producing explicit finite pp-gadget search",
        "proof-producing canonical finite-database gadget synthesis",
        "typed direct-TM program-DAG compilation",
        "semantic forward/reverse helper-DAG compilation",
    ),
    lean_imports=(
        "ComplexityReduction.Agent.GenerativeReduction.Plugins.BooleanCSPReflection",
        # The wrapper exports the declarations for authored source, while the
        # typed index filters by declaration-owning module.  Include both so
        # exact open goals can retrieve and recursively apply the reflection
        # theorems instead of falling through to model synthesis.
        "ComplexityReduction.Agent.Reduction.Reflection",
        "ComplexityReduction.Agent.GenerativeReduction.Plugins."
        "BooleanCSPFiniteGadget",
        "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores",
    ),
    finite_synthesis_plugins=(
        BooleanCSPDirectTMCompilerPlugin(),
        BooleanCSPSemanticCompilerPlugin(),
        BooleanCSPExplicitFiniteGadgetPlugin(),
        BooleanCSPCanonicalDatabaseFinitePlugin(),
    ),
)


__all__ = [
    "BooleanCSPCanonicalDatabaseFinitePlugin",
    "BooleanCSPDirectTMCompilerPlugin",
    "BooleanCSPExplicitFiniteGadgetPlugin",
    "BooleanCSPFiniteReflectionSolver",
    "BooleanCSPSemanticCompilerPlugin",
    "PLUGIN",
]
