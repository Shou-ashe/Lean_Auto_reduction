"""Optional finite-reflection capabilities for Boolean CSP premises."""

from __future__ import annotations

from typing import Mapping, Sequence

from ..finite_synthesis import (
    FiniteCandidateWitness,
    FiniteSupportReceipt,
)
from ..models import PremiseKind, TheoremPremise
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


def _compact(value: str) -> str:
    return " ".join(value.split())


class BooleanCSPCanonicalDatabaseFinitePlugin:
    """Materialize canonical finite-database gadgets with Lean certificates.

    The adapter recognizes only the stable public Boolean-CSP interface.  It
    never receives a benchmark ID or an oracle row; the concrete language is
    inferred by Lean from the exact goal and all finite class checks are proved
    through the public reflection theorems.
    """

    name = "boolean-csp-canonical-database"

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
        "proof-producing canonical finite-database gadget synthesis",
    ),
    lean_imports=(
        "ComplexityReduction.Agent.GenerativeReduction.Plugins.BooleanCSPReflection",
        # The wrapper exports the declarations for authored source, while the
        # typed index filters by declaration-owning module.  Include both so
        # exact open goals can retrieve and recursively apply the reflection
        # theorems instead of falling through to model synthesis.
        "ComplexityReduction.Agent.Reduction.Reflection",
        "ComplexityReduction.Domain.BooleanCSP.Hardness.CanonicalHardCores",
    ),
    finite_synthesis_plugins=(BooleanCSPCanonicalDatabaseFinitePlugin(),),
)


__all__ = [
    "BooleanCSPCanonicalDatabaseFinitePlugin",
    "BooleanCSPFiniteReflectionSolver",
    "PLUGIN",
]
