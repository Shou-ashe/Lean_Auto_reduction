/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.CSP.Hardness.ThreeSATLike
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem

/-!
The canonical V2 presentation of the fixed Boolean CSP language that mirrors
bundled 3SAT clauses.

The general finite-table presentation indexes relation symbols through an
abstract `Fintype.equivFin`.  This family instead owns the audited concrete
eight-way polarity code used by its reusable direct-TM gadget.  The carrier
and predicate remain CR's `Formula threeSATLikeLanguage`; only the explicit,
encoder-bound representation is selected here.
-/

namespace ComplexityReduction
namespace Presentation
namespace ThreeSATLike

open Encoding
open ComplexityReduction.CSP
open ComplexityReduction.CSP.Examples

noncomputable section

/-- The fixed Boolean CSP language used as the Clause/CNF-to-CSP hub. -/
abbrev language : BoolLanguage := threeSATLikeLanguage

/-- The executable relation code follows the fixed polarity constructor order. -/
def relationCode : ThreeSATLikeSymbol → Nat
  | .posPosPos => 0
  | .negPosPos => 1
  | .posNegPos => 2
  | .posPosNeg => 4
  | .negNegPos => 3
  | .negPosNeg => 5
  | .posNegNeg => 6
  | .negNegNeg => 7

/-- The concrete polarity code is faithful for this one closed language. -/
theorem relationCode_injective : Function.Injective relationCode := by
  intro left right equality
  cases left <;> cases right <;> simp [relationCode] at equality ⊢

/-- The numeric payload of one fixed-language CSP constraint. -/
def constraintCode (constraint : Constraint language) : Nat × List Nat :=
  (relationCode constraint.symbol, constraint.varsList)

/-- The numeric payload of an ordered fixed-language CSP formula. -/
def formulaCode (formula : Formula language) : List (Nat × List Nat) :=
  formula.map constraintCode

private theorem list_ofFn_injective {α : Type} {n : Nat} :
    Function.Injective (List.ofFn : (Fin n → α) → List α) := by
  intro left right equality
  funext index
  have entryEquality := congrArg (fun values : List α => values[index.val]?) equality
  simpa [List.getElem?_ofFn, index.isLt] using entryEquality

/-- Constraint coding is faithful at the selected fixed relation language. -/
theorem constraintCode_injective : Function.Injective constraintCode := by
  rintro ⟨leftSymbol, leftVars⟩ ⟨rightSymbol, rightVars⟩ equality
  have symbolEquality : leftSymbol = rightSymbol :=
    relationCode_injective (congrArg Prod.fst equality)
  cases symbolEquality
  have varsEquality : leftVars = rightVars :=
    list_ofFn_injective (congrArg Prod.snd equality)
  cases varsEquality
  rfl

/-- Formula coding is faithful at the selected fixed relation language. -/
theorem formulaCode_injective : Function.Injective formulaCode := by
  exact List.map_injective_iff.mpr constraintCode_injective

/-- Standard direct-TM payload layout for one coded constraint. -/
abbrev constraintCodeEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.EncodedType.prod ComplexityReduction.EncodedType.nat
    (ComplexityReduction.EncodedType.list ComplexityReduction.EncodedType.nat)

/-- Standard direct-TM payload layout for an ordered coded formula. -/
abbrev formulaCodeEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.EncodedType.list constraintCodeEncodedType

private theorem formulaCodeEncodedType_encode_injective :
    Function.Injective formulaCodeEncodedType.encode :=
  ComplexityReduction.EncodedType.list_encode_injective
    (ComplexityReduction.EncodedType.prod_encode_injective
      ComplexityReduction.EncodedType.nat_encode_injective
      (ComplexityReduction.EncodedType.list_encode_injective
        ComplexityReduction.EncodedType.nat_encode_injective))

/--
The exact lawful encoder for the fixed 3SAT-like CSP formula carrier.
The explicit relation code is part of this representation's identity; it is
not inferred from carrier equality or a bare finite enumeration.
-/
def encodedType : ComplexityReduction.EncodedType where
  Carrier := Formula language
  Symbol := formulaCodeEncodedType.Symbol
  finite_symbol := formulaCodeEncodedType.finite_symbol
  encode := fun formula => formulaCodeEncodedType.encode (formulaCode formula)

/-- The selected executable formula encoding is faithful. -/
theorem encodedType_encode_injective : Function.Injective encodedType.encode := by
  intro left right equality
  apply formulaCode_injective
  exact formulaCodeEncodedType_encode_injective equality

/-- The closed structural shape of the explicit relation-code formula layout. -/
def representationShape : CodecShape :=
  .list (.prod .unaryNat (.list .unaryNat))

/-- The canonical lawful representation for the 3SAT-like CSP hub. -/
def lawfulRepresentation : LawfulEncodedType where
  encodedType := encodedType
  representation := representationShape.identity
  faithful := ⟨encodedType_encode_injective⟩

@[simp] theorem lawfulRepresentation_encodedType :
    lawfulRepresentation.encodedType = encodedType :=
  rfl

@[simp] theorem lawfulRepresentation_representation :
    lawfulRepresentation.representation = representationShape.identity :=
  rfl

/-- The represented carrier is exactly CR's fixed 3SAT-like CSP syntax. -/
theorem lawfulRepresentation_carrier_eq_formula :
    lawfulRepresentation.Carrier = Formula language :=
  rfl

/-- The semantic endpoint predicate is fixed-language CSP satisfiability. -/
def problemAt : ProblemAt lawfulRepresentation where
  isYes := Formula.Satisfiable

/-- The canonical presented CSP hub for Clause/CNF shared gadgets. -/
@[complexity_reduction_ir_typed_problem]
def presentedProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt lawfulRepresentation problemAt

@[simp] theorem presentedProblem_representation :
    presentedProblem.representation = lawfulRepresentation :=
  rfl

@[simp] theorem presentedProblem_representationIdentity :
    presentedProblem.representationIdentity = representationShape.identity :=
  rfl

@[simp] theorem presentedProblem_accepts (formula : presentedProblem.Instance) :
    presentedProblem.accepts formula ↔ Formula.Satisfiable formula :=
  Iff.rfl

end
end ThreeSATLike
end Presentation
end ComplexityReduction
