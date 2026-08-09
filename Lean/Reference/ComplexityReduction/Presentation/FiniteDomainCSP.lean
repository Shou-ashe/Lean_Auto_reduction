/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.CSP.FiniteDomain.Basic
import ComplexityReduction.Encoding.PresentedProblem

/-!
Canonical explicit presentations for fixed finite-domain CSP languages.

The existing `FiniteDomain.cspDecisionProblem` uses the raw compatibility
encoding, and the older IR's numeric source code records only support and size
facts.  Neither supplies faithful encoding evidence.  This leaf consequently
owns a concrete faithful formula codec: a finite relation symbol is encoded by
its fixed `Fintype` index, and its dependent variable scope is encoded as an
ordered list of unary natural numbers.

The resulting codec is intentionally user-locked.  The finite enumeration of
relation symbols and the dependent formula-to-code translation are domain
specific; they are not a closed constructor of `StructuralRepresentationOrigin`.
This leaf therefore exports no structural certificate or automatic-presentation
admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace FiniteDomainCSP

open Encoding
open ComplexityReduction.CSP.FiniteDomain

noncomputable section

/-- The fixed numeric identity of one relation symbol in a finite CSP language. -/
def relationCode {D : Type} (Γ : Language D) (symbol : Γ.Symbol) : Nat :=
  (Fintype.equivFin Γ.Symbol symbol).val

/-- The relation-symbol code is faithful for exactly the language's finite symbol type. -/
theorem relationCode_injective {D : Type} (Γ : Language D) :
    Function.Injective (relationCode Γ) := by
  intro left right equality
  exact Fintype.equivFin Γ.Symbol |>.injective (Fin.ext equality)

/-- The numeric payload of one dependent finite-domain CSP constraint. -/
def constraintCode {D : Type} {Γ : Language D} (constraint : Constraint Γ) :
    Nat × List Nat :=
  (relationCode Γ constraint.symbol, constraint.varsList)

/-- The ordered numeric payload of one finite-domain CSP formula. -/
def formulaCode {D : Type} (Γ : Language D) (formula : Formula Γ) :
    List (Nat × List Nat) :=
  formula.map constraintCode

private theorem list_ofFn_injective {α : Type} {n : Nat} :
    Function.Injective (List.ofFn : (Fin n → α) → List α) := by
  intro left right equality
  funext index
  have entryEquality := congrArg (fun values : List α => values[index.val]?) equality
  simpa [List.getElem?_ofFn, index.isLt] using entryEquality

/-- The numeric dependent-constraint payload is faithful. -/
theorem constraintCode_injective {D : Type} (Γ : Language D) :
    Function.Injective (@constraintCode D Γ) := by
  rintro ⟨leftSymbol, leftVars⟩ ⟨rightSymbol, rightVars⟩ equality
  have symbolEquality : leftSymbol = rightSymbol :=
    relationCode_injective Γ (congrArg Prod.fst equality)
  cases symbolEquality
  have varsEquality : leftVars = rightVars :=
    list_ofFn_injective (congrArg Prod.snd equality)
  cases varsEquality
  rfl

/-- The numeric finite-domain CSP formula payload is faithful. -/
theorem formulaCode_injective {D : Type} (Γ : Language D) :
    Function.Injective (formulaCode Γ) := by
  exact List.map_injective_iff.mpr (constraintCode_injective Γ)

/-- Standard code layout for one finite-domain CSP constraint. -/
abbrev constraintCodeEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.EncodedType.prod ComplexityReduction.EncodedType.nat
    (ComplexityReduction.EncodedType.list ComplexityReduction.EncodedType.nat)

/-- Standard code layout for the ordered list of finite-domain CSP constraints. -/
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
The faithful finite-alphabet encoding of formulas over one fixed finite-domain
CSP language.  Its carrier is the original CSP syntax, not an erased IR view.
-/
def encodedType {D : Type} (Γ : Language D) : ComplexityReduction.EncodedType where
  Carrier := Formula Γ
  Symbol := formulaCodeEncodedType.Symbol
  finite_symbol := formulaCodeEncodedType.finite_symbol
  encode := fun formula => formulaCodeEncodedType.encode (formulaCode Γ formula)

/-- Faithfulness of the concrete finite-domain CSP formula encoding. -/
theorem encodedType_encode_injective {D : Type} (Γ : Language D) :
    Function.Injective (encodedType Γ).encode := by
  intro left right equality
  apply formulaCode_injective Γ
  exact formulaCodeEncodedType_encode_injective equality

/-- The complete identity of the finite-domain CSP formula-code layout. -/
def representationShape : CodecShape :=
  .list (.prod .unaryNat (.list .unaryNat))

/--
The exact lawful V2 presentation for formulas over the fixed language `Γ`.

This is an explicit custom presentation.  In particular, no structural
certificate is exported for it, despite the faithful standard code payload.
-/
def lawfulRepresentation {D : Type} (Γ : Language D) : LawfulEncodedType where
  encodedType := encodedType Γ
  representation := representationShape.identity
  faithful := ⟨encodedType_encode_injective Γ⟩

@[simp]
theorem lawfulRepresentation_encodedType {D : Type} (Γ : Language D) :
    (lawfulRepresentation Γ).encodedType = encodedType Γ :=
  rfl

@[simp]
theorem lawfulRepresentation_representation {D : Type} (Γ : Language D) :
    (lawfulRepresentation Γ).representation = representationShape.identity :=
  rfl

/-- The presentation carrier remains the exact fixed-language CSP formula syntax. -/
theorem lawfulRepresentation_carrier_eq_formula {D : Type} (Γ : Language D) :
    (lawfulRepresentation Γ).Carrier = Formula Γ :=
  rfl

/-- The presentation exposes precisely the V2 finite-domain CSP formula encoder. -/
@[simp]
theorem lawfulRepresentation_encode {D : Type} (Γ : Language D)
    (formula : (lawfulRepresentation Γ).Carrier) :
    (lawfulRepresentation Γ).encode formula = (encodedType Γ).encode formula :=
  rfl

/-- The semantic finite-domain CSP problem before attaching its faithful presentation. -/
def semanticProblem {D : Type} (Γ : Language D) : ComplexityReduction.DecisionProblem where
  Instance := Formula Γ
  isYes := Formula.Satisfiable

@[simp]
theorem semanticProblem_instance {D : Type} (Γ : Language D) :
    (semanticProblem Γ).Instance = Formula Γ :=
  rfl

@[simp]
theorem semanticProblem_isYes {D : Type} (Γ : Language D) (formula : Formula Γ) :
    (semanticProblem Γ).isYes formula ↔ Formula.Satisfiable formula :=
  Iff.rfl

/-- The semantic predicate at the exact custom finite-domain CSP presentation. -/
def problemAt {D : Type} (Γ : Language D) : ProblemAt (lawfulRepresentation Γ) where
  isYes := Formula.Satisfiable

/-- The user-locked presented finite-domain CSP problem for one fixed language. -/
def presentedProblem {D : Type} (Γ : Language D) : PresentedProblem :=
  PresentedProblem.ofProblemAt (lawfulRepresentation Γ) (problemAt Γ)

@[simp]
theorem presentedProblem_representation {D : Type} (Γ : Language D) :
    (presentedProblem Γ).representation = lawfulRepresentation Γ :=
  rfl

@[simp]
theorem presentedProblem_backendEndpoint_instance {D : Type} (Γ : Language D) :
    (presentedProblem Γ).backendEndpoint.Instance = encodedType Γ :=
  rfl

@[simp]
theorem presentedProblem_representationIdentity {D : Type} (Γ : Language D) :
    (presentedProblem Γ).representationIdentity = representationShape.identity :=
  rfl

@[simp]
theorem problemAt_isYes {D : Type} (Γ : Language D)
    (formula : (lawfulRepresentation Γ).Carrier) :
    (problemAt Γ).isYes formula ↔ Formula.Satisfiable formula :=
  Iff.rfl

/-- The V2 endpoint has exactly the legacy library's fixed-language CSP semantics. -/
@[simp]
theorem presentedProblem_accepts {D : Type} (Γ : Language D)
    (formula : (presentedProblem Γ).Instance) :
    (presentedProblem Γ).accepts formula ↔ Formula.Satisfiable formula :=
  Iff.rfl

/-- The typed endpoint's semantic predicate agrees exactly with the CR CSP decision problem. -/
@[simp]
theorem presentedProblem_accepts_iff_cspDecisionProblem {D : Type} (Γ : Language D)
    (formula : (presentedProblem Γ).Instance) :
    (presentedProblem Γ).accepts formula ↔
      (ComplexityReduction.CSP.FiniteDomain.cspDecisionProblem Γ).isYes formula :=
  Iff.rfl

end

end FiniteDomainCSP
end Presentation
end ComplexityReduction
