/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CNFTo3SAT

/-!
Faithful finite-alphabet encodings for project-local SAT syntax.

This is the SAT-local copy of the structured `Literal`/`Clause`/`CNF` encoding
needed by the Cook-Levin direct-TM generator route.  It deliberately lives
outside the Karp21 namespace so SAT/Cook-Levin files do not import Karp21
modules.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Structured syntax encodings -/

/-- Product encoding of a SAT literal as `(variable, negation)`. -/
def literalTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.bool

/-- Faithful finite-alphabet encoding for SAT literals. -/
def literalStructuredEncodedType : EncodedType where
  Carrier := Literal
  Symbol := literalTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun l => literalTupleStructuredEncodedType.encode (l.var, l.neg)

instance literalStructuredSymbolInhabited : Inhabited literalStructuredEncodedType.Symbol :=
  ⟨none⟩

/-- Clauses are delimiter-separated lists of structured literals. -/
def clauseStructuredEncodedType : EncodedType :=
  EncodedType.list literalStructuredEncodedType

/-- CNFs are delimiter-separated lists of structured clauses. -/
def cnfStructuredEncodedType : EncodedType :=
  EncodedType.list clauseStructuredEncodedType

/--
Bundled 3CNFs encoded by their underlying structured CNF; the `isThree` proof is
proof-irrelevant and carries no symbols.
-/
def threeCNFStructuredEncodedType : EncodedType where
  Carrier := ThreeCNF
  Symbol := cnfStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun φ => cnfStructuredEncodedType.encode φ.clauses

theorem literalStructuredEncodedType_encode_injective :
    Function.Injective literalStructuredEncodedType.encode := by
  intro l m h
  change
    literalTupleStructuredEncodedType.encode (l.var, l.neg) =
      literalTupleStructuredEncodedType.encode (m.var, m.neg) at h
  have hTuple :
      (l.var, l.neg) = (m.var, m.neg) :=
    (EncodedType.prod_encode_injective
      EncodedType.nat_encode_injective EncodedType.bool_encode_injective) h
  cases l with
  | mk var neg =>
      cases m with
      | mk var' neg' =>
          cases hTuple
          rfl

theorem clauseStructuredEncodedType_encode_injective :
    Function.Injective clauseStructuredEncodedType.encode :=
  EncodedType.list_encode_injective literalStructuredEncodedType_encode_injective

theorem cnfStructuredEncodedType_encode_injective :
    Function.Injective cnfStructuredEncodedType.encode :=
  EncodedType.list_encode_injective clauseStructuredEncodedType_encode_injective

theorem threeCNFStructuredEncodedType_encode_injective :
    Function.Injective threeCNFStructuredEncodedType.encode := by
  intro φ ψ h
  cases φ with
  | mk clauses hThree =>
      cases ψ with
      | mk clauses' hThree' =>
          change
            cnfStructuredEncodedType.encode clauses =
              cnfStructuredEncodedType.encode clauses' at h
          have hClauses : clauses = clauses' :=
            cnfStructuredEncodedType_encode_injective h
          subst hClauses
          have hProof : hThree = hThree' := Subsingleton.elim _ _
          cases hProof
          rfl

/-! ### Basic direct-TM syntax constructors -/

/-- Rebuild a SAT literal from its tuple encoding carrier. -/
def literalTupleToLiteral (p : Nat × Bool) : Literal :=
  { var := p.1, neg := p.2 }

/-- Tuple-to-literal conversion preserves the structured literal encoding. -/
noncomputable def literalTupleToLiteralTMBackedMap :
    TMBackedCostedMap
      literalTupleStructuredEncodedType literalStructuredEncodedType literalTupleToLiteral :=
  TMBackedCostedMap.ofEncodingEquiv
    literalTupleStructuredEncodedType literalStructuredEncodedType literalTupleToLiteral
    (Equiv.refl _) (by
      intro p
      cases p with
      | mk var neg =>
          change
            literalTupleStructuredEncodedType.encode (var, neg) =
              List.map id (literalTupleStructuredEncodedType.encode (var, neg))
          rw [List.map_id])

/-- Tuple view of a structured SAT literal. -/
def literalToTuple (l : Literal) : literalTupleStructuredEncodedType.Carrier :=
  (l.var, l.neg)

/-- Literal-to-tuple conversion preserves the structured literal encoding. -/
noncomputable def literalToTupleTMBackedMap :
    TMBackedCostedMap
      literalStructuredEncodedType literalTupleStructuredEncodedType literalToTuple :=
  TMBackedCostedMap.ofEncodingEquiv
    literalStructuredEncodedType literalTupleStructuredEncodedType literalToTuple
    (Equiv.refl _) (by
      intro l
      change literalTupleStructuredEncodedType.encode (l.var, l.neg) =
        List.map id (literalTupleStructuredEncodedType.encode (l.var, l.neg))
      simp)

/-- The variable projection of a structured literal is direct TM polynomial-time. -/
theorem literal_var_tm_polytime :
    TMPolyTimeMap literalStructuredEncodedType EncodedType.nat Literal.var := by
  have hTuple := literalToTupleTMBackedMap.tm_polytime
  have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.bool
  have hComp := TMPolyTimeMap.comp hFst hTuple
  simpa [Function.comp, literalToTuple] using hComp

/-- The negation-bit projection of a structured literal is direct TM polynomial-time. -/
theorem literal_neg_tm_polytime :
    TMPolyTimeMap literalStructuredEncodedType EncodedType.bool Literal.neg := by
  have hTuple := literalToTupleTMBackedMap.tm_polytime
  have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
  have hComp := TMPolyTimeMap.comp hSnd hTuple
  simpa [Function.comp, literalToTuple] using hComp

/-- Positive literal construction is direct TM-backed. -/
noncomputable def literalPositiveTMBackedMap :
    TMBackedCostedMap EncodedType.nat literalStructuredEncodedType Literal.positive where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := EncodedType.nat) (Y := literalStructuredEncodedType)
      (LinearSizeBound.intro_with 1 3 (by
        intro n
        simp [literalStructuredEncodedType, literalTupleStructuredEncodedType,
          Literal.positive, EncodedType.inputSize, EncodedType.prod,
          EncodedType.nat, EncodedType.bool]))
  tm_polytime := by
    have hTuple :
        TMPolyTimeMap EncodedType.nat literalTupleStructuredEncodedType
          (fun n : Nat => (n, false)) :=
      TMPolyTimeMap.prod_id_const EncodedType.nat EncodedType.bool false
    have hLiteral :
        TMPolyTimeMap literalTupleStructuredEncodedType literalStructuredEncodedType
          literalTupleToLiteral :=
      literalTupleToLiteralTMBackedMap.tm_polytime
    have hComp := TMPolyTimeMap.comp hLiteral hTuple
    simpa [Function.comp, literalTupleToLiteral, Literal.positive] using hComp

/-- Negative literal construction is direct TM-backed. -/
noncomputable def literalNegativeTMBackedMap :
    TMBackedCostedMap EncodedType.nat literalStructuredEncodedType Literal.negative where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := EncodedType.nat) (Y := literalStructuredEncodedType)
      (LinearSizeBound.intro_with 1 3 (by
        intro n
        simp [literalStructuredEncodedType, literalTupleStructuredEncodedType,
          Literal.negative, EncodedType.inputSize, EncodedType.prod,
          EncodedType.nat, EncodedType.bool]))
  tm_polytime := by
    have hTuple :
        TMPolyTimeMap EncodedType.nat literalTupleStructuredEncodedType
          (fun n : Nat => (n, true)) :=
      TMPolyTimeMap.prod_id_const EncodedType.nat EncodedType.bool true
    have hLiteral :
        TMPolyTimeMap literalTupleStructuredEncodedType literalStructuredEncodedType
          literalTupleToLiteral :=
      literalTupleToLiteralTMBackedMap.tm_polytime
    have hComp := TMPolyTimeMap.comp hLiteral hTuple
    simpa [Function.comp, literalTupleToLiteral, Literal.negative] using hComp

/-- Toggle the Boolean component of a product-encoded literal symbol. -/
def toggleRightBoolSymbol : Option (Bool ⊕ Bool) → Option (Bool ⊕ Bool)
  | some (Sum.inr b) => some (Sum.inr (!b))
  | s => s

theorem toggleRightBoolSymbol_involutive :
    Function.Involutive toggleRightBoolSymbol := by
  intro s
  cases s with
  | none => rfl
  | some side =>
      cases side with
      | inl b => rfl
      | inr b =>
          cases b <;> rfl

/-- The Boolean-component toggle is its own inverse on literal symbols. -/
def toggleRightBoolSymbolEquiv :
    Option (Bool ⊕ Bool) ≃ Option (Bool ⊕ Bool) where
  toFun := toggleRightBoolSymbol
  invFun := toggleRightBoolSymbol
  left_inv := toggleRightBoolSymbol_involutive
  right_inv := toggleRightBoolSymbol_involutive

/-- Symbol equivalence implementing literal negation under the structured encoding. -/
abbrev literalNegateSymbolEquiv :
    literalStructuredEncodedType.Symbol ≃ literalStructuredEncodedType.Symbol :=
  toggleRightBoolSymbolEquiv

theorem literalStructured_encode_negate (l : Literal) :
    literalStructuredEncodedType.encode (Clause.negate l) =
      (literalStructuredEncodedType.encode l).map literalNegateSymbolEquiv := by
  change
    literalStructuredEncodedType.encode (Clause.negate l) =
      (literalStructuredEncodedType.encode l).map toggleRightBoolSymbol
  cases l with
  | mk var neg =>
      cases neg <;>
        simp [literalStructuredEncodedType, literalTupleStructuredEncodedType,
          Clause.negate, EncodedType.prod, EncodedType.nat, EncodedType.bool,
          toggleRightBoolSymbol]

/-- Literal negation is a direct TM-backed map under the structured encoding. -/
noncomputable def literalNegateTMBackedMap :
    TMBackedCostedMap
      literalStructuredEncodedType literalStructuredEncodedType Clause.negate :=
  TMBackedCostedMap.ofEncodingEquiv
    literalStructuredEncodedType literalStructuredEncodedType Clause.negate
    literalNegateSymbolEquiv literalStructured_encode_negate

/-- Positive auxiliary-literal construction is direct TM-backed. -/
noncomputable def posAuxTMBackedMap :
    TMBackedCostedMap EncodedType.nat literalStructuredEncodedType Clause.posAux :=
  literalPositiveTMBackedMap

/-- Negative auxiliary-literal construction is direct TM-backed. -/
noncomputable def negAuxTMBackedMap :
    TMBackedCostedMap EncodedType.nat literalStructuredEncodedType Clause.negAux :=
  literalNegativeTMBackedMap

/-- Clause singleton output is direct TM-backed under the structured CNF encoding. -/
noncomputable def clauseSingletonTMBackedMap :
    TMBackedCostedMap
      clauseStructuredEncodedType cnfStructuredEncodedType
      (fun c : Clause => [c]) := by
  simpa [cnfStructuredEncodedType] using
    (TMBackedCostedMap.listSingleton clauseStructuredEncodedType)

end SAT
end ComplexityReduction
