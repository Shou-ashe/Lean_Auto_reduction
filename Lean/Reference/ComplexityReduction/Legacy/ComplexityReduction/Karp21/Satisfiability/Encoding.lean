/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMComplexityClasses
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Basic
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CNFTo3SATCosted
import ComplexityReduction.Legacy.ComplexityReduction.SAT.ThreeSATInNP
import Mathlib.Tactic

/-!
Karp's general satisfiability target over the project-local CNF syntax.

This module proves the local CNF SAT ↔ bundled 3SAT wrapper used by the Karp21
catalog. It is intentionally a project-local encoded-problem theorem surface:
the broader textbook TM/P/NP semantics bridge remains tracked separately.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction
open Turing.TM2.Stmt

/--
General CNF satisfiability uses the same finite alphabet as local 3SAT, encoded
through the verified splitting map.  The encoded problem predicate is still
ordinary `SAT.CNF.Satisfiable`; the split encoding is only the local size model
needed for the costed wrapper.
-/
def satisfiabilityEncodedType : EncodedType where
  Carrier := SAT.CNF
  Symbol := SAT.ThreeSATSymbol
  finite_symbol := inferInstance
  encode := fun φ => SAT.ThreeSATEncoding.encodeThreeCNF (SAT.CNF.splitToThreeCNF φ)

/-- General CNF satisfiability as Karp's first target. -/
def satisfiabilityDecisionProblem : EncodedDecisionProblem where
  Instance := satisfiabilityEncodedType
  isYes := SAT.CNF.Satisfiable

/-- Karp's 3-satisfiability target reuses the local bundled 3CNF decision problem. -/
def threeSatisfiabilityDecisionProblem : EncodedDecisionProblem :=
  SAT.threeSATDecisionProblem

/--
Structured finite-alphabet encoding of SAT literals as `(variable, negation)`.
This is separate from the historical local 3SAT string encoding so that the
instance syntax is proved faithful by reusable product/list injectivity lemmas.
-/
def literalTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.bool

/-- Faithful finite-alphabet encoding for SAT literals. -/
def literalStructuredEncodedType : EncodedType where
  Carrier := SAT.Literal
  Symbol := literalTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun l => literalTupleStructuredEncodedType.encode (l.var, l.neg)

instance literalStructuredSymbolInhabited : Inhabited literalStructuredEncodedType.Symbol :=
  ⟨none⟩

/-- Clauses are encoded as delimiter-separated lists of faithfully encoded literals. -/
def clauseStructuredEncodedType : EncodedType :=
  EncodedType.list literalStructuredEncodedType

/-- CNF formulas are encoded as delimiter-separated lists of faithfully encoded clauses. -/
def cnfStructuredEncodedType : EncodedType :=
  EncodedType.list clauseStructuredEncodedType

/--
Bundled 3CNF formulas are encoded by the faithful encoding of their underlying
CNF syntax.  The `isThree` proof is proof-irrelevant and therefore need not add
payload symbols.
-/
def threeCNFStructuredEncodedType : EncodedType where
  Carrier := SAT.ThreeCNF
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

/-- Rebuild a SAT literal from its faithful tuple encoding carrier. -/
def literalTupleToLiteral (p : Nat × Bool) : SAT.Literal :=
  { var := p.1, neg := p.2 }

/-- Tuple-to-literal conversion preserves the faithful literal encoding exactly. -/
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

/-- Toggle only the Boolean component of a product-encoded literal symbol. -/
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

/-- Symbol equivalence implementing literal negation under the faithful encoding. -/
abbrev literalNegateSymbolEquiv :
    literalStructuredEncodedType.Symbol ≃ literalStructuredEncodedType.Symbol :=
  toggleRightBoolSymbolEquiv

theorem literalStructured_encode_negate (l : SAT.Literal) :
    literalStructuredEncodedType.encode (SAT.Clause.negate l) =
      (literalStructuredEncodedType.encode l).map literalNegateSymbolEquiv := by
  change
    literalStructuredEncodedType.encode (SAT.Clause.negate l) =
      (literalStructuredEncodedType.encode l).map toggleRightBoolSymbol
  cases l with
  | mk var neg =>
      cases neg <;>
        simp [literalStructuredEncodedType, literalTupleStructuredEncodedType,
          SAT.Clause.negate, EncodedType.prod, EncodedType.nat, EncodedType.bool,
          toggleRightBoolSymbol]

/-- Literal negation is a direct TM-backed map under the faithful literal encoding. -/
noncomputable def literalNegateTMBackedMap :
    TMBackedCostedMap
      literalStructuredEncodedType literalStructuredEncodedType SAT.Clause.negate :=
  TMBackedCostedMap.ofEncodingEquiv
    literalStructuredEncodedType literalStructuredEncodedType SAT.Clause.negate
    literalNegateSymbolEquiv literalStructured_encode_negate

/-- The positive auxiliary-literal writer is direct TM-backed. -/
noncomputable def posAuxTMBackedMap :
    TMBackedCostedMap EncodedType.nat literalStructuredEncodedType SAT.Clause.posAux where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := EncodedType.nat) (Y := literalStructuredEncodedType)
      (LinearSizeBound.intro_with 1 3 (by
        intro n
        simp [literalStructuredEncodedType, literalTupleStructuredEncodedType,
          SAT.Clause.posAux, EncodedType.inputSize, EncodedType.prod,
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
    simpa [Function.comp, literalTupleToLiteral, SAT.Clause.posAux] using hComp

/-- The negative auxiliary-literal writer is direct TM-backed. -/
noncomputable def negAuxTMBackedMap :
    TMBackedCostedMap EncodedType.nat literalStructuredEncodedType SAT.Clause.negAux where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := EncodedType.nat) (Y := literalStructuredEncodedType)
      (LinearSizeBound.intro_with 1 3 (by
        intro n
        simp [literalStructuredEncodedType, literalTupleStructuredEncodedType,
          SAT.Clause.negAux, EncodedType.inputSize, EncodedType.prod,
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
    simpa [Function.comp, literalTupleToLiteral, SAT.Clause.negAux] using hComp

/-- Unary successor is direct TM-backed under the project unary `Nat` encoding. -/
noncomputable def natSuccTMBackedMap :
    TMBackedCostedMap EncodedType.nat EncodedType.nat Nat.succ where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := EncodedType.nat) (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 1 1 (by
        intro n
        simp [EncodedType.inputSize, EncodedType.nat]))
  tm_polytime :=
    ⟨{ tm := TM2Programs.prefixMapMachine Bool Bool true id
       inputAlphabet := Equiv.refl Bool
       outputAlphabet := Equiv.refl Bool
       time := 4 * Polynomial.X + 3
       outputsFun := by
        intro n
        simpa [EncodedType.nat, List.replicate_succ, Polynomial.eval_add,
          Polynomial.eval_mul, Polynomial.eval_X] using
          TM2Programs.prefixMap_outputs Bool Bool true id (EncodedType.nat.encode n) }⟩

/-- Unary payloads without the final terminating `false` symbol. -/
def unaryPayloadEncodedType : EncodedType where
  Carrier := Nat
  Symbol := Bool
  finite_symbol := inferInstance
  encode := fun n => List.replicate n true

/-- Append the terminating `false` symbol to a unary payload. -/
noncomputable def unaryPayloadToNatTMBackedMap :
    TMBackedCostedMap unaryPayloadEncodedType EncodedType.nat id where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := unaryPayloadEncodedType) (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 1 1 (by
        intro n
        simp [unaryPayloadEncodedType, EncodedType.inputSize, EncodedType.nat]))
  tm_polytime :=
    ⟨{ tm := TM2Programs.suffixMapMachine Bool Bool false id
       inputAlphabet := Equiv.refl Bool
       outputAlphabet := Equiv.refl Bool
       time := 4 * Polynomial.X + 3
       outputsFun := by
        intro n
        change Turing.TM2OutputsInTime
          (TM2Programs.suffixMapMachine Bool Bool false id)
          (List.map (Equiv.refl Bool).invFun (unaryPayloadEncodedType.encode n))
          (some (List.map (Equiv.refl Bool).invFun (EncodedType.nat.encode (id n))))
          ((4 * Polynomial.X + 3).eval (unaryPayloadEncodedType.encode n).length)
        have hOut :=
          TM2Programs.suffixMap_outputs Bool Bool false id
            (unaryPayloadEncodedType.encode n)
        convert hOut using 1
        · change List.map id (unaryPayloadEncodedType.encode n) =
            unaryPayloadEncodedType.encode n
          rw [List.map_id]
        · apply congrArg some
          change List.map id (List.replicate n true ++ [false]) =
            List.map id (List.replicate n true) ++ [false]
          simp
        · simp [unaryPayloadEncodedType, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_X] }⟩

/--
The raw unary payload whose length is the encoded input length of `X`.  This is
useful when a TM-friendly fresh-variable bound may be any bound above all
variables, rather than the exact semantic `varBound`.
-/
def encodedInputSizePayloadEncodedType (X : EncodedType) : EncodedType where
  Carrier := X.Carrier
  Symbol := Bool
  finite_symbol := inferInstance
  encode := fun x => List.replicate (X.inputSize x) true

def encodedInputSizePayloadKeep {X : EncodedType} (_ : X.Symbol) : Option Bool :=
  some true

theorem encodedInputSizePayload_encode_filterMap (X : EncodedType) (x : X.Carrier) :
    (X.encode x).filterMap (encodedInputSizePayloadKeep (X := X)) =
      (encodedInputSizePayloadEncodedType X).encode x := by
  change
    (X.encode x).filterMap (fun _ : X.Symbol => some true) =
      List.replicate (X.encode x).length true
  induction X.encode x with
  | nil =>
      rfl
  | cons _ rest ih =>
      rw [List.filterMap_cons]
      simp only [List.length_cons]
      rw [ih, List.replicate_succ]

/-- Direct TM-backed writer for the unterminated unary length of an encoded input. -/
noncomputable def encodedInputSizeUnaryPayloadTMBackedMap (X : EncodedType) :
    TMBackedCostedMap X unaryPayloadEncodedType (fun x : X.Carrier => X.inputSize x) where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := X) (Y := unaryPayloadEncodedType)
      (LinearSizeBound.intro_with 1 0 (by
        intro x
        simp [unaryPayloadEncodedType, EncodedType.inputSize]))
  tm_polytime :=
    ⟨{ tm := TM2Programs.filterMapMachine X.Symbol Bool encodedInputSizePayloadKeep
       inputAlphabet := Equiv.refl X.Symbol
       outputAlphabet := Equiv.refl Bool
       time := 4 * Polynomial.X + 2
       outputsFun := by
        intro x
        change Turing.TM2OutputsInTime
          (TM2Programs.filterMapMachine X.Symbol Bool encodedInputSizePayloadKeep)
          (List.map (Equiv.refl X.Symbol).invFun (X.encode x))
          (some
            (List.map (Equiv.refl Bool).invFun
              (unaryPayloadEncodedType.encode (X.inputSize x))))
          ((4 * Polynomial.X + 2).eval (X.encode x).length)
        have hOut :=
          TM2Programs.filterMap_outputs X.Symbol Bool encodedInputSizePayloadKeep
            (X.encode x)
        convert hOut using 1
        · change List.map id (X.encode x) = X.encode x
          rw [List.map_id]
        · apply congrArg some
          change List.map id (unaryPayloadEncodedType.encode (X.inputSize x)) =
            List.filterMap encodedInputSizePayloadKeep (X.encode x)
          rw [List.map_id]
          simpa [unaryPayloadEncodedType, EncodedType.inputSize] using
            (encodedInputSizePayload_encode_filterMap X x).symm
        · simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] }⟩

/-- Direct TM-backed writer for `X.inputSize x` as a terminated unary natural. -/
noncomputable def encodedInputSizeNatTMBackedMap (X : EncodedType) :
    TMBackedCostedMap X EncodedType.nat (fun x : X.Carrier => X.inputSize x) where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := X) (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 1 1 (by
        intro x
        simp [EncodedType.inputSize, EncodedType.nat]))
  tm_polytime := by
    have hComp :=
      TMPolyTimeMap.comp
        unaryPayloadToNatTMBackedMap.tm_polytime
        (encodedInputSizeUnaryPayloadTMBackedMap X).tm_polytime
    simpa [Function.comp] using hComp

/--
Clause singleton output is a direct TM-backed map under the faithful structured
clause/CNF encodings.
-/
noncomputable def clauseSingletonTMBackedMap :
    TMBackedCostedMap
      clauseStructuredEncodedType cnfStructuredEncodedType
      (fun c : SAT.Clause => [c]) := by
  simpa [cnfStructuredEncodedType] using
    (TMBackedCostedMap.listSingleton clauseStructuredEncodedType)

/--
For clauses already of length at most three, the splitter's clause-level output
is exactly the singleton clause writer.
-/
theorem splitWith_eq_clauseSingleton_of_length_le_three
    (next : Nat) (c : SAT.Clause) (hc : c.length ≤ 3) :
    SAT.Clause.splitWith next c = [c] :=
  SAT.CNF.splitWith_eq_singleton_of_length_le_three next c hc

/-- General CNF satisfiability with a faithful finite-alphabet syntax encoding. -/
def satisfiabilityStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := cnfStructuredEncodedType
  isYes := SAT.CNF.Satisfiable

/-- Bundled local 3SAT with a faithful finite-alphabet syntax encoding. -/
def threeSATStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := threeCNFStructuredEncodedType
  isYes := SAT.ThreeCNF.Satisfiable

/-- The structured finite-alphabet CNF SAT encoding is faithful. -/
theorem satisfiabilityStructuredEncoding_faithful :
    satisfiabilityStructuredDecisionProblem.FaithfulEncoding where
  injective := cnfStructuredEncodedType_encode_injective

theorem satisfiabilityStructuredEncoding_predicateRespects :
    satisfiabilityStructuredDecisionProblem.PredicateRespectsEncoding :=
  satisfiabilityStructuredEncoding_faithful.predicateRespects

theorem satisfiabilityStructuredEncoding_accepts_encode_iff (φ : SAT.CNF) :
    satisfiabilityStructuredDecisionProblem.toEncodedLanguage.accepts
        (cnfStructuredEncodedType.encode φ) ↔
      SAT.CNF.Satisfiable φ :=
  satisfiabilityStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff φ

/-- The structured finite-alphabet bundled 3SAT encoding is faithful. -/
theorem threeSATStructuredEncoding_faithful :
    threeSATStructuredDecisionProblem.FaithfulEncoding where
  injective := threeCNFStructuredEncodedType_encode_injective

theorem threeSATStructuredEncoding_predicateRespects :
    threeSATStructuredDecisionProblem.PredicateRespectsEncoding :=
  threeSATStructuredEncoding_faithful.predicateRespects

theorem threeSATStructuredEncoding_accepts_encode_iff (φ : SAT.ThreeCNF) :
    threeSATStructuredDecisionProblem.toEncodedLanguage.accepts
        (threeCNFStructuredEncodedType.encode φ) ↔
      SAT.ThreeCNF.Satisfiable φ :=
  threeSATStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff φ


end Karp21
end ComplexityReduction
