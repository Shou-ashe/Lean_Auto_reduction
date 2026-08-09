/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatMul

/-!
Reusable direct-TM unary arithmetic helpers.

These are bridge-level versions of the small unary helpers used by several Karp21
routes.  Keeping them out of the Karp21 namespace lets SAT/Cook-Levin code use
the same direct `TMPolyTimeMap` witnesses without introducing a SAT -> Karp21
import dependency.
-/

namespace ComplexityReduction

/-! ### Unary payloads and input length -/

/-- Unary payloads without the terminating `false` symbol of `EncodedType.nat`. -/
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
The raw unary payload whose length is the encoded input length of `X`.
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

/-! ### Unary addition and fixed polynomials -/

def natAddInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

def natAddPayloadKeep : natAddInputEncodedType.Symbol → Option Bool
  | some (Sum.inl true) => some true
  | some (Sum.inr true) => some true
  | _ => none

set_option linter.unusedSimpArgs false in
theorem natAddPayload_encode_filterMap (p : Nat × Nat) :
    (natAddInputEncodedType.encode p).filterMap natAddPayloadKeep =
      unaryPayloadEncodedType.encode (p.1 + p.2) := by
  rcases p with ⟨m, n⟩
  simp [natAddInputEncodedType, EncodedType.prod, EncodedType.nat, unaryPayloadEncodedType,
    natAddPayloadKeep, List.filterMap_append, List.replicate_append_replicate]

theorem natAdd_tm_polytime :
    TMPolyTimeMap
      natAddInputEncodedType
      EncodedType.nat
      (fun p : Nat × Nat => p.1 + p.2) := by
  have hPayload :
      TMPolyTimeMap
        natAddInputEncodedType
        unaryPayloadEncodedType
        (fun p : Nat × Nat => p.1 + p.2) :=
    (TMBackedCostedMap.symbolFilterMap
      natAddInputEncodedType unaryPayloadEncodedType
      (fun p : Nat × Nat => p.1 + p.2)
      natAddPayloadKeep
      (fun p => (natAddPayload_encode_filterMap p).symm)).tm_polytime
  have hComp :=
    TMPolyTimeMap.comp unaryPayloadToNatTMBackedMap.tm_polytime hPayload
  simpa [Function.comp] using hComp

noncomputable def natAddTMBackedMap :
    TMBackedCostedMap
      natAddInputEncodedType
      EncodedType.nat
      (fun p : Nat × Nat => p.1 + p.2) where
  costed :=
    CostedMap.of_encodedLinearSizeBound (X := natAddInputEncodedType) (Y := EncodedType.nat)
      (LinearSizeBound.intro_with 1 1 (by
        intro p
        have hPayloadLen :=
          List.length_filterMap_le natAddPayloadKeep (natAddInputEncodedType.encode p)
        rw [natAddPayload_encode_filterMap p] at hPayloadLen
        simp [unaryPayloadEncodedType, EncodedType.inputSize, EncodedType.nat] at hPayloadLen ⊢
        omega))
  tm_polytime := natAdd_tm_polytime

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

/-- Direct TM witness for adding a fixed natural constant. -/
theorem nat_add_const_tm_polytime (k : Nat) :
    TMPolyTimeMap EncodedType.nat EncodedType.nat (fun n : Nat => n + k) := by
  have hRight : TMPolyTimeMap EncodedType.nat EncodedType.nat (fun _ : Nat => k) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.nat k
  have hPair :
      TMPolyTimeMap EncodedType.nat natAddInputEncodedType (fun n : Nat => (n, k)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id EncodedType.nat) hRight
  have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hPair
  simpa [Function.comp, natAddInputEncodedType] using hComp

/-- Direct TM witness for multiplying by a fixed natural constant. -/
theorem nat_mul_const_tm_polytime (k : Nat) :
    TMPolyTimeMap EncodedType.nat EncodedType.nat (fun n : Nat => n * k) := by
  have hRight : TMPolyTimeMap EncodedType.nat EncodedType.nat (fun _ : Nat => k) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.nat k
  have hPair :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat) (fun n : Nat => (n, k)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id EncodedType.nat) hRight
  have hComp := TMPolyTimeMap.comp GenericNatTM.natMul_tm_polytime hPair
  simpa [Function.comp] using hComp

/-- Direct TM witness for a fixed power `n ^ degree`. -/
theorem nat_pow_fixed_tm_polytime (degree : Nat) :
    TMPolyTimeMap EncodedType.nat EncodedType.nat (fun n : Nat => n ^ degree) := by
  induction degree with
  | zero =>
      simpa using TMPolyTimeMap.const EncodedType.nat EncodedType.nat (1 : Nat)
  | succ degree ih =>
      have hPair :
          TMPolyTimeMap EncodedType.nat
            (EncodedType.prod EncodedType.nat EncodedType.nat)
            (fun n : Nat => (n, n ^ degree)) :=
        TMPolyTimeMap.prod_mk (TMPolyTimeMap.id EncodedType.nat) ih
      have hComp := TMPolyTimeMap.comp GenericNatTM.natMul_tm_polytime hPair
      simpa [Function.comp, pow_succ'] using hComp

/-- Direct TM witness for `coeff * n ^ degree + const`. -/
theorem nat_poly_monomial_tm_polytime (degree coeff const : Nat) :
    TMPolyTimeMap EncodedType.nat EncodedType.nat
      (fun n : Nat => coeff * n ^ degree + const) := by
  have hPow := nat_pow_fixed_tm_polytime degree
  have hCoeffLeft : TMPolyTimeMap EncodedType.nat EncodedType.nat (fun _ : Nat => coeff) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.nat coeff
  have hMulInput :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun n : Nat => (coeff, n ^ degree)) :=
    TMPolyTimeMap.prod_mk hCoeffLeft hPow
  have hMul :
      TMPolyTimeMap EncodedType.nat EncodedType.nat
        (fun n : Nat => coeff * n ^ degree) := by
    have hComp := TMPolyTimeMap.comp GenericNatTM.natMul_tm_polytime hMulInput
    simpa [Function.comp] using hComp
  have hConst : TMPolyTimeMap EncodedType.nat EncodedType.nat (fun _ : Nat => const) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.nat const
  have hAddInput :
      TMPolyTimeMap EncodedType.nat natAddInputEncodedType
        (fun n : Nat => (coeff * n ^ degree, const)) :=
    TMPolyTimeMap.prod_mk hMul hConst
  have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hAddInput
  simpa [Function.comp, natAddInputEncodedType] using hComp

/-- Evaluate a fixed natural-coefficient polynomial on a unary natural input. -/
def natPolynomialEval (p : Polynomial Nat) (n : Nat) : Nat :=
  p.eval n

/-- Direct TM witness for evaluating any fixed natural-coefficient polynomial on unary `Nat`. -/
theorem nat_polynomial_eval_tm_polytime (p : Polynomial Nat) :
    TMPolyTimeMap EncodedType.nat EncodedType.nat (natPolynomialEval p) := by
  refine Polynomial.induction_on p ?hC ?hAdd ?hMonomial
  · intro a
    convert (TMPolyTimeMap.const EncodedType.nat EncodedType.nat a) using 1
    funext n
    simp [natPolynomialEval]
  · intro p q hp hq
    have hPair :
        TMPolyTimeMap EncodedType.nat natAddInputEncodedType
          (fun n : Nat => (natPolynomialEval p n, natPolynomialEval q n)) :=
      TMPolyTimeMap.prod_mk hp hq
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hPair
    convert hComp using 1
    funext n
    simp [Function.comp, natPolynomialEval, Polynomial.eval_add]
  · intro degree coeff _ih
    have hMono := nat_poly_monomial_tm_polytime (degree + 1) coeff 0
    convert hMono using 1
    funext n
    simp [natPolynomialEval, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

end ComplexityReduction
