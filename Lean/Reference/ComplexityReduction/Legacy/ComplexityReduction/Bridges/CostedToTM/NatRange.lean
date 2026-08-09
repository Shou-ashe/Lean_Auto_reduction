/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatArithmetic
import Mathlib.Data.List.Range
import Mathlib.Tactic

/-!
Direct standard-TM unary range generation.

This bridge-level file provides the `Nat -> List Nat` range generator without
depending on any Karp21 namespace, so SAT/Cook-Levin generator witnesses can use
it without introducing a SAT -> Karp21 import edge.
-/

namespace ComplexityReduction

/-! ### Unary range generation -/

def rawUnitListEncodedType : EncodedType :=
  EncodedType.list (EncodedType.raw Unit)

def natToRawUnitListKeep : Bool → Option rawUnitListEncodedType.Symbol
  | true => some none
  | false => none

theorem rawUnitList_encode_replicate (n : Nat) :
    rawUnitListEncodedType.encode (List.replicate n ()) =
      List.replicate n (none : Option Unit) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        none :: rawUnitListEncodedType.encode (List.replicate n ()) =
          none :: List.replicate n (none : Option Unit)
      rw [ih]
      rfl

theorem natToRawUnitList_encode_filterMap (n : Nat) :
    (EncodedType.nat.encode n).filterMap natToRawUnitListKeep =
      rawUnitListEncodedType.encode (List.replicate n ()) := by
  rw [rawUnitList_encode_replicate]
  simp [EncodedType.nat, natToRawUnitListKeep]
  rfl

noncomputable def natToRawUnitListTMBackedMap :
    TMBackedCostedMap
      EncodedType.nat rawUnitListEncodedType
      (fun n : Nat => List.replicate n ()) :=
  TMBackedCostedMap.symbolFilterMap
    EncodedType.nat rawUnitListEncodedType
    (fun n : Nat => List.replicate n ())
    natToRawUnitListKeep
    (fun n => (natToRawUnitList_encode_filterMap n).symm)

def natRangeBuilderAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat)

def natRangeBuilderStepInputEncodedType : EncodedType :=
  EncodedType.prod natRangeBuilderAccEncodedType (EncodedType.raw Unit)

def natRangeBuilderInit : Nat × List Nat :=
  (0, [])

def natRangeBuilderStep
    (p : (Nat × List Nat) × Unit) : Nat × List Nat :=
  let next := p.1.1
  let out : List Nat := p.1.2
  (Nat.succ next, out ++ [next])

def natRangeFromUnits (xs : List Unit) : List Nat :=
  (xs.foldl (fun acc x => natRangeBuilderStep (acc, x)) natRangeBuilderInit).2

theorem rawUnitList_inputSize_eq_length (xs : List Unit) :
    rawUnitListEncodedType.inputSize xs = xs.length := by
  simp [rawUnitListEncodedType, EncodedType.inputSize, EncodedType.list, EncodedType.raw]

theorem rawUnitList_inputSize_cons (u : Unit) (rest : List Unit) :
    rawUnitListEncodedType.inputSize (u :: rest) =
      rawUnitListEncodedType.inputSize rest + 1 := by
  simp [rawUnitListEncodedType, EncodedType.inputSize, EncodedType.list, EncodedType.raw]

theorem list_inputSize_append (X : EncodedType) (xs ys : List X.Carrier) :
    (EncodedType.list X).inputSize (xs ++ ys) =
      (EncodedType.list X).inputSize xs + (EncodedType.list X).inputSize ys := by
  simp [EncodedType.inputSize, EncodedType.list, List.flatMap_append]

theorem natList_inputSize_append (xs ys : List Nat) :
    (EncodedType.list EncodedType.nat).inputSize (xs ++ ys) =
      (EncodedType.list EncodedType.nat).inputSize xs +
        (EncodedType.list EncodedType.nat).inputSize ys := by
  simpa using list_inputSize_append EncodedType.nat xs ys

theorem natList_inputSize_singleton (n : Nat) :
    (EncodedType.list EncodedType.nat).inputSize [n] = n + 2 := by
  simp [EncodedType.inputSize, EncodedType.list, EncodedType.nat]

theorem natList_range_inputSize_le (n : Nat) :
    (EncodedType.list EncodedType.nat).inputSize (List.range n) ≤ n * (n + 2) := by
  induction n with
  | zero =>
      simp [EncodedType.inputSize, EncodedType.list]
      exact ⟨rfl, rfl⟩
  | succ n ih =>
      rw [List.range_succ]
      rw [natList_inputSize_append]
      have hSingleton : EncodedType.nat.list.inputSize [n] = n + 2 :=
        natList_inputSize_singleton n
      calc
        EncodedType.nat.list.inputSize (List.range n) + EncodedType.nat.list.inputSize [n]
            ≤ n * (n + 2) + (n + 2) := Nat.add_le_add ih (le_of_eq hSingleton)
        _ ≤ (n + 1) * (n + 1 + 2) := by
            nlinarith

theorem natRangeBuilderAcc_range_inputSize_le (n : Nat) :
    natRangeBuilderAccEncodedType.inputSize (n, List.range n) ≤ (n + 2) * (n + 2) := by
  have hRange := natList_range_inputSize_le n
  simp [natRangeBuilderAccEncodedType, EncodedType.inputSize_prod]
  nlinarith

theorem natRangeBuilderStep_range (n : Nat) (u : Unit) :
    natRangeBuilderStep ((n, List.range n), u) = (n + 1, List.range (n + 1)) := by
  simp [natRangeBuilderStep, List.range_succ]

theorem natRangeBuilderFold_range_aux (N : Nat) :
    ∀ (rest : List Unit) (m : Nat),
      m + rawUnitListEncodedType.inputSize rest = N →
        rest.foldl (fun acc x => natRangeBuilderStep (acc, x)) (m, List.range m) =
          (N, List.range N)
  | [], m, h => by
      simp [rawUnitList_inputSize_eq_length] at h
      subst N
      simp
  | u :: rest, m, h => by
      have hNext : (m + 1) + rawUnitListEncodedType.inputSize rest = N := by
        rw [rawUnitList_inputSize_eq_length] at h ⊢
        simp at h ⊢
        omega
      simp [natRangeBuilderStep_range m u]
      exact natRangeBuilderFold_range_aux N rest (m + 1) hNext

theorem natRangeFromUnits_eq_range (xs : List Unit) :
    natRangeFromUnits xs = List.range xs.length := by
  have hFold :=
    natRangeBuilderFold_range_aux (rawUnitListEncodedType.inputSize xs) xs 0 (by simp)
  rw [rawUnitList_inputSize_eq_length xs] at hFold
  simpa [natRangeFromUnits, natRangeBuilderInit] using congrArg Prod.snd hFold

theorem natRangeFromUnits_replicate (n : Nat) :
    natRangeFromUnits (List.replicate n ()) = List.range n := by
  simpa using natRangeFromUnits_eq_range (List.replicate n ())

theorem natRangeFromUnits_inputSize_le (xs : List Unit) :
    (EncodedType.list EncodedType.nat).inputSize (natRangeFromUnits xs) ≤
      3 * rawUnitListEncodedType.inputSize xs ^ 2 + 10 := by
  have hRange := natList_range_inputSize_le xs.length
  rw [natRangeFromUnits_eq_range, rawUnitList_inputSize_eq_length]
  nlinarith

theorem natRangeFromUnits_polynomialSizeBound :
    PolynomialSizeBound
      (fun xs : List Unit => rawUnitListEncodedType.inputSize xs)
      (fun ys : List Nat => (EncodedType.list EncodedType.nat).inputSize ys)
      natRangeFromUnits :=
  PolynomialSizeBound.intro_with 2 3 10 natRangeFromUnits_inputSize_le

theorem natRangeBuilderStep_tm_polytime :
    TMPolyTimeMap
      natRangeBuilderStepInputEncodedType
      natRangeBuilderAccEncodedType
      natRangeBuilderStep := by
  let X := natRangeBuilderStepInputEncodedType
  have hAcc :
      TMPolyTimeMap X natRangeBuilderAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, natRangeBuilderStepInputEncodedType] using
      TMPolyTimeMap.fst natRangeBuilderAccEncodedType (EncodedType.raw Unit)
  have hNext :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat (EncodedType.list EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, natRangeBuilderAccEncodedType, X] using hComp
  have hOut :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat) (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat (EncodedType.list EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, natRangeBuilderAccEncodedType, X] using hComp
  have hNextSucc :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => Nat.succ p.1.1) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hNext
    simpa [Function.comp] using hComp
  have hNextSingleton :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => ([p.1.1] : List Nat)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.nat) hNext
    simpa [Function.comp] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod (EncodedType.list EncodedType.nat)
          (EncodedType.list EncodedType.nat))
        (fun p : X.Carrier => ((p.1.2 : List Nat), ([p.1.1] : List Nat))) :=
    TMPolyTimeMap.prod_mk hOut hNextSingleton
  have hOutAppend :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier =>
          List.append (p.1.2 : List Nat) ([p.1.1] : List Nat)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.nat) hAppendInput
    simpa [Function.comp] using hComp
  have hPair :
      TMPolyTimeMap X natRangeBuilderAccEncodedType
        (fun p : X.Carrier =>
          (Nat.succ p.1.1, List.append (p.1.2 : List Nat) ([p.1.1] : List Nat))) :=
    TMPolyTimeMap.prod_mk hNextSucc hOutAppend
  simpa [natRangeBuilderStep, X, natRangeBuilderAccEncodedType] using hPair

theorem natRangeBuilderStep_inputSize_le
    (p : natRangeBuilderStepInputEncodedType.Carrier) :
    natRangeBuilderAccEncodedType.inputSize (natRangeBuilderStep p) ≤
      3 * natRangeBuilderStepInputEncodedType.inputSize p + 5 := by
  rcases p with ⟨⟨next, out⟩, u⟩
  simp [natRangeBuilderStep, natRangeBuilderStepInputEncodedType,
    natRangeBuilderAccEncodedType, EncodedType.prod, EncodedType.nat,
    EncodedType.list, EncodedType.raw, EncodedType.inputSize]
  omega

theorem natRangeBuilderStep_linearSizeBound :
    LinearSizeBound
      (fun p : natRangeBuilderStepInputEncodedType.Carrier =>
        natRangeBuilderStepInputEncodedType.inputSize p)
      (fun acc : natRangeBuilderAccEncodedType.Carrier =>
        natRangeBuilderAccEncodedType.inputSize acc)
      natRangeBuilderStep :=
  LinearSizeBound.intro_with 3 5 natRangeBuilderStep_inputSize_le

noncomputable def natRangeBuilderStepTMBackedMap :
    TMBackedCostedMap
      natRangeBuilderStepInputEncodedType
      natRangeBuilderAccEncodedType
      natRangeBuilderStep where
  costed := CostedMap.of_encodedLinearSizeBound natRangeBuilderStep_linearSizeBound
  tm_polytime := natRangeBuilderStep_tm_polytime

noncomputable def natRangeBuilderFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod natRangeBuilderAccEncodedType (EncodedType.raw Unit)).encode
        natRangeBuilderAccEncodedType.encode
        natRangeBuilderStep) :
    Polynomial Nat :=
  let bound := (Polynomial.X + Polynomial.C 2) * (Polynomial.X + Polynomial.C 2)
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm bound
    (hStep.time.comp (bound + Polynomial.X + Polynomial.C 5))

theorem natRangeBuilderFold_loopTime_le
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod natRangeBuilderAccEncodedType (EncodedType.raw Unit)).encode
        natRangeBuilderAccEncodedType.encode
        natRangeBuilderStep)
    (source : List Unit) :
    2 +
      TM2Programs.listFoldTypedLoopTime
        (EncodedType.raw Unit) natRangeBuilderAccEncodedType
        natRangeBuilderStep hStep natRangeBuilderInit source ≤
        (natRangeBuilderFoldTimePolynomial hStep).eval
          (rawUnitListEncodedType.inputSize source) := by
  let X := EncodedType.raw Unit
  let Y := natRangeBuilderAccEncodedType
  let N := rawUnitListEncodedType.inputSize source
  let bound : Polynomial Nat :=
    (Polynomial.X + Polynomial.C 2) * (Polynomial.X + Polynomial.C 2)
  let B := bound.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hBoundEval : B = (N + 2) * (N + 2) := by
    simp [B, bound, Polynomial.eval_add, Polynomial.eval_mul]
  have hLoopAux :
      ∀ (rest : List Unit) (m : Nat),
        m + rawUnitListEncodedType.inputSize rest = N →
          TM2Programs.listFoldTypedLoopTime
            X Y natRangeBuilderStep hStep (m, List.range m) rest ≤
            C * rawUnitListEncodedType.inputSize rest := by
    intro rest
    induction rest with
    | nil =>
        intro m _h
        simp [TM2Programs.listFoldTypedLoopTime, rawUnitList_inputSize_eq_length]
    | cons u rest ih =>
        intro m hRest
        have hmSuccN : m + 1 ≤ N := by
          rw [rawUnitList_inputSize_eq_length] at hRest
          simp at hRest
          omega
        have hRestTail : (m + 1) + rawUnitListEncodedType.inputSize rest = N := by
          rw [rawUnitList_inputSize_eq_length] at hRest ⊢
          simp at hRest ⊢
          omega
        have hAcc :
            Y.inputSize (m, List.range m) ≤ B := by
          have hAccBase := natRangeBuilderAcc_range_inputSize_le m
          rw [hBoundEval]
          exact le_trans hAccBase (Nat.mul_le_mul (by omega) (by omega))
        have hNext :
            Y.inputSize (natRangeBuilderStep ((m, List.range m), u)) ≤ B := by
          rw [natRangeBuilderStep_range m u]
          have hNextBase := natRangeBuilderAcc_range_inputSize_le (m + 1)
          rw [hBoundEval]
          exact le_trans hNextBase (Nat.mul_le_mul (by omega) (by omega))
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod Y X).inputSize ((m, List.range m), u)) ≤ T := by
          have hArg :
              (EncodedType.prod Y X).inputSize ((m, List.range m), u) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change Y.inputSize (m, List.range m) + 1 + X.inputSize u ≤ B + N + 5
            have hx : X.inputSize u = 0 := by rfl
            rw [hx]
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm (X.encode u).length
                (Y.encode (m, List.range m)).length
                (Y.encode (natRangeBuilderStep ((m, List.range m), u))).length
                (hStep.time.eval ((EncodedType.prod Y X).inputSize ((m, List.range m), u))) ≤
              C * (X.inputSize u + 1) := by
          exact
            TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
              (by simpa [Y, EncodedType.inputSize] using hAcc)
              (by simpa [Y, EncodedType.inputSize] using hNext)
              hStepTime
        have hTail :=
          ih (m + 1) hRestTail
        calc
          TM2Programs.listFoldTypedLoopTime X Y natRangeBuilderStep hStep
              (m, List.range m) (u :: rest)
              =
            TM2Programs.listFoldTypedLoopTime X Y natRangeBuilderStep hStep
              (natRangeBuilderStep ((m, List.range m), u)) rest +
              TM2Programs.listFoldBlockTime hStep.tm (X.encode u).length
                (Y.encode (m, List.range m)).length
                (Y.encode (natRangeBuilderStep ((m, List.range m), u))).length
                (hStep.time.eval ((EncodedType.prod Y X).inputSize ((m, List.range m), u))) := by
                rfl
          _ =
            TM2Programs.listFoldTypedLoopTime X Y natRangeBuilderStep hStep
              (m + 1, List.range (m + 1)) rest +
              TM2Programs.listFoldBlockTime hStep.tm (X.encode u).length
                (Y.encode (m, List.range m)).length
                (Y.encode (natRangeBuilderStep ((m, List.range m), u))).length
                (hStep.time.eval ((EncodedType.prod Y X).inputSize ((m, List.range m), u))) := by
                rw [natRangeBuilderStep_range m u]
                rfl
          _ ≤ C * rawUnitListEncodedType.inputSize rest + C * (X.inputSize u + 1) :=
                Nat.add_le_add hTail hBlock
          _ ≤ C * rawUnitListEncodedType.inputSize (u :: rest) := by
                have hConsSize :
                    rawUnitListEncodedType.inputSize (u :: rest) =
                      rawUnitListEncodedType.inputSize rest + 1 := by
                  exact rawUnitList_inputSize_cons u rest
                rw [hConsSize]
                simp [X, EncodedType.inputSize, EncodedType.raw, Nat.mul_add]
  have hLoop :
      TM2Programs.listFoldTypedLoopTime
        X Y natRangeBuilderStep hStep natRangeBuilderInit source ≤ C * N := by
    simpa [X, Y, natRangeBuilderInit, N] using hLoopAux source 0 (by simp [N])
  have hTimeEval :
      (natRangeBuilderFoldTimePolynomial hStep).eval N = (C + 2) * (N + 1) := by
    simp [natRangeBuilderFoldTimePolynomial, bound, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp]
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem natRangeBuilderFold_tm_polytime :
    TMPolyTimeMap
      rawUnitListEncodedType
      natRangeBuilderAccEncodedType
      (fun xs : List Unit =>
        xs.foldl (fun acc x => natRangeBuilderStep (acc, x)) natRangeBuilderInit) := by
  rcases natRangeBuilderStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed
      (EncodedType.raw Unit) natRangeBuilderAccEncodedType
      natRangeBuilderStep natRangeBuilderInit hStep
      (natRangeBuilderFoldTimePolynomial hStep) ?_
  intro source
  exact natRangeBuilderFold_loopTime_le hStep source

theorem natRangeFromUnits_tm_polytime :
    TMPolyTimeMap
      rawUnitListEncodedType
      (EncodedType.list EncodedType.nat)
      natRangeFromUnits := by
  have hFold := natRangeBuilderFold_tm_polytime
  have hSnd := TMPolyTimeMap.snd EncodedType.nat (EncodedType.list EncodedType.nat)
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, natRangeFromUnits, natRangeBuilderAccEncodedType] using hComp

noncomputable def natRangeFromUnitsTMBackedMap :
    TMBackedCostedMap
      rawUnitListEncodedType
      (EncodedType.list EncodedType.nat)
      natRangeFromUnits where
  costed := CostedMap.of_encodedPolynomialSizeBound natRangeFromUnits_polynomialSizeBound
  tm_polytime := natRangeFromUnits_tm_polytime

theorem natRange_inputSize_le (n : Nat) :
    (EncodedType.list EncodedType.nat).inputSize (List.range n) ≤
      3 * EncodedType.nat.inputSize n ^ 2 + 10 := by
  have hRange := natList_range_inputSize_le n
  simp [EncodedType.inputSize_nat]
  nlinarith

theorem natRange_polynomialSizeBound :
    PolynomialSizeBound
      (fun n : Nat => EncodedType.nat.inputSize n)
      (fun ys : List Nat => (EncodedType.list EncodedType.nat).inputSize ys)
      (fun n : Nat => List.range n) :=
  PolynomialSizeBound.intro_with 2 3 10 natRange_inputSize_le

theorem natRange_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      (EncodedType.list EncodedType.nat)
      (fun n : Nat => List.range n) := by
  have hComp :=
    TMPolyTimeMap.comp natRangeFromUnits_tm_polytime natToRawUnitListTMBackedMap.tm_polytime
  convert hComp using 1
  funext n
  exact (natRangeFromUnits_replicate n).symm

noncomputable def natRangeTMBackedMap :
    TMBackedCostedMap
      EncodedType.nat
      (EncodedType.list EncodedType.nat)
      (fun n : Nat => List.range n) where
  costed := CostedMap.of_encodedPolynomialSizeBound natRange_polynomialSizeBound
  tm_polytime := natRange_tm_polytime

end ComplexityReduction
