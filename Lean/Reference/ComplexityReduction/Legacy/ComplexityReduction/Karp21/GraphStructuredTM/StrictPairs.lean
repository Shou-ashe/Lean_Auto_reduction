/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.PairCandidates

/-!
TM-backed strict unordered vertex-pair candidate generation.

This is the next graph-complement assembly layer after all ordered candidates:
it emits exactly the pairs `u < v < n`.  It still does not inspect the source
edge list, so it is not yet a complement-edge enumerator.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics.Graph

/-! ### Strict vertex-pair candidate generation -/

def strictNatPairCandidatesAccEncodedType : EncodedType :=
  natPairCandidatesAccEncodedType

def strictNatPairCandidatesCore : Nat → List (Nat × Nat)
  | 0 => []
  | n + 1 => strictNatPairCandidatesCore n ++ natPairCandidateCtx n

def strictNatPairCandidatesAcc (n : Nat) :
    strictNatPairCandidatesAccEncodedType.Carrier :=
  (n, (natPairCandidateCtx n, strictNatPairCandidatesCore n))

def strictNatPairCandidatesBuilderInit :
    strictNatPairCandidatesAccEncodedType.Carrier :=
  strictNatPairCandidatesAcc 0

def strictNatPairCandidatesBuilderStep
    (p : strictNatPairCandidatesAccEncodedType.Carrier × Unit) :
    strictNatPairCandidatesAccEncodedType.Carrier :=
  let next : Nat := p.1.1
  let ctx : List (Nat × Nat) := p.1.2.1
  let pairs : List (Nat × Nat) := p.1.2.2
  let nextSucc : Nat := Nat.succ next
  let nextCtx : List (Nat × Nat) := ctx.map vertexPairRightSucc ++ [(next, nextSucc)]
  (nextSucc, (nextCtx, pairs ++ ctx))

def strictNatPairCandidatesFromUnits (xs : List Unit) : List (Nat × Nat) :=
  (xs.foldl
      (fun acc x => strictNatPairCandidatesBuilderStep (acc, x))
      strictNatPairCandidatesBuilderInit).2.2

def strictNatPairCandidates (n : Nat) : List (Nat × Nat) :=
  strictNatPairCandidatesFromUnits (List.replicate n ())

theorem strictNatPairCandidatesBuilderStep_acc (n : Nat) (u : Unit) :
    strictNatPairCandidatesBuilderStep (strictNatPairCandidatesAcc n, u) =
      strictNatPairCandidatesAcc (n + 1) := by
  simp [strictNatPairCandidatesBuilderStep, strictNatPairCandidatesAcc,
    strictNatPairCandidatesCore, natPairCandidateCtx_succ]

theorem strictNatPairCandidatesFold_acc_aux (N : Nat) :
    ∀ (rest : List Unit) (m : Nat),
      m + rawUnitListEncodedType.inputSize rest = N →
        rest.foldl
            (fun acc x => strictNatPairCandidatesBuilderStep (acc, x))
            (strictNatPairCandidatesAcc m) =
          strictNatPairCandidatesAcc N
  | [], m, h => by
      simp [rawUnitList_inputSize_eq_length] at h
      subst N
      simp
  | u :: rest, m, h => by
      have hNext : (m + 1) + rawUnitListEncodedType.inputSize rest = N := by
        rw [rawUnitList_inputSize_eq_length] at h ⊢
        simp at h ⊢
        omega
      simp [strictNatPairCandidatesBuilderStep_acc m u]
      exact strictNatPairCandidatesFold_acc_aux N rest (m + 1) hNext

theorem strictNatPairCandidatesFromUnits_eq_core (xs : List Unit) :
    strictNatPairCandidatesFromUnits xs =
      strictNatPairCandidatesCore xs.length := by
  have hFold :=
    strictNatPairCandidatesFold_acc_aux (rawUnitListEncodedType.inputSize xs) xs 0 (by simp)
  rw [rawUnitList_inputSize_eq_length xs] at hFold
  simpa [strictNatPairCandidatesFromUnits, strictNatPairCandidatesBuilderInit,
    strictNatPairCandidatesAcc] using congrArg (fun p => p.2.2) hFold

theorem strictNatPairCandidates_replicate (n : Nat) :
    strictNatPairCandidates n = strictNatPairCandidatesCore n := by
  simpa [strictNatPairCandidates] using
    strictNatPairCandidatesFromUnits_eq_core (List.replicate n ())

theorem mem_strictNatPairCandidatesCore_iff (n : Nat) (e : Nat × Nat) :
    e ∈ strictNatPairCandidatesCore n ↔ e.1 < n ∧ e.2 < n ∧ e.1 < e.2 := by
  induction n with
  | zero =>
      cases e
      simp [strictNatPairCandidatesCore]
  | succ n ih =>
      cases e with
      | mk u v =>
          constructor
          · intro h
            simp [strictNatPairCandidatesCore, ih, mem_natPairCandidateCtx_iff] at h
            omega
          · intro h
            have hCases :
                (u < n ∧ v < n ∧ u < v) ∨ (u < n ∧ v = n) := by
              omega
            simpa [strictNatPairCandidatesCore, ih, mem_natPairCandidateCtx_iff] using hCases

theorem strictNatPairCandidatesCore_length_le_square (n : Nat) :
    (strictNatPairCandidatesCore n).length ≤ n * n := by
  induction n with
  | zero =>
      simp [strictNatPairCandidatesCore]
  | succ n ih =>
      calc
        (strictNatPairCandidatesCore (n + 1)).length =
            (strictNatPairCandidatesCore n).length + n := by
              simp [strictNatPairCandidatesCore, natPairCandidateCtx_length]
        _ ≤ n * n + n := Nat.add_le_add_right ih n
        _ ≤ (n + 1) * (n + 1) := by
              nlinarith

theorem strictNatPairCandidatesCore_inputSize_le (n : Nat) :
    vertexPairListEncodedType.inputSize (strictNatPairCandidatesCore n) ≤
      (n * n) * (2 * n + 4) := by
  have hList :=
    encodedList_inputSize_le_length_mul_bound vertexPairEncodedType
      (strictNatPairCandidatesCore n) (2 * n + 3)
      (by
        intro e he
        have hmem := (mem_strictNatPairCandidatesCore_iff n e).1 he
        exact vertexPair_inputSize_le_of_lt hmem.1 hmem.2.1)
  have hLen := strictNatPairCandidatesCore_length_le_square n
  change vertexPairEncodedType.list.inputSize (strictNatPairCandidatesCore n) ≤
    (n * n) * (2 * n + 4)
  calc
    vertexPairEncodedType.list.inputSize (strictNatPairCandidatesCore n)
        ≤ (strictNatPairCandidatesCore n).length * (2 * n + 3 + 1) := hList
    _ ≤ (n * n) * (2 * n + 3 + 1) :=
          Nat.mul_le_mul_right (2 * n + 3 + 1) hLen
    _ = (n * n) * (2 * n + 4) := by
          ring

theorem strictNatPairCandidatesAcc_inputSize_le (n : Nat) :
    strictNatPairCandidatesAccEncodedType.inputSize
        (strictNatPairCandidatesAcc n) ≤
      10 * ((n + 2) * (n + 2) * (n + 2)) + 20 := by
  have hCtx := natPairCandidateCtx_inputSize_le n
  have hCore := strictNatPairCandidatesCore_inputSize_le n
  simp [strictNatPairCandidatesAccEncodedType, natPairCandidatesAccEncodedType,
    strictNatPairCandidatesAcc, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat] at *
  nlinarith

theorem strictNatPairCandidatesCore_inputSize_le_cubic (n : Nat) :
    vertexPairListEncodedType.inputSize (strictNatPairCandidatesCore n) ≤
      10 * ((n + 2) * (n + 2) * (n + 2)) + 20 := by
  have hCore := strictNatPairCandidatesCore_inputSize_le n
  nlinarith

theorem strictNatPairCandidatesFromUnits_inputSize_le (xs : List Unit) :
    vertexPairListEncodedType.inputSize (strictNatPairCandidatesFromUnits xs) ≤
      10 * ((rawUnitListEncodedType.inputSize xs + 2) *
        (rawUnitListEncodedType.inputSize xs + 2) *
        (rawUnitListEncodedType.inputSize xs + 2)) + 20 := by
  rw [strictNatPairCandidatesFromUnits_eq_core, rawUnitList_inputSize_eq_length]
  exact strictNatPairCandidatesCore_inputSize_le_cubic xs.length

theorem strictNatPairCandidatesFromUnits_polynomialSizeBound :
    PolynomialSizeBound
      (fun xs : List Unit => rawUnitListEncodedType.inputSize xs)
      (fun ys : List (Nat × Nat) => vertexPairListEncodedType.inputSize ys)
      strictNatPairCandidatesFromUnits :=
  PolynomialSizeBound.intro_with 3 1000 1000 (by
    intro xs
    have h := strictNatPairCandidatesFromUnits_inputSize_le xs
    exact h.trans (natPairCandidatesCubicBound_poly (rawUnitListEncodedType.inputSize xs)))

theorem strictNatPairCandidates_inputSize_le (n : Nat) :
    vertexPairListEncodedType.inputSize (strictNatPairCandidates n) ≤
      10 * ((EncodedType.nat.inputSize n + 2) *
        (EncodedType.nat.inputSize n + 2) *
        (EncodedType.nat.inputSize n + 2)) + 20 := by
  rw [strictNatPairCandidates, strictNatPairCandidatesFromUnits_eq_core]
  have hCore := strictNatPairCandidatesCore_inputSize_le_cubic n
  have hMono := natPairCandidatesCubicBound_mono (m := n) (N := n + 1) (by omega)
  simpa [EncodedType.inputSize_nat] using hCore.trans hMono

theorem strictNatPairCandidates_polynomialSizeBound :
    PolynomialSizeBound
      (fun n : Nat => EncodedType.nat.inputSize n)
      (fun ys : List (Nat × Nat) => vertexPairListEncodedType.inputSize ys)
      strictNatPairCandidates :=
  PolynomialSizeBound.intro_with 3 1000 1000 (by
    intro n
    have h := strictNatPairCandidates_inputSize_le n
    exact h.trans (natPairCandidatesCubicBound_poly (EncodedType.nat.inputSize n)))

theorem mem_strictNatPairCandidates_iff (n : Nat) (e : Nat × Nat) :
    e ∈ strictNatPairCandidates n ↔ e.1 < n ∧ e.2 < n ∧ e.1 < e.2 := by
  rw [strictNatPairCandidates_replicate]
  exact mem_strictNatPairCandidatesCore_iff n e

theorem strictNatPairCandidatesBuilderStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod strictNatPairCandidatesAccEncodedType (EncodedType.raw Unit))
      strictNatPairCandidatesAccEncodedType
      strictNatPairCandidatesBuilderStep := by
  let A := strictNatPairCandidatesAccEncodedType
  let R := vertexPairListEncodedType
  let X := EncodedType.prod A (EncodedType.raw Unit)
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst A (EncodedType.raw Unit)
  have hNext : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat (EncodedType.prod R R)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [A, X, strictNatPairCandidatesAccEncodedType,
      natPairCandidatesAccEncodedType] using hComp
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod R R) (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat (EncodedType.prod R R)
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [A, X, strictNatPairCandidatesAccEncodedType,
      natPairCandidatesAccEncodedType] using hComp
  have hCtx : TMPolyTimeMap X R (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst R R
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [X] using hComp
  have hPairs : TMPolyTimeMap X R (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd R R
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [X] using hComp
  have hNextSucc :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => Nat.succ p.1.1) := by
    have hComp := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hNext
    simpa [Function.comp] using hComp
  have hCtxUpdatedOld :
      TMPolyTimeMap X R (fun p : X.Carrier => p.1.2.1.map vertexPairRightSucc) := by
    have hMap := TMPolyTimeMap.list_map vertexPairRightSucc_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hCtx
    simpa [Function.comp, R, vertexPairListEncodedType] using hComp
  have hNewCtxEntry :
      TMPolyTimeMap X vertexPairEncodedType
        (fun p : X.Carrier => ((p.1.1 : Nat), Nat.succ (p.1.1 : Nat))) :=
    TMPolyTimeMap.prod_mk hNext hNextSucc
  have hNewCtxSingleton :
      TMPolyTimeMap X R
        (fun p : X.Carrier => [((p.1.1 : Nat), Nat.succ (p.1.1 : Nat))]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton vertexPairEncodedType)
      hNewCtxEntry
    simpa [Function.comp, R, vertexPairListEncodedType] using hComp
  have hNextCtxInput :
      TMPolyTimeMap X (EncodedType.prod R R)
        (fun p : X.Carrier =>
          ((p.1.2.1 : List (Nat × Nat)).map vertexPairRightSucc,
            [((p.1.1 : Nat), Nat.succ (p.1.1 : Nat))])) :=
    TMPolyTimeMap.prod_mk hCtxUpdatedOld hNewCtxSingleton
  have hNextCtx :
      TMPolyTimeMap X R
        (fun p : X.Carrier =>
          List.append ((p.1.2.1 : List (Nat × Nat)).map vertexPairRightSucc)
            ([((p.1.1 : Nat), Nat.succ (p.1.1 : Nat))] : List (Nat × Nat))) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append vertexPairEncodedType)
      hNextCtxInput
    simpa [Function.comp, R, vertexPairListEncodedType] using hComp
  have hPairsCtxInput :
      TMPolyTimeMap X (EncodedType.prod R R)
        (fun p : X.Carrier => (p.1.2.2, p.1.2.1)) :=
    TMPolyTimeMap.prod_mk hPairs hCtx
  have hPairsCtx :
      TMPolyTimeMap X R
        (fun p : X.Carrier =>
          List.append (p.1.2.2 : List (Nat × Nat))
            (p.1.2.1 : List (Nat × Nat))) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append vertexPairEncodedType)
      hPairsCtxInput
    simpa [Function.comp, R, vertexPairListEncodedType] using hComp
  have hOutPayload :
      TMPolyTimeMap X (EncodedType.prod R R)
        (fun p : X.Carrier =>
          (List.append ((p.1.2.1 : List (Nat × Nat)).map vertexPairRightSucc)
              ([((p.1.1 : Nat), Nat.succ (p.1.1 : Nat))] : List (Nat × Nat)),
            List.append (p.1.2.2 : List (Nat × Nat))
              (p.1.2.1 : List (Nat × Nat)))) :=
    TMPolyTimeMap.prod_mk hNextCtx hPairsCtx
  have hOut :=
    TMPolyTimeMap.prod_mk hNextSucc hOutPayload
  convert hOut using 1

noncomputable def strictNatPairCandidatesFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod strictNatPairCandidatesAccEncodedType (EncodedType.raw Unit)).encode
        strictNatPairCandidatesAccEncodedType.encode
        strictNatPairCandidatesBuilderStep) :
    Polynomial Nat :=
  let bound :=
    Polynomial.C 10 *
      ((Polynomial.X + Polynomial.C 2) *
        (Polynomial.X + Polynomial.C 2) *
        (Polynomial.X + Polynomial.C 2)) +
      Polynomial.C 20
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm bound
    (hStep.time.comp (bound + Polynomial.X + Polynomial.C 5))

theorem strictNatPairCandidatesFold_loopTime_le
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod strictNatPairCandidatesAccEncodedType (EncodedType.raw Unit)).encode
        strictNatPairCandidatesAccEncodedType.encode
        strictNatPairCandidatesBuilderStep)
    (source : List Unit) :
    2 +
      TM2Programs.listFoldTypedLoopTime
        (EncodedType.raw Unit) strictNatPairCandidatesAccEncodedType
        strictNatPairCandidatesBuilderStep hStep
        strictNatPairCandidatesBuilderInit source ≤
        (strictNatPairCandidatesFoldTimePolynomial hStep).eval
          (rawUnitListEncodedType.inputSize source) := by
  let X := EncodedType.raw Unit
  let Y := strictNatPairCandidatesAccEncodedType
  let N := rawUnitListEncodedType.inputSize source
  let bound : Polynomial Nat :=
    Polynomial.C 10 *
      ((Polynomial.X + Polynomial.C 2) *
        (Polynomial.X + Polynomial.C 2) *
        (Polynomial.X + Polynomial.C 2)) +
      Polynomial.C 20
  let B := bound.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hBoundEval :
      B = 10 * ((N + 2) * (N + 2) * (N + 2)) + 20 := by
    simp [B, bound, Polynomial.eval_add, Polynomial.eval_mul]
  have hLoopAux :
      ∀ (rest : List Unit) (m : Nat),
        m + rawUnitListEncodedType.inputSize rest = N →
          TM2Programs.listFoldTypedLoopTime
            X Y strictNatPairCandidatesBuilderStep hStep
              (strictNatPairCandidatesAcc m) rest ≤
            C * rawUnitListEncodedType.inputSize rest := by
    intro rest
    induction rest with
    | nil =>
        intro m _h
        simp [TM2Programs.listFoldTypedLoopTime, rawUnitList_inputSize_eq_length]
    | cons u rest ih =>
        intro m hRest
        have hmN : m ≤ N := by
          omega
        have hmSuccN : m + 1 ≤ N := by
          rw [rawUnitList_inputSize_eq_length] at hRest
          simp at hRest
          omega
        have hRestTail : (m + 1) + rawUnitListEncodedType.inputSize rest = N := by
          rw [rawUnitList_inputSize_eq_length] at hRest ⊢
          simp at hRest ⊢
          omega
        have hAcc :
            Y.inputSize (strictNatPairCandidatesAcc m) ≤ B := by
          have hBase := strictNatPairCandidatesAcc_inputSize_le m
          exact hBase.trans (by
            rw [hBoundEval]
            exact natPairCandidatesCubicBound_mono hmN)
        have hNext :
            Y.inputSize
                (strictNatPairCandidatesBuilderStep
                  (strictNatPairCandidatesAcc m, u)) ≤ B := by
          rw [strictNatPairCandidatesBuilderStep_acc m u]
          have hBase := strictNatPairCandidatesAcc_inputSize_le (m + 1)
          exact hBase.trans (by
            rw [hBoundEval]
            exact natPairCandidatesCubicBound_mono hmSuccN)
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod Y X).inputSize
                  (strictNatPairCandidatesAcc m, u)) ≤ T := by
          have hArg :
              (EncodedType.prod Y X).inputSize
                  (strictNatPairCandidatesAcc m, u) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change Y.inputSize (strictNatPairCandidatesAcc m) + 1 + X.inputSize u ≤
              B + N + 5
            have hx : X.inputSize u = 0 := by rfl
            rw [hx]
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm (X.encode u).length
                (Y.encode (strictNatPairCandidatesAcc m)).length
                (Y.encode
                  (strictNatPairCandidatesBuilderStep
                    (strictNatPairCandidatesAcc m, u))).length
                (hStep.time.eval
                  ((EncodedType.prod Y X).inputSize
                    (strictNatPairCandidatesAcc m, u))) ≤
              C * (X.inputSize u + 1) := by
          exact
            TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
              (by simpa [Y, EncodedType.inputSize] using hAcc)
              (by simpa [Y, EncodedType.inputSize] using hNext)
              hStepTime
        have hTail :=
          ih (m + 1) hRestTail
        calc
          TM2Programs.listFoldTypedLoopTime X Y strictNatPairCandidatesBuilderStep hStep
              (strictNatPairCandidatesAcc m) (u :: rest)
              =
            TM2Programs.listFoldTypedLoopTime X Y strictNatPairCandidatesBuilderStep hStep
              (strictNatPairCandidatesBuilderStep
                (strictNatPairCandidatesAcc m, u)) rest +
              TM2Programs.listFoldBlockTime hStep.tm (X.encode u).length
                (Y.encode (strictNatPairCandidatesAcc m)).length
                (Y.encode
                  (strictNatPairCandidatesBuilderStep
                    (strictNatPairCandidatesAcc m, u))).length
                (hStep.time.eval
                  ((EncodedType.prod Y X).inputSize
                    (strictNatPairCandidatesAcc m, u))) := by
                rfl
          _ =
            TM2Programs.listFoldTypedLoopTime X Y strictNatPairCandidatesBuilderStep hStep
              (strictNatPairCandidatesAcc (m + 1)) rest +
              TM2Programs.listFoldBlockTime hStep.tm (X.encode u).length
                (Y.encode (strictNatPairCandidatesAcc m)).length
                (Y.encode
                  (strictNatPairCandidatesBuilderStep
                    (strictNatPairCandidatesAcc m, u))).length
                (hStep.time.eval
                  ((EncodedType.prod Y X).inputSize
                    (strictNatPairCandidatesAcc m, u))) := by
                rw [strictNatPairCandidatesBuilderStep_acc m u]
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
        X Y strictNatPairCandidatesBuilderStep hStep
          strictNatPairCandidatesBuilderInit source ≤ C * N := by
    simpa [X, Y, strictNatPairCandidatesBuilderInit, N] using
      hLoopAux source 0 (by simp [N])
  have hTimeEval :
      (strictNatPairCandidatesFoldTimePolynomial hStep).eval N = (C + 2) * (N + 1) := by
    simp [strictNatPairCandidatesFoldTimePolynomial, bound, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp]
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem strictNatPairCandidatesFold_tm_polytime :
    TMPolyTimeMap
      rawUnitListEncodedType
      strictNatPairCandidatesAccEncodedType
      (fun xs : List Unit =>
        xs.foldl
          (fun acc x => strictNatPairCandidatesBuilderStep (acc, x))
          strictNatPairCandidatesBuilderInit) := by
  rcases strictNatPairCandidatesBuilderStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed
      (EncodedType.raw Unit) strictNatPairCandidatesAccEncodedType
      strictNatPairCandidatesBuilderStep strictNatPairCandidatesBuilderInit hStep
      (strictNatPairCandidatesFoldTimePolynomial hStep) ?_
  intro source
  exact strictNatPairCandidatesFold_loopTime_le hStep source

theorem strictNatPairCandidatesFromUnits_tm_polytime :
    TMPolyTimeMap
      rawUnitListEncodedType
      vertexPairListEncodedType
      strictNatPairCandidatesFromUnits := by
  have hFold := strictNatPairCandidatesFold_tm_polytime
  have hPayload :=
    TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod vertexPairListEncodedType vertexPairListEncodedType)
  have hPairs := TMPolyTimeMap.snd vertexPairListEncodedType vertexPairListEncodedType
  have hPayloadComp := TMPolyTimeMap.comp hPayload hFold
  have hPairsComp := TMPolyTimeMap.comp hPairs hPayloadComp
  simpa [Function.comp, strictNatPairCandidatesFromUnits,
    strictNatPairCandidatesAccEncodedType, natPairCandidatesAccEncodedType] using hPairsComp

noncomputable def strictNatPairCandidatesFromUnitsTMBackedMap :
    TMBackedCostedMap
      rawUnitListEncodedType
      vertexPairListEncodedType
      strictNatPairCandidatesFromUnits where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      strictNatPairCandidatesFromUnits_polynomialSizeBound
  tm_polytime := strictNatPairCandidatesFromUnits_tm_polytime

theorem strictNatPairCandidates_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      vertexPairListEncodedType
      strictNatPairCandidates := by
  have hComp :=
    TMPolyTimeMap.comp strictNatPairCandidatesFromUnits_tm_polytime
      natToRawUnitListTMBackedMap.tm_polytime
  convert hComp using 1

noncomputable def strictNatPairCandidatesTMBackedMap :
    TMBackedCostedMap
      EncodedType.nat
      vertexPairListEncodedType
      strictNatPairCandidates where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound strictNatPairCandidates_polynomialSizeBound
  tm_polytime := strictNatPairCandidates_tm_polytime

end Karp21
end ComplexityReduction
