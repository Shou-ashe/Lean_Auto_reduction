/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.SplitWith.RunnerStepChoice

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction
open Turing.TM2.Stmt

def splitWithTraceRunnerInit : splitWithTraceLoopAccEncodedType.Carrier :=
  ([], ((0 : Nat), []))

def splitWithTraceRunnerStep
    (p : splitWithTraceLoopAccEncodedType.Carrier ×
      splitWithTraceRunnerInstructionEncodedType.Carrier) :
    splitWithTraceLoopAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl input => ([], input)
  | Sum.inr _ => splitWithTraceLoopAccStep p.1

theorem splitWithTraceRunnerStep_eq_dispatch_choice
    (p : splitWithTraceLoopAccEncodedType.Carrier ×
      splitWithTraceRunnerInstructionEncodedType.Carrier) :
    splitWithTraceRunnerStep p =
      splitWithTraceRunnerStepChoiceDispatch (splitWithTraceRunnerStepChoice p) := by
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem splitWithTraceRunnerStep_inputSize_le
    (p : splitWithTraceLoopAccEncodedType.Carrier ×
      splitWithTraceRunnerInstructionEncodedType.Carrier) :
    splitWithTraceLoopAccEncodedType.inputSize (splitWithTraceRunnerStep p) ≤
      3 *
        (EncodedType.prod
          splitWithTraceLoopAccEncodedType
          splitWithTraceRunnerInstructionEncodedType).inputSize p + 34 := by
  rw [splitWithTraceRunnerStep_eq_dispatch_choice]
  have hChoice := splitWithTraceRunnerStepChoice_inputSize_le p
  have hDispatch :=
    splitWithTraceRunnerStepChoiceDispatch_inputSize_le (splitWithTraceRunnerStepChoice p)
  omega

noncomputable def splitWithTraceRunnerStepTMBackedMap :
    TMBackedCostedMap
      (EncodedType.prod
        splitWithTraceLoopAccEncodedType
        splitWithTraceRunnerInstructionEncodedType)
      splitWithTraceLoopAccEncodedType
      splitWithTraceRunnerStep where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := EncodedType.prod
        splitWithTraceLoopAccEncodedType
        splitWithTraceRunnerInstructionEncodedType)
      (Y := splitWithTraceLoopAccEncodedType)
      (LinearSizeBound.intro_with 3 34 (by
        intro p
        exact splitWithTraceRunnerStep_inputSize_le p))
  tm_polytime := by
    have hChoice :
        TMPolyTimeMap
          (EncodedType.prod
            splitWithTraceLoopAccEncodedType
            splitWithTraceRunnerInstructionEncodedType)
          splitWithTraceRunnerStepChoiceEncodedType
          splitWithTraceRunnerStepChoice :=
      splitWithTraceRunnerStepChoiceTMBackedMap.tm_polytime
    have hDispatch :
        TMPolyTimeMap
          splitWithTraceRunnerStepChoiceEncodedType
          splitWithTraceLoopAccEncodedType
          splitWithTraceRunnerStepChoiceDispatch :=
      splitWithTraceRunnerStepChoiceDispatchTMBackedMap.tm_polytime
    have hStep :
        TMPolyTimeMap
          (EncodedType.prod
            splitWithTraceLoopAccEncodedType
            splitWithTraceRunnerInstructionEncodedType)
          splitWithTraceLoopAccEncodedType
          (splitWithTraceRunnerStepChoiceDispatch ∘ splitWithTraceRunnerStepChoice) :=
      TMPolyTimeMap.comp hDispatch hChoice
    convert hStep using 1
    funext p
    exact splitWithTraceRunnerStep_eq_dispatch_choice p

def splitWithTraceRunnerFold
    (p : splitWithInputEncodedType.Carrier) :
    splitWithTraceLoopAccEncodedType.Carrier :=
  (splitWithTraceRunnerInstructions p).foldl
    (fun acc instr => splitWithTraceRunnerStep (acc, instr))
    splitWithTraceRunnerInit

theorem splitWithTraceRunnerFuel_fold_eq_iterate
    (fuel : List Unit) (a : splitWithTraceLoopAccEncodedType.Carrier) :
    (fuel.map
        (fun _ : Unit => (Sum.inr () : splitWithTraceRunnerInstructionEncodedType.Carrier))).foldl
        (fun acc instr => splitWithTraceRunnerStep (acc, instr)) a =
      splitWithTraceLoopAccIterate fuel.length a := by
  induction fuel generalizing a with
  | nil =>
      rfl
  | cons _ rest ih =>
      simpa [splitWithTraceRunnerStep, splitWithTraceLoopAccIterate] using
        ih (splitWithTraceLoopAccStep a)

theorem splitWithTraceRunnerFold_eq_iterate
    (p : splitWithInputEncodedType.Carrier) :
    splitWithTraceRunnerFold p =
      splitWithTraceLoopAccIterate p.2.length (([] : List splitWithLongHeadCoreEncodedType.Carrier), p) := by
  rcases p with ⟨next, c⟩
  simp [splitWithTraceRunnerFold, splitWithTraceRunnerInstructions, splitWithTraceRunnerStep,
    splitWithTraceRunnerInit]
  simpa [List.map_map] using
    splitWithTraceRunnerFuel_fold_eq_iterate
      (c.map fun _ => ()) (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c))

theorem splitWithTraceRunnerInstructions_inputSize_ge_inputSize
    (p : splitWithInputEncodedType.Carrier) :
    splitWithInputEncodedType.inputSize p ≤
      (EncodedType.list splitWithTraceRunnerInstructionEncodedType).inputSize
        (splitWithTraceRunnerInstructions p) := by
  rcases p with ⟨next, c⟩
  rw [splitWithTraceRunnerInstructions, EncodedType.inputSize_list_cons]
  have hInit :
      splitWithTraceRunnerInstructionEncodedType.inputSize
          (Sum.inl (next, c) : splitWithTraceRunnerInstructionEncodedType.Carrier) =
        splitWithInputEncodedType.inputSize (next, c) + 1 := by
    simp [splitWithTraceRunnerInstructionEncodedType, splitWithTraceRunnerFuelEncodedType,
      EncodedType.inputSize, EncodedType.sum]
  rw [hInit]
  omega

theorem splitWithTraceRunnerInstructions_inputSize_ge_clause_length
    (p : splitWithInputEncodedType.Carrier) :
    p.2.length ≤
      (EncodedType.list splitWithTraceRunnerInstructionEncodedType).inputSize
        (splitWithTraceRunnerInstructions p) := by
  have hInput := splitWithTraceRunnerInstructions_inputSize_ge_inputSize p
  have hInputClause :
      p.2.length ≤ splitWithInputEncodedType.inputSize p := by
    rcases p with ⟨next, c⟩
    have hClauseLen : c.length ≤ clauseStructuredEncodedType.inputSize c := by
      clear hInput next
      induction c with
      | nil =>
          simp [clauseStructuredEncodedType, EncodedType.inputSize, EncodedType.list]
      | cons l rest ih =>
          change rest.length ≤
            (EncodedType.list literalStructuredEncodedType).inputSize rest at ih
          change (l :: rest).length ≤
            (EncodedType.list literalStructuredEncodedType).inputSize (l :: rest)
          rw [EncodedType.inputSize_list_cons]
          simp
          omega
    change c.length ≤
      (EncodedType.prod EncodedType.nat clauseStructuredEncodedType).inputSize (next, c)
    rw [EncodedType.inputSize_prod]
    simp [EncodedType.nat]
    omega
  omega

theorem splitWithTraceRunnerFold_inputSize_le
    (p : splitWithInputEncodedType.Carrier) :
    splitWithTraceLoopAccEncodedType.inputSize (splitWithTraceRunnerFold p) ≤
      20 *
          ((EncodedType.list splitWithTraceRunnerInstructionEncodedType).inputSize
            (splitWithTraceRunnerInstructions p)) ^ 2 +
        20 := by
  rcases p with ⟨next, c⟩
  change Nat at next
  let N :=
    (EncodedType.list splitWithTraceRunnerInstructionEncodedType).inputSize
      (splitWithTraceRunnerInstructions (next, c))
  have hFold := splitWithTraceRunnerFold_eq_iterate (next, c)
  have hIter :=
    splitWithTraceLoopAccIterate_inputSize_le c.length
      (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c))
  have hInputLeN := splitWithTraceRunnerInstructions_inputSize_ge_inputSize (next, c)
  have hLenLeN := splitWithTraceRunnerInstructions_inputSize_ge_clause_length (next, c)
  have hNextLeN : next ≤ N := by
    have hNextInput : next ≤ splitWithInputEncodedType.inputSize (next, c) := by
      simp [splitWithInputEncodedType, EncodedType.inputSize, EncodedType.prod,
        EncodedType.nat]
    omega
  have hInitSize :
      splitWithTraceLoopAccEncodedType.inputSize
          (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c)) ≤ N + 1 := by
    change
      (EncodedType.prod (EncodedType.list splitWithLongHeadCoreEncodedType)
        splitWithInputEncodedType).inputSize
          (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c)) ≤ N + 1
    rw [EncodedType.inputSize_prod, EncodedType.inputSize_list_nil]
    change 0 + 1 + splitWithInputEncodedType.inputSize (next, c) ≤ N + 1
    omega
  rw [hFold]
  calc
    splitWithTraceLoopAccEncodedType.inputSize
        (splitWithTraceLoopAccIterate c.length
          (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c)))
        ≤ splitWithTraceLoopAccEncodedType.inputSize
            (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c)) +
          c.length *
            (2 *
                (splitWithTraceLoopAccNext
                    (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c)) +
                  c.length) +
              10) := hIter
    _ ≤ (N + 1) + N * (2 * (N + N) + 10) := by
          change
            splitWithTraceLoopAccEncodedType.inputSize
                (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c)) +
              c.length * (2 * (next + c.length) + 10) ≤
                (N + 1) + N * (2 * (N + N) + 10)
          nlinarith [hInitSize, hLenLeN, hNextLeN]
    _ ≤ 20 * N ^ 2 + 20 := by
          nlinarith [sq_nonneg (N : Int)]

noncomputable def splitWithTraceRunnerFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.C 20 * (Polynomial.X * Polynomial.X) + Polynomial.C 20

@[simp] theorem splitWithTraceRunnerFoldAccBoundPolynomial_eval (n : Nat) :
    splitWithTraceRunnerFoldAccBoundPolynomial.eval n = 20 * (n * n) + 20 := by
  simp [splitWithTraceRunnerFoldAccBoundPolynomial, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_X]

theorem splitWithTraceLoopAccIterate_prefix_inputSize_le
    (next : Nat) (c : SAT.Clause) (k : Nat) (hk : k ≤ c.length) :
    splitWithTraceLoopAccEncodedType.inputSize
        (splitWithTraceLoopAccIterate k
          (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c))) ≤
      splitWithTraceRunnerFoldAccBoundPolynomial.eval
        ((EncodedType.list splitWithTraceRunnerInstructionEncodedType).inputSize
          (splitWithTraceRunnerInstructions (next, c))) := by
  let N :=
    (EncodedType.list splitWithTraceRunnerInstructionEncodedType).inputSize
      (splitWithTraceRunnerInstructions (next, c))
  have hIter :=
    splitWithTraceLoopAccIterate_inputSize_le k
      (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c))
  have hInputLeN := splitWithTraceRunnerInstructions_inputSize_ge_inputSize (next, c)
  have hLenLeN := splitWithTraceRunnerInstructions_inputSize_ge_clause_length (next, c)
  have hLenLeN' : c.length ≤ N := by
    simpa [N] using hLenLeN
  have hkN : k ≤ N := by omega
  have hNextLeN : next ≤ N := by
    have hNextInput : next ≤ splitWithInputEncodedType.inputSize (next, c) := by
      simp [splitWithInputEncodedType, EncodedType.inputSize, EncodedType.prod,
        EncodedType.nat]
    omega
  have hInitSize :
      splitWithTraceLoopAccEncodedType.inputSize
          (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c)) ≤ N + 1 := by
    change
      (EncodedType.prod (EncodedType.list splitWithLongHeadCoreEncodedType)
        splitWithInputEncodedType).inputSize
          (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c)) ≤ N + 1
    rw [EncodedType.inputSize_prod, EncodedType.inputSize_list_nil]
    change 0 + 1 + splitWithInputEncodedType.inputSize (next, c) ≤ N + 1
    omega
  calc
    splitWithTraceLoopAccEncodedType.inputSize
        (splitWithTraceLoopAccIterate k
          (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c)))
        ≤ splitWithTraceLoopAccEncodedType.inputSize
            (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c)) +
          k *
            (2 *
                (splitWithTraceLoopAccNext
                    (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c)) +
                  k) +
              10) := hIter
    _ ≤ (N + 1) + N * (2 * (N + N) + 10) := by
          change
            splitWithTraceLoopAccEncodedType.inputSize
                (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c)) +
              k * (2 * (next + k) + 10) ≤
                (N + 1) + N * (2 * (N + N) + 10)
          nlinarith [hInitSize, hkN, hNextLeN]
    _ ≤ splitWithTraceRunnerFoldAccBoundPolynomial.eval N := by
          simp
          nlinarith [sq_nonneg (N : Int)]

theorem splitWithTraceRunnerFuel_loopTime_le
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod
          splitWithTraceLoopAccEncodedType
          splitWithTraceRunnerInstructionEncodedType).encode
        splitWithTraceLoopAccEncodedType.encode
        splitWithTraceRunnerStep)
    (fuel : List Unit) (a : splitWithTraceLoopAccEncodedType.Carrier) (B T : Nat)
    (hAcc : ∀ k, k ≤ fuel.length →
      splitWithTraceLoopAccEncodedType.inputSize (splitWithTraceLoopAccIterate k a) ≤ B)
    (hStepTime : ∀ b : splitWithTraceLoopAccEncodedType.Carrier,
      splitWithTraceLoopAccEncodedType.inputSize b ≤ B →
        hStep.time.eval
            ((EncodedType.prod
              splitWithTraceLoopAccEncodedType
              splitWithTraceRunnerInstructionEncodedType).inputSize (b, Sum.inr ())) ≤ T) :
    TM2Programs.listFoldTypedLoopTime
        splitWithTraceRunnerInstructionEncodedType
        splitWithTraceLoopAccEncodedType
        splitWithTraceRunnerStep hStep a
        (fuel.map (fun _ => (Sum.inr () : splitWithTraceRunnerInstructionEncodedType.Carrier))) ≤
      TM2Programs.listFoldBlockTimeCoeff hStep.tm B T *
        TM2Programs.listFoldSourceLength splitWithTraceRunnerInstructionEncodedType.encode
          (fuel.map
            (fun _ => (Sum.inr () : splitWithTraceRunnerInstructionEncodedType.Carrier))) := by
  induction fuel generalizing a with
  | nil =>
      simp [TM2Programs.listFoldTypedLoopTime, TM2Programs.listFoldSourceLength]
  | cons _ rest ih =>
      have hAcc0 : splitWithTraceLoopAccEncodedType.inputSize a ≤ B := by
        simpa [splitWithTraceLoopAccIterate] using hAcc 0 (by simp)
      have hAcc1 :
          splitWithTraceLoopAccEncodedType.inputSize (splitWithTraceLoopAccStep a) ≤ B := by
        simpa [splitWithTraceLoopAccIterate] using hAcc 1 (by simp)
      have hTailAcc : ∀ k, k ≤ rest.length →
          splitWithTraceLoopAccEncodedType.inputSize
              (splitWithTraceLoopAccIterate k (splitWithTraceLoopAccStep a)) ≤ B := by
        intro k hk
        have hk' : k + 1 ≤ (Unit.unit :: rest).length := by
          simp
          omega
        simpa [splitWithTraceLoopAccIterate] using hAcc (k + 1) hk'
      have hTail :=
        ih (splitWithTraceLoopAccStep a) hTailAcc
      have hBlock :
          TM2Programs.listFoldBlockTime hStep.tm
              (splitWithTraceRunnerInstructionEncodedType.encode
                (Sum.inr () : splitWithTraceRunnerInstructionEncodedType.Carrier)).length
              (splitWithTraceLoopAccEncodedType.encode a).length
              (splitWithTraceLoopAccEncodedType.encode
                (splitWithTraceRunnerStep (a,
                  (Sum.inr () : splitWithTraceRunnerInstructionEncodedType.Carrier)))).length
              (hStep.time.eval
                ((EncodedType.prod
                  splitWithTraceLoopAccEncodedType
                  splitWithTraceRunnerInstructionEncodedType).inputSize
                    (a, Sum.inr ()))) ≤
            TM2Programs.listFoldBlockTimeCoeff hStep.tm B T *
              ((splitWithTraceRunnerInstructionEncodedType.encode
                (Sum.inr () : splitWithTraceRunnerInstructionEncodedType.Carrier)).length + 1) := by
        exact
          TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
            (by simpa [EncodedType.inputSize] using hAcc0)
            (by simpa [splitWithTraceRunnerStep, EncodedType.inputSize] using hAcc1)
            (hStepTime a hAcc0)
      simp [TM2Programs.listFoldTypedLoopTime, TM2Programs.listFoldSourceLength,
        splitWithTraceRunnerStep] at hTail hBlock ⊢
      nlinarith [hTail, hBlock]

noncomputable def splitWithTraceRunnerFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod
          splitWithTraceLoopAccEncodedType
          splitWithTraceRunnerInstructionEncodedType).encode
        splitWithTraceLoopAccEncodedType.encode
        splitWithTraceRunnerStep) : Polynomial Nat :=
  let B := splitWithTraceRunnerFoldAccBoundPolynomial
  let T := hStep.time.comp (B + Polynomial.X + Polynomial.C 2)
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm B T

theorem splitWithTraceRunnerFold_loopTime_le
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod
          splitWithTraceLoopAccEncodedType
          splitWithTraceRunnerInstructionEncodedType).encode
        splitWithTraceLoopAccEncodedType.encode
        splitWithTraceRunnerStep)
    (p : splitWithTraceRunnerInstructionsImageEncodedType.Carrier) :
    2 +
        TM2Programs.listFoldTypedLoopTime
          splitWithTraceRunnerInstructionEncodedType
          splitWithTraceLoopAccEncodedType
          splitWithTraceRunnerStep hStep splitWithTraceRunnerInit
          (splitWithTraceRunnerInstructions p) ≤
      (splitWithTraceRunnerFoldTimePolynomial hStep).eval
        (splitWithTraceRunnerInstructionsImageEncodedType.inputSize p) := by
  rcases p with ⟨next, c⟩
  change Nat at next
  let fuel : List Unit := List.replicate c.length ()
  let instrFuel : List splitWithTraceRunnerInstructionEncodedType.Carrier :=
    fuel.map fun _ => (Sum.inr () : splitWithTraceRunnerInstructionEncodedType.Carrier)
  let first : splitWithTraceRunnerInstructionEncodedType.Carrier := Sum.inl (next, c)
  let N :=
    (EncodedType.list splitWithTraceRunnerInstructionEncodedType).inputSize
      (splitWithTraceRunnerInstructions (next, c))
  let B := splitWithTraceRunnerFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 2)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hImageSize :
      splitWithTraceRunnerInstructionsImageEncodedType.inputSize (next, c) = N := rfl
  have hInputLeN := splitWithTraceRunnerInstructions_inputSize_ge_inputSize (next, c)
  have hFuelAcc : ∀ k, k ≤ fuel.length →
      splitWithTraceLoopAccEncodedType.inputSize
        (splitWithTraceLoopAccIterate k
          (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c))) ≤ B := by
    intro k hk
    have hk' : k ≤ c.length := by
      simpa [fuel] using hk
    simpa [B, N] using splitWithTraceLoopAccIterate_prefix_inputSize_le next c k hk'
  have hInitAcc :
      splitWithTraceLoopAccEncodedType.inputSize splitWithTraceRunnerInit ≤ B := by
    simp [splitWithTraceRunnerInit, splitWithTraceLoopAccEncodedType,
      splitWithInputEncodedType, EncodedType.inputSize, EncodedType.prod,
      EncodedType.list, EncodedType.nat, clauseStructuredEncodedType, B]
  have hAfterInit :
      splitWithTraceLoopAccEncodedType.inputSize
        (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c)) ≤ B := by
    simpa [fuel, splitWithTraceLoopAccIterate] using hFuelAcc 0 (by simp)
  have hRightStepTime : ∀ b : splitWithTraceLoopAccEncodedType.Carrier,
      splitWithTraceLoopAccEncodedType.inputSize b ≤ B →
        hStep.time.eval
            ((EncodedType.prod
              splitWithTraceLoopAccEncodedType
              splitWithTraceRunnerInstructionEncodedType).inputSize (b, Sum.inr ())) ≤ T := by
    intro b hb
    have hInstr :
        splitWithTraceRunnerInstructionEncodedType.inputSize
            (Sum.inr () : splitWithTraceRunnerInstructionEncodedType.Carrier) ≤ N + 1 := by
      simp [splitWithTraceRunnerInstructionEncodedType, splitWithTraceRunnerFuelEncodedType,
        EncodedType.inputSize, EncodedType.sum, EncodedType.raw]
    have hArg :
        (EncodedType.prod
          splitWithTraceLoopAccEncodedType
          splitWithTraceRunnerInstructionEncodedType).inputSize (b, Sum.inr ()) ≤
          B + N + 2 := by
      rw [EncodedType.inputSize_prod]
      nlinarith
    exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
  have hFuelLoop :=
    splitWithTraceRunnerFuel_loopTime_le hStep fuel
      (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c)) B T
      hFuelAcc hRightStepTime
  have hFirstInstrSize :
      splitWithTraceRunnerInstructionEncodedType.inputSize first ≤ N := by
    have hN :
        N =
          splitWithTraceRunnerInstructionEncodedType.inputSize first + 1 +
            (EncodedType.list splitWithTraceRunnerInstructionEncodedType).inputSize
              instrFuel := by
      simp [N, first, instrFuel, fuel, splitWithTraceRunnerInstructions]
    omega
  have hFirstStepTime :
      hStep.time.eval
          ((EncodedType.prod
            splitWithTraceLoopAccEncodedType
            splitWithTraceRunnerInstructionEncodedType).inputSize
              (splitWithTraceRunnerInit, first)) ≤ T := by
    have hArg :
        (EncodedType.prod
          splitWithTraceLoopAccEncodedType
          splitWithTraceRunnerInstructionEncodedType).inputSize
            (splitWithTraceRunnerInit, first) ≤ B + N + 2 := by
      rw [EncodedType.inputSize_prod]
      nlinarith [hInitAcc, hFirstInstrSize]
    exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
  have hFirstBlock :
      TM2Programs.listFoldBlockTime hStep.tm
          (splitWithTraceRunnerInstructionEncodedType.encode first).length
          (splitWithTraceLoopAccEncodedType.encode splitWithTraceRunnerInit).length
          (splitWithTraceLoopAccEncodedType.encode
            (splitWithTraceRunnerStep (splitWithTraceRunnerInit, first))).length
          (hStep.time.eval
            ((EncodedType.prod
              splitWithTraceLoopAccEncodedType
              splitWithTraceRunnerInstructionEncodedType).inputSize
                (splitWithTraceRunnerInit, first))) ≤
        C * ((splitWithTraceRunnerInstructionEncodedType.encode first).length + 1) := by
    exact
      TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
        (by simpa [EncodedType.inputSize] using hInitAcc)
        (by
          simpa [splitWithTraceRunnerStep, splitWithTraceRunnerInit, first,
            EncodedType.inputSize] using hAfterInit)
        hFirstStepTime
  have hInstrs :
      splitWithTraceRunnerInstructions (next, c) = first :: instrFuel := by
    simp [splitWithTraceRunnerInstructions, first, instrFuel, fuel]
  have hFuelLoop' :
      TM2Programs.listFoldTypedLoopTime
          splitWithTraceRunnerInstructionEncodedType
          splitWithTraceLoopAccEncodedType
          splitWithTraceRunnerStep hStep
          (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c))
          instrFuel ≤
        C * TM2Programs.listFoldSourceLength
          splitWithTraceRunnerInstructionEncodedType.encode instrFuel := by
    simpa [instrFuel] using hFuelLoop
  have hSource :
      N =
        (splitWithTraceRunnerInstructionEncodedType.encode first).length + 1 +
          TM2Programs.listFoldSourceLength splitWithTraceRunnerInstructionEncodedType.encode
            instrFuel := by
    calc
      N = (EncodedType.list splitWithTraceRunnerInstructionEncodedType).inputSize
            (first :: instrFuel) := by
              simp [N, hInstrs]
      _ = splitWithTraceRunnerInstructionEncodedType.inputSize first + 1 +
            (EncodedType.list splitWithTraceRunnerInstructionEncodedType).inputSize
              instrFuel := by
              rw [EncodedType.inputSize_list_cons]
      _ =
          (splitWithTraceRunnerInstructionEncodedType.encode first).length + 1 +
            TM2Programs.listFoldSourceLength splitWithTraceRunnerInstructionEncodedType.encode
              instrFuel := rfl
  have hLoop :
      TM2Programs.listFoldTypedLoopTime
          splitWithTraceRunnerInstructionEncodedType
          splitWithTraceLoopAccEncodedType
          splitWithTraceRunnerStep hStep splitWithTraceRunnerInit
          (splitWithTraceRunnerInstructions (next, c)) ≤
        C * N := by
    have hFirstStep :
        splitWithTraceRunnerStep (splitWithTraceRunnerInit, first) =
          (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c)) := by
      rfl
    calc
      TM2Programs.listFoldTypedLoopTime
          splitWithTraceRunnerInstructionEncodedType
          splitWithTraceLoopAccEncodedType
          splitWithTraceRunnerStep hStep splitWithTraceRunnerInit
          (splitWithTraceRunnerInstructions (next, c))
          =
        TM2Programs.listFoldTypedLoopTime
          splitWithTraceRunnerInstructionEncodedType
          splitWithTraceLoopAccEncodedType
          splitWithTraceRunnerStep hStep
          (splitWithTraceRunnerStep (splitWithTraceRunnerInit, first))
          instrFuel +
        TM2Programs.listFoldBlockTime hStep.tm
          (splitWithTraceRunnerInstructionEncodedType.encode first).length
          (splitWithTraceLoopAccEncodedType.encode splitWithTraceRunnerInit).length
          (splitWithTraceLoopAccEncodedType.encode
            (splitWithTraceRunnerStep (splitWithTraceRunnerInit, first))).length
          (hStep.time.eval
            ((EncodedType.prod
              splitWithTraceLoopAccEncodedType
              splitWithTraceRunnerInstructionEncodedType).inputSize
                (splitWithTraceRunnerInit, first))) := by
            rw [hInstrs]
            rfl
      _ =
        TM2Programs.listFoldTypedLoopTime
          splitWithTraceRunnerInstructionEncodedType
          splitWithTraceLoopAccEncodedType
          splitWithTraceRunnerStep hStep
          (([] : List splitWithLongHeadCoreEncodedType.Carrier), (next, c))
          instrFuel +
        TM2Programs.listFoldBlockTime hStep.tm
          (splitWithTraceRunnerInstructionEncodedType.encode first).length
          (splitWithTraceLoopAccEncodedType.encode splitWithTraceRunnerInit).length
          (splitWithTraceLoopAccEncodedType.encode
            (splitWithTraceRunnerStep (splitWithTraceRunnerInit, first))).length
          (hStep.time.eval
            ((EncodedType.prod
              splitWithTraceLoopAccEncodedType
              splitWithTraceRunnerInstructionEncodedType).inputSize
                (splitWithTraceRunnerInit, first))) := by
            rw [hFirstStep]
            rfl
      _ ≤ C *
            TM2Programs.listFoldSourceLength splitWithTraceRunnerInstructionEncodedType.encode
              instrFuel +
          C * ((splitWithTraceRunnerInstructionEncodedType.encode first).length + 1) :=
            Nat.add_le_add hFuelLoop' hFirstBlock
      _ ≤ C * N := by
            nlinarith [hSource, Nat.zero_le C]
  rw [hImageSize]
  have hTimeEval :
      (splitWithTraceRunnerFoldTimePolynomial hStep).eval N = (C + 2) * (N + 1) := by
    simp [splitWithTraceRunnerFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem splitWithTraceRunnerFoldImage_polynomialSizeBound :
    PolynomialSizeBound
      (fun p : splitWithTraceRunnerInstructionsImageEncodedType.Carrier =>
        splitWithTraceRunnerInstructionsImageEncodedType.inputSize p)
      (fun a : splitWithTraceLoopAccEncodedType.Carrier =>
        splitWithTraceLoopAccEncodedType.inputSize a)
      splitWithTraceRunnerFold := by
  refine PolynomialSizeBound.intro_with 2 20 20 ?_
  intro p
  simpa [splitWithTraceRunnerInstructionsImageEncodedType] using
    splitWithTraceRunnerFold_inputSize_le p

noncomputable def splitWithTraceRunnerFoldImageTMBackedMap :
    TMBackedCostedMap
      splitWithTraceRunnerInstructionsImageEncodedType
      splitWithTraceLoopAccEncodedType
      splitWithTraceRunnerFold where
  costed := CostedMap.of_encodedPolynomialSizeBound
    splitWithTraceRunnerFoldImage_polynomialSizeBound
  tm_polytime := by
    rcases splitWithTraceRunnerStepTMBackedMap.tm_polytime with ⟨hStep⟩
    let X := splitWithTraceRunnerInstructionEncodedType
    let Y := splitWithTraceLoopAccEncodedType
    refine ⟨?_⟩
    exact
      { tm :=
          TM2Programs.listFoldMachine X.Symbol Y.Symbol hStep.tm
            hStep.inputAlphabet.invFun hStep.outputAlphabet.toFun
            (Y.encode splitWithTraceRunnerInit)
        inputAlphabet := Equiv.refl (Option X.Symbol)
        outputAlphabet := Equiv.refl Y.Symbol
        time := splitWithTraceRunnerFoldTimePolynomial hStep
        outputsFun := by
          intro p
          let xs := splitWithTraceRunnerInstructions p
          let machine :=
            TM2Programs.listFoldMachine X.Symbol Y.Symbol hStep.tm
              hStep.inputAlphabet.invFun hStep.outputAlphabet.toFun
              (Y.encode splitWithTraceRunnerInit)
          have hRaw :=
            TM2Programs.listFoldTyped_outputsInTime X Y splitWithTraceRunnerStep
              splitWithTraceRunnerInit hStep xs
          have hTime :
              2 + TM2Programs.listFoldTypedLoopTime X Y splitWithTraceRunnerStep
                    hStep splitWithTraceRunnerInit xs ≤
                (splitWithTraceRunnerFoldTimePolynomial hStep).eval
                  (splitWithTraceRunnerInstructionsImageEncodedType.encode p).length := by
            simpa [X, Y, xs, splitWithTraceRunnerInstructionsImageEncodedType,
              EncodedType.inputSize] using
              splitWithTraceRunnerFold_loopTime_le hStep p
          have hMono := TM2Programs.evalsToInTime_mono hRaw hTime
          have hInput :
              List.map (Equiv.refl (Option X.Symbol)).invFun
                  (splitWithTraceRunnerInstructionsImageEncodedType.encode p) =
                (EncodedType.list X).encode xs := by
            change List.map id (splitWithTraceRunnerInstructionsImageEncodedType.encode p) =
              (EncodedType.list X).encode xs
            simp [X, xs, splitWithTraceRunnerInstructionsImageEncodedType]
          have hOutput :
              List.map (Equiv.refl Y.Symbol).invFun
                  (Y.encode (splitWithTraceRunnerFold p)) =
                Y.encode (xs.foldl (fun acc instr => splitWithTraceRunnerStep (acc, instr))
                  splitWithTraceRunnerInit) := by
            change List.map id (Y.encode (splitWithTraceRunnerFold p)) =
              Y.encode (xs.foldl (fun acc instr => splitWithTraceRunnerStep (acc, instr))
                splitWithTraceRunnerInit)
            rw [List.map_id]
            rfl
          unfold Turing.TM2OutputsInTime
          convert hMono using 1
          · exact congrArg (Turing.initList machine) hInput
          · exact congrArg (Option.map (Turing.haltList machine)) (congrArg some hOutput) }

def splitWithTraceLoopAccCurrentOutput
    (a : splitWithTraceLoopAccEncodedType.Carrier) :
    splitWithTraceOutputEncodedType.Carrier :=
  (a.1, a.2.2)

theorem splitWithTraceLoopAccCurrentOutput_inputSize_le
    (a : splitWithTraceLoopAccEncodedType.Carrier) :
    splitWithTraceOutputEncodedType.inputSize (splitWithTraceLoopAccCurrentOutput a) ≤
      splitWithTraceLoopAccEncodedType.inputSize a := by
  rcases a with ⟨heads, p⟩
  rcases p with ⟨next, c⟩
  simp [splitWithTraceLoopAccCurrentOutput, splitWithTraceOutputEncodedType,
    splitWithTraceLoopAccEncodedType, splitWithInputEncodedType, EncodedType.inputSize,
    EncodedType.prod]
  omega

noncomputable def splitWithTraceLoopAccCurrentOutputTMBackedMap :
    TMBackedCostedMap
      splitWithTraceLoopAccEncodedType
      splitWithTraceOutputEncodedType
      splitWithTraceLoopAccCurrentOutput where
  costed :=
    CostedMap.of_encodedLinearSizeBound
      (X := splitWithTraceLoopAccEncodedType)
      (Y := splitWithTraceOutputEncodedType)
      (LinearSizeBound.intro_with 1 0 (by
        intro a
        have h := splitWithTraceLoopAccCurrentOutput_inputSize_le a
        omega))
  tm_polytime := by
    let Heads := EncodedType.list splitWithLongHeadCoreEncodedType
    let Input := splitWithInputEncodedType
    let X := splitWithTraceLoopAccEncodedType
    have hHeads :
        TMPolyTimeMap X Heads (fun a : X.Carrier => a.1) :=
      TMPolyTimeMap.fst Heads Input
    have hInput :
        TMPolyTimeMap X Input (fun a : X.Carrier => a.2) :=
      TMPolyTimeMap.snd Heads Input
    have hClauseFromInput :
        TMPolyTimeMap Input clauseStructuredEncodedType
          (fun p : Input.Carrier => p.2) :=
      TMPolyTimeMap.snd EncodedType.nat clauseStructuredEncodedType
    have hClause :
        TMPolyTimeMap X clauseStructuredEncodedType (fun a : X.Carrier => a.2.2) :=
      TMPolyTimeMap.comp hClauseFromInput hInput
    have hPair :
        TMPolyTimeMap X splitWithTraceOutputEncodedType splitWithTraceLoopAccCurrentOutput :=
      TMPolyTimeMap.prod_mk hHeads hClause
    simpa [X, Heads, Input, splitWithTraceOutputEncodedType,
      splitWithTraceLoopAccEncodedType, splitWithTraceLoopAccCurrentOutput] using hPair

theorem splitWithTrace_eq_nil_heads_of_length_le_three
    (next : Nat) (c : SAT.Clause) (h : c.length ≤ 3) :
    splitWithTrace next c =
      (([] : List splitWithLongHeadCoreEncodedType.Carrier), c) := by
  simpa [splitWithShortTraceOutput] using
    splitWithTrace_eq_shortTraceOutput ⟨(next, c), h⟩

theorem splitWithTraceLoopAccCurrentOutput_eq_value_of_short
    (a : splitWithTraceLoopAccEncodedType.Carrier) (h : a.2.2.length ≤ 3) :
    splitWithTraceLoopAccCurrentOutput a = splitWithTraceLoopAccValue a := by
  rcases a with ⟨heads, p⟩
  rcases p with ⟨next, c⟩
  have hTrace := splitWithTrace_eq_nil_heads_of_length_le_three next c h
  simp [splitWithTraceLoopAccCurrentOutput, splitWithTraceLoopAccValue, hTrace]

theorem splitWithTraceRunnerFold_current_length_le_three
    (p : splitWithInputEncodedType.Carrier) :
    (splitWithTraceRunnerFold p).2.2.length ≤ 3 := by
  rw [splitWithTraceRunnerFold_eq_iterate]
  exact splitWithTraceLoopAccIterate_base_length_le_three
    ([] : List splitWithLongHeadCoreEncodedType.Carrier) p.1 p.2

theorem splitWithTraceRunnerFold_currentOutput_eq_trace
    (p : splitWithInputEncodedType.Carrier) :
    splitWithTraceLoopAccCurrentOutput (splitWithTraceRunnerFold p) =
      splitWithTrace p.1 p.2 := by
  have hShort := splitWithTraceRunnerFold_current_length_le_three p
  have hValue :=
    splitWithTraceLoopAccIterate_value p.2.length
      (([] : List splitWithLongHeadCoreEncodedType.Carrier), p)
  have hFold := splitWithTraceRunnerFold_eq_iterate p
  calc
    splitWithTraceLoopAccCurrentOutput (splitWithTraceRunnerFold p)
        = splitWithTraceLoopAccValue (splitWithTraceRunnerFold p) := by
          exact splitWithTraceLoopAccCurrentOutput_eq_value_of_short
            (splitWithTraceRunnerFold p) hShort
    _ = splitWithTraceLoopAccValue
          (([] : List splitWithLongHeadCoreEncodedType.Carrier), p) := by
          rw [hFold]
          exact hValue
    _ = splitWithTrace p.1 p.2 := by
          simp [splitWithTraceLoopAccValue]

theorem splitWithTrace_base_length_le_three (next : Nat) (c : SAT.Clause) :
    (splitWithTrace next c).2.length ≤ 3 := by
  fun_induction SAT.Clause.splitWith next c with
  | case1 next =>
      simp [splitWithTrace]
  | case2 next l1 =>
      simp [splitWithTrace]
  | case3 next l1 l2 =>
      simp [splitWithTrace]
  | case4 next l1 l2 l3 =>
      simp [splitWithTrace]
  | case5 next l1 l2 l3 l4 rest ih =>
      simpa [splitWithTrace, splitWithLongTailClause] using ih

theorem splitWithTrace_heads_length_le_clause_length (next : Nat) (c : SAT.Clause) :
    (splitWithTrace next c).1.length ≤ c.length := by
  fun_induction SAT.Clause.splitWith next c with
  | case1 next =>
      simp [splitWithTrace]
  | case2 next l1 =>
      simp [splitWithTrace]
  | case3 next l1 l2 =>
      simp [splitWithTrace]
  | case4 next l1 l2 l3 =>
      simp [splitWithTrace]
  | case5 next l1 l2 l3 l4 rest ih =>
      simpa [splitWithTrace, splitWithLongTailClause] using Nat.succ_le_succ ih

theorem splitWith_eq_traceCNF (next : Nat) (c : SAT.Clause) :
    SAT.Clause.splitWith next c =
      splitWithTraceCNF (splitWithTrace next c).1 (splitWithTrace next c).2 := by
  fun_induction SAT.Clause.splitWith next c with
  | case1 next =>
      simp [splitWithTrace, splitWithTraceCNF]
  | case2 next l1 =>
      simp [splitWithTrace, splitWithTraceCNF]
  | case3 next l1 l2 =>
      simp [splitWithTrace, splitWithTraceCNF]
  | case4 next l1 l2 l3 =>
      simp [splitWithTrace, splitWithTraceCNF]
  | case5 next l1 l2 l3 l4 rest ih =>
      simp [splitWithTrace, splitWithTraceCNF,
        splitWithLongHeadCons, splitWithLongHeadClause, splitWithLongTailClause, ih]

theorem splitWith_eq_traceOutputToCNF (next : Nat) (c : SAT.Clause) :
    SAT.Clause.splitWith next c =
      splitWithTraceOutputToCNF ((splitWithTrace next c).1, (splitWithTrace next c).2) := by
  rw [splitWith_eq_traceCNF next c]
  simpa [splitWithTraceOutputToCNF] using
    splitWithTraceCNF_eq_map_headClauses_append
      (splitWithTrace next c).1 (splitWithTrace next c).2


end Karp21
end ComplexityReduction
