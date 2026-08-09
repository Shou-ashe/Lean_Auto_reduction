/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetSystem
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Sum

/-!
Generic unary-index lookup for encoded lists.

The runner scans a list with a countdown index and returns a fixed fallback
outside the list, matching `List.getD`.  It is used by certificate verifiers
whose checked suffix certificate is a nat-list of indices into an encoded
source list.
-/

namespace ComplexityReduction
namespace Karp21

namespace EncodedListLookup

def accEncodedType (X : EncodedType) : EncodedType :=
  EncodedType.prod EncodedType.nat (EncodedType.prod EncodedType.bool X)

abbrev Acc (X : EncodedType) :=
  Nat × Bool × X.Carrier

def instructionEncodedType (X : EncodedType) : EncodedType :=
  EncodedType.sum EncodedType.nat X

def instructionListEncodedType (X : EncodedType) : EncodedType :=
  EncodedType.list (instructionEncodedType X)

def inputEncodedType (X : EncodedType) : EncodedType :=
  EncodedType.prod EncodedType.nat (EncodedType.list X)

def initAcc (X : EncodedType) (fallback : X.Carrier) : Acc X :=
  (0, false, fallback)

def initInstruction (X : EncodedType) (target : Nat) :
    (instructionEncodedType X).Carrier :=
  Sum.inl target

def elementInstruction (X : EncodedType) (x : X.Carrier) :
    (instructionEncodedType X).Carrier :=
  Sum.inr x

def instructions (X : EncodedType) (p : Nat × List X.Carrier) :
    List (instructionEncodedType X).Carrier :=
  initInstruction X p.1 :: p.2.map (elementInstruction X)

def elementStep (X : EncodedType) (p : Acc X × X.Carrier) : Acc X :=
  let remaining := p.1.1
  let found := p.1.2.1
  let value := p.1.2.2
  let x := p.2
  if found then
    p.1
  else if decide (remaining = 0) then
    (0, true, x)
  else
    (remaining - 1, false, value)

def step (X : EncodedType) (fallback : X.Carrier)
    (p : Acc X × (instructionEncodedType X).Carrier) : Acc X :=
  match p.2 with
  | Sum.inl target => (target, false, fallback)
  | Sum.inr x => elementStep X (p.1, x)

def fromInstructions (X : EncodedType) (fallback : X.Carrier)
    (xs : List (instructionEncodedType X).Carrier) : X.Carrier :=
  (xs.foldl (fun acc instr => step X fallback (acc, instr)) (initAcc X fallback)).2.2

def fromInput (X : EncodedType) (fallback : X.Carrier)
    (p : Nat × List X.Carrier) : X.Carrier :=
  fromInstructions X fallback (instructions X p)

def getD (X : EncodedType) (fallback : X.Carrier)
    (p : List X.Carrier × Nat) : X.Carrier :=
  p.1.getD p.2 fallback

/-! ### Semantics -/

theorem elementStep_found (X : EncodedType) (remaining : Nat)
    (value x : X.Carrier) :
    elementStep X ((remaining, true, value), x) =
      (remaining, true, value) := by
  simp [elementStep]

theorem elementInstructions_fold_found (X : EncodedType)
    (xs : List X.Carrier) (remaining : Nat) (value : X.Carrier)
    (fallback : X.Carrier) :
    (xs.map (elementInstruction X)).foldl
        (fun acc instr => step X fallback (acc, instr))
        (remaining, true, value) =
      (remaining, true, value) := by
  induction xs generalizing remaining value with
  | nil =>
      simp
  | cons x xs ih =>
      simpa [elementInstruction, step, elementStep]
        using ih remaining value

theorem elementInstructions_value_eq_getD (X : EncodedType)
    (xs : List X.Carrier) (target : Nat) (fallback : X.Carrier) :
    ((xs.map (elementInstruction X)).foldl
        (fun acc instr => step X fallback (acc, instr))
        (target, false, fallback)).2.2 =
      xs.getD target fallback := by
  induction xs generalizing target with
  | nil =>
      cases target <;> simp
  | cons x xs ih =>
      cases target with
      | zero =>
          have h := elementInstructions_fold_found X xs 0 x fallback
          simpa [elementInstruction, step, elementStep]
            using congrArg (fun q : Acc X => q.2.2) h
      | succ target =>
          simpa [elementInstruction, step, elementStep] using ih target

theorem fromInput_eq_getD (X : EncodedType) (fallback : X.Carrier)
    (p : Nat × List X.Carrier) :
    fromInput X fallback p = p.2.getD p.1 fallback := by
  rcases p with ⟨target, xs⟩
  have h := elementInstructions_value_eq_getD X xs target fallback
  simp [fromInput, fromInstructions, instructions, initInstruction, initAcc, step] at h ⊢
  exact h

theorem getD_inputSize_le (X : EncodedType) (fallback : X.Carrier)
    (source : List X.Carrier) (j : Nat) :
    X.inputSize (source.getD j fallback) ≤
      (EncodedType.list X).inputSize source + X.inputSize fallback := by
  by_cases hj : j < source.length
  · rw [List.getD_eq_getElem (l := source) (d := fallback) hj]
    have hMem : source[j] ∈ source := List.getElem_mem hj
    have hElem := Clique.encodedList_element_inputSize_le
      (X := X) (x := source[j]) (xs := source) hMem
    omega
  · have hLen : source.length ≤ j := Nat.le_of_not_gt hj
    rw [List.getD_eq_default (l := source) (d := fallback) (n := j) hLen]
    omega

/-! ### TM witnesses -/

theorem elementStep_tm_polytime (X : EncodedType) :
    TMPolyTimeMap
      (EncodedType.prod (accEncodedType X) X)
      (accEncodedType X)
      (elementStep X) := by
  let P := EncodedType.prod (accEncodedType X) X
  let A := accEncodedType X
  have hAcc : TMPolyTimeMap P A (fun p : (Acc X) × X.Carrier => p.1) := by
    simpa [P] using TMPolyTimeMap.fst A X
  have hElem : TMPolyTimeMap P X (fun p : (Acc X) × X.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd A X
  have hRemaining : TMPolyTimeMap P EncodedType.nat
      (fun p : (Acc X) × X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.bool X)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, accEncodedType, P] using hComp
  have hTail : TMPolyTimeMap P (EncodedType.prod EncodedType.bool X)
      (fun p : (Acc X) × X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.bool X)
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, accEncodedType, P] using hComp
  have hFound : TMPolyTimeMap P EncodedType.bool
      (fun p : (Acc X) × X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool X
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, P] using hComp
  have hValue : TMPolyTimeMap P X
      (fun p : (Acc X) × X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool X
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, P] using hComp
  have hZero : TMPolyTimeMap P EncodedType.nat
      (fun _ : (Acc X) × X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const P EncodedType.nat
      (show EncodedType.nat.Carrier from (0 : Nat))
  have hOne : TMPolyTimeMap P EncodedType.nat
      (fun _ : (Acc X) × X.Carrier => (1 : Nat)) :=
    TMPolyTimeMap.const P EncodedType.nat
      (show EncodedType.nat.Carrier from (1 : Nat))
  have hTrue : TMPolyTimeMap P EncodedType.bool
      (fun _ : (Acc X) × X.Carrier => true) :=
    TMPolyTimeMap.const P EncodedType.bool true
  have hFalse : TMPolyTimeMap P EncodedType.bool
      (fun _ : (Acc X) × X.Carrier => false) :=
    TMPolyTimeMap.const P EncodedType.bool false
  have hRemainingZeroInput :
      TMPolyTimeMap P (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : (Acc X) × X.Carrier => (p.1.1, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hRemaining hZero
  have hRemainingIsZero : TMPolyTimeMap P EncodedType.bool
      (fun p : (Acc X) × X.Carrier => decide (p.1.1 = 0)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hRemainingZeroInput
    simpa [Function.comp, P] using hComp
  have hPredInput :
      TMPolyTimeMap P (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : (Acc X) × X.Carrier => (p.1.1, (1 : Nat))) :=
    TMPolyTimeMap.prod_mk hRemaining hOne
  have hPred : TMPolyTimeMap P EncodedType.nat
      (fun p : (Acc X) × X.Carrier => p.1.1 - 1) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hPredInput
    simpa [Function.comp, P] using hComp
  have hHitTail : TMPolyTimeMap P (EncodedType.prod EncodedType.bool X)
      (fun p : (Acc X) × X.Carrier => (true, p.2)) :=
    TMPolyTimeMap.prod_mk hTrue hElem
  have hHit : TMPolyTimeMap P A
      (fun p : (Acc X) × X.Carrier => (show Acc X from (0, true, p.2))) :=
    TMPolyTimeMap.prod_mk hZero hHitTail
  have hMissTail : TMPolyTimeMap P (EncodedType.prod EncodedType.bool X)
      (fun p : (Acc X) × X.Carrier => (false, p.1.2.2)) :=
    TMPolyTimeMap.prod_mk hFalse hValue
  have hMiss : TMPolyTimeMap P A
      (fun p : (Acc X) × X.Carrier => (p.1.1 - 1, false, p.1.2.2)) :=
    TMPolyTimeMap.prod_mk hPred hMissTail
  have hZeroBranchInput :
      TMPolyTimeMap P (EncodedType.prod EncodedType.bool P)
        (fun p : (Acc X) × X.Carrier => (decide (p.1.1 = 0), p)) :=
    TMPolyTimeMap.prod_mk hRemainingIsZero (TMPolyTimeMap.id P)
  have hZeroBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool P) A
        (fun p : Bool × ((Acc X) × X.Carrier) =>
          match p.1 with
          | true => (show Acc X from (0, true, p.2.2))
          | false => (show Acc X from (p.2.1.1 - 1, false, p.2.1.2.2))) :=
    graphBoolProduct_dispatch_tm_polytime P A
      (fFalse := fun p : (Acc X) × X.Carrier =>
        (show Acc X from (p.1.1 - 1, false, p.1.2.2)))
      (fTrue := fun p : (Acc X) × X.Carrier =>
        (show Acc X from (0, true, p.2)))
      hMiss hHit
  have hNotFound : TMPolyTimeMap P A
      (fun p : (Acc X) × X.Carrier =>
        if decide (p.1.1 = 0) then
          (show Acc X from (0, true, p.2))
        else
          (show Acc X from (p.1.1 - 1, false, p.1.2.2))) := by
    have hComp := TMPolyTimeMap.comp hZeroBranch hZeroBranchInput
    convert hComp using 1
    funext p
    by_cases h : p.1.1 = 0 <;> simp [Function.comp, h]
  have hFoundBranchInput :
      TMPolyTimeMap P (EncodedType.prod EncodedType.bool P)
        (fun p : (Acc X) × X.Carrier => (p.1.2.1, p)) :=
    TMPolyTimeMap.prod_mk hFound (TMPolyTimeMap.id P)
  have hFoundBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool P) A
        (fun p : Bool × ((Acc X) × X.Carrier) =>
          match p.1 with
          | true => p.2.1
          | false =>
              if decide (p.2.1.1 = 0) then
                (show Acc X from (0, true, p.2.2))
              else
                (show Acc X from (p.2.1.1 - 1, false, p.2.1.2.2))) :=
    graphBoolProduct_dispatch_tm_polytime P A
      (fFalse := fun p : (Acc X) × X.Carrier =>
        if decide (p.1.1 = 0) then
          (show Acc X from (0, true, p.2))
        else
          (show Acc X from (p.1.1 - 1, false, p.1.2.2)))
      (fTrue := fun p : (Acc X) × X.Carrier => p.1)
      hNotFound hAcc
  have hOut := TMPolyTimeMap.comp hFoundBranch hFoundBranchInput
  convert hOut using 1
  funext p
  cases hFound : p.1.2.1 <;>
    simp [Function.comp, elementStep, hFound]
  rfl

theorem stepLeft_tm_polytime (X : EncodedType) (fallback : X.Carrier) :
    TMPolyTimeMap EncodedType.nat (accEncodedType X)
      (fun target : Nat => (show Acc X from (target, false, fallback))) := by
  have hTarget : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hFalse : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ : Nat => false) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool false
  have hFallback : TMPolyTimeMap EncodedType.nat X (fun _ : Nat => fallback) :=
    TMPolyTimeMap.const EncodedType.nat X fallback
  have hTail : TMPolyTimeMap EncodedType.nat (EncodedType.prod EncodedType.bool X)
      (fun _ : Nat => (false, fallback)) :=
    TMPolyTimeMap.prod_mk hFalse hFallback
  have hOut := TMPolyTimeMap.prod_mk hTarget hTail
  simpa [accEncodedType] using hOut

theorem step_tm_polytime (X : EncodedType) (fallback : X.Carrier) :
    TMPolyTimeMap
      (EncodedType.prod (accEncodedType X) (instructionEncodedType X))
      (accEncodedType X)
      (step X fallback) := by
  have hChoice :=
    prodSumChoice_tm_polytime (accEncodedType X) EncodedType.nat X
  have hRight : TMPolyTimeMap
      (EncodedType.prod (accEncodedType X) X)
      (accEncodedType X)
      (fun p : (Acc X) × X.Carrier => elementStep X p) :=
    elementStep_tm_polytime X
  have hBranches := TMPolyTimeMap.sum_elim (stepLeft_tm_polytime X fallback) hRight
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem instructions_tm_polytime (X : EncodedType) :
    TMPolyTimeMap
      (inputEncodedType X)
      (instructionListEncodedType X)
      (instructions X) := by
  let P := inputEncodedType X
  have hTarget : TMPolyTimeMap P EncodedType.nat (fun p : P.Carrier => p.1) := by
    simpa [P, inputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat (EncodedType.list X)
  have hValues : TMPolyTimeMap P (EncodedType.list X) (fun p : P.Carrier => p.2) := by
    simpa [P, inputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat (EncodedType.list X)
  have hInit : TMPolyTimeMap P (instructionEncodedType X)
      (fun p : P.Carrier => initInstruction X p.1) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.inl EncodedType.nat X) hTarget
    simpa [Function.comp, initInstruction, instructionEncodedType, P] using hComp
  have hInitSingleton : TMPolyTimeMap P (instructionListEncodedType X)
      (fun p : P.Carrier => [initInstruction X p.1]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton (instructionEncodedType X)) hInit
    simpa [Function.comp, instructionListEncodedType, P] using hComp
  have hElemInstr : TMPolyTimeMap X (instructionEncodedType X) (elementInstruction X) := by
    simpa [elementInstruction, instructionEncodedType] using
      TMPolyTimeMap.inr EncodedType.nat X
  have hMapped : TMPolyTimeMap P (instructionListEncodedType X)
      (fun p : P.Carrier => p.2.map (elementInstruction X)) := by
    have hMap := TMPolyTimeMap.list_map hElemInstr
    have hComp := TMPolyTimeMap.comp hMap hValues
    simpa [Function.comp, instructionListEncodedType, P] using hComp
  have hAppendInput :
      TMPolyTimeMap P
        (EncodedType.prod (instructionListEncodedType X) (instructionListEncodedType X))
        (fun p : P.Carrier =>
          ([initInstruction X p.1], p.2.map (elementInstruction X))) :=
    TMPolyTimeMap.prod_mk hInitSingleton hMapped
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append (instructionEncodedType X)) hAppendInput
  simpa [Function.comp, instructions, instructionListEncodedType, P] using hAppend

theorem initAcc_bound (X : EncodedType) (fallback : X.Carrier)
    (xs : List (instructionEncodedType X).Carrier) :
    (accEncodedType X).inputSize (initAcc X fallback) ≤
      (Polynomial.C (X.inputSize fallback + 10)).eval
        ((instructionListEncodedType X).inputSize xs) := by
  simp [initAcc, accEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat, EncodedType.inputSize_bool]
  omega

theorem step_growth (X : EncodedType) (fallback : X.Carrier)
    (source : List (instructionEncodedType X).Carrier)
    (acc : (accEncodedType X).Carrier)
    (instr : (instructionEncodedType X).Carrier)
    (hInstr :
      (instructionEncodedType X).inputSize instr ≤
        (instructionListEncodedType X).inputSize source) :
    (accEncodedType X).inputSize (step X fallback (acc, instr)) ≤
      (accEncodedType X).inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C (X.inputSize fallback + 20)).eval
          ((instructionListEncodedType X).inputSize source) := by
  rcases acc with ⟨remaining, found, value⟩
  change Nat at remaining
  change Bool at found
  cases instr with
  | inl target =>
      change Nat at target
      have hTargetLt :
          target + 1 < (instructionListEncodedType X).inputSize source := by
        simpa [instructionEncodedType, EncodedType.inputSize,
          EncodedType.sum, EncodedType.nat] using hInstr
      have hTargetSize :
          target + 2 ≤ (instructionListEncodedType X).inputSize source := by
        omega
      simp [step, accEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat,
        EncodedType.inputSize_bool, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X]
      omega
  | inr x =>
      have hElemSize :
          X.inputSize x + 1 ≤ (instructionListEncodedType X).inputSize source := by
        simpa [instructionEncodedType, EncodedType.inputSize,
          EncodedType.sum] using hInstr
      cases found
      · by_cases hZero : remaining = 0
        · simp [step, elementStep, hZero, accEncodedType, EncodedType.inputSize_prod,
            EncodedType.inputSize_nat, EncodedType.inputSize_bool, Polynomial.eval_add,
            Polynomial.eval_mul, Polynomial.eval_X]
          omega
        · simp [step, elementStep, hZero, accEncodedType, EncodedType.inputSize_prod,
            EncodedType.inputSize_nat, EncodedType.inputSize_bool, Polynomial.eval_add,
            Polynomial.eval_mul, Polynomial.eval_X]
          omega
      · by_cases hZero : remaining = 0
        · simp [step, elementStep, hZero, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_X]
        · simp [step, elementStep, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_X]

theorem fold_tm_polytime (X : EncodedType) (fallback : X.Carrier) :
    TMPolyTimeMap
      (instructionListEncodedType X)
      (accEncodedType X)
      (fun xs : (instructionListEncodedType X).Carrier =>
        xs.foldl (fun acc instr => step X fallback (acc, instr))
          (initAcc X fallback)) := by
  rcases step_tm_polytime X fallback with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      (instructionEncodedType X) (accEncodedType X)
      (step X fallback) (initAcc X fallback) hStep
      (Polynomial.C (X.inputSize fallback + 10))
      (Polynomial.C 10 * Polynomial.X + Polynomial.C (X.inputSize fallback + 20)) ?_ ?_
  · intro xs
    exact initAcc_bound X fallback xs
  · intro source acc instr hInstr
    exact step_growth X fallback source acc instr hInstr

theorem fromInstructions_tm_polytime (X : EncodedType) (fallback : X.Carrier) :
    TMPolyTimeMap
      (instructionListEncodedType X)
      X
      (fromInstructions X fallback) := by
  have hFold := fold_tm_polytime X fallback
  have hTail :=
    TMPolyTimeMap.snd EncodedType.nat (EncodedType.prod EncodedType.bool X)
  have hValue := TMPolyTimeMap.snd EncodedType.bool X
  have hTailComp := TMPolyTimeMap.comp hTail hFold
  have hValueComp := TMPolyTimeMap.comp hValue hTailComp
  simpa [Function.comp, fromInstructions, accEncodedType] using hValueComp

theorem fromInput_tm_polytime (X : EncodedType) (fallback : X.Carrier) :
    TMPolyTimeMap
      (inputEncodedType X)
      X
      (fromInput X fallback) := by
  have hComp :=
    TMPolyTimeMap.comp (fromInstructions_tm_polytime X fallback)
      (instructions_tm_polytime X)
  simpa [Function.comp, fromInput] using hComp

theorem getD_tm_polytime (X : EncodedType) (fallback : X.Carrier) :
    TMPolyTimeMap
      (EncodedType.prod (EncodedType.list X) EncodedType.nat)
      X
      (getD X fallback) := by
  let P := EncodedType.prod (EncodedType.list X) EncodedType.nat
  have hValues : TMPolyTimeMap P (EncodedType.list X) (fun p : P.Carrier => p.1) := by
    simpa [P] using TMPolyTimeMap.fst (EncodedType.list X) EncodedType.nat
  have hTarget : TMPolyTimeMap P EncodedType.nat (fun p : P.Carrier => p.2) := by
    simpa [P] using TMPolyTimeMap.snd (EncodedType.list X) EncodedType.nat
  have hInput : TMPolyTimeMap P (inputEncodedType X)
      (fun p : P.Carrier => (p.2, p.1)) :=
    TMPolyTimeMap.prod_mk hTarget hValues
  have hComp := TMPolyTimeMap.comp (fromInput_tm_polytime X fallback) hInput
  convert hComp using 1
  funext p
  rcases p with ⟨xs, target⟩
  exact (fromInput_eq_getD X fallback (target, xs)).symm

end EncodedListLookup

end Karp21
end ComplexityReduction
