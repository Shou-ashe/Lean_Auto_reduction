/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ListLookupTM
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Sum

/-!
Direct standard-TM map for splitting an encoded unary nat list at a unary index.

The runner is intentionally small and generic over the Karp21 nat-list encoding:
an initial instruction loads the split index, then each nat payload is appended
to the left output while the countdown is positive, and to the right output
after the countdown reaches zero.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics

namespace NatListSplit

abbrev accEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod setStructuredEncodedType setStructuredEncodedType)

abbrev Acc :=
  Nat × List Nat × List Nat

abbrev inputEncodedType : EncodedType :=
  EncodedListLookup.inputEncodedType EncodedType.nat

abbrev instructionEncodedType : EncodedType :=
  EncodedListLookup.instructionEncodedType EncodedType.nat

abbrev instructionListEncodedType : EncodedType :=
  EncodedListLookup.instructionListEncodedType EncodedType.nat

abbrev outputEncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType setStructuredEncodedType

def initAcc : Acc :=
  (0, [], [])

def elementStep (p : Acc × Nat) : Acc :=
  let remaining := p.1.1
  let left := p.1.2.1
  let right := p.1.2.2
  let x := p.2
  if decide (remaining = 0) then
    (0, left, right ++ [x])
  else
    (remaining - 1, left ++ [x], right)

def step (p : Acc × instructionEncodedType.Carrier) : Acc :=
  match p.2 with
  | Sum.inl target => (target, [], [])
  | Sum.inr x => elementStep (p.1, x)

def fromInstructions (xs : List instructionEncodedType.Carrier) : List Nat × List Nat :=
  let out := xs.foldl (fun acc instr => step (acc, instr)) initAcc
  (out.2.1, out.2.2)

def split (p : Nat × List Nat) : List Nat × List Nat :=
  fromInstructions (EncodedListLookup.instructions EncodedType.nat p)

/-! ### Semantics -/

theorem elementFold_eq
    (xs : List Nat) (remaining : Nat) (left right : List Nat) :
    xs.foldl (fun acc x => elementStep (acc, x)) (remaining, left, right) =
      (remaining - xs.length, left ++ xs.take remaining, right ++ xs.drop remaining) := by
  induction xs generalizing remaining left right with
  | nil =>
      simp
  | cons x xs ih =>
      cases remaining with
      | zero =>
          have h := ih 0 left (right ++ [x])
          simpa [elementStep, List.append_assoc] using h
      | succ remaining =>
          have h := ih remaining (left ++ [x]) right
          simpa [elementStep, List.append_assoc] using h

theorem mappedElementFold_eq (xs : List Nat) (acc : Acc) :
    (xs.map (EncodedListLookup.elementInstruction EncodedType.nat)).foldl
        (fun acc instr => step (acc, instr)) acc =
      xs.foldl (fun acc x => elementStep (acc, x)) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      simpa [EncodedListLookup.elementInstruction, step] using
        ih (elementStep (acc, x))

theorem split_eq_splitAt (n : Nat) (xs : List Nat) :
    split (n, xs) = (xs.take n, xs.drop n) := by
  change
    (((EncodedListLookup.instructions EncodedType.nat (n, xs)).foldl
      (fun acc instr => step (acc, instr)) initAcc).2.1,
      ((EncodedListLookup.instructions EncodedType.nat (n, xs)).foldl
        (fun acc instr => step (acc, instr)) initAcc).2.2) =
      (xs.take n, xs.drop n)
  rw [EncodedListLookup.instructions]
  simp [EncodedListLookup.initInstruction, step, initAcc]
  change
    ((xs.map (EncodedListLookup.elementInstruction EncodedType.nat)).foldl
      (fun acc instr => step (acc, instr)) (n, [], [])).2 =
      (xs.take n, xs.drop n)
  rw [mappedElementFold_eq]
  have h := elementFold_eq xs n [] []
  simpa using congrArg (fun q : Acc => (q.2.1, q.2.2)) h

/-! ### TM witnesses -/

theorem elementStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod accEncodedType EncodedType.nat)
      accEncodedType
      elementStep := by
  let P := EncodedType.prod accEncodedType EncodedType.nat
  let Tail := EncodedType.prod setStructuredEncodedType setStructuredEncodedType
  have hAcc : TMPolyTimeMap P accEncodedType (fun p : Acc × Nat => p.1) := by
    simpa [P] using TMPolyTimeMap.fst accEncodedType EncodedType.nat
  have hX : TMPolyTimeMap P EncodedType.nat (fun p : Acc × Nat => p.2) := by
    simpa [P] using TMPolyTimeMap.snd accEncodedType EncodedType.nat
  have hRemaining : TMPolyTimeMap P EncodedType.nat (fun p : Acc × Nat => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat Tail
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, accEncodedType, Tail, P] using hComp
  have hTail : TMPolyTimeMap P Tail (fun p : Acc × Nat => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat Tail
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, accEncodedType, Tail, P] using hComp
  have hLeft : TMPolyTimeMap P setStructuredEncodedType (fun p : Acc × Nat => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, Tail, P] using hComp
  have hRight : TMPolyTimeMap P setStructuredEncodedType (fun p : Acc × Nat => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, Tail, P] using hComp
  have hZero : TMPolyTimeMap P EncodedType.nat (fun _ : Acc × Nat => (0 : Nat)) :=
    TMPolyTimeMap.const P EncodedType.nat (0 : Nat)
  have hOne : TMPolyTimeMap P EncodedType.nat (fun _ : Acc × Nat => (1 : Nat)) :=
    TMPolyTimeMap.const P EncodedType.nat (1 : Nat)
  have hRemainingZeroInput :
      TMPolyTimeMap P (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Acc × Nat => (p.1.1, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hRemaining hZero
  have hRemainingIsZero : TMPolyTimeMap P EncodedType.bool
      (fun p : Acc × Nat => decide (p.1.1 = 0)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hRemainingZeroInput
    simpa [Function.comp, P] using hComp
  have hPredInput :
      TMPolyTimeMap P (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Acc × Nat => (p.1.1, (1 : Nat))) :=
    TMPolyTimeMap.prod_mk hRemaining hOne
  have hPred : TMPolyTimeMap P EncodedType.nat (fun p : Acc × Nat => p.1.1 - 1) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hPredInput
    simpa [Function.comp, P] using hComp
  have hSingleton : TMPolyTimeMap P setStructuredEncodedType
      (fun p : Acc × Nat => [p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton EncodedType.nat) hX
    simpa [Function.comp, setStructuredEncodedType, P] using hComp
  have hLeftAppendInput :
      TMPolyTimeMap P
        (EncodedType.prod setStructuredEncodedType setStructuredEncodedType)
        (fun p : Acc × Nat => (p.1.2.1, [p.2])) :=
    TMPolyTimeMap.prod_mk hLeft hSingleton
  have hLeftAppend : TMPolyTimeMap P setStructuredEncodedType
      (fun p : Acc × Nat => p.1.2.1 ++ [p.2]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.nat)
      hLeftAppendInput
    simpa [Function.comp, setStructuredEncodedType, P] using hComp
  have hRightAppendInput :
      TMPolyTimeMap P
        (EncodedType.prod setStructuredEncodedType setStructuredEncodedType)
        (fun p : Acc × Nat => (p.1.2.2, [p.2])) :=
    TMPolyTimeMap.prod_mk hRight hSingleton
  have hRightAppend : TMPolyTimeMap P setStructuredEncodedType
      (fun p : Acc × Nat => p.1.2.2 ++ [p.2]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.nat)
      hRightAppendInput
    simpa [Function.comp, setStructuredEncodedType, P] using hComp
  have hRightBranchTail : TMPolyTimeMap P Tail
      (fun p : Acc × Nat => (p.1.2.1, p.1.2.2 ++ [p.2])) :=
    TMPolyTimeMap.prod_mk hLeft hRightAppend
  have hRightBranch : TMPolyTimeMap P accEncodedType
      (fun p : Acc × Nat => (show Acc from (0, p.1.2.1, p.1.2.2 ++ [p.2]))) :=
    TMPolyTimeMap.prod_mk hZero hRightBranchTail
  have hLeftBranchTail : TMPolyTimeMap P Tail
      (fun p : Acc × Nat => (p.1.2.1 ++ [p.2], p.1.2.2)) :=
    TMPolyTimeMap.prod_mk hLeftAppend hRight
  have hLeftBranch : TMPolyTimeMap P accEncodedType
      (fun p : Acc × Nat => (show Acc from (p.1.1 - 1, p.1.2.1 ++ [p.2], p.1.2.2))) :=
    TMPolyTimeMap.prod_mk hPred hLeftBranchTail
  have hBranchInput :
      TMPolyTimeMap P (EncodedType.prod EncodedType.bool P)
        (fun p : Acc × Nat => (decide (p.1.1 = 0), p)) :=
    TMPolyTimeMap.prod_mk hRemainingIsZero (TMPolyTimeMap.id P)
  have hBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool P) accEncodedType
        (fun p : Bool × (Acc × Nat) =>
          match p.1 with
          | true => (show Acc from (0, p.2.1.2.1, p.2.1.2.2 ++ [p.2.2]))
          | false => (show Acc from (p.2.1.1 - 1, p.2.1.2.1 ++ [p.2.2], p.2.1.2.2))) :=
    graphBoolProduct_dispatch_tm_polytime P accEncodedType
      (fFalse := fun p : Acc × Nat =>
        (show Acc from (p.1.1 - 1, p.1.2.1 ++ [p.2], p.1.2.2)))
      (fTrue := fun p : Acc × Nat =>
        (show Acc from (0, p.1.2.1, p.1.2.2 ++ [p.2])))
      hLeftBranch hRightBranch
  have hOut := TMPolyTimeMap.comp hBranch hBranchInput
  convert hOut using 1
  funext p
  by_cases h : p.1.1 = 0 <;> simp [Function.comp, elementStep, h]

theorem stepLeft_tm_polytime :
    TMPolyTimeMap EncodedType.nat accEncodedType
      (fun target : Nat => (show Acc from (target, [], []))) := by
  have hTarget : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hEmptyLeft : TMPolyTimeMap EncodedType.nat setStructuredEncodedType
      (fun _ : Nat => ([] : List Nat)) :=
    TMPolyTimeMap.const EncodedType.nat setStructuredEncodedType []
  have hEmptyRight : TMPolyTimeMap EncodedType.nat setStructuredEncodedType
      (fun _ : Nat => ([] : List Nat)) :=
    TMPolyTimeMap.const EncodedType.nat setStructuredEncodedType []
  have hTail :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod setStructuredEncodedType setStructuredEncodedType)
        (fun _ : Nat => (([] : List Nat), ([] : List Nat))) :=
    TMPolyTimeMap.prod_mk hEmptyLeft hEmptyRight
  have hOut := TMPolyTimeMap.prod_mk hTarget hTail
  simpa [accEncodedType] using hOut

theorem step_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod accEncodedType instructionEncodedType)
      accEncodedType
      step := by
  have hChoice :=
    prodSumChoice_tm_polytime accEncodedType EncodedType.nat EncodedType.nat
  have hBranches := TMPolyTimeMap.sum_elim stepLeft_tm_polytime elementStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem initAcc_bound (xs : List instructionEncodedType.Carrier) :
    accEncodedType.inputSize initAcc ≤
      (Polynomial.C 10).eval (instructionListEncodedType.inputSize xs) := by
  have h : accEncodedType.inputSize initAcc ≤ 10 := by
    have hEmpty : setStructuredEncodedType.inputSize ([] : List Nat) = 0 :=
      EncodedType.inputSize_list_nil EncodedType.nat
    simp [accEncodedType, initAcc, EncodedType.inputSize_prod,
      EncodedType.inputSize_nat, hEmpty]
  simpa using h

theorem step_growth
    (source : List instructionEncodedType.Carrier)
    (acc : accEncodedType.Carrier)
    (instr : instructionEncodedType.Carrier)
    (hInstr : instructionEncodedType.inputSize instr ≤ instructionListEncodedType.inputSize source) :
    accEncodedType.inputSize (step (acc, instr)) ≤
      accEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 100).eval
          (instructionListEncodedType.inputSize source) := by
  rcases acc with ⟨remaining, left, right⟩
  change Nat at remaining
  change List Nat at left right
  cases instr with
  | inl target =>
      change Nat at target
      have hTarget :
          target + 1 < instructionListEncodedType.inputSize source := by
        simpa [instructionEncodedType, EncodedListLookup.instructionEncodedType,
          EncodedType.inputSize, EncodedType.sum, EncodedType.nat] using hInstr
      have hResetSize :
          accEncodedType.inputSize ((target, ([] : List Nat), ([] : List Nat)) : Acc) =
            target + 3 := by
        have hEmpty : setStructuredEncodedType.inputSize ([] : List Nat) = 0 := by
          exact EncodedType.inputSize_list_nil EncodedType.nat
        simp [accEncodedType, EncodedType.inputSize_prod, EncodedType.inputSize_nat, hEmpty]
      change
        accEncodedType.inputSize ((target, ([] : List Nat), ([] : List Nat)) : Acc) ≤
          accEncodedType.inputSize (remaining, left, right) +
            (Polynomial.C 10 * Polynomial.X + Polynomial.C 100).eval
              (instructionListEncodedType.inputSize source)
      rw [hResetSize]
      simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      omega
  | inr x =>
      change Nat at x
      have hX :
          x + 1 + 1 ≤ instructionListEncodedType.inputSize source := by
        simpa [instructionEncodedType, EncodedListLookup.instructionEncodedType,
          EncodedType.inputSize, EncodedType.sum, EncodedType.nat] using hInstr
      have hLeftAppend :
          setStructuredEncodedType.inputSize (left ++ [x]) =
            setStructuredEncodedType.inputSize left + EncodedType.nat.inputSize x + 1 := by
        simpa [setStructuredEncodedType, EncodedType.inputSize_list_cons,
          EncodedType.inputSize_list_nil] using
          Clique.encodedList_inputSize_append EncodedType.nat left [x]
      have hRightAppend :
          setStructuredEncodedType.inputSize (right ++ [x]) =
            setStructuredEncodedType.inputSize right + EncodedType.nat.inputSize x + 1 := by
        simpa [setStructuredEncodedType, EncodedType.inputSize_list_cons,
          EncodedType.inputSize_list_nil] using
          Clique.encodedList_inputSize_append EncodedType.nat right [x]
      by_cases hZero : remaining = 0
      · simp [step, elementStep, hZero, accEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_X, hRightAppend] at hX ⊢
        omega
      · simp [step, elementStep, hZero, accEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_X, hLeftAppend] at hX ⊢
        omega

theorem fold_tm_polytime :
    TMPolyTimeMap
      instructionListEncodedType
      accEncodedType
      (fun xs : instructionListEncodedType.Carrier =>
        xs.foldl (fun acc instr => step (acc, instr)) initAcc) := by
  rcases step_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      instructionEncodedType accEncodedType step initAcc hStep
      (Polynomial.C 10) (Polynomial.C 10 * Polynomial.X + Polynomial.C 100)
      ?_ ?_
  · intro xs
    exact initAcc_bound xs
  · intro source acc instr hInstr
    exact step_growth source acc instr hInstr

theorem fromInstructions_tm_polytime :
    TMPolyTimeMap
      instructionListEncodedType
      outputEncodedType
      fromInstructions := by
  have hFold := fold_tm_polytime
  have hTail := TMPolyTimeMap.snd EncodedType.nat
    (EncodedType.prod setStructuredEncodedType setStructuredEncodedType)
  have hComp := TMPolyTimeMap.comp hTail hFold
  simpa [Function.comp, fromInstructions, accEncodedType, outputEncodedType] using hComp

theorem split_tm_polytime :
    TMPolyTimeMap inputEncodedType outputEncodedType split := by
  have hComp := TMPolyTimeMap.comp fromInstructions_tm_polytime
    (EncodedListLookup.instructions_tm_polytime EncodedType.nat)
  simpa [Function.comp, split, inputEncodedType, instructionListEncodedType] using hComp

end NatListSplit

end Karp21
end ComplexityReduction
