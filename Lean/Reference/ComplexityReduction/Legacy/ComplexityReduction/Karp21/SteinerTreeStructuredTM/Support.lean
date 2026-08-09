/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SteinerTreeStructuredTM.WellFormed
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.MembershipRunner

/-!
Executable compact-support generation for the compact
Exact-Cover-to-Steiner-Tree route.
-/

namespace ComplexityReduction
namespace Karp21
namespace SteinerTree

open ComplexityReduction.Combinatorics

/-! ### Support list for one source set -/

def compactSupportAccEncodedType : EncodedType :=
  EncodedType.prod setStructuredEncodedType (EncodedType.list EncodedType.nat)

def compactSupportInstructionEncodedType : EncodedType :=
  EncodedType.sum setStructuredEncodedType EncodedType.nat

def compactSupportInstructionListEncodedType : EncodedType :=
  EncodedType.list compactSupportInstructionEncodedType

def compactSupportInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat setStructuredEncodedType

def compactSupportInitAcc : compactSupportAccEncodedType.Carrier :=
  ([], [])

def compactSupportInitInstruction (S : List Nat) :
    compactSupportInstructionEncodedType.Carrier :=
  Sum.inl S

def compactSupportElementInstruction (x : Nat) :
    compactSupportInstructionEncodedType.Carrier :=
  Sum.inr x

def compactSupportInstructions (p : Nat × List Nat) :
    List compactSupportInstructionEncodedType.Carrier :=
  compactSupportInitInstruction p.2 ::
    (List.range p.1).map compactSupportElementInstruction

def compactSupportElementStep (p : compactSupportAccEncodedType.Carrier × Nat) :
    compactSupportAccEncodedType.Carrier :=
  if HittingSet.setContainsBool (p.2, p.1.1) then
    (p.1.1, (show List Nat from p.1.2) ++ [p.2])
  else
    p.1

def compactSupportStep
    (p : compactSupportAccEncodedType.Carrier × compactSupportInstructionEncodedType.Carrier) :
    compactSupportAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl S => (S, [])
  | Sum.inr x => compactSupportElementStep (p.1, x)

def compactSupportFromInstructions
    (xs : List compactSupportInstructionEncodedType.Carrier) : List Nat :=
  (xs.foldl (fun acc instr => compactSupportStep (acc, instr)) compactSupportInitAcc).2

def compactSupportExecutable (p : Nat × List Nat) : List Nat :=
  compactSupportFromInstructions (compactSupportInstructions p)

theorem compactSupportElementFold_eq_filter
    (xs : List Nat) (S out : List Nat) :
    ((xs.map compactSupportElementInstruction).foldl
        (fun acc instr => compactSupportStep (acc, instr)) (S, out)).2 =
      out ++ xs.filter (fun x => HittingSet.setContainsBool (x, S)) := by
  induction xs generalizing out with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.map_cons, List.foldl_cons]
      by_cases h : HittingSet.setContainsBool (x, S) = true
      · simp [compactSupportElementInstruction, compactSupportStep,
          compactSupportElementStep, h]
        have hTail := ih (out ++ [x])
        simpa [compactSupportStep, List.append_assoc] using hTail
      · have hFalse : HittingSet.setContainsBool (x, S) = false := by
          cases hBool : HittingSet.setContainsBool (x, S)
          · rfl
          · exact False.elim (h hBool)
        simp [compactSupportElementInstruction, compactSupportStep,
          compactSupportElementStep, hFalse]
        have hTail := ih out
        simpa [compactSupportStep] using hTail

theorem compactSupportExecutable_eq_filter (bound : Nat) (S : List Nat) :
    compactSupportExecutable (bound, S) =
      (List.range bound).filter (fun x => HittingSet.setContainsBool (x, S)) := by
  change
    (((List.range bound).map compactSupportElementInstruction).foldl
        (fun acc instr => compactSupportStep (acc, instr)) (S, [])).2 =
      (List.range bound).filter (fun x => HittingSet.setContainsBool (x, S))
  simpa using compactSupportElementFold_eq_filter (List.range bound) S []

theorem compactSupportExecutable_eq_compactSupport (I : ExactCoverInput) (S : List Nat) :
    compactSupportExecutable (I.system.universeSize, S) = compactSupport I S := by
  classical
  rw [compactSupportExecutable_eq_filter]
  rw [List.range_eq_range']
  simp [compactSupport, HittingSet.setContainsBool_eq_decide]

theorem compactSupportInitInstruction_tm_polytime :
    TMPolyTimeMap
      setStructuredEncodedType
      compactSupportInstructionEncodedType
      compactSupportInitInstruction := by
  simpa [compactSupportInstructionEncodedType, compactSupportInitInstruction] using
    TMPolyTimeMap.inl setStructuredEncodedType EncodedType.nat

theorem compactSupportElementInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      compactSupportInstructionEncodedType
      compactSupportElementInstruction := by
  simpa [compactSupportInstructionEncodedType, compactSupportElementInstruction] using
    TMPolyTimeMap.inr setStructuredEncodedType EncodedType.nat

theorem compactSupportInstructions_tm_polytime :
    TMPolyTimeMap
      compactSupportInputEncodedType
      compactSupportInstructionListEncodedType
      compactSupportInstructions := by
  let X := compactSupportInputEncodedType
  have hBound : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, compactSupportInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat setStructuredEncodedType
  have hSet : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, compactSupportInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat setStructuredEncodedType
  have hInit :
      TMPolyTimeMap X compactSupportInstructionEncodedType
        (fun p : X.Carrier => compactSupportInitInstruction p.2) := by
    have hComp := TMPolyTimeMap.comp compactSupportInitInstruction_tm_polytime hSet
    simpa [Function.comp, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => List.range p.1) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hBound
    simpa [Function.comp, X] using hComp
  have hMapped :
      TMPolyTimeMap X compactSupportInstructionListEncodedType
        (fun p : X.Carrier =>
          (List.range p.1).map compactSupportElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactSupportElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, compactSupportInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactSupportInstructionEncodedType
          compactSupportInstructionListEncodedType)
        (fun p : X.Carrier =>
          (compactSupportInitInstruction p.2,
            (List.range p.1).map compactSupportElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hMapped
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons compactSupportInstructionEncodedType) hConsInput
  simpa [Function.comp, compactSupportInstructions,
    compactSupportInstructionListEncodedType, X] using hCons

theorem compactSupportStepLeft_tm_polytime :
    TMPolyTimeMap
      setStructuredEncodedType
      compactSupportAccEncodedType
      (fun S : List Nat => (S, [])) := by
  have hSet := TMPolyTimeMap.id setStructuredEncodedType
  have hNil :
      TMPolyTimeMap setStructuredEncodedType (EncodedType.list EncodedType.nat)
        (fun _ : List Nat => ([] : List Nat)) :=
    TMPolyTimeMap.const setStructuredEncodedType (EncodedType.list EncodedType.nat) []
  simpa [compactSupportAccEncodedType] using TMPolyTimeMap.prod_mk hSet hNil

theorem compactSupportElementStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactSupportAccEncodedType EncodedType.nat)
      compactSupportAccEncodedType
      compactSupportElementStep := by
  let X := EncodedType.prod compactSupportAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X compactSupportAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst compactSupportAccEncodedType EncodedType.nat
  have hX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd compactSupportAccEncodedType EncodedType.nat
  have hSet : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst setStructuredEncodedType (EncodedType.list EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, compactSupportAccEncodedType, X] using hComp
  have hOut :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat) (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType (EncodedType.list EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, compactSupportAccEncodedType, X] using hComp
  have hContainsInput :
      TMPolyTimeMap X HittingSet.setContainsInstructionInputEncodedType
        (fun p : X.Carrier => (p.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hX hSet
  have hContains : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => HittingSet.setContainsBool (p.2, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setContainsBool_tm_polytime hContainsInput
    simpa [Function.comp, X] using hComp
  have hSingleton :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat) (fun p : X.Carrier => [p.2]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.nat) hX
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod (EncodedType.list EncodedType.nat)
          (EncodedType.list EncodedType.nat))
        (fun p : X.Carrier => ((show List Nat from p.1.2), ([p.2] : List Nat))) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => (show List Nat from p.1.2) ++ ([p.2] : List Nat)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.nat)
      hAppendInput
    simpa [Function.comp, X] using hComp
  have hTrue :
      TMPolyTimeMap X compactSupportAccEncodedType
        (fun p : X.Carrier =>
          (p.1.1, (show List Nat from p.1.2) ++ ([p.2] : List Nat))) :=
    TMPolyTimeMap.prod_mk hSet hAppend
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (HittingSet.setContainsBool (p.2, p.1.1), p)) :=
    TMPolyTimeMap.prod_mk hContains (TMPolyTimeMap.id X)
  have hBranch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool X)
        compactSupportAccEncodedType
        (fun p : Bool × X.Carrier =>
          match p.1 with
          | true => (p.2.1.1, (show List Nat from p.2.1.2) ++ ([p.2.2] : List Nat))
          | false => p.2.1) :=
    graphBoolProduct_dispatch_tm_polytime X compactSupportAccEncodedType
      (fFalse := fun p : X.Carrier => p.1)
      (fTrue := fun p : X.Carrier =>
        (p.1.1, (show List Nat from p.1.2) ++ ([p.2] : List Nat)))
      hAcc hTrue
  have hComp := TMPolyTimeMap.comp hBranch hBranchInput
  convert hComp using 1
  funext p
  cases h : HittingSet.setContainsBool (p.2, p.1.1) <;>
    simp [Function.comp, compactSupportElementStep, h]

theorem compactSupportStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactSupportAccEncodedType compactSupportInstructionEncodedType)
      compactSupportAccEncodedType
      compactSupportStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      compactSupportAccEncodedType setStructuredEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim compactSupportStepLeft_tm_polytime
      compactSupportElementStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem compactSupportInitAcc_bound
    (xs : List compactSupportInstructionEncodedType.Carrier) :
  compactSupportAccEncodedType.inputSize compactSupportInitAcc ≤
      (Polynomial.C 5).eval (compactSupportInstructionListEncodedType.inputSize xs) := by
  simp [compactSupportInitAcc, compactSupportAccEncodedType, setStructuredEncodedType,
    EncodedType.inputSize_prod]

theorem compactSupportStep_growth
    (source : List compactSupportInstructionEncodedType.Carrier)
    (acc : compactSupportAccEncodedType.Carrier)
    (instr : compactSupportInstructionEncodedType.Carrier)
    (hInstr :
      compactSupportInstructionEncodedType.inputSize instr ≤
        compactSupportInstructionListEncodedType.inputSize source) :
    compactSupportAccEncodedType.inputSize (compactSupportStep (acc, instr)) ≤
      compactSupportAccEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 20).eval
          (compactSupportInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨S, out⟩
  cases instr with
  | inl newSet =>
      have hSet :
          setStructuredEncodedType.inputSize newSet + 1 ≤
            compactSupportInstructionListEncodedType.inputSize source := by
        simpa [compactSupportInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum] using hInstr
      simp [compactSupportStep, compactSupportAccEncodedType, EncodedType.inputSize_prod,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      omega
  | inr x =>
      change Nat at x
      by_cases hContains : HittingSet.setContainsBool (x, S) = true
      · have hx :
            x + 2 ≤ compactSupportInstructionListEncodedType.inputSize source := by
          have hxTagged :
              x + 1 < compactSupportInstructionListEncodedType.inputSize source := by
            simpa [compactSupportInstructionEncodedType, EncodedType.inputSize,
              EncodedType.sum, EncodedType.nat] using hInstr
          omega
        have hAppendSize :
            (EncodedType.list EncodedType.nat).inputSize
                ((show List Nat from out) ++ ([x] : List Nat)) =
              (EncodedType.list EncodedType.nat).inputSize out + (x + 2) := by
          rw [natList_inputSize_append]
          simp [EncodedType.inputSize, EncodedType.list, EncodedType.nat]
        simp [compactSupportStep, compactSupportElementStep, hContains,
          compactSupportAccEncodedType, EncodedType.inputSize_prod,
          hAppendSize,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        omega
      · have hFalse : HittingSet.setContainsBool (x, S) = false := by
          cases h : HittingSet.setContainsBool (x, S)
          · rfl
          · exact False.elim (hContains h)
        simp [compactSupportStep, compactSupportElementStep, hFalse,
          compactSupportAccEncodedType, EncodedType.inputSize_prod,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

theorem compactSupportFold_tm_polytime :
    TMPolyTimeMap
      compactSupportInstructionListEncodedType
      compactSupportAccEncodedType
      (fun xs : List compactSupportInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactSupportStep (acc, instr))
          compactSupportInitAcc) := by
  rcases compactSupportStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      compactSupportInstructionEncodedType compactSupportAccEncodedType
      compactSupportStep compactSupportInitAcc hStep
      (Polynomial.C 5) (Polynomial.C 10 * Polynomial.X + Polynomial.C 20) ?_ ?_
  · intro xs
    exact compactSupportInitAcc_bound xs
  · intro source acc instr hInstr
    exact compactSupportStep_growth source acc instr hInstr

theorem compactSupportFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactSupportInstructionListEncodedType
      (EncodedType.list EncodedType.nat)
      compactSupportFromInstructions := by
  have hFold := compactSupportFold_tm_polytime
  have hSnd := TMPolyTimeMap.snd setStructuredEncodedType (EncodedType.list EncodedType.nat)
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, compactSupportFromInstructions, compactSupportAccEncodedType]
    using hComp

theorem compactSupportExecutable_tm_polytime :
    TMPolyTimeMap
      compactSupportInputEncodedType
      (EncodedType.list EncodedType.nat)
      compactSupportExecutable := by
  have hComp := TMPolyTimeMap.comp compactSupportFromInstructions_tm_polytime
    compactSupportInstructions_tm_polytime
  simpa [Function.comp, compactSupportExecutable] using hComp

end SteinerTree
end Karp21
end ComplexityReduction
