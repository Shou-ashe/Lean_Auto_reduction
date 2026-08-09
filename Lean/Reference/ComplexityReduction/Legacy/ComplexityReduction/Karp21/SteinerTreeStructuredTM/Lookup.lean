/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SteinerTreeStructuredTM.EdgeBlocks

/-!
Unary lookup for set families used by the compact Steiner Tree assembly.

The runner scans a `List (List Nat)` with a countdown index and returns `[]`
outside the family, matching `List.getD`.
-/

namespace ComplexityReduction
namespace Karp21
namespace SteinerTree

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

def setFamilyGetDAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.bool setStructuredEncodedType)

abbrev SetFamilyGetDAccCarrier := Nat × (Bool × List Nat)

def setFamilyGetDInstructionEncodedType : EncodedType :=
  EncodedType.sum EncodedType.nat setStructuredEncodedType

def setFamilyGetDInstructionListEncodedType : EncodedType :=
  EncodedType.list setFamilyGetDInstructionEncodedType

def setFamilyGetDInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat setFamilyStructuredEncodedType

def setFamilyGetDInitAcc : SetFamilyGetDAccCarrier :=
  (0, (false, []))

def setFamilyGetDInitInstruction (target : Nat) :
    setFamilyGetDInstructionEncodedType.Carrier :=
  Sum.inl target

def setFamilyGetDSetInstruction (S : List Nat) :
    setFamilyGetDInstructionEncodedType.Carrier :=
  Sum.inr S

def setFamilyGetDInstructions (p : Nat × List (List Nat)) :
    List setFamilyGetDInstructionEncodedType.Carrier :=
  setFamilyGetDInitInstruction p.1 :: p.2.map setFamilyGetDSetInstruction

def setFamilyGetDSetStep (p : SetFamilyGetDAccCarrier × List Nat) :
    SetFamilyGetDAccCarrier :=
  let remaining := p.1.1
  let found := p.1.2.1
  let value := p.1.2.2
  let S := p.2
  if found then
    p.1
  else if decide (remaining = 0) then
    (0, (true, S))
  else
    (remaining - 1, (false, value))

def setFamilyGetDStep
    (p : SetFamilyGetDAccCarrier × setFamilyGetDInstructionEncodedType.Carrier) :
    SetFamilyGetDAccCarrier :=
  match p.2 with
  | Sum.inl target => (target, (false, []))
  | Sum.inr S => setFamilyGetDSetStep (p.1, S)

def setFamilyGetDFromInstructions
    (xs : List setFamilyGetDInstructionEncodedType.Carrier) : List Nat :=
  (xs.foldl (fun acc instr => setFamilyGetDStep (acc, instr)) setFamilyGetDInitAcc).2.2

def setFamilyGetDFromInput (p : Nat × List (List Nat)) : List Nat :=
  setFamilyGetDFromInstructions (setFamilyGetDInstructions p)

def setFamilyGetD (p : List (List Nat) × Nat) : List Nat :=
  p.1.getD p.2 []

/-! ### Semantics -/

theorem setFamilyGetDSetStep_found (remaining : Nat) (value S : List Nat) :
    setFamilyGetDSetStep ((remaining, (true, value)), S) =
      (remaining, (true, value)) := by
  simp [setFamilyGetDSetStep]

theorem setFamilyGetDSetInstructions_fold_found
    (xs : List (List Nat)) (remaining : Nat) (value : List Nat) :
    (xs.map setFamilyGetDSetInstruction).foldl
        (fun acc instr => setFamilyGetDStep (acc, instr))
        (remaining, (true, value)) =
      (remaining, (true, value)) := by
  induction xs generalizing remaining value with
  | nil =>
      simp
  | cons S Ss ih =>
      simpa [setFamilyGetDSetInstruction, setFamilyGetDStep, setFamilyGetDSetStep]
        using ih remaining value

theorem setFamilyGetDSetInstructions_value_eq_getD
    (xs : List (List Nat)) (target : Nat) :
    ((xs.map setFamilyGetDSetInstruction).foldl
        (fun acc instr => setFamilyGetDStep (acc, instr))
        (target, (false, []))).2.2 =
      xs.getD target [] := by
  induction xs generalizing target with
  | nil =>
      cases target <;> simp
  | cons S Ss ih =>
      cases target with
      | zero =>
          have h := setFamilyGetDSetInstructions_fold_found Ss 0 S
          simpa [setFamilyGetDSetInstruction, setFamilyGetDStep, setFamilyGetDSetStep]
            using congrArg (fun q : SetFamilyGetDAccCarrier => q.2.2) h
      | succ target =>
          simpa [setFamilyGetDSetInstruction, setFamilyGetDStep, setFamilyGetDSetStep]
            using ih target

theorem setFamilyGetDFromInput_eq_getD (p : Nat × List (List Nat)) :
    setFamilyGetDFromInput p = p.2.getD p.1 [] := by
  rcases p with ⟨target, sets⟩
  have h := setFamilyGetDSetInstructions_value_eq_getD sets target
  simp [setFamilyGetDFromInput, setFamilyGetDFromInstructions,
    setFamilyGetDInstructions, setFamilyGetDInitInstruction, setFamilyGetDInitAcc,
    setFamilyGetDStep] at h ⊢
  exact h

/-! ### TM witnesses -/

theorem setFamilyGetDSetStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setFamilyGetDAccEncodedType setStructuredEncodedType)
      setFamilyGetDAccEncodedType
      setFamilyGetDSetStep := by
  let X := EncodedType.prod setFamilyGetDAccEncodedType setStructuredEncodedType
  let A := setFamilyGetDAccEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : SetFamilyGetDAccCarrier × List Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst A setStructuredEncodedType
  have hSet : TMPolyTimeMap X setStructuredEncodedType
      (fun p : SetFamilyGetDAccCarrier × List Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd A setStructuredEncodedType
  have hRemaining : TMPolyTimeMap X EncodedType.nat
      (fun p : SetFamilyGetDAccCarrier × List Nat => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.bool setStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, setFamilyGetDAccEncodedType, X] using hComp
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool setStructuredEncodedType)
        (fun p : SetFamilyGetDAccCarrier × List Nat => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.bool setStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, setFamilyGetDAccEncodedType, X] using hComp
  have hFound : TMPolyTimeMap X EncodedType.bool
      (fun p : SetFamilyGetDAccCarrier × List Nat => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hValue : TMPolyTimeMap X setStructuredEncodedType
      (fun p : SetFamilyGetDAccCarrier × List Nat => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.nat
      (fun _ : SetFamilyGetDAccCarrier × List Nat => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat
      (show EncodedType.nat.Carrier from (0 : Nat))
  have hOne : TMPolyTimeMap X EncodedType.nat
      (fun _ : SetFamilyGetDAccCarrier × List Nat => (1 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat
      (show EncodedType.nat.Carrier from (1 : Nat))
  have hTrue : TMPolyTimeMap X EncodedType.bool
      (fun _ : SetFamilyGetDAccCarrier × List Nat => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hFalse : TMPolyTimeMap X EncodedType.bool
      (fun _ : SetFamilyGetDAccCarrier × List Nat => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hRemainingZeroInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : SetFamilyGetDAccCarrier × List Nat => (p.1.1, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hRemaining hZero
  have hRemainingIsZero :
      TMPolyTimeMap X EncodedType.bool
        (fun p : SetFamilyGetDAccCarrier × List Nat => decide (p.1.1 = 0)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hRemainingZeroInput
    simpa [Function.comp, X] using hComp
  have hPredInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : SetFamilyGetDAccCarrier × List Nat => (p.1.1, (1 : Nat))) :=
    TMPolyTimeMap.prod_mk hRemaining hOne
  have hPred :
      TMPolyTimeMap X EncodedType.nat
        (fun p : SetFamilyGetDAccCarrier × List Nat => p.1.1 - 1) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hPredInput
    simpa [Function.comp, X] using hComp
  have hHitTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool setStructuredEncodedType)
        (fun p : SetFamilyGetDAccCarrier × List Nat => (true, p.2)) :=
    TMPolyTimeMap.prod_mk hTrue hSet
  have hHit :
      TMPolyTimeMap X A
        (fun p : SetFamilyGetDAccCarrier × List Nat =>
          (show SetFamilyGetDAccCarrier from (0, (true, p.2)))) :=
    TMPolyTimeMap.prod_mk hZero hHitTail
  have hMissTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool setStructuredEncodedType)
        (fun p : SetFamilyGetDAccCarrier × List Nat => (false, p.1.2.2)) :=
    TMPolyTimeMap.prod_mk hFalse hValue
  have hMiss :
      TMPolyTimeMap X A
        (fun p : SetFamilyGetDAccCarrier × List Nat => (p.1.1 - 1, (false, p.1.2.2))) :=
    TMPolyTimeMap.prod_mk hPred hMissTail
  have hZeroBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : SetFamilyGetDAccCarrier × List Nat => (decide (p.1.1 = 0), p)) :=
    TMPolyTimeMap.prod_mk hRemainingIsZero (TMPolyTimeMap.id X)
  have hZeroBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × (SetFamilyGetDAccCarrier × List Nat) =>
          match p.1 with
          | true => (show SetFamilyGetDAccCarrier from (0, (true, p.2.2)))
          | false =>
              (show SetFamilyGetDAccCarrier from
                (p.2.1.1 - 1, (false, p.2.1.2.2)))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : SetFamilyGetDAccCarrier × List Nat =>
        (show SetFamilyGetDAccCarrier from (p.1.1 - 1, (false, p.1.2.2))))
      (fTrue := fun p : SetFamilyGetDAccCarrier × List Nat =>
        (show SetFamilyGetDAccCarrier from (0, (true, p.2))))
      hMiss hHit
  have hNotFound :
      TMPolyTimeMap X A
        (fun p : SetFamilyGetDAccCarrier × List Nat =>
          if decide (p.1.1 = 0) then
            (show SetFamilyGetDAccCarrier from (0, (true, p.2)))
          else
            (show SetFamilyGetDAccCarrier from (p.1.1 - 1, (false, p.1.2.2)))) := by
    have hComp := TMPolyTimeMap.comp hZeroBranch hZeroBranchInput
    convert hComp using 1
    funext p
    by_cases h : p.1.1 = 0 <;> simp [Function.comp, h]
  have hFoundBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : SetFamilyGetDAccCarrier × List Nat => (p.1.2.1, p)) :=
    TMPolyTimeMap.prod_mk hFound (TMPolyTimeMap.id X)
  have hFoundBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × (SetFamilyGetDAccCarrier × List Nat) =>
          match p.1 with
          | true => p.2.1
          | false =>
              if decide (p.2.1.1 = 0) then
                (show SetFamilyGetDAccCarrier from (0, (true, p.2.2)))
              else
                (show SetFamilyGetDAccCarrier from
                  (p.2.1.1 - 1, (false, p.2.1.2.2)))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : SetFamilyGetDAccCarrier × List Nat =>
        if decide (p.1.1 = 0) then
          (show SetFamilyGetDAccCarrier from (0, (true, p.2)))
        else
          (show SetFamilyGetDAccCarrier from (p.1.1 - 1, (false, p.1.2.2))))
      (fTrue := fun p : SetFamilyGetDAccCarrier × List Nat => p.1)
      hNotFound hAcc
  have hOut := TMPolyTimeMap.comp hFoundBranch hFoundBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨remaining, found, value⟩, S⟩
  cases found <;> by_cases h : remaining = 0 <;>
    simp [Function.comp, setFamilyGetDSetStep, h]

theorem setFamilyGetDStepLeft_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      setFamilyGetDAccEncodedType
      (fun target : Nat => (show SetFamilyGetDAccCarrier from (target, (false, [])))) := by
  have hTarget := TMPolyTimeMap.id EncodedType.nat
  have hFalse : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ : Nat => false) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool false
  have hEmpty :
      TMPolyTimeMap EncodedType.nat setStructuredEncodedType
        (fun _ : Nat => ([] : List Nat)) :=
    TMPolyTimeMap.const EncodedType.nat setStructuredEncodedType []
  have hTail :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod EncodedType.bool setStructuredEncodedType)
        (fun _ : Nat => (false, ([] : List Nat))) :=
    TMPolyTimeMap.prod_mk hFalse hEmpty
  have hOut := TMPolyTimeMap.prod_mk hTarget hTail
  simpa [setFamilyGetDAccEncodedType] using hOut

theorem setFamilyGetDStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setFamilyGetDAccEncodedType setFamilyGetDInstructionEncodedType)
      setFamilyGetDAccEncodedType
      setFamilyGetDStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      setFamilyGetDAccEncodedType EncodedType.nat setStructuredEncodedType
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim setFamilyGetDStepLeft_tm_polytime
      setFamilyGetDSetStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem setFamilyGetDInstructions_tm_polytime :
    TMPolyTimeMap
      setFamilyGetDInputEncodedType
      setFamilyGetDInstructionListEncodedType
      setFamilyGetDInstructions := by
  let X := setFamilyGetDInputEncodedType
  have hTarget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, setFamilyGetDInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
  have hSets :
      TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, setFamilyGetDInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
  have hInit :
      TMPolyTimeMap X setFamilyGetDInstructionEncodedType
        (fun p : X.Carrier => setFamilyGetDInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl EncodedType.nat setStructuredEncodedType) hTarget
    simpa [Function.comp, setFamilyGetDInstructionEncodedType,
      setFamilyGetDInitInstruction, X] using hComp
  have hSetInstruction :
      TMPolyTimeMap setStructuredEncodedType setFamilyGetDInstructionEncodedType
        setFamilyGetDSetInstruction := by
    simpa [setFamilyGetDInstructionEncodedType, setFamilyGetDSetInstruction] using
      TMPolyTimeMap.inr EncodedType.nat setStructuredEncodedType
  have hMappedSets :
      TMPolyTimeMap X setFamilyGetDInstructionListEncodedType
        (fun p : X.Carrier => p.2.map setFamilyGetDSetInstruction) := by
    have hMap := TMPolyTimeMap.list_map hSetInstruction
    have hComp := TMPolyTimeMap.comp hMap hSets
    simpa [Function.comp, setFamilyGetDInstructionListEncodedType,
      setFamilyStructuredEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod setFamilyGetDInstructionEncodedType
          setFamilyGetDInstructionListEncodedType)
        (fun p : X.Carrier =>
          (setFamilyGetDInitInstruction p.1,
            p.2.map setFamilyGetDSetInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hMappedSets
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons setFamilyGetDInstructionEncodedType)
      hConsInput
  simpa [Function.comp, setFamilyGetDInstructions,
    setFamilyGetDInstructionListEncodedType, X] using hCons

theorem setFamilyGetDInitAcc_bound
    (xs : List setFamilyGetDInstructionEncodedType.Carrier) :
    setFamilyGetDAccEncodedType.inputSize setFamilyGetDInitAcc ≤
      (Polynomial.C 10).eval (setFamilyGetDInstructionListEncodedType.inputSize xs) := by
  have hNil : EncodedType.nat.list.inputSize ([] : List Nat) = 0 :=
    EncodedType.inputSize_list_nil EncodedType.nat
  simp [setFamilyGetDInitAcc, setFamilyGetDAccEncodedType, setStructuredEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_nat, EncodedType.inputSize_bool, hNil]

theorem setFamilyGetDStep_growth
    (source : List setFamilyGetDInstructionEncodedType.Carrier)
    (acc : setFamilyGetDAccEncodedType.Carrier)
    (instr : setFamilyGetDInstructionEncodedType.Carrier)
    (hInstr :
      setFamilyGetDInstructionEncodedType.inputSize instr ≤
        setFamilyGetDInstructionListEncodedType.inputSize source) :
    setFamilyGetDAccEncodedType.inputSize (setFamilyGetDStep (acc, instr)) ≤
      setFamilyGetDAccEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 20).eval
          (setFamilyGetDInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨remaining, found, value⟩
  change Nat at remaining
  change Bool at found
  cases instr with
  | inl target =>
      change Nat at target
      have hTargetSize :
          target + 2 ≤ setFamilyGetDInstructionListEncodedType.inputSize source := by
        simpa [setFamilyGetDInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum, EncodedType.nat] using hInstr
      have hNil : EncodedType.nat.list.inputSize ([] : List Nat) = 0 :=
        EncodedType.inputSize_list_nil EncodedType.nat
      simp [setFamilyGetDStep, setFamilyGetDAccEncodedType, setStructuredEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_nat, EncodedType.inputSize_bool,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, hNil]
      omega
  | inr S =>
      have hSetSize :
          setStructuredEncodedType.inputSize S + 1 ≤
            setFamilyGetDInstructionListEncodedType.inputSize source := by
        simpa [setFamilyGetDInstructionEncodedType, EncodedType.inputSize,
          EncodedType.sum] using hInstr
      cases found
      · by_cases hZero : remaining = 0
        · simp [setFamilyGetDStep, setFamilyGetDSetStep, hZero]
          simp [setFamilyGetDAccEncodedType, EncodedType.inputSize_prod,
            EncodedType.inputSize_nat, EncodedType.inputSize_bool]
          omega
        · simp [setFamilyGetDStep, setFamilyGetDSetStep, hZero]
          simp [setFamilyGetDAccEncodedType, EncodedType.inputSize_prod,
            EncodedType.inputSize_nat, EncodedType.inputSize_bool]
          omega
      · by_cases hZero : remaining = 0
        · simp [setFamilyGetDStep, setFamilyGetDSetStep,
            Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        · simp [setFamilyGetDStep, setFamilyGetDSetStep,
            Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

theorem setFamilyGetDFold_tm_polytime :
    TMPolyTimeMap
      setFamilyGetDInstructionListEncodedType
      setFamilyGetDAccEncodedType
      (fun xs : List setFamilyGetDInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => setFamilyGetDStep (acc, instr))
          setFamilyGetDInitAcc) := by
  rcases setFamilyGetDStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      setFamilyGetDInstructionEncodedType setFamilyGetDAccEncodedType
      setFamilyGetDStep setFamilyGetDInitAcc hStep
      (Polynomial.C 10) (Polynomial.C 10 * Polynomial.X + Polynomial.C 20) ?_ ?_
  · intro xs
    exact setFamilyGetDInitAcc_bound xs
  · intro source acc instr hInstr
    exact setFamilyGetDStep_growth source acc instr hInstr

theorem setFamilyGetDFromInstructions_tm_polytime :
    TMPolyTimeMap
      setFamilyGetDInstructionListEncodedType
      setStructuredEncodedType
      setFamilyGetDFromInstructions := by
  have hFold := setFamilyGetDFold_tm_polytime
  have hTail :=
    TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.bool setStructuredEncodedType)
  have hValue := TMPolyTimeMap.snd EncodedType.bool setStructuredEncodedType
  have hTailComp := TMPolyTimeMap.comp hTail hFold
  have hValueComp := TMPolyTimeMap.comp hValue hTailComp
  simpa [Function.comp, setFamilyGetDFromInstructions, setFamilyGetDAccEncodedType]
    using hValueComp

theorem setFamilyGetDFromInput_tm_polytime :
    TMPolyTimeMap
      setFamilyGetDInputEncodedType
      setStructuredEncodedType
      setFamilyGetDFromInput := by
  have hComp :=
    TMPolyTimeMap.comp setFamilyGetDFromInstructions_tm_polytime
      setFamilyGetDInstructions_tm_polytime
  simpa [Function.comp, setFamilyGetDFromInput] using hComp

theorem setFamilyGetD_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod setFamilyStructuredEncodedType EncodedType.nat)
      setStructuredEncodedType
      setFamilyGetD := by
  let X := EncodedType.prod setFamilyStructuredEncodedType EncodedType.nat
  have hSets :
      TMPolyTimeMap X setFamilyStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst setFamilyStructuredEncodedType EncodedType.nat
  have hTarget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd setFamilyStructuredEncodedType EncodedType.nat
  have hInput :
      TMPolyTimeMap X setFamilyGetDInputEncodedType
        (fun p : X.Carrier => (p.2, p.1)) :=
    TMPolyTimeMap.prod_mk hTarget hSets
  have hComp := TMPolyTimeMap.comp setFamilyGetDFromInput_tm_polytime hInput
  convert hComp using 1
  funext p
  rcases p with ⟨sets, target⟩
  exact (setFamilyGetDFromInput_eq_getD (target, sets)).symm

end SteinerTree
end Karp21
end ComplexityReduction
