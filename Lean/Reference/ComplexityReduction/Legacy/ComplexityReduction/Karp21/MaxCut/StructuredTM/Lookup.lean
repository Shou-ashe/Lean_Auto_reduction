import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.StructuredTM.Replicate
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM

namespace ComplexityReduction
namespace Karp21
namespace MaxCut

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Unary list lookup used by the direct structured Partition-to-MaxCut route.

The runner scans a weight list with a countdown index.  It keeps the first value
seen when the countdown reaches zero, and returns `0` when the index is out of
range, matching `List.getD`.
-/

def natListGetDAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat (EncodedType.prod EncodedType.bool EncodedType.nat)

abbrev NatListGetDAccCarrier := Nat × (Bool × Nat)

def natListGetDInstructionEncodedType : EncodedType :=
  EncodedType.sum EncodedType.nat EncodedType.nat

def natListGetDInstructionListEncodedType : EncodedType :=
  EncodedType.list natListGetDInstructionEncodedType

def natListGetDInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat partitionWeightsStructuredEncodedType

def natListGetDInitAcc : NatListGetDAccCarrier :=
  (0, (false, 0))

def natListGetDInitInstruction (target : Nat) :
    natListGetDInstructionEncodedType.Carrier :=
  Sum.inl target

def natListGetDWeightInstruction (w : Nat) :
    natListGetDInstructionEncodedType.Carrier :=
  Sum.inr w

def natListGetDInstructions (p : Nat × List Nat) :
    List natListGetDInstructionEncodedType.Carrier :=
  natListGetDInitInstruction p.1 :: p.2.map natListGetDWeightInstruction

def natListGetDWeightStep (p : NatListGetDAccCarrier × Nat) :
    NatListGetDAccCarrier :=
  let remaining := p.1.1
  let found := p.1.2.1
  let value := p.1.2.2
  let w := p.2
  if found then
    p.1
  else if decide (remaining = 0) then
    (0, (true, w))
  else
    (remaining - 1, (false, value))

def natListGetDStep
    (p : NatListGetDAccCarrier × natListGetDInstructionEncodedType.Carrier) :
    NatListGetDAccCarrier :=
  match p.2 with
  | Sum.inl target => (target, (false, 0))
  | Sum.inr w => natListGetDWeightStep (p.1, w)

def natListGetDFromInstructions
    (xs : List natListGetDInstructionEncodedType.Carrier) : Nat :=
  (xs.foldl (fun acc instr => natListGetDStep (acc, instr)) natListGetDInitAcc).2.2

def natListGetDFromInput (p : Nat × List Nat) : Nat :=
  natListGetDFromInstructions (natListGetDInstructions p)

def natListGetD (p : List Nat × Nat) : Nat :=
  p.1.getD p.2 0

/-! ### Semantics -/

theorem natListGetDWeightStep_found (remaining value w : Nat) :
    natListGetDWeightStep ((remaining, (true, value)), w) =
      (remaining, (true, value)) := by
  simp [natListGetDWeightStep]

theorem natListGetDWeightInstructions_fold_found
    (xs : List Nat) (remaining value : Nat) :
    (xs.map natListGetDWeightInstruction).foldl
        (fun acc instr => natListGetDStep (acc, instr))
        (remaining, (true, value)) =
      (remaining, (true, value)) := by
  induction xs generalizing remaining value with
  | nil =>
      simp
  | cons w ws ih =>
      simpa [natListGetDWeightInstruction, natListGetDStep, natListGetDWeightStep] using
        ih remaining value

theorem natListGetDWeightInstructions_value_eq_getD
    (xs : List Nat) (target : Nat) :
    ((xs.map natListGetDWeightInstruction).foldl
        (fun acc instr => natListGetDStep (acc, instr))
        (target, (false, 0))).2.2 =
      xs.getD target 0 := by
  induction xs generalizing target with
  | nil =>
      cases target <;> simp
  | cons w ws ih =>
      cases target with
      | zero =>
          have h := natListGetDWeightInstructions_fold_found ws 0 w
          simpa [natListGetDWeightInstruction, natListGetDStep, natListGetDWeightStep] using
            congrArg (fun q : NatListGetDAccCarrier => q.2.2) h
      | succ target =>
          simpa [natListGetDWeightInstruction, natListGetDStep, natListGetDWeightStep]
            using ih target

theorem natListGetDFromInput_eq_getD (p : Nat × List Nat) :
    natListGetDFromInput p = p.2.getD p.1 0 := by
  rcases p with ⟨target, xs⟩
  have h := natListGetDWeightInstructions_value_eq_getD xs target
  simp [natListGetDFromInput, natListGetDFromInstructions, natListGetDInstructions,
    natListGetDInitInstruction, natListGetDInitAcc, natListGetDStep] at h ⊢
  exact h

@[simp] theorem natListGetDAccEncodedType_inputSize
    (remaining : Nat) (found : Bool) (value : Nat) :
    natListGetDAccEncodedType.inputSize
        ((remaining, (found, value)) : NatListGetDAccCarrier) =
      remaining + value + 5 := by
  simp [natListGetDAccEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat, EncodedType.inputSize_bool]
  omega

@[simp] theorem natListGetDInstructionEncodedType_inputSize_inl (target : Nat) :
    natListGetDInstructionEncodedType.inputSize (Sum.inl target) = target + 2 := by
  simp [natListGetDInstructionEncodedType, EncodedType.inputSize, EncodedType.sum,
    EncodedType.nat]

@[simp] theorem natListGetDInstructionEncodedType_inputSize_inr (w : Nat) :
    natListGetDInstructionEncodedType.inputSize (Sum.inr w) = w + 2 := by
  simp [natListGetDInstructionEncodedType, EncodedType.inputSize, EncodedType.sum,
    EncodedType.nat]

/-! ### TM witnesses -/

theorem natListGetDWeightStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod natListGetDAccEncodedType EncodedType.nat)
      natListGetDAccEncodedType
      natListGetDWeightStep := by
  let X := EncodedType.prod natListGetDAccEncodedType EncodedType.nat
  let A := natListGetDAccEncodedType
  have hAcc : TMPolyTimeMap X A (fun p : NatListGetDAccCarrier × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst A EncodedType.nat
  have hWeight : TMPolyTimeMap X EncodedType.nat
      (fun p : NatListGetDAccCarrier × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd A EncodedType.nat
  have hRemaining : TMPolyTimeMap X EncodedType.nat
      (fun p : NatListGetDAccCarrier × Nat => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod EncodedType.bool EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, natListGetDAccEncodedType, X] using hComp
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.nat)
        (fun p : NatListGetDAccCarrier × Nat => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod EncodedType.bool EncodedType.nat)
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, natListGetDAccEncodedType, X] using hComp
  have hFound : TMPolyTimeMap X EncodedType.bool
      (fun p : NatListGetDAccCarrier × Nat => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hValue : TMPolyTimeMap X EncodedType.nat
      (fun p : NatListGetDAccCarrier × Nat => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.nat
      (fun _ : NatListGetDAccCarrier × Nat => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat
      (show EncodedType.nat.Carrier from (0 : Nat))
  have hOne : TMPolyTimeMap X EncodedType.nat
      (fun _ : NatListGetDAccCarrier × Nat => (1 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat
      (show EncodedType.nat.Carrier from (1 : Nat))
  have hTrue : TMPolyTimeMap X EncodedType.bool
      (fun _ : NatListGetDAccCarrier × Nat => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hFalse : TMPolyTimeMap X EncodedType.bool
      (fun _ : NatListGetDAccCarrier × Nat => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hRemainingZeroInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : NatListGetDAccCarrier × Nat => (p.1.1, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hRemaining hZero
  have hRemainingIsZero :
      TMPolyTimeMap X EncodedType.bool
        (fun p : NatListGetDAccCarrier × Nat => decide (p.1.1 = 0)) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq hRemainingZeroInput
    simpa [Function.comp, X] using hComp
  have hPredInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : NatListGetDAccCarrier × Nat => (p.1.1, (1 : Nat))) :=
    TMPolyTimeMap.prod_mk hRemaining hOne
  have hPred :
      TMPolyTimeMap X EncodedType.nat
        (fun p : NatListGetDAccCarrier × Nat => p.1.1 - 1) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hPredInput
    simpa [Function.comp, X] using hComp
  have hHitTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.nat)
        (fun p : NatListGetDAccCarrier × Nat => (true, p.2)) :=
    TMPolyTimeMap.prod_mk hTrue hWeight
  have hHit :
      TMPolyTimeMap X A
        (fun p : NatListGetDAccCarrier × Nat =>
          (show NatListGetDAccCarrier from (0, (true, p.2)))) :=
    TMPolyTimeMap.prod_mk hZero hHitTail
  have hMissTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.nat)
        (fun p : NatListGetDAccCarrier × Nat => (false, p.1.2.2)) :=
    TMPolyTimeMap.prod_mk hFalse hValue
  have hMiss :
      TMPolyTimeMap X A
        (fun p : NatListGetDAccCarrier × Nat => (p.1.1 - 1, (false, p.1.2.2))) :=
    TMPolyTimeMap.prod_mk hPred hMissTail
  have hZeroBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : NatListGetDAccCarrier × Nat => (decide (p.1.1 = 0), p)) :=
    TMPolyTimeMap.prod_mk hRemainingIsZero (TMPolyTimeMap.id X)
  have hZeroBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × (NatListGetDAccCarrier × Nat) =>
          match p.1 with
          | true => (show NatListGetDAccCarrier from (0, (true, p.2.2)))
          | false =>
              (show NatListGetDAccCarrier from
                (p.2.1.1 - 1, (false, p.2.1.2.2)))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : NatListGetDAccCarrier × Nat =>
        (show NatListGetDAccCarrier from (p.1.1 - 1, (false, p.1.2.2))))
      (fTrue := fun p : NatListGetDAccCarrier × Nat =>
        (show NatListGetDAccCarrier from (0, (true, p.2))))
      hMiss hHit
  have hNotFound :
      TMPolyTimeMap X A
        (fun p : NatListGetDAccCarrier × Nat =>
          if decide (p.1.1 = 0) then
            (show NatListGetDAccCarrier from (0, (true, p.2)))
          else
            (show NatListGetDAccCarrier from (p.1.1 - 1, (false, p.1.2.2)))) := by
    have hComp := TMPolyTimeMap.comp hZeroBranch hZeroBranchInput
    convert hComp using 1
    funext p
    by_cases h : p.1.1 = 0 <;> simp [Function.comp, h]
  have hFoundBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : NatListGetDAccCarrier × Nat => (p.1.2.1, p)) :=
    TMPolyTimeMap.prod_mk hFound (TMPolyTimeMap.id X)
  have hFoundBranch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool × (NatListGetDAccCarrier × Nat) =>
          match p.1 with
          | true => p.2.1
          | false =>
              if decide (p.2.1.1 = 0) then
                (show NatListGetDAccCarrier from (0, (true, p.2.2)))
              else
                (show NatListGetDAccCarrier from
                  (p.2.1.1 - 1, (false, p.2.1.2.2)))) :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : NatListGetDAccCarrier × Nat =>
        if decide (p.1.1 = 0) then
          (show NatListGetDAccCarrier from (0, (true, p.2)))
        else
          (show NatListGetDAccCarrier from (p.1.1 - 1, (false, p.1.2.2))))
      (fTrue := fun p : NatListGetDAccCarrier × Nat => p.1)
      hNotFound hAcc
  have hOut := TMPolyTimeMap.comp hFoundBranch hFoundBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨remaining, found, value⟩, w⟩
  cases found <;> by_cases h : remaining = 0 <;>
    simp [Function.comp, natListGetDWeightStep, h]

theorem natListGetDStepLeft_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      natListGetDAccEncodedType
      (fun target : Nat => (show NatListGetDAccCarrier from (target, (false, 0)))) := by
  have hTarget := TMPolyTimeMap.id EncodedType.nat
  have hFalse : TMPolyTimeMap EncodedType.nat EncodedType.bool (fun _ : Nat => false) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.bool false
  have hZero :
      TMPolyTimeMap EncodedType.nat EncodedType.nat
        (fun _ : EncodedType.nat.Carrier =>
          (show EncodedType.nat.Carrier from (0 : Nat))) :=
    TMPolyTimeMap.const EncodedType.nat EncodedType.nat
      (show EncodedType.nat.Carrier from (0 : Nat))
  have hTail :
      TMPolyTimeMap EncodedType.nat
        (EncodedType.prod EncodedType.bool EncodedType.nat)
        (fun _ : Nat => (false, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hFalse hZero
  have hOut := TMPolyTimeMap.prod_mk hTarget hTail
  simpa [natListGetDAccEncodedType] using hOut

theorem natListGetDStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod natListGetDAccEncodedType natListGetDInstructionEncodedType)
      natListGetDAccEncodedType
      natListGetDStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      natListGetDAccEncodedType EncodedType.nat EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim natListGetDStepLeft_tm_polytime
      natListGetDWeightStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem natListGetDInstructions_tm_polytime :
    TMPolyTimeMap
      natListGetDInputEncodedType
      natListGetDInstructionListEncodedType
      natListGetDInstructions := by
  let X := natListGetDInputEncodedType
  have hTarget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, natListGetDInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat partitionWeightsStructuredEncodedType
  have hWeights :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, natListGetDInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat partitionWeightsStructuredEncodedType
  have hInit :
      TMPolyTimeMap X natListGetDInstructionEncodedType
        (fun p : X.Carrier => natListGetDInitInstruction p.1) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl EncodedType.nat EncodedType.nat) hTarget
    simpa [Function.comp, natListGetDInstructionEncodedType,
      natListGetDInitInstruction, X] using hComp
  have hWeightInstruction :
      TMPolyTimeMap EncodedType.nat natListGetDInstructionEncodedType
        natListGetDWeightInstruction := by
    simpa [natListGetDInstructionEncodedType, natListGetDWeightInstruction] using
      TMPolyTimeMap.inr EncodedType.nat EncodedType.nat
  have hMappedWeights :
      TMPolyTimeMap X natListGetDInstructionListEncodedType
        (fun p : X.Carrier => p.2.map natListGetDWeightInstruction) := by
    have hMap := TMPolyTimeMap.list_map hWeightInstruction
    have hComp := TMPolyTimeMap.comp hMap hWeights
    simpa [Function.comp, natListGetDInstructionListEncodedType,
      partitionWeightsStructuredEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod natListGetDInstructionEncodedType
          natListGetDInstructionListEncodedType)
        (fun p : X.Carrier =>
          (natListGetDInitInstruction p.1,
            p.2.map natListGetDWeightInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hMappedWeights
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons natListGetDInstructionEncodedType)
      hConsInput
  simpa [Function.comp, natListGetDInstructions, natListGetDInstructionListEncodedType, X]
    using hCons

theorem natListGetDInitAcc_bound
    (xs : List natListGetDInstructionEncodedType.Carrier) :
    natListGetDAccEncodedType.inputSize natListGetDInitAcc ≤
      (Polynomial.C 10).eval (natListGetDInstructionListEncodedType.inputSize xs) := by
  simp [natListGetDInitAcc, natListGetDAccEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat, EncodedType.inputSize_bool]

theorem natListGetDStep_growth
    (source : List natListGetDInstructionEncodedType.Carrier)
    (acc : natListGetDAccEncodedType.Carrier)
    (instr : natListGetDInstructionEncodedType.Carrier)
    (hInstr :
      natListGetDInstructionEncodedType.inputSize instr ≤
        natListGetDInstructionListEncodedType.inputSize source) :
    natListGetDAccEncodedType.inputSize (natListGetDStep (acc, instr)) ≤
      natListGetDAccEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 20).eval
          (natListGetDInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨remaining, found, value⟩
  change Nat at remaining
  change Bool at found
  change Nat at value
  cases instr with
  | inl target =>
      change Nat at target
      have hTargetSize :
          target + 2 ≤ natListGetDInstructionListEncodedType.inputSize source := by
        simpa using hInstr
      simp [natListGetDStep, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at ⊢
      omega
  | inr w =>
      change Nat at w
      have hWeightSize :
          w + 2 ≤ natListGetDInstructionListEncodedType.inputSize source := by
        simpa using hInstr
      cases found
      · by_cases hZero : remaining = 0
        · simp [natListGetDStep, natListGetDWeightStep, hZero]
          simp [natListGetDAccEncodedType, EncodedType.inputSize_prod,
            EncodedType.inputSize_nat, EncodedType.inputSize_bool]
          omega
        · simp [natListGetDStep, natListGetDWeightStep, hZero]
          simp [natListGetDAccEncodedType, EncodedType.inputSize_prod,
            EncodedType.inputSize_nat, EncodedType.inputSize_bool]
          omega
      · by_cases hZero : remaining = 0
        · simp [natListGetDStep, natListGetDWeightStep,
            Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        · simp [natListGetDStep, natListGetDWeightStep,
            Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

theorem natListGetDFold_tm_polytime :
    TMPolyTimeMap
      natListGetDInstructionListEncodedType
      natListGetDAccEncodedType
      (fun xs : List natListGetDInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => natListGetDStep (acc, instr)) natListGetDInitAcc) := by
  rcases natListGetDStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      natListGetDInstructionEncodedType natListGetDAccEncodedType
      natListGetDStep natListGetDInitAcc hStep
      (Polynomial.C 10) (Polynomial.C 10 * Polynomial.X + Polynomial.C 20) ?_ ?_
  · intro xs
    exact natListGetDInitAcc_bound xs
  · intro source acc instr hInstr
    exact natListGetDStep_growth source acc instr hInstr

theorem natListGetDFromInstructions_tm_polytime :
    TMPolyTimeMap
      natListGetDInstructionListEncodedType
      EncodedType.nat
      natListGetDFromInstructions := by
  have hFold := natListGetDFold_tm_polytime
  have hTail :=
    TMPolyTimeMap.snd EncodedType.nat (EncodedType.prod EncodedType.bool EncodedType.nat)
  have hValue := TMPolyTimeMap.snd EncodedType.bool EncodedType.nat
  have hTailComp := TMPolyTimeMap.comp hTail hFold
  have hValueComp := TMPolyTimeMap.comp hValue hTailComp
  simpa [Function.comp, natListGetDFromInstructions, natListGetDAccEncodedType]
    using hValueComp

theorem natListGetDFromInput_tm_polytime :
    TMPolyTimeMap
      natListGetDInputEncodedType
      EncodedType.nat
      natListGetDFromInput := by
  have hComp :=
    TMPolyTimeMap.comp natListGetDFromInstructions_tm_polytime
      natListGetDInstructions_tm_polytime
  simpa [Function.comp, natListGetDFromInput] using hComp

theorem natListGetD_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod partitionWeightsStructuredEncodedType EncodedType.nat)
      EncodedType.nat
      natListGetD := by
  let X := EncodedType.prod partitionWeightsStructuredEncodedType EncodedType.nat
  have hWeights :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst partitionWeightsStructuredEncodedType EncodedType.nat
  have hTarget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd partitionWeightsStructuredEncodedType EncodedType.nat
  have hInput :
      TMPolyTimeMap X natListGetDInputEncodedType
        (fun p : X.Carrier => (p.2, p.1)) :=
    TMPolyTimeMap.prod_mk hTarget hWeights
  have hComp := TMPolyTimeMap.comp natListGetDFromInput_tm_polytime hInput
  convert hComp using 1
  funext p
  rcases p with ⟨weights, target⟩
  exact (natListGetDFromInput_eq_getD (target, weights)).symm

end MaxCut
end Karp21
end ComplexityReduction
