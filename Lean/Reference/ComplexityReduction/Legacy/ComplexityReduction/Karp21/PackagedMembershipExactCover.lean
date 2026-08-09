/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetSystem
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipExactCoverAtMostOne
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SteinerTreeStructuredTM.WellFormed
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.HittingSet.IndexRunner
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.Part5
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FiniteWitness
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatRange
import Mathlib.Tactic

/-!
Direct standard-TM NP membership witness for faithful structured Exact Cover.

The certificate is a list of indices into the original set family.  The verifier
checks that the indices are bounded, that every universe element is covered by
some selected index, and that no universe element is covered by two selected
indices.  Soundness decodes the selected sets and deduplicates them before
returning the textbook Exact Cover witness.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics

namespace ExactCover

def asSetCoveringInput (I : ExactCoverInput) : SetCoveringInput where
  system := I.system
  k := I.system.sets.length

/-! ### Universe-element checks -/

def elementCoveringIndices (sets : List (List Nat)) (x : Nat) : List Nat :=
  HittingSet.setIndexIndicesFromFamily (x, sets)

def elementCoveringIndices_mem_iff
    (sets : List (List Nat)) (x j : Nat) :
    j ∈ elementCoveringIndices sets x ↔ j < sets.length ∧ x ∈ sets.getD j [] := by
  let I : SetCoveringInput := { system := { universeSize := 0, sets := sets }, k := 0 }
  have hIdx := HittingSet.setIndexIndicesFromFamily_eq_indicesContaining I x
  have hMem := HittingSet.mem_indicesContaining_iff I x j
  simpa [elementCoveringIndices, I, HittingSet.indicesContaining] using
    hIdx ▸ hMem

def elementCoveredByIndicesBool
    (p : (List (List Nat) × List Nat) × Nat) : Bool :=
  HittingSet.setHitBool (elementCoveringIndices p.1.1 p.2, p.1.2)

def elementAtMostOnceByIndicesBool
    (p : (List (List Nat) × List Nat) × Nat) : Bool :=
  atMostOneHitBool (elementCoveringIndices p.1.1 p.2, p.1.2)

def elementExactCoverOKBool
    (p : (List (List Nat) × List Nat) × Nat) : Bool :=
  graphBoolAndPair
    (elementCoveredByIndicesBool p, elementAtMostOnceByIndicesBool p)

theorem elementCoveredByIndicesBool_eq_true_iff
    (sets : List (List Nat)) (idxs : List Nat) (x : Nat) :
    elementCoveredByIndicesBool ((sets, idxs), x) = true ↔
      ∃ j ∈ idxs, j < sets.length ∧ x ∈ sets.getD j [] := by
  rw [elementCoveredByIndicesBool, HittingSet.setHitBool_eq_true_iff]
  constructor
  · rintro ⟨j, hj, hTarget⟩
    exact ⟨j, hj, (elementCoveringIndices_mem_iff sets x j).1 hTarget⟩
  · rintro ⟨j, hj, hTarget⟩
    exact ⟨j, hj, (elementCoveringIndices_mem_iff sets x j).2 hTarget⟩

theorem elementAtMostOnceByIndicesBool_eq_true_iff
    (sets : List (List Nat)) (idxs : List Nat) (x : Nat) :
    elementAtMostOnceByIndicesBool ((sets, idxs), x) = true ↔
      AtMostOneHitList (elementCoveringIndices sets x) idxs := by
  simpa [elementAtMostOnceByIndicesBool] using
    atMostOneHitBool_eq_true_iff (elementCoveringIndices sets x, idxs)

theorem elementExactCoverOKBool_eq_true_iff
    (sets : List (List Nat)) (idxs : List Nat) (x : Nat) :
    elementExactCoverOKBool ((sets, idxs), x) = true ↔
      (∃ j ∈ idxs, j < sets.length ∧ x ∈ sets.getD j []) ∧
        AtMostOneHitList (elementCoveringIndices sets x) idxs := by
  rw [elementExactCoverOKBool, graphBoolAndPair_eq_true_iff,
    elementCoveredByIndicesBool_eq_true_iff,
    elementAtMostOnceByIndicesBool_eq_true_iff]

theorem elementExactCoverOKBool_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod
        (EncodedType.prod setFamilyStructuredEncodedType setStructuredEncodedType)
        EncodedType.nat)
      EncodedType.bool
      elementExactCoverOKBool := by
  let X :=
    EncodedType.prod
      (EncodedType.prod setFamilyStructuredEncodedType setStructuredEncodedType)
      EncodedType.nat
  have hPayload : TMPolyTimeMap X
      (EncodedType.prod setFamilyStructuredEncodedType setStructuredEncodedType)
      (fun p : X.Carrier => p.1) := by
    simpa [X] using
      TMPolyTimeMap.fst
        (EncodedType.prod setFamilyStructuredEncodedType setStructuredEncodedType)
        EncodedType.nat
  have hX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using
      TMPolyTimeMap.snd
        (EncodedType.prod setFamilyStructuredEncodedType setStructuredEncodedType)
        EncodedType.nat
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType
      (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst setFamilyStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, X] using hComp
  have hIdxs : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd setFamilyStructuredEncodedType setStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, X] using hComp
  have hTargetInput :
      TMPolyTimeMap X HittingSet.setIndexInstructionInputEncodedType
        (fun p : X.Carrier => (p.2, p.1.1)) :=
    TMPolyTimeMap.prod_mk hX hSets
  have hTarget :
      TMPolyTimeMap X setStructuredEncodedType
        (fun p : X.Carrier => elementCoveringIndices p.1.1 p.2) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setIndexIndicesFromFamily_tm_polytime
      hTargetInput
    simpa [Function.comp, HittingSet.setIndexInstructionInputEncodedType,
      elementCoveringIndices, setStructuredEncodedType, X] using hComp
  have hHitInput :
      TMPolyTimeMap X HittingSet.setHitInstructionInputEncodedType
        (fun p : X.Carrier => (elementCoveringIndices p.1.1 p.2, p.1.2)) :=
    TMPolyTimeMap.prod_mk hTarget hIdxs
  have hCovered :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => elementCoveredByIndicesBool p) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setHitBool_tm_polytime hHitInput
    simpa [Function.comp, elementCoveredByIndicesBool,
      HittingSet.setHitInstructionInputEncodedType, X] using hComp
  have hAtMostInput :
      TMPolyTimeMap X atMostOneHitInputEncodedType
        (fun p : X.Carrier => (elementCoveringIndices p.1.1 p.2, p.1.2)) :=
    TMPolyTimeMap.prod_mk hTarget hIdxs
  have hAtMost :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => elementAtMostOnceByIndicesBool p) := by
    have hComp := TMPolyTimeMap.comp atMostOneHitBool_tm_polytime hAtMostInput
    simpa [Function.comp, elementAtMostOnceByIndicesBool,
      atMostOneHitInputEncodedType, X] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (elementCoveredByIndicesBool p, elementAtMostOnceByIndicesBool p)) :=
    TMPolyTimeMap.prod_mk hCovered hAtMost
  have hAnd := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
  simpa [Function.comp, elementExactCoverOKBool, X] using hAnd

def universeCheckPayloadEncodedType : EncodedType :=
  EncodedType.prod setFamilyStructuredEncodedType setStructuredEncodedType

def universeCheckAccEncodedType : EncodedType :=
  EncodedType.prod universeCheckPayloadEncodedType EncodedType.bool

def universeCheckInstructionEncodedType : EncodedType :=
  EncodedType.sum universeCheckPayloadEncodedType EncodedType.nat

def universeCheckInstructionListEncodedType : EncodedType :=
  EncodedType.list universeCheckInstructionEncodedType

def universeCheckInputEncodedType : EncodedType :=
  EncodedType.prod exactCoverStructuredEncodedType setStructuredEncodedType

def universeCheckInitAcc : (List (List Nat) × List Nat) × Bool :=
  (([], []), true)

def universeCheckInitInstruction (payload : List (List Nat) × List Nat) :
    universeCheckInstructionEncodedType.Carrier :=
  Sum.inl payload

def universeCheckElementInstruction (x : Nat) :
    universeCheckInstructionEncodedType.Carrier :=
  Sum.inr x

def universeCheckInstructions (p : ExactCoverInput × List Nat) :
    List universeCheckInstructionEncodedType.Carrier :=
  universeCheckInitInstruction (p.1.system.sets, p.2) ::
    (List.range p.1.system.universeSize).map universeCheckElementInstruction

def universeCheckElementStep
    (p : universeCheckAccEncodedType.Carrier × Nat) :
    universeCheckAccEncodedType.Carrier :=
  (p.1.1, graphBoolAndPair (p.1.2, elementExactCoverOKBool (p.1.1, p.2)))

def universeCheckStep
    (p : universeCheckAccEncodedType.Carrier × universeCheckInstructionEncodedType.Carrier) :
    universeCheckAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl payload => (payload, true)
  | Sum.inr x => universeCheckElementStep (p.1, x)

def universeCheckFromInstructions
    (xs : List universeCheckInstructionEncodedType.Carrier) : Bool :=
  (xs.foldl (fun acc instr => universeCheckStep (acc, instr)) universeCheckInitAcc).2

def universeCheckBool (p : ExactCoverInput × List Nat) : Bool :=
  universeCheckFromInstructions (universeCheckInstructions p)

theorem universeCheckElementFold_eq_true_iff
    (xs : List Nat) (payload : List (List Nat) × List Nat) (ok : Bool) :
    ((xs.map universeCheckElementInstruction).foldl
        (fun acc instr => universeCheckStep (acc, instr)) (payload, ok)).2 = true ↔
      ok = true ∧ ∀ x ∈ xs, elementExactCoverOKBool (payload, x) = true := by
  induction xs generalizing ok with
  | nil =>
      constructor
      · intro h
        exact ⟨h, by simp⟩
      · intro h
        exact h.1
  | cons x xs ih =>
      rw [List.map_cons, List.foldl_cons]
      have hTail := ih (graphBoolAndPair (ok, elementExactCoverOKBool (payload, x)))
      simp [universeCheckElementInstruction, universeCheckStep, universeCheckElementStep,
        graphBoolAndPair_eq_true_iff, and_assoc] at hTail ⊢
      exact hTail

theorem universeCheckBool_eq_true_iff (I : ExactCoverInput) (idxs : List Nat) :
    universeCheckBool (I, idxs) = true ↔
      ∀ x, x < I.system.universeSize →
        (∃ j ∈ idxs, j < I.system.sets.length ∧ x ∈ I.system.sets.getD j []) ∧
          AtMostOneHitList (elementCoveringIndices I.system.sets x) idxs := by
  change
    (((universeCheckInitInstruction (I.system.sets, idxs) ::
      (List.range I.system.universeSize).map universeCheckElementInstruction).foldl
        (fun acc instr => universeCheckStep (acc, instr))
        universeCheckInitAcc).2 = true) ↔ _
  rw [List.foldl_cons]
  have hFold :=
    universeCheckElementFold_eq_true_iff
      (List.range I.system.universeSize) (I.system.sets, idxs) true
  constructor
  · intro h x hx
    rcases hFold.1 h with ⟨_hok, hAll⟩
    have hxMem : x ∈ List.range I.system.universeSize := by simpa using hx
    exact (elementExactCoverOKBool_eq_true_iff I.system.sets idxs x).1 (hAll x hxMem)
  · intro h
    apply hFold.2
    refine ⟨rfl, ?_⟩
    intro x hxMem
    exact (elementExactCoverOKBool_eq_true_iff I.system.sets idxs x).2
      (h x (by simpa using hxMem))

theorem universeCheckInitInstruction_tm_polytime :
    TMPolyTimeMap
      universeCheckPayloadEncodedType
      universeCheckInstructionEncodedType
      universeCheckInitInstruction := by
  simpa [universeCheckInstructionEncodedType, universeCheckInitInstruction] using
    TMPolyTimeMap.inl universeCheckPayloadEncodedType EncodedType.nat

theorem universeCheckElementInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      universeCheckInstructionEncodedType
      universeCheckElementInstruction := by
  simpa [universeCheckInstructionEncodedType, universeCheckElementInstruction] using
    TMPolyTimeMap.inr universeCheckPayloadEncodedType EncodedType.nat

theorem universeCheckInstructions_tm_polytime :
    TMPolyTimeMap
      universeCheckInputEncodedType
      universeCheckInstructionListEncodedType
      universeCheckInstructions := by
  let X := universeCheckInputEncodedType
  have hI : TMPolyTimeMap X exactCoverStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, universeCheckInputEncodedType] using
      TMPolyTimeMap.fst exactCoverStructuredEncodedType setStructuredEncodedType
  have hIdxs : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, universeCheckInputEncodedType] using
      TMPolyTimeMap.snd exactCoverStructuredEncodedType setStructuredEncodedType
  have hSystem : TMPolyTimeMap X setSystemStructuredEncodedType
      (fun p : X.Carrier => p.1.system) := by
    have hComp := TMPolyTimeMap.comp
      SteinerTree.exactCoverSystemTMBackedMap.tm_polytime hI
    simpa [Function.comp, X] using hComp
  have hTuple : TMPolyTimeMap X setSystemTupleStructuredEncodedType
      (fun p : X.Carrier => (p.1.system.universeSize, p.1.system.sets)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setSystemInputToTupleTMBackedMap.tm_polytime
      hSystem
    simpa [Function.comp, HittingSet.setSystemInputToTuple, X] using hComp
  have hUniverse : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.1.system.universeSize) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTuple
    simpa [Function.comp, setSystemTupleStructuredEncodedType, X] using hComp
  have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType
      (fun p : X.Carrier => p.1.system.sets) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTuple
    simpa [Function.comp, setSystemTupleStructuredEncodedType, X] using hComp
  have hPayload : TMPolyTimeMap X universeCheckPayloadEncodedType
      (fun p : X.Carrier => (p.1.system.sets, p.2)) :=
    TMPolyTimeMap.prod_mk hSets hIdxs
  have hInit : TMPolyTimeMap X universeCheckInstructionEncodedType
      (fun p : X.Carrier => universeCheckInitInstruction (p.1.system.sets, p.2)) := by
    have hComp := TMPolyTimeMap.comp universeCheckInitInstruction_tm_polytime hPayload
    simpa [Function.comp, universeCheckPayloadEncodedType, X] using hComp
  have hInitSingleton : TMPolyTimeMap X universeCheckInstructionListEncodedType
      (fun p : X.Carrier => [universeCheckInitInstruction (p.1.system.sets, p.2)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton universeCheckInstructionEncodedType) hInit
    simpa [Function.comp, universeCheckInstructionListEncodedType, X] using hComp
  have hRange : TMPolyTimeMap X setStructuredEncodedType
      (fun p : X.Carrier => List.range p.1.system.universeSize) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hUniverse
    simpa [Function.comp, setStructuredEncodedType, X] using hComp
  have hElementInstructions :
      TMPolyTimeMap X universeCheckInstructionListEncodedType
        (fun p : X.Carrier =>
          (List.range p.1.system.universeSize).map universeCheckElementInstruction) := by
    have hMap := TMPolyTimeMap.list_map universeCheckElementInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, universeCheckInstructionListEncodedType, setStructuredEncodedType, X]
      using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod universeCheckInstructionListEncodedType
          universeCheckInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([universeCheckInitInstruction (p.1.system.sets, p.2)],
            (List.range p.1.system.universeSize).map universeCheckElementInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hElementInstructions
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append universeCheckInstructionEncodedType) hAppendInput
  simpa [Function.comp, universeCheckInstructions, universeCheckInstructionListEncodedType, X]
    using hOut

theorem universeCheckElementStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod universeCheckAccEncodedType EncodedType.nat)
      universeCheckAccEncodedType
      universeCheckElementStep := by
  let X := EncodedType.prod universeCheckAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X universeCheckAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst universeCheckAccEncodedType EncodedType.nat
  have hX : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd universeCheckAccEncodedType EncodedType.nat
  have hPayload : TMPolyTimeMap X universeCheckPayloadEncodedType
      (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst universeCheckPayloadEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, universeCheckAccEncodedType, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd universeCheckPayloadEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, universeCheckAccEncodedType, X] using hComp
  have hElementInput :
      TMPolyTimeMap X
        (EncodedType.prod universeCheckPayloadEncodedType EncodedType.nat)
        (fun p : X.Carrier => (p.1.1, p.2)) :=
    TMPolyTimeMap.prod_mk hPayload hX
  have hElementOK : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => elementExactCoverOKBool (p.1.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp elementExactCoverOKBool_tm_polytime hElementInput
    simpa [Function.comp, universeCheckPayloadEncodedType, X] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier => (p.1.2, elementExactCoverOKBool (p.1.1, p.2))) :=
    TMPolyTimeMap.prod_mk hOk hElementOK
  have hAnd : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => graphBoolAndPair (p.1.2, elementExactCoverOKBool (p.1.1, p.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp, X] using hComp
  have hOut := TMPolyTimeMap.prod_mk hPayload hAnd
  simpa [universeCheckElementStep, universeCheckAccEncodedType, X] using hOut

theorem universeCheckStepLeft_tm_polytime :
    TMPolyTimeMap
      universeCheckPayloadEncodedType
      universeCheckAccEncodedType
      (fun payload : universeCheckPayloadEncodedType.Carrier => (payload, true)) := by
  have hPayload := TMPolyTimeMap.id universeCheckPayloadEncodedType
  have hTrue : TMPolyTimeMap universeCheckPayloadEncodedType EncodedType.bool
      (fun _ => true) :=
    TMPolyTimeMap.const universeCheckPayloadEncodedType EncodedType.bool true
  simpa [universeCheckAccEncodedType] using TMPolyTimeMap.prod_mk hPayload hTrue

theorem universeCheckStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod universeCheckAccEncodedType universeCheckInstructionEncodedType)
      universeCheckAccEncodedType
      universeCheckStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      universeCheckAccEncodedType universeCheckPayloadEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim universeCheckStepLeft_tm_polytime
      universeCheckElementStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem universeCheckStep_growth
    (source : List universeCheckInstructionEncodedType.Carrier)
    (acc : universeCheckAccEncodedType.Carrier)
    (instr : universeCheckInstructionEncodedType.Carrier)
    (hInstr :
      universeCheckInstructionEncodedType.inputSize instr ≤
        universeCheckInstructionListEncodedType.inputSize source) :
    universeCheckAccEncodedType.inputSize (universeCheckStep (acc, instr)) ≤
      universeCheckAccEncodedType.inputSize acc +
        (Polynomial.X + Polynomial.C 20).eval
          (universeCheckInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨payload, ok⟩
  cases instr with
  | inl newPayload =>
      have hLocal :
          universeCheckAccEncodedType.inputSize (newPayload, true) ≤
            universeCheckInstructionEncodedType.inputSize (Sum.inl newPayload) + 20 := by
        simp [universeCheckAccEncodedType,
          universeCheckInstructionEncodedType, EncodedType.inputSize,
          EncodedType.prod, EncodedType.sum, EncodedType.bool]
      exact calc
        universeCheckAccEncodedType.inputSize
            (universeCheckStep ((payload, ok), Sum.inl newPayload))
            ≤ universeCheckInstructionEncodedType.inputSize (Sum.inl newPayload) + 20 := by
              simpa [universeCheckStep] using hLocal
        _ ≤ universeCheckInstructionListEncodedType.inputSize source + 20 :=
              Nat.add_le_add_right hInstr 20
        _ ≤ universeCheckAccEncodedType.inputSize (payload, ok) +
              (Polynomial.X + Polynomial.C 20).eval
                (universeCheckInstructionListEncodedType.inputSize source) := by
              simp [Polynomial.eval_add]
  | inr x =>
      cases h : elementExactCoverOKBool (payload, x) <;>
        cases ok <;>
          simp [universeCheckStep, universeCheckElementStep, h,
            universeCheckAccEncodedType, EncodedType.inputSize_prod,
            EncodedType.inputSize_bool, Polynomial.eval_add]

theorem universeCheckFold_tm_polytime :
    TMPolyTimeMap
      universeCheckInstructionListEncodedType
      universeCheckAccEncodedType
      (fun xs : List universeCheckInstructionEncodedType.Carrier =>
        xs.foldl (fun acc x => universeCheckStep (acc, x)) universeCheckInitAcc) := by
  rcases universeCheckStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      universeCheckInstructionEncodedType universeCheckAccEncodedType
      universeCheckStep universeCheckInitAcc hStep
      (Polynomial.C 20) (Polynomial.X + Polynomial.C 20) ?_ ?_
  · intro xs
    have hNilSet : setStructuredEncodedType.inputSize ([] : List Nat) = 0 := by
      native_decide
    have hNilFamily : setFamilyStructuredEncodedType.inputSize ([] : List (List Nat)) = 0 := by
      native_decide
    simp [universeCheckInitAcc, universeCheckAccEncodedType, universeCheckPayloadEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_bool, hNilSet, hNilFamily]
  · intro source acc instr hInstr
    exact universeCheckStep_growth source acc instr hInstr

theorem universeCheckFromInstructions_tm_polytime :
    TMPolyTimeMap
      universeCheckInstructionListEncodedType
      EncodedType.bool
      universeCheckFromInstructions := by
  have hFold := universeCheckFold_tm_polytime
  have hSnd := TMPolyTimeMap.snd universeCheckPayloadEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hSnd hFold
  simpa [Function.comp, universeCheckFromInstructions, universeCheckAccEncodedType] using hComp

theorem universeCheckBool_tm_polytime :
    TMPolyTimeMap
      universeCheckInputEncodedType
      EncodedType.bool
      universeCheckBool := by
  have hComp := TMPolyTimeMap.comp universeCheckFromInstructions_tm_polytime
    universeCheckInstructions_tm_polytime
  simpa [Function.comp, universeCheckBool] using hComp

/-! ### Full finite verifier -/

def exactCoverStructuredFiniteVerify (I : ExactCoverInput) (idxs : List Nat) : Bool :=
  graphBoolAndPair
    (SteinerTree.exactCoverWellFormedBool I,
      graphBoolAndPair
        (HittingSet.boundedNatListBool (I.system.sets.length, idxs),
          universeCheckBool (I, idxs)))

theorem exactCoverStructuredFiniteVerify_eq_true_iff
    (I : ExactCoverInput) (idxs : List Nat) :
    exactCoverStructuredFiniteVerify I idxs = true ↔
      SetSystemWellFormed I.system ∧
        (∀ j ∈ idxs, j < I.system.sets.length) ∧
        ∀ x, x < I.system.universeSize →
          (∃ j ∈ idxs, j < I.system.sets.length ∧ x ∈ I.system.sets.getD j []) ∧
            AtMostOneHitList (elementCoveringIndices I.system.sets x) idxs := by
  rw [exactCoverStructuredFiniteVerify, graphBoolAndPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff, SteinerTree.exactCoverWellFormedBool_eq_true_iff,
    HittingSet.boundedNatListBool_eq_true_iff, universeCheckBool_eq_true_iff]

theorem exactCoverStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod exactCoverStructuredEncodedType setStructuredEncodedType)
      EncodedType.bool
      (fun p : ExactCoverInput × List Nat =>
        exactCoverStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod exactCoverStructuredEncodedType setStructuredEncodedType
  have hI : TMPolyTimeMap X exactCoverStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst exactCoverStructuredEncodedType setStructuredEncodedType
  have hIdxs : TMPolyTimeMap X setStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd exactCoverStructuredEncodedType setStructuredEncodedType
  have hSystem : TMPolyTimeMap X setSystemStructuredEncodedType
      (fun p : X.Carrier => p.1.system) := by
    have hComp := TMPolyTimeMap.comp
      SteinerTree.exactCoverSystemTMBackedMap.tm_polytime hI
    simpa [Function.comp, X] using hComp
  have hTuple : TMPolyTimeMap X setSystemTupleStructuredEncodedType
      (fun p : X.Carrier => (p.1.system.universeSize, p.1.system.sets)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.setSystemInputToTupleTMBackedMap.tm_polytime
      hSystem
    simpa [Function.comp, HittingSet.setSystemInputToTuple, X] using hComp
  have hSetsLength : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.1.system.sets.length) := by
    have hSets : TMPolyTimeMap X setFamilyStructuredEncodedType
        (fun p : X.Carrier => p.1.system.sets) := by
      have hSnd := TMPolyTimeMap.snd EncodedType.nat setFamilyStructuredEncodedType
      have hComp := TMPolyTimeMap.comp hSnd hTuple
      simpa [Function.comp, setSystemTupleStructuredEncodedType, X] using hComp
    have hComp := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap setStructuredEncodedType).tm_polytime hSets
    simpa [Function.comp, setFamilyStructuredEncodedType, X] using hComp
  have hWellFormed : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => SteinerTree.exactCoverWellFormedBool p.1) := by
    have hComp := TMPolyTimeMap.comp SteinerTree.exactCoverWellFormedBool_tm_polytime hI
    simpa [Function.comp, X] using hComp
  have hBoundInput :
      TMPolyTimeMap X HittingSet.boundedNatInstructionInputEncodedType
        (fun p : X.Carrier => (p.1.system.sets.length, p.2)) :=
    TMPolyTimeMap.prod_mk hSetsLength hIdxs
  have hBound : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => HittingSet.boundedNatListBool (p.1.system.sets.length, p.2)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.boundedNatListBool_tm_polytime hBoundInput
    simpa [Function.comp, HittingSet.boundedNatInstructionInputEncodedType, X] using hComp
  have hUniverseInput :
      TMPolyTimeMap X universeCheckInputEncodedType
        (fun p : X.Carrier => (p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hI hIdxs
  have hUniverse : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => universeCheckBool (p.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp universeCheckBool_tm_polytime hUniverseInput
    simpa [Function.comp, universeCheckInputEncodedType, X] using hComp
  have hTailInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (HittingSet.boundedNatListBool (p.1.system.sets.length, p.2),
            universeCheckBool (p.1, p.2))) :=
    TMPolyTimeMap.prod_mk hBound hUniverse
  have hTail : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (HittingSet.boundedNatListBool (p.1.system.sets.length, p.2),
            universeCheckBool (p.1, p.2))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hTailInput
    simpa [Function.comp, X] using hComp
  have hAllInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (SteinerTree.exactCoverWellFormedBool p.1,
            graphBoolAndPair
              (HittingSet.boundedNatListBool (p.1.system.sets.length, p.2),
                universeCheckBool (p.1, p.2)))) :=
    TMPolyTimeMap.prod_mk hWellFormed hTail
  have hAll := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAllInput
  simpa [Function.comp, exactCoverStructuredFiniteVerify, X] using hAll

theorem exactCoverIndexCertificate_inputSize_le_poly
    (I : ExactCoverInput) (idxs : List Nat)
    (hLen : idxs.length ≤ I.system.sets.length)
    (hBounds : ∀ j ∈ idxs, j < I.system.sets.length) :
    setStructuredEncodedType.inputSize idxs ≤
      2 * (exactCoverStructuredEncodedType.inputSize I) ^ 2 + 2 := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hCert := HittingSet.boundedNatList_inputSize_le I.system.sets.length idxs hBounds
  have hSets : I.system.sets.length ≤ S := by
    simpa [S] using Knapsack.exactCover_sets_length_le_structured_inputSize I
  calc
    setStructuredEncodedType.inputSize idxs
        ≤ idxs.length * (I.system.sets.length + 1) := hCert
    _ ≤ I.system.sets.length * (I.system.sets.length + 1) :=
        Nat.mul_le_mul_right (I.system.sets.length + 1) hLen
    _ ≤ S * (S + 1) := Nat.mul_le_mul hSets (Nat.succ_le_succ hSets)
    _ ≤ 2 * S ^ 2 + 2 := by nlinarith

theorem idxOf_selected_nodup {sets selected : List (List Nat)}
    (hNodup : selected.Nodup) (hFamily : ∀ S ∈ selected, S ∈ sets) :
    (selected.map sets.idxOf).Nodup := by
  exact hNodup.map_on (by
    intro A hA B hB hEq
    have hALt : sets.idxOf A < sets.length :=
      List.idxOf_lt_length_iff.mpr (hFamily A hA)
    have hBLt : sets.idxOf B < sets.length :=
      List.idxOf_lt_length_iff.mpr (hFamily B hB)
    have hAget : sets.getD (sets.idxOf A) [] = A := by
      rw [List.getD_eq_getElem (l := sets) (d := []) hALt]
      exact List.idxOf_get hALt
    have hBget : sets.getD (sets.idxOf B) [] = B := by
      rw [List.getD_eq_getElem (l := sets) (d := []) hBLt]
      exact List.idxOf_get hBLt
    calc
      A = sets.getD (sets.idxOf A) [] := hAget.symm
      _ = sets.getD (sets.idxOf B) [] := by rw [hEq]
      _ = B := hBget)

theorem exactCoverVerifier_complete
    {I : ExactCoverInput} {selected : List (List Nat)}
    (hWellFormed : SetSystemWellFormed I.system)
    (hFamily : ∀ S ∈ selected, IsSetInFamily I.system S)
    (hNodup : selected.Nodup)
    (hDisjoint : PairwiseDisjointFamily selected)
    (hCovers : CoversUniverse I.system selected) :
    exactCoverStructuredFiniteVerify I (selected.map I.system.sets.idxOf) = true := by
  classical
  refine (exactCoverStructuredFiniteVerify_eq_true_iff I
    (selected.map I.system.sets.idxOf)).2 ?_
  have hBounds : ∀ j ∈ selected.map I.system.sets.idxOf,
      j < I.system.sets.length := by
    intro j hj
    rcases List.mem_map.mp hj with ⟨S, hS, rfl⟩
    exact List.idxOf_lt_length_iff.mpr (hFamily S hS)
  have hIdxNodup :
      (selected.map I.system.sets.idxOf).Nodup :=
    idxOf_selected_nodup hNodup hFamily
  refine ⟨hWellFormed, hBounds, ?_⟩
  · intro x hx
    constructor
    · rcases hCovers x hx with ⟨S, hS, hxS⟩
      refine ⟨I.system.sets.idxOf S, List.mem_map.mpr ⟨S, hS, rfl⟩, ?_, ?_⟩
      · exact List.idxOf_lt_length_iff.mpr (hFamily S hS)
      · rw [List.getD_eq_getElem (l := I.system.sets) (d := [])
          (List.idxOf_lt_length_iff.mpr (hFamily S hS))]
        simpa [List.idxOf_get] using hxS
    · apply AtMostOneHitList.of_nodup_unique hIdxNodup
      intro a ha b hb haT hbT
      rcases List.mem_map.mp ha with ⟨A, hA, rfl⟩
      rcases List.mem_map.mp hb with ⟨B, hB, rfl⟩
      have hALt : I.system.sets.idxOf A < I.system.sets.length :=
        List.idxOf_lt_length_iff.mpr (hFamily A hA)
      have hBLt : I.system.sets.idxOf B < I.system.sets.length :=
        List.idxOf_lt_length_iff.mpr (hFamily B hB)
      have hxA : x ∈ A := by
        have hMem := (elementCoveringIndices_mem_iff I.system.sets x
          (I.system.sets.idxOf A)).1 haT
        rw [List.getD_eq_getElem (l := I.system.sets) (d := []) hALt] at hMem
        simpa [List.idxOf_get] using hMem.2
      have hxB : x ∈ B := by
        have hMem := (elementCoveringIndices_mem_iff I.system.sets x
          (I.system.sets.idxOf B)).1 hbT
        rw [List.getD_eq_getElem (l := I.system.sets) (d := []) hBLt] at hMem
        simpa [List.idxOf_get] using hMem.2
      by_cases hAB : A = B
      · subst B
        rfl
      · exact False.elim (hDisjoint A hA B hB hAB x hxA hxB)

theorem exactCoverVerifier_sound
    {I : ExactCoverInput} {idxs : List Nat}
    (hVerify : exactCoverStructuredFiniteVerify I idxs = true) :
    ExactCover I := by
  rcases (exactCoverStructuredFiniteVerify_eq_true_iff I idxs).1 hVerify with
    ⟨hWellFormed, hBounds, hAll⟩
  let decoded : List (List Nat) := idxs.map fun j => I.system.sets.getD j []
  let selected : List (List Nat) := decoded.dedup
  refine ⟨hWellFormed, selected, ?_, List.nodup_dedup decoded, ?_, ?_⟩
  · intro S hS
    have hDecoded : S ∈ decoded := List.mem_dedup.mp hS
    rcases List.mem_map.mp hDecoded with ⟨j, hj, rfl⟩
    rw [List.getD_eq_getElem (l := I.system.sets) (d := []) (hBounds j hj)]
    exact List.getElem_mem _
  · intro A hA B hB hNe x hxA hxB
    have hAdecoded : A ∈ decoded := List.mem_dedup.mp hA
    have hBdecoded : B ∈ decoded := List.mem_dedup.mp hB
    rcases List.mem_map.mp hAdecoded with ⟨j, hj, hjA⟩
    rcases List.mem_map.mp hBdecoded with ⟨k, hk, hkB⟩
    have hxLt : x < I.system.universeSize := by
      have hAfam : A ∈ I.system.sets := by
        subst A
        rw [List.getD_eq_getElem (l := I.system.sets) (d := []) (hBounds j hj)]
        exact List.getElem_mem _
      exact hWellFormed A hAfam x hxA
    rcases hAll x hxLt with ⟨_hCover, hAtMost⟩
    have hjTarget : j ∈ elementCoveringIndices I.system.sets x := by
      refine (elementCoveringIndices_mem_iff I.system.sets x j).2 ?_
      subst A
      exact ⟨hBounds j hj, hxA⟩
    have hkTarget : k ∈ elementCoveringIndices I.system.sets x := by
      refine (elementCoveringIndices_mem_iff I.system.sets x k).2 ?_
      subst B
      exact ⟨hBounds k hk, hxB⟩
    have hjk : j = k :=
      AtMostOneHitList.eq_of_mem hAtMost hj hk hjTarget hkTarget
    apply hNe
    subst A
    subst B
    rw [hjk]
  · intro x hx
    rcases hAll x hx with ⟨hCover, _hAtMost⟩
    rcases hCover with ⟨j, hj, _hjLt, hxj⟩
    refine ⟨I.system.sets.getD j [], ?_, hxj⟩
    exact List.mem_dedup.mpr (List.mem_map.mpr ⟨j, hj, rfl⟩)

end ExactCover

/-- Direct finite-certificate TM verifier for faithful structured Exact Cover. -/
noncomputable def exactCoverStructuredFiniteTMVerifier :
    TMVerifier exactCoverStructuredDecisionProblem where
  Cert := setStructuredEncodedType
  verify := ExactCover.exactCoverStructuredFiniteVerify
  verifier_polytime := ExactCover.exactCoverStructuredFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨2, 2, 2, ?_⟩
    intro I hYes
    rcases hYes with ⟨_hWellFormed, selected, hFamily, hNodup, hDisjoint, hCovers⟩
    let idxs := selected.map I.system.sets.idxOf
    have hBounds : ∀ j ∈ idxs, j < I.system.sets.length := by
      intro j hj
      rcases List.mem_map.mp hj with ⟨S, hS, rfl⟩
      exact List.idxOf_lt_length_iff.mpr (hFamily S hS)
    have hLen : idxs.length ≤ I.system.sets.length := by
      have hSelectedLen :
          selected.length ≤ I.system.sets.length :=
        FiniteWitness.nodup_length_le_of_mem hNodup hFamily
      simpa [idxs] using hSelectedLen
    refine ⟨idxs, ?_, ?_⟩
    · exact ExactCover.exactCoverIndexCertificate_inputSize_le_poly I idxs hLen hBounds
    · exact ExactCover.exactCoverVerifier_complete
        _hWellFormed hFamily hNodup hDisjoint hCovers
  sound := by
    intro I idxs hVerify
    exact ExactCover.exactCoverVerifier_sound hVerify

theorem exactCoverStructured_TMInNP :
    TMInNP exactCoverStructuredDecisionProblem :=
  TMInNP.intro exactCoverStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
