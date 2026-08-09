/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipExactCover
import ComplexityReduction.Problems.Karp21.HittingSetStandardTM

/-!
Standard-axiom reconstruction of the structured Exact Cover checker.

The legacy checker executable and semantic lemmas are retained exactly.  This
leaf replaces the two inherited `native_decide` proof leaves: the inner
set-hit fold and the empty-list size calculation used by the universe fold.
It exports direct-TM evidence for the same Boolean checker, plus the matching
standard certificate-size bound, without claiming native membership.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace ExactCoverStandardTM

open ComplexityReduction
open ComplexityReduction.Karp21
open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.Karp21.ExactCover

/-- Standard At-Most-One fold with a kernel-proved empty-list size. -/
theorem atMostOneHitFold_tm_polytime :
    TMPolyTimeMap
      atMostOneHitInstructionListEncodedType
      atMostOneHitAccEncodedType
      (fun xs : List atMostOneHitInstructionEncodedType.Carrier =>
        xs.foldl (fun acc x => atMostOneHitStep (acc, x)) atMostOneHitRunnerInit) := by
  rcases ComplexityReduction.Karp21.ExactCover.atMostOneHitStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      atMostOneHitInstructionEncodedType atMostOneHitAccEncodedType
      atMostOneHitStep atMostOneHitRunnerInit hStep
      (Polynomial.C 20) (Polynomial.X + Polynomial.C 20) ?_ ?_
  · intro xs
    have hNil : setStructuredEncodedType.inputSize ([] : List Nat) = 0 := by
      exact EncodedType.inputSize_list_nil EncodedType.nat
    simp [atMostOneHitRunnerInit, atMostOneHitAccEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_nat, hNil]
  · intro source acc instr hInstr
    exact ComplexityReduction.Karp21.ExactCover.atMostOneHitStep_growth
      source acc instr hInstr

/-- Standard projection from the reconstructed At-Most-One fold. -/
theorem atMostOneHitFromInstructions_tm_polytime :
    TMPolyTimeMap atMostOneHitInstructionListEncodedType EncodedType.bool
      atMostOneHitFromInstructions := by
  have hCount :
      TMPolyTimeMap atMostOneHitInstructionListEncodedType EncodedType.nat
        (fun xs : atMostOneHitInstructionListEncodedType.Carrier =>
          (xs.foldl (fun acc x => atMostOneHitStep (acc, x)) atMostOneHitRunnerInit).2) := by
    have hSnd := TMPolyTimeMap.snd setStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd atMostOneHitFold_tm_polytime
    simpa [Function.comp, atMostOneHitAccEncodedType] using hComp
  have hOne : TMPolyTimeMap atMostOneHitInstructionListEncodedType EncodedType.nat
      (fun _ => (1 : Nat)) :=
    TMPolyTimeMap.const atMostOneHitInstructionListEncodedType EncodedType.nat (1 : Nat)
  have hInput :
      TMPolyTimeMap atMostOneHitInstructionListEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun xs => ((xs.foldl (fun acc x => atMostOneHitStep (acc, x))
          atMostOneHitRunnerInit).2, (1 : Nat))) :=
    TMPolyTimeMap.prod_mk hCount hOne
  have hComp := TMPolyTimeMap.comp HittingSet.natLeBool_tm_polytime hInput
  simpa [Function.comp, atMostOneHitFromInstructions] using hComp

/-- Standard direct-TM evidence for the At-Most-One Boolean checker. -/
theorem atMostOneHitBool_tm_polytime :
    TMPolyTimeMap atMostOneHitInputEncodedType EncodedType.bool atMostOneHitBool := by
  have hComp := TMPolyTimeMap.comp atMostOneHitFromInstructions_tm_polytime
    ComplexityReduction.Karp21.ExactCover.atMostOneHitInstructions_tm_polytime
  simpa [Function.comp, atMostOneHitBool] using hComp

/-- Standard direct-TM evidence for one universe-element Exact Cover check. -/
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
    have hComp := TMPolyTimeMap.comp
      HittingSetStandardTM.setHitBool_tm_polytime hHitInput
    simpa [Function.comp, elementCoveredByIndicesBool,
      HittingSet.setHitInstructionInputEncodedType, X] using hComp
  have hAtMostInput :
      TMPolyTimeMap X atMostOneHitInputEncodedType
        (fun p : X.Carrier => (elementCoveringIndices p.1.1 p.2, p.1.2)) :=
    TMPolyTimeMap.prod_mk hTarget hIdxs
  have hAtMost :
      TMPolyTimeMap X EncodedType.bool
        (fun p : X.Carrier => elementAtMostOnceByIndicesBool p) := by
    have hComp := TMPolyTimeMap.comp
      ExactCoverStandardTM.atMostOneHitBool_tm_polytime hAtMostInput
    simpa [Function.comp, elementAtMostOnceByIndicesBool,
      atMostOneHitInputEncodedType, X] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (elementCoveredByIndicesBool p, elementAtMostOnceByIndicesBool p)) :=
    TMPolyTimeMap.prod_mk hCovered hAtMost
  have hAnd := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
  simpa [Function.comp, elementExactCoverOKBool, X] using hAnd

/-- Standard universe-fold step using the reconstructed element checker. -/
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

/-- Standard direct-TM evidence for the sum-dispatched universe step. -/
theorem universeCheckStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod universeCheckAccEncodedType universeCheckInstructionEncodedType)
      universeCheckAccEncodedType
      universeCheckStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      universeCheckAccEncodedType universeCheckPayloadEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim
      ComplexityReduction.Karp21.ExactCover.universeCheckStepLeft_tm_polytime
      universeCheckElementStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

/-- Standard universe fold with kernel-proved empty structural sizes. -/
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
      exact EncodedType.inputSize_list_nil EncodedType.nat
    have hNilFamily : setFamilyStructuredEncodedType.inputSize ([] : List (List Nat)) = 0 := by
      exact EncodedType.inputSize_list_nil setStructuredEncodedType
    simp [universeCheckInitAcc, universeCheckAccEncodedType, universeCheckPayloadEncodedType,
      EncodedType.inputSize_prod, EncodedType.inputSize_bool, hNilSet, hNilFamily]
  · intro source acc instr hInstr
    exact ComplexityReduction.Karp21.ExactCover.universeCheckStep_growth
      source acc instr hInstr

/-- Standard projection from the reconstructed universe fold. -/
theorem universeCheckFromInstructions_tm_polytime :
    TMPolyTimeMap universeCheckInstructionListEncodedType EncodedType.bool
      universeCheckFromInstructions := by
  have hSnd := TMPolyTimeMap.snd universeCheckPayloadEncodedType EncodedType.bool
  have hComp := TMPolyTimeMap.comp hSnd universeCheckFold_tm_polytime
  simpa [Function.comp, universeCheckFromInstructions, universeCheckAccEncodedType] using hComp

/-- Standard direct-TM evidence for the complete universe check. -/
theorem universeCheckBool_tm_polytime :
    TMPolyTimeMap universeCheckInputEncodedType EncodedType.bool universeCheckBool := by
  have hComp := TMPolyTimeMap.comp universeCheckFromInstructions_tm_polytime
    ComplexityReduction.Karp21.ExactCover.universeCheckInstructions_tm_polytime
  simpa [Function.comp, universeCheckBool] using hComp

/-- Standard direct-TM evidence for the unchanged structured Exact Cover checker. -/
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

/-- Standard certificate-size bound for the unchanged index witness. -/
theorem exactCoverIndexCertificate_inputSize_le_poly
    (I : ExactCoverInput) (idxs : List Nat)
    (hLen : idxs.length ≤ I.system.sets.length)
    (hBounds : ∀ j ∈ idxs, j < I.system.sets.length) :
    setStructuredEncodedType.inputSize idxs ≤
      2 * (exactCoverStructuredEncodedType.inputSize I) ^ 2 + 2 := by
  let S := exactCoverStructuredEncodedType.inputSize I
  have hCert := HittingSetStandardTM.boundedNatList_inputSize_le
    I.system.sets.length idxs hBounds
  have hSets : I.system.sets.length ≤ S := by
    simpa [S] using Knapsack.exactCover_sets_length_le_structured_inputSize I
  calc
    setStructuredEncodedType.inputSize idxs
        ≤ idxs.length * (I.system.sets.length + 1) := hCert
    _ ≤ I.system.sets.length * (I.system.sets.length + 1) :=
        Nat.mul_le_mul_right (I.system.sets.length + 1) hLen
    _ ≤ S * (S + 1) := Nat.mul_le_mul hSets (Nat.succ_le_succ hSets)
    _ ≤ 2 * S ^ 2 + 2 := by nlinarith

end ExactCoverStandardTM
end Karp21
end Problems
end ComplexityReduction

assert_standard_axioms
  ComplexityReduction.Problems.Karp21.ExactCoverStandardTM.atMostOneHitFold_tm_polytime,
  ComplexityReduction.Problems.Karp21.ExactCoverStandardTM.elementExactCoverOKBool_tm_polytime,
  ComplexityReduction.Problems.Karp21.ExactCoverStandardTM.universeCheckFold_tm_polytime,
  ComplexityReduction.Problems.Karp21.ExactCoverStandardTM.exactCoverStructuredFiniteVerify_tm_polytime,
  ComplexityReduction.Problems.Karp21.ExactCoverStandardTM.exactCoverIndexCertificate_inputSize_le_poly
