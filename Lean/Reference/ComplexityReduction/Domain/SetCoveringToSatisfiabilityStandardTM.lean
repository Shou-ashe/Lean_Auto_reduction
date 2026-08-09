/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.Assembly
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Presentation.Satisfiability
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Protocol.ComponentResolver

/-!
Kernel-audited reconstruction of the compact structured Set-Covering-to-CNF
executable.

The read-only construction is the canonical compact semantic map, but its
direct-TM proof uses several closed `native_decide` bounds.  This domain leaf
rebuilds those bounded-fold witnesses with kernel `decide`, retaining exactly
the existing executable functions.  It deliberately does not yet export a V2
primitive: that requires the entire compact map to be reconstructed, not a
partial prefix of its implementation.
-/

namespace ComplexityReduction
namespace Domain
namespace SetCoveringToSatisfiabilityStandardTM

open ComplexityReduction
open ComplexityReduction.Karp21
open ComplexityReduction.Karp21.ExactCover
open ComplexityReduction.Combinatorics
open Certificate Encoding Program

/-- Kernel-audited initial invariant for one at-least-one choice-pair row. -/
private theorem choicePairRowInitAcc_bound
    (xs : List setCoveringChoicePairRowInstructionEncodedType.Carrier) :
    setCoveringChoicePairRowFoldInv
        (setCoveringChoicePairRowInstructionListEncodedType.inputSize xs)
        setCoveringChoicePairRowInitAcc ∧
      setCoveringChoicePairRowAccEncodedType.inputSize setCoveringChoicePairRowInitAcc ≤
        setCoveringChoicePairRowFoldBase.eval
          (setCoveringChoicePairRowInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · simp [setCoveringChoicePairRowFoldBase]
    decide

/-- Kernel-audited direct-TM realization of one at-least-one choice-pair row fold. -/
private theorem choicePairRowFold_tmPolyTime :
    TMPolyTimeMap
      setCoveringChoicePairRowInstructionListEncodedType
      setCoveringChoicePairRowAccEncodedType
      (fun xs : List setCoveringChoicePairRowInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => setCoveringChoicePairRowStep (acc, instr))
          setCoveringChoicePairRowInitAcc) := by
  rcases setCoveringChoicePairRowStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      setCoveringChoicePairRowInstructionEncodedType setCoveringChoicePairRowAccEncodedType
      setCoveringChoicePairRowStep setCoveringChoicePairRowInitAcc hStep
      setCoveringChoicePairRowFoldBase setCoveringChoicePairRowFoldGrow
      setCoveringChoicePairRowFoldInv ?_ ?_
  · intro xs
    exact choicePairRowInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact setCoveringChoicePairRowStep_growth source acc instr hInv hInstr

/-- Kernel-audited projection from the at-least-one row fold. -/
private theorem choicePairRowFromInstructions_tmPolyTime :
    TMPolyTimeMap
      setCoveringChoicePairRowInstructionListEncodedType
      setCoveringChoicePairListEncodedType
      setCoveringChoicePairRowFromInstructions := by
  have hFold := choicePairRowFold_tmPolyTime
  have hOut :=
    TMPolyTimeMap.snd setCoveringChoicePairRowContextEncodedType
      setCoveringChoicePairListEncodedType
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, setCoveringChoicePairRowFromInstructions,
    setCoveringChoicePairRowAccEncodedType] using hComp

/-- Kernel-audited executable for one at-least-one choice-pair row. -/
theorem choicePairRowExecutable_tmPolyTime :
    TMPolyTimeMap
      setCoveringChoicePairRowContextEncodedType
      setCoveringChoicePairListEncodedType
      setCoveringChoicePairRowExecutable := by
  have hComp :=
    TMPolyTimeMap.comp choicePairRowFromInstructions_tmPolyTime
      setCoveringChoicePairRowInstructions_tm_polytime
  simpa [Function.comp, setCoveringChoicePairRowExecutable] using hComp

/-- Kernel-audited direct-TM evidence for an at-least-one slot clause. -/
theorem slotAtLeastClauseExecutable_tmPolyTime :
    TMPolyTimeMap
      setCoveringChoicePairRowContextEncodedType
      clauseStructuredEncodedType
      setCoveringSlotAtLeastClauseExecutable := by
  have hPairs := choicePairRowExecutable_tmPolyTime
  have hMap := TMPolyTimeMap.list_map setCoveringChoiceLitFromPair_tm_polytime
  have hComp := TMPolyTimeMap.comp hMap hPairs
  simpa [Function.comp, setCoveringSlotAtLeastClauseExecutable,
    setCoveringChoicePairListEncodedType, vertexPairListEncodedType,
    clauseStructuredEncodedType] using hComp

/-- Kernel-audited initial invariant for the inner at-most-one choice fold. -/
private theorem atMostChoiceInitAcc_bound
    (xs : List setCoveringAtMostChoiceInstructionEncodedType.Carrier) :
    setCoveringAtMostChoiceFoldInv
        (setCoveringAtMostChoiceInstructionListEncodedType.inputSize xs)
        setCoveringAtMostChoiceInitAcc ∧
      setCoveringAtMostChoiceAccEncodedType.inputSize setCoveringAtMostChoiceInitAcc ≤
        setCoveringAtMostChoiceFoldBase.eval
          (setCoveringAtMostChoiceInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · simp [setCoveringAtMostChoiceFoldBase]
    decide

/-- Kernel-audited direct-TM realization of the inner at-most-one choice fold. -/
private theorem atMostChoiceFold_tmPolyTime :
    TMPolyTimeMap
      setCoveringAtMostChoiceInstructionListEncodedType
      setCoveringAtMostChoiceAccEncodedType
      (fun xs : List setCoveringAtMostChoiceInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => setCoveringAtMostChoiceStep (acc, instr))
          setCoveringAtMostChoiceInitAcc) := by
  rcases setCoveringAtMostChoiceStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      setCoveringAtMostChoiceInstructionEncodedType setCoveringAtMostChoiceAccEncodedType
      setCoveringAtMostChoiceStep setCoveringAtMostChoiceInitAcc hStep
      setCoveringAtMostChoiceFoldBase setCoveringAtMostChoiceFoldGrow
      setCoveringAtMostChoiceFoldInv ?_ ?_
  · intro xs
    exact atMostChoiceInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact setCoveringAtMostChoiceStep_growth source acc instr hInv hInstr

/-- Kernel-audited projection from the inner at-most-one choice fold. -/
private theorem atMostChoiceFromInstructions_tmPolyTime :
    TMPolyTimeMap
      setCoveringAtMostChoiceInstructionListEncodedType
      cnfStructuredEncodedType
      setCoveringAtMostChoiceFromInstructions := by
  have hFold := atMostChoiceFold_tmPolyTime
  have hOut :=
    TMPolyTimeMap.snd setCoveringAtMostChoiceContextEncodedType cnfStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hOut hFold
  simpa [Function.comp, setCoveringAtMostChoiceFromInstructions,
    setCoveringAtMostChoiceAccEncodedType] using hComp

/-- Kernel-audited executable for one at-most-one choice context. -/
theorem atMostChoiceExecutable_tmPolyTime :
    TMPolyTimeMap
      setCoveringAtMostChoiceContextEncodedType
      cnfStructuredEncodedType
      setCoveringAtMostChoiceExecutable := by
  have hComp :=
    TMPolyTimeMap.comp atMostChoiceFromInstructions_tmPolyTime
      setCoveringAtMostChoiceInstructions_tm_polytime
  simpa [Function.comp, setCoveringAtMostChoiceExecutable] using hComp

/-- Rebuild the outer at-most-one step using the audited inner-choice runner. -/
private theorem atMostSlotStepRight_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringAtMostSlotAccEncodedType EncodedType.nat)
      setCoveringAtMostSlotAccEncodedType
      (fun p : setCoveringAtMostSlotAccEncodedType.Carrier × Nat =>
        (p.1.1, (show SAT.CNF from p.1.2) ++
          setCoveringAtMostChoiceExecutable
            (setCoveringAtMostSlotChoiceContext p.1.1 p.2))) := by
  let X := EncodedType.prod setCoveringAtMostSlotAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X setCoveringAtMostSlotAccEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst setCoveringAtMostSlotAccEncodedType EncodedType.nat
  have hChoice : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd setCoveringAtMostSlotAccEncodedType EncodedType.nat
  have hCtx :
      TMPolyTimeMap X setCoveringChoicePairRowContextEncodedType
        (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst setCoveringChoicePairRowContextEncodedType
      cnfStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, setCoveringAtMostSlotAccEncodedType, X] using hComp
  have hOut :
      TMPolyTimeMap X cnfStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd setCoveringChoicePairRowContextEncodedType
      cnfStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, setCoveringAtMostSlotAccEncodedType, X] using hComp
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hCtx
    simpa [Function.comp, setCoveringChoicePairRowContextEncodedType,
      vertexPairEncodedType, X] using hComp
  have hChoiceCount :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hCtx
    simpa [Function.comp, setCoveringChoicePairRowContextEncodedType,
      vertexPairEncodedType, X] using hComp
  have hRow :
      TMPolyTimeMap X vertexPairEncodedType
        (fun p : X.Carrier => (p.1.1.1, p.1.1.2)) := by
    simpa [vertexPairEncodedType] using TMPolyTimeMap.prod_mk hSlot hChoiceCount
  have hChoiceCtx :
      TMPolyTimeMap X setCoveringAtMostChoiceContextEncodedType
        (fun p : X.Carrier => setCoveringAtMostSlotChoiceContext p.1.1 p.2) := by
    simpa [setCoveringAtMostSlotChoiceContext, setCoveringAtMostChoiceContextEncodedType]
      using TMPolyTimeMap.prod_mk hRow hChoice
  have hBlock :
      TMPolyTimeMap X cnfStructuredEncodedType
        (fun p : X.Carrier =>
          setCoveringAtMostChoiceExecutable
            (setCoveringAtMostSlotChoiceContext p.1.1 p.2)) := by
    have hComp := TMPolyTimeMap.comp atMostChoiceExecutable_tmPolyTime hChoiceCtx
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show SAT.CNF from p.1.2),
            setCoveringAtMostChoiceExecutable
              (setCoveringAtMostSlotChoiceContext p.1.1 p.2))) :=
    TMPolyTimeMap.prod_mk hOut hBlock
  have hAppend :
      TMPolyTimeMap X cnfStructuredEncodedType
        (fun p : X.Carrier =>
          (show SAT.CNF from p.1.2) ++
            setCoveringAtMostChoiceExecutable
              (setCoveringAtMostSlotChoiceContext p.1.1 p.2)) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
      hAppendInput
    simpa [Function.comp, cnfStructuredEncodedType, X] using hComp
  simpa [setCoveringAtMostSlotAccEncodedType] using TMPolyTimeMap.prod_mk hCtx hAppend

/-- Kernel-audited outer at-most-one step. -/
private theorem atMostSlotStep_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringAtMostSlotAccEncodedType
        setCoveringAtMostSlotInstructionEncodedType)
      setCoveringAtMostSlotAccEncodedType
      setCoveringAtMostSlotStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      setCoveringAtMostSlotAccEncodedType
      setCoveringChoicePairRowContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim setCoveringAtMostSlotStepLeft_tm_polytime
      atMostSlotStepRight_tmPolyTime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

/-- Kernel-audited initial invariant for the outer at-most-one slot fold. -/
private theorem atMostSlotInitAcc_bound
    (xs : List setCoveringAtMostSlotInstructionEncodedType.Carrier) :
    setCoveringAtMostSlotFoldInv
        (setCoveringAtMostSlotInstructionListEncodedType.inputSize xs)
        setCoveringAtMostSlotInitAcc ∧
      setCoveringAtMostSlotAccEncodedType.inputSize setCoveringAtMostSlotInitAcc ≤
        setCoveringAtMostSlotFoldBase.eval
          (setCoveringAtMostSlotInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · simp [setCoveringAtMostSlotFoldBase]
    decide

/-- Kernel-audited direct-TM realization of the outer at-most-one slot fold. -/
private theorem atMostSlotFold_tmPolyTime :
    TMPolyTimeMap
      setCoveringAtMostSlotInstructionListEncodedType
      setCoveringAtMostSlotAccEncodedType
      (fun xs : List setCoveringAtMostSlotInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => setCoveringAtMostSlotStep (acc, instr))
          setCoveringAtMostSlotInitAcc) := by
  rcases atMostSlotStep_tmPolyTime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      setCoveringAtMostSlotInstructionEncodedType setCoveringAtMostSlotAccEncodedType
      setCoveringAtMostSlotStep setCoveringAtMostSlotInitAcc hStep
      setCoveringAtMostSlotFoldBase setCoveringAtMostSlotFoldGrow
      setCoveringAtMostSlotFoldInv ?_ ?_
  · intro xs
    exact atMostSlotInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact setCoveringAtMostSlotStep_growth source acc instr hInv hInstr

/-- Kernel-audited executable for all at-most-one clauses of one slot. -/
theorem atMostSlotExecutable_tmPolyTime :
    TMPolyTimeMap
      setCoveringChoicePairRowContextEncodedType
      cnfStructuredEncodedType
      setCoveringAtMostSlotExecutable := by
  have hOut :=
    TMPolyTimeMap.snd setCoveringChoicePairRowContextEncodedType cnfStructuredEncodedType
  have hFold := atMostSlotFold_tmPolyTime
  have hFrom := TMPolyTimeMap.comp hOut hFold
  have hExecutable := TMPolyTimeMap.comp hFrom setCoveringAtMostSlotInstructions_tm_polytime
  simpa [Function.comp, setCoveringAtMostSlotFromInstructions,
    setCoveringAtMostSlotAccEncodedType, setCoveringAtMostSlotExecutable] using hExecutable

/-- Kernel-audited direct-TM evidence for the complete CNF block of one slot. -/
theorem slotClausesForExecutable_tmPolyTime :
    TMPolyTimeMap
      setCoveringChoicePairRowContextEncodedType
      cnfStructuredEncodedType
      setCoveringSlotClausesForExecutable := by
  have hInput :
      TMPolyTimeMap
        setCoveringChoicePairRowContextEncodedType
        (EncodedType.prod clauseStructuredEncodedType cnfStructuredEncodedType)
        (fun ctx : SetCoveringChoicePairRowContext =>
          (setCoveringSlotAtLeastClauseExecutable ctx,
            setCoveringAtMostSlotExecutable ctx)) :=
    TMPolyTimeMap.prod_mk slotAtLeastClauseExecutable_tmPolyTime atMostSlotExecutable_tmPolyTime
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons clauseStructuredEncodedType) hInput
  simpa [Function.comp, setCoveringSlotClausesForExecutable,
    cnfStructuredEncodedType] using hCons

/-- Kernel-audited initial invariant for the coverage literals of one slot. -/
private theorem coverageSlotInitAcc_bound
    (xs : List setCoveringCoverageSlotInstructionEncodedType.Carrier) :
    setCoveringCoverageSlotFoldInv
        (setCoveringCoverageSlotInstructionListEncodedType.inputSize xs)
        setCoveringCoverageSlotInitAcc ∧
      setCoveringCoverageSlotAccEncodedType.inputSize setCoveringCoverageSlotInitAcc ≤
        setCoveringCoverageSlotFoldBase.eval
          (setCoveringCoverageSlotInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · simp [setCoveringCoverageSlotFoldBase]
    decide

/-- Kernel-audited direct-TM realization of the coverage-literals fold. -/
private theorem coverageSlotFold_tmPolyTime :
    TMPolyTimeMap
      setCoveringCoverageSlotInstructionListEncodedType
      setCoveringCoverageSlotAccEncodedType
      (fun xs : List setCoveringCoverageSlotInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => setCoveringCoverageSlotStep (acc, instr))
          setCoveringCoverageSlotInitAcc) := by
  rcases setCoveringCoverageSlotStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      setCoveringCoverageSlotInstructionEncodedType setCoveringCoverageSlotAccEncodedType
      setCoveringCoverageSlotStep setCoveringCoverageSlotInitAcc hStep
      setCoveringCoverageSlotFoldBase setCoveringCoverageSlotFoldGrow
      setCoveringCoverageSlotFoldInv ?_ ?_
  · intro xs
    exact coverageSlotInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact setCoveringCoverageSlotStep_growth source acc instr hInv hInstr

/-- Kernel-audited executable for coverage literals at one selected slot. -/
theorem coverageSlotLitsExecutable_tmPolyTime :
    TMPolyTimeMap
      setCoveringCoverageSlotContextEncodedType
      clauseStructuredEncodedType
      setCoveringCoverageSlotLitsExecutable := by
  have hOut := TMPolyTimeMap.snd EncodedType.nat clauseStructuredEncodedType
  have hFold := coverageSlotFold_tmPolyTime
  have hFrom := TMPolyTimeMap.comp hOut hFold
  have hExecutable :=
    TMPolyTimeMap.comp hFrom setCoveringCoverageSlotInstructions_tm_polytime
  simpa [Function.comp, setCoveringCoverageSlotFromInstructions,
    setCoveringCoverageSlotAccEncodedType, setCoveringCoverageSlotLitsExecutable] using hExecutable

/-- Rebuild a coverage-clause fold step using the audited coverage-slot runner. -/
private theorem coverageClauseStepRight_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringCoverageClauseAccEncodedType EncodedType.nat)
      setCoveringCoverageClauseAccEncodedType
      (fun p : setCoveringCoverageClauseAccEncodedType.Carrier × Nat =>
        (p.1.1, (show SAT.Clause from p.1.2) ++
          setCoveringCoverageSlotLitsExecutable (p.2, p.1.1))) := by
  let X := EncodedType.prod setCoveringCoverageClauseAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X setCoveringCoverageClauseAccEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst setCoveringCoverageClauseAccEncodedType EncodedType.nat
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd setCoveringCoverageClauseAccEncodedType EncodedType.nat
  have hIdxs :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat) (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst (EncodedType.list EncodedType.nat)
      clauseStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, setCoveringCoverageClauseAccEncodedType, X] using hComp
  have hOut :
      TMPolyTimeMap X clauseStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd (EncodedType.list EncodedType.nat)
      clauseStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, setCoveringCoverageClauseAccEncodedType, X] using hComp
  have hCoverageCtx :
      TMPolyTimeMap X setCoveringCoverageSlotContextEncodedType
        (fun p : X.Carrier => (p.2, p.1.1)) := by
    simpa [setCoveringCoverageSlotContextEncodedType] using TMPolyTimeMap.prod_mk hSlot hIdxs
  have hBlock :
      TMPolyTimeMap X clauseStructuredEncodedType
        (fun p : X.Carrier =>
          setCoveringCoverageSlotLitsExecutable (p.2, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp coverageSlotLitsExecutable_tmPolyTime hCoverageCtx
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod clauseStructuredEncodedType clauseStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show SAT.Clause from p.1.2),
            setCoveringCoverageSlotLitsExecutable (p.2, p.1.1))) :=
    TMPolyTimeMap.prod_mk hOut hBlock
  have hAppend :
      TMPolyTimeMap X clauseStructuredEncodedType
        (fun p : X.Carrier =>
          (show SAT.Clause from p.1.2) ++
            setCoveringCoverageSlotLitsExecutable (p.2, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append literalStructuredEncodedType) hAppendInput
    simpa [Function.comp, clauseStructuredEncodedType, X] using hComp
  simpa [setCoveringCoverageClauseAccEncodedType] using TMPolyTimeMap.prod_mk hIdxs hAppend

/-- Kernel-audited direct-TM realization of a coverage-clause fold step. -/
private theorem coverageClauseStep_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod setCoveringCoverageClauseAccEncodedType
        setCoveringCoverageClauseInstructionEncodedType)
      setCoveringCoverageClauseAccEncodedType
      setCoveringCoverageClauseStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      setCoveringCoverageClauseAccEncodedType
      setCoveringCoverageClauseCoreContextEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim setCoveringCoverageClauseStepLeft_tm_polytime
      coverageClauseStepRight_tmPolyTime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

/-- Kernel-audited initial invariant for a complete coverage-clause fold. -/
private theorem coverageClauseInitAcc_bound
    (xs : List setCoveringCoverageClauseInstructionEncodedType.Carrier) :
    setCoveringCoverageClauseFoldInv
        (setCoveringCoverageClauseInstructionListEncodedType.inputSize xs)
        setCoveringCoverageClauseInitAcc ∧
      setCoveringCoverageClauseAccEncodedType.inputSize setCoveringCoverageClauseInitAcc ≤
        setCoveringCoverageClauseFoldBase.eval
          (setCoveringCoverageClauseInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · simp [setCoveringCoverageClauseFoldBase, setCoveringCoverageClauseInitAcc,
      setCoveringCoverageClauseAccEncodedType]
    decide

/-- Kernel-audited direct-TM realization of one complete coverage clause. -/
private theorem coverageClauseFold_tmPolyTime :
    TMPolyTimeMap
      setCoveringCoverageClauseInstructionListEncodedType
      setCoveringCoverageClauseAccEncodedType
      (fun xs : List setCoveringCoverageClauseInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => setCoveringCoverageClauseStep (acc, instr))
          setCoveringCoverageClauseInitAcc) := by
  rcases coverageClauseStep_tmPolyTime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      setCoveringCoverageClauseInstructionEncodedType setCoveringCoverageClauseAccEncodedType
      setCoveringCoverageClauseStep setCoveringCoverageClauseInitAcc hStep
      setCoveringCoverageClauseFoldBase setCoveringCoverageClauseFoldGrow
      setCoveringCoverageClauseFoldInv ?_ ?_
  · intro xs
    exact coverageClauseInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact setCoveringCoverageClauseStep_growth source acc instr hInv hInstr

/-- Kernel-audited executable for the CNF clause covering one universe element. -/
theorem coverageClauseExecutable_tmPolyTime :
    TMPolyTimeMap
      setCoveringCoverageClauseContextEncodedType
      clauseStructuredEncodedType
      setCoveringCoverageClauseExecutable := by
  have hOut := TMPolyTimeMap.snd (EncodedType.list EncodedType.nat) clauseStructuredEncodedType
  have hFold := coverageClauseFold_tmPolyTime
  have hFrom := TMPolyTimeMap.comp hOut hFold
  have hCore := TMPolyTimeMap.comp hFrom setCoveringCoverageClauseInstructions_tm_polytime
  have hExecutable := TMPolyTimeMap.comp hCore setCoveringCoverageClauseCoreContext_tm_polytime
  simpa [Function.comp, setCoveringCoverageClauseFromInstructions,
    setCoveringCoverageClauseAccEncodedType, setCoveringCoverageClauseCoreExecutable,
    setCoveringCoverageClauseExecutable] using hExecutable

/-- Kernel-audited initial invariant for the all-elements coverage-context fold. -/
private theorem coverageClausesInitAcc_bound
    (xs : List setCoveringCoverageClausesInstructionEncodedType.Carrier) :
    setCoveringCoverageClausesFoldInv
        (setCoveringCoverageClausesInstructionListEncodedType.inputSize xs)
        setCoveringCoverageClausesInitAcc ∧
      setCoveringCoverageClausesAccEncodedType.inputSize setCoveringCoverageClausesInitAcc ≤
        setCoveringCoverageClausesFoldBase.eval
          (setCoveringCoverageClausesInstructionListEncodedType.inputSize xs) := by
  constructor
  · exact Or.inl rfl
  · simp [setCoveringCoverageClausesFoldBase, setCoveringCoverageClausesInitAcc,
      setCoveringCoverageClausesAccEncodedType]
    decide

/-- Kernel-audited growth proof for the all-elements coverage-context fold. -/
private theorem coverageClausesContextStep_growth
    (source : List setCoveringCoverageClausesInstructionEncodedType.Carrier)
    (acc : setCoveringCoverageClausesAccEncodedType.Carrier)
    (instr : setCoveringCoverageClausesInstructionEncodedType.Carrier)
    (hInv :
      setCoveringCoverageClausesFoldInv
        (setCoveringCoverageClausesInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      setCoveringCoverageClausesInstructionEncodedType.inputSize instr ≤
        setCoveringCoverageClausesInstructionListEncodedType.inputSize source) :
    setCoveringCoverageClausesFoldInv
        (setCoveringCoverageClausesInstructionListEncodedType.inputSize source)
        (setCoveringCoverageClausesContextStep (acc, instr)) ∧
      setCoveringCoverageClausesAccEncodedType.inputSize
          (setCoveringCoverageClausesContextStep (acc, instr)) ≤
        setCoveringCoverageClausesAccEncodedType.inputSize acc +
          setCoveringCoverageClausesFoldGrow.eval
            (setCoveringCoverageClausesInstructionListEncodedType.inputSize source) := by
  let N := setCoveringCoverageClausesInstructionListEncodedType.inputSize source
  rcases acc with ⟨I, out⟩
  cases instr with
  | inl ctx =>
      have hCtx : setCoveringCoverageClauseContextEncodedType.inputSize ctx ≤ N := by
        exact Nat.le_of_lt (by
          simpa [N, setCoveringCoverageClausesInstructionEncodedType,
            EncodedType.inputSize, EncodedType.sum] using hInstr)
      have hSource : setCoveringStructuredEncodedType.inputSize ctx.1 ≤ N := by
        have hCtxProd :
            setCoveringStructuredEncodedType.inputSize ctx.1 + 1 +
                EncodedType.nat.inputSize ctx.2 ≤ N := by
          simpa [setCoveringCoverageClauseContextEncodedType,
            EncodedType.inputSize_prod] using hCtx
        omega
      constructor
      · exact Or.inr (Or.inr hSource)
      · have hEmpty :
            setCoveringCoverageClausesContextListEncodedType.inputSize
                ([] : List SetCoveringCoverageClauseContext) = 0 := by
          exact EncodedType.inputSize_list_nil setCoveringCoverageClauseContextEncodedType
        have hNewAcc :
            setCoveringCoverageClausesAccEncodedType.inputSize
                (ctx.1, ([] : List SetCoveringCoverageClauseContext)) ≤ N + 1 := by
          simp [setCoveringCoverageClausesAccEncodedType, EncodedType.inputSize_prod, hEmpty]
          omega
        have hGrowLarge :
            N + 1 ≤ setCoveringCoverageClausesAccEncodedType.inputSize (I, out) +
              setCoveringCoverageClausesFoldGrow.eval N := by
          have hPoly : N + 1 ≤ setCoveringCoverageClausesFoldGrow.eval N := by
            rw [setCoveringCoverageClausesFoldGrow_eval]
            omega
          exact hPoly.trans (Nat.le_add_left _ _)
        simpa [setCoveringCoverageClausesContextStep, N] using hNewAcc.trans hGrowLarge
  | inr x =>
      change Nat at x
      have hNatLtN : EncodedType.nat.inputSize x < N := by
        simpa [N, setCoveringCoverageClausesInstructionEncodedType,
          EncodedType.inputSize, EncodedType.sum] using hInstr
      have hX : EncodedType.nat.inputSize x ≤ N := Nat.le_of_lt hNatLtN
      have hNge2 : 2 ≤ N := by
        have hOne : 1 ≤ EncodedType.nat.inputSize x := by
          simp [EncodedType.inputSize_nat]
        omega
      have hZeroSize :
          setCoveringStructuredEncodedType.inputSize setCoveringCoverageClausesZeroInput = 4 := by
        change setCoveringTupleStructuredEncodedType.inputSize
          ({ universeSize := 0, sets := [] }, (0 : Nat)) = 4
        simp [setCoveringTupleStructuredEncodedType, setSystemStructuredEncodedType,
          setSystemTupleStructuredEncodedType, setFamilyStructuredEncodedType]
        decide
      have hxSize : x + 1 ≤ N := by
        simpa [EncodedType.inputSize_nat] using hX
      have hZeroBound :
          setCoveringStructuredEncodedType.inputSize setCoveringCoverageClausesZeroInput ≤
            N + 2 := by
        rw [hZeroSize]
        omega
      have hSourceInv :
          I = setCoveringCoverageClausesZeroInput ∨
            setCoveringStructuredEncodedType.inputSize I ≤ N := by
        rcases hInv with hInit | hSource
        · injection hInit with hIEq _hOut
          exact Or.inl hIEq
        · rcases hSource with hZero | hSource
          · exact Or.inl hZero
          · exact Or.inr hSource
      have hSourceBound : setCoveringStructuredEncodedType.inputSize I ≤ N + 2 := by
        rcases hSourceInv with hZero | hSource
        · rw [hZero]
          exact hZeroBound
        · omega
      have hCtx :
          setCoveringCoverageClauseContextEncodedType.inputSize (I, x) ≤ 2 * N + 3 := by
        simp [setCoveringCoverageClauseContextEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat]
        omega
      have hSingleton :
          setCoveringCoverageClausesContextListEncodedType.inputSize [(I, x)] ≤ 2 * N + 4 := by
        change (EncodedType.list setCoveringCoverageClauseContextEncodedType).inputSize
            [(I, x)] ≤ 2 * N + 4
        rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_nil]
        omega
      have hSingletonGrow :
          setCoveringCoverageClausesContextListEncodedType.inputSize [(I, x)] ≤
            setCoveringCoverageClausesFoldGrow.eval N := by
        rw [setCoveringCoverageClausesFoldGrow_eval]
        omega
      have hAppend :
          setCoveringCoverageClausesContextListEncodedType.inputSize
              ((show List SetCoveringCoverageClauseContext from out) ++
                ([(I, x)] : List SetCoveringCoverageClauseContext)) =
            setCoveringCoverageClausesContextListEncodedType.inputSize out +
              setCoveringCoverageClausesContextListEncodedType.inputSize
                ([(I, x)] : List SetCoveringCoverageClauseContext) := by
        simpa [setCoveringCoverageClausesContextListEncodedType] using
          list_inputSize_append setCoveringCoverageClauseContextEncodedType out
            ([(I, x)] : List SetCoveringCoverageClauseContext)
      constructor
      · exact Or.inr hSourceInv
      · change
          setCoveringCoverageClausesAccEncodedType.inputSize
              (I,
                (show List SetCoveringCoverageClauseContext from out) ++
                  ([(I, x)] : List SetCoveringCoverageClauseContext)) ≤
            setCoveringCoverageClausesAccEncodedType.inputSize (I, out) +
              setCoveringCoverageClausesFoldGrow.eval N
        simp [setCoveringCoverageClausesAccEncodedType, EncodedType.inputSize_prod] at hAppend ⊢
        rw [hAppend]
        rw [setCoveringCoverageClausesFoldGrow_eval] at hSingletonGrow
        let A := setCoveringStructuredEncodedType.inputSize I
        let B := setCoveringCoverageClausesContextListEncodedType.inputSize out
        let S :=
          setCoveringCoverageClausesContextListEncodedType.inputSize
            ([(I, x)] : List SetCoveringCoverageClauseContext)
        have hS : S ≤ 4 * N + 10 := by
          simpa [S] using hSingletonGrow
        change A + 1 + (B + S) ≤ A + 1 + B + (4 * N + 10)
        omega

/-- Kernel-audited executable context list for all source-universe elements. -/
private theorem coverageClausesContextsExecutable_tmPolyTime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      setCoveringCoverageClausesContextListEncodedType
      setCoveringCoverageClausesContextsExecutable := by
  rcases setCoveringCoverageClausesContextStep_tm_polytime with ⟨hStep⟩
  have hFold :
      TMPolyTimeMap
        setCoveringCoverageClausesInstructionListEncodedType
        setCoveringCoverageClausesAccEncodedType
        (fun xs : List setCoveringCoverageClausesInstructionEncodedType.Carrier =>
          xs.foldl (fun acc instr => setCoveringCoverageClausesContextStep (acc, instr))
            setCoveringCoverageClausesInitAcc) := by
    refine
      TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
        setCoveringCoverageClausesInstructionEncodedType setCoveringCoverageClausesAccEncodedType
        setCoveringCoverageClausesContextStep setCoveringCoverageClausesInitAcc hStep
        setCoveringCoverageClausesFoldBase setCoveringCoverageClausesFoldGrow
        setCoveringCoverageClausesFoldInv ?_ ?_
    · intro xs
      exact coverageClausesInitAcc_bound xs
    · intro source acc instr hInv hInstr
      exact coverageClausesContextStep_growth source acc instr hInv hInstr
  have hOut := TMPolyTimeMap.snd setCoveringStructuredEncodedType
    setCoveringCoverageClausesContextListEncodedType
  have hFrom := TMPolyTimeMap.comp hOut hFold
  have hExecutable :=
    TMPolyTimeMap.comp hFrom setCoveringCoverageClausesInstructions_tm_polytime
  simpa [Function.comp, setCoveringCoverageClausesContextsFromInstructions,
    setCoveringCoverageClausesAccEncodedType,
    setCoveringCoverageClausesContextsExecutable] using hExecutable

/-- Kernel-audited direct-TM evidence for all coverage clauses. -/
theorem coverageClausesExecutable_tmPolyTime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      cnfStructuredEncodedType
      setCoveringCoverageClausesExecutable := by
  have hContexts := coverageClausesContextsExecutable_tmPolyTime
  have hMap := TMPolyTimeMap.list_map coverageClauseExecutable_tmPolyTime
  have hComp := TMPolyTimeMap.comp hMap hContexts
  simpa [Function.comp, setCoveringCoverageClausesExecutable,
    setCoveringCoverageClausesContextListEncodedType, cnfStructuredEncodedType] using hComp

/-- Kernel-audited generation of all slot contexts from the source bound. -/
private theorem slotAtLeastContextsExecutable_tmPolyTime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      setCoveringChoicePairListEncodedType
      setCoveringSlotAtLeastContextsExecutable := by
  have hRows :=
    TMPolyTimeMap.comp choicePairRowExecutable_tmPolyTime
      setCoveringSlotAtLeastContextInput_tm_polytime
  have hSwap := TMPolyTimeMap.list_map setCoveringChoicePairSwap_tm_polytime
  have hComp := TMPolyTimeMap.comp hSwap hRows
  simpa [Function.comp, setCoveringSlotAtLeastContextsExecutable,
    setCoveringChoicePairListEncodedType, vertexPairListEncodedType,
    setCoveringSlotAtLeastContextInput] using hComp

/-- Rebuild the all-slots fold step using the audited per-slot CNF block. -/
private theorem slotClausesFoldStep_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod cnfStructuredEncodedType setCoveringChoicePairRowContextEncodedType)
      cnfStructuredEncodedType
      setCoveringSlotClausesFoldStep := by
  let X := EncodedType.prod cnfStructuredEncodedType setCoveringChoicePairRowContextEncodedType
  have hOut : TMPolyTimeMap X cnfStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst cnfStructuredEncodedType
      setCoveringChoicePairRowContextEncodedType
  have hCtx :
      TMPolyTimeMap X setCoveringChoicePairRowContextEncodedType
        (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd cnfStructuredEncodedType
      setCoveringChoicePairRowContextEncodedType
  have hBlock :
      TMPolyTimeMap X cnfStructuredEncodedType
        (fun p : X.Carrier => setCoveringSlotClausesForExecutable p.2) := by
    have hComp := TMPolyTimeMap.comp slotClausesForExecutable_tmPolyTime hCtx
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show SAT.CNF from p.1), setCoveringSlotClausesForExecutable p.2)) :=
    TMPolyTimeMap.prod_mk hOut hBlock
  have hAppend :
      TMPolyTimeMap X cnfStructuredEncodedType
        (fun p : X.Carrier =>
          (show SAT.CNF from p.1) ++ setCoveringSlotClausesForExecutable p.2) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType)
      hAppendInput
    simpa [Function.comp, cnfStructuredEncodedType, X] using hComp
  simpa [setCoveringSlotClausesFoldStep, X] using hAppend

/-- Kernel-audited direct-TM evidence for the aggregate all-slots fold. -/
private theorem slotClausesFromContexts_tmPolyTime :
    TMPolyTimeMap
      setCoveringChoicePairListEncodedType
      cnfStructuredEncodedType
      setCoveringSlotClausesFromContexts := by
  rcases slotClausesFoldStep_tmPolyTime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      setCoveringChoicePairRowContextEncodedType cnfStructuredEncodedType
      setCoveringSlotClausesFoldStep ([] : SAT.CNF) hStep
      (Polynomial.C 0) setCoveringSlotClausesFoldGrow
      (fun _ _ => True) ?_ ?_
  · intro _xs
    constructor
    · trivial
    · have hNil : cnfStructuredEncodedType.inputSize ([] : SAT.CNF) = 0 := by
        change (EncodedType.list clauseStructuredEncodedType).inputSize ([] : SAT.CNF) = 0
        exact EncodedType.inputSize_list_nil clauseStructuredEncodedType
      simp [hNil]
  · intro source acc ctx hAcc hCtx
    simpa [setCoveringChoicePairListEncodedType, vertexPairListEncodedType] using
      setCoveringSlotClausesFoldStep_growth source acc ctx hAcc hCtx

/-- Kernel-audited direct-TM evidence for every compact slot clause. -/
theorem slotClausesExecutable_tmPolyTime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      cnfStructuredEncodedType
      setCoveringSlotClausesExecutable := by
  have hComp :=
    TMPolyTimeMap.comp slotClausesFromContexts_tmPolyTime
      slotAtLeastContextsExecutable_tmPolyTime
  simpa [Function.comp, setCoveringSlotClausesExecutable] using hComp

/-- Standard-axiom direct-TM evidence for CR's exact compact Set-Covering CNF executable. -/
theorem compactCNF_tmPolyTime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      cnfStructuredEncodedType
      setCoveringCNFExecutable := by
  let X := setCoveringStructuredEncodedType
  have hSlots :
      TMPolyTimeMap X cnfStructuredEncodedType setCoveringSlotClausesExecutable := by
    simpa [X] using slotClausesExecutable_tmPolyTime
  have hCoverage :
      TMPolyTimeMap X cnfStructuredEncodedType setCoveringCoverageClausesExecutable := by
    simpa [X] using coverageClausesExecutable_tmPolyTime
  have hAppendInput :
      TMPolyTimeMap X (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun I : X.Carrier =>
          (setCoveringSlotClausesExecutable I, setCoveringCoverageClausesExecutable I)) :=
    TMPolyTimeMap.prod_mk hSlots hCoverage
  have hAppend :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
  simpa [Function.comp, setCoveringCNFExecutable, cnfStructuredEncodedType, X] using hAppend

/-- The canonical V2 structured Set-Covering hub retained by the compact gadget. -/
abbrev sourceProblem : PresentedProblem :=
  Presentation.SetSystem.setCoveringStructuredProblem

/-- The canonical V2 structured CNF/SAT hub emitted by the compact gadget. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.Satisfiability.structuredProblem

/-- Compatibility cost for the exact compact executable, paired with its rebuilt direct-TM proof. -/
noncomputable def compactCNFTMBackedMap :
    TMBackedCostedMap
      sourceProblem.representation.encodedType
      targetProblem.representation.encodedType
      setCoveringCNFExecutable where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      setCoveringCNFExecutable_polynomialSizeBound
  tm_polytime := compactCNF_tmPolyTime

/-- The exact component request for the compact Set-Covering-to-CNF shared gadget. -/
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget sourceProblem targetProblem

def sharedGadgetRequest : SharedGadgetRequest := .exact

/-- The standard-audited compact executable is admitted once as a typed primitive. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def sharedGadgetPrimitive :
    Primitive sourceProblem.representation targetProblem.representation :=
  Primitive.ofTMPolyTime setCoveringCNFExecutable compactCNF_tmPolyTime

/-- The reusable compact computation remains one primitive atom. -/
noncomputable def sharedGadgetProgram :
    PolyProg sourceProblem.representation targetProblem.representation :=
  .atom sharedGadgetPrimitive

@[simp] theorem sharedGadgetProgram_run (input : sourceProblem.Instance) :
    sharedGadgetProgram.run input = setCoveringCNFExecutable input :=
  rfl

/-- The semantic iff is indexed by the exact same compact executable. -/
theorem sharedGadgetProgram_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (sharedGadgetProgram.run input) := by
  change SetCovering input ↔ SAT.CNF.Satisfiable (sharedGadgetProgram.run input)
  rw [sharedGadgetProgram_run]
  exact setCoveringCNFExecutable_correct input

/-- The authoritative reusable Set-Covering-to-CNF shared-gadget certificate. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def sharedGadget : CertifiedReduction sourceProblem targetProblem where
  program := sharedGadgetProgram
  correct := sharedGadgetProgram_correct

/-- The exact component request accepts only the program-indexed certificate. -/
noncomputable def sharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget sourceProblem targetProblem :=
  Protocol.ComponentResolver.accept sharedGadgetRequest sharedGadget

@[simp] theorem sharedGadget_directTM :
    sharedGadget.directTM = sharedGadget.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM sharedGadget

@[simp] theorem sharedGadget_compileTM_eq_standardTM :
    sharedGadget.program.compileTM = compactCNF_tmPolyTime :=
  rfl

@[simp] theorem sharedGadgetResolution_eq_accepted :
    sharedGadgetResolution = .accepted sharedGadget :=
  rfl

end SetCoveringToSatisfiabilityStandardTM
end Domain
end ComplexityReduction
