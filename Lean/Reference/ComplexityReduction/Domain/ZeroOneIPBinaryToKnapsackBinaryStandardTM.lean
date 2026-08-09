/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryArithmetic
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Presentation.KnapsackBinary
import ComplexityReduction.Presentation.ZeroOneIPBinary
import ComplexityReduction.Protocol.ComponentResolver

/-!
Standard-axiom direct-TM reconstruction for the binary structured
0-1-Integer-Programming-to-Knapsack gadget.

The read-only CR assembly uses `native_decide` only for the closed initial
accumulator-size bound of the variable-item fold.  This leaf rebuilds that
fold with kernel-reduced `decide`, then passes its direct witness through the
existing parameterized item/code/arithmetic constructors.  The executable and
the semantic compact map remain exactly CR's textbook construction.
-/

namespace ComplexityReduction
namespace Domain
namespace ZeroOneIPBinaryToKnapsackBinaryStandardTM

open ComplexityReduction
open ComplexityReduction.Karp21
open ComplexityReduction.Karp21.Knapsack
open ComplexityReduction.Combinatorics
open Certificate Encoding Program

/-- Kernel-audited closed bound for the variable-item fold's empty input. -/
theorem compactEmptyIntegerProgrammingInput_inputSize_le :
    integerProgrammingBinaryStructuredEncodedType.inputSize
        compactEmptyIntegerProgrammingInput ≤ 20 := by
  decide

/-- Kernel-audited initial invariant for the variable-item bounded fold. -/
theorem compactVariableItemVectorsInitAcc_bound :
    (xs : List compactVariableItemVectorsInstructionEncodedType.Carrier) →
      compactVariableItemVectorsFoldInv
          (compactVariableItemVectorsInstructionListEncodedType.inputSize xs)
          compactVariableItemVectorsInitAcc ∧
        compactVariableItemVectorsAccEncodedType.inputSize compactVariableItemVectorsInitAcc ≤
          (Polynomial.C 30).eval
            (compactVariableItemVectorsInstructionListEncodedType.inputSize xs) := by
  intro xs
  constructor
  · have hEmpty := compactEmptyIntegerProgrammingInput_inputSize_le
    simpa [compactVariableItemVectorsFoldInv, compactVariableItemVectorsInitAcc] using
      hEmpty.trans (by omega)
  · have hReset :=
      compactVariableItemVectorsResetAcc_inputSize_le compactEmptyIntegerProgrammingInput
    have hEmpty := compactEmptyIntegerProgrammingInput_inputSize_le
    simpa [compactVariableItemVectorsInitAcc, Polynomial.eval] using hReset.trans (by omega)

/-- Kernel-audited direct-TM realization of the bounded variable-item fold. -/
theorem compactVariableItemVectorsFold_tmPolyTime :
    TMPolyTimeMap
      compactVariableItemVectorsInstructionListEncodedType
      compactVariableItemVectorsAccEncodedType
      (fun xs : List compactVariableItemVectorsInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactVariableItemVectorsStep (acc, instr))
          compactVariableItemVectorsInitAcc) := by
  rcases compactVariableItemVectorsStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      compactVariableItemVectorsInstructionEncodedType
      compactVariableItemVectorsAccEncodedType
      compactVariableItemVectorsStep compactVariableItemVectorsInitAcc hStep
      (Polynomial.C 30)
      (Polynomial.C 4 * Polynomial.X * Polynomial.X +
        Polynomial.C 200 * Polynomial.X + Polynomial.C 2000)
      compactVariableItemVectorsFoldInv ?_ ?_
  · intro xs
    exact compactVariableItemVectorsInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact compactVariableItemVectorsStep_growth source acc instr hInv hInstr

/-- Kernel-audited projection from the variable-item fold accumulator. -/
theorem compactVariableItemDigitVectorsFromInstructions_tmPolyTime :
    TMPolyTimeMap
      compactVariableItemVectorsInstructionListEncodedType
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      compactVariableItemDigitVectorsFromInstructions := by
  let Vec := EncodedType.list EncodedType.binaryNat
  let L := EncodedType.list Vec
  let Tail := EncodedType.prod EncodedType.binaryNat L
  have hTail : TMPolyTimeMap compactVariableItemVectorsAccEncodedType Tail
      (fun acc : CompactVariableItemVectorsAcc => acc.2) := by
    simpa [compactVariableItemVectorsAccEncodedType, Tail, L, Vec] using
      TMPolyTimeMap.snd integerProgrammingBinaryStructuredEncodedType Tail
  have hOut : TMPolyTimeMap Tail L
      (fun tail : Nat × List (List Nat) => tail.2) := by
    simpa [Tail, L, Vec] using
      TMPolyTimeMap.snd EncodedType.binaryNat L
  have hTailComp := TMPolyTimeMap.comp hTail compactVariableItemVectorsFold_tmPolyTime
  have hOutComp := TMPolyTimeMap.comp hOut hTailComp
  simpa [Function.comp, compactVariableItemDigitVectorsFromInstructions, Tail, L, Vec]
    using hOutComp

/-- Kernel-audited executable for the variable truth-item digit vectors. -/
theorem compactVariableItemDigitVectorsExecutable_tmPolyTime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      compactVariableItemDigitVectorsExecutable := by
  have hComp := TMPolyTimeMap.comp
    compactVariableItemDigitVectorsFromInstructions_tmPolyTime
    compactVariableItemVectorsInstructions_tm_polytime
  simpa [Function.comp, compactVariableItemDigitVectorsExecutable] using hComp

/-- Kernel-audited direct-TM realization of the variable truth-item vectors. -/
theorem compactVariableItemDigitVectors_tmPolyTime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      compactVariableItemDigitVectors := by
  convert compactVariableItemDigitVectorsExecutable_tmPolyTime using 1
  funext I
  exact (compactVariableItemDigitVectorsExecutable_eq I).symm

/-- Kernel-audited initial invariant for the inner slack-vector bounded fold. -/
theorem compactSlackRowVectorsInitAcc_bound :
    (xs : List compactSlackRowVectorsInstructionEncodedType.Carrier) →
      compactSlackRowVectorsFoldInv
          (compactSlackRowVectorsInstructionListEncodedType.inputSize xs)
          compactSlackRowVectorsInitAcc ∧
        compactSlackRowVectorsAccEncodedType.inputSize compactSlackRowVectorsInitAcc ≤
          (Polynomial.C 40).eval
            (compactSlackRowVectorsInstructionListEncodedType.inputSize xs) := by
  intro xs
  constructor
  · constructor
    · have hEmpty := compactEmptyIntegerProgrammingInput_inputSize_le
      simpa [compactSlackRowVectorsInitAcc] using hEmpty.trans (by omega)
    · simp [compactSlackRowVectorsInitAcc, EncodedType.inputSize, EncodedType.binaryNat]
  · have hReset :=
      compactSlackRowVectorsResetAcc_inputSize_le compactEmptyIntegerProgrammingInput 0 0
    have hPayload :
        compactSlackRowVectorsInstructionPayloadEncodedType.inputSize
            (compactEmptyIntegerProgrammingInput, ((0 : Nat), (0 : Nat))) ≤ 40 := by
      change integerProgrammingBinaryStructuredEncodedType.inputSize
            compactEmptyIntegerProgrammingInput + 1 +
          (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat).inputSize
            ((0 : Nat), (0 : Nat)) ≤ 40
      have hPair :
          (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat).inputSize
              ((0 : Nat), (0 : Nat)) = 1 := by
        rw [EncodedType.inputSize_prod]
        simp [EncodedType.inputSize, EncodedType.binaryNat]
      rw [hPair]
      have hEmpty := compactEmptyIntegerProgrammingInput_inputSize_le
      omega
    simpa [compactSlackRowVectorsInitAcc, Polynomial.eval] using hReset.trans hPayload

/-- Kernel-audited direct-TM realization of the inner slack-vector fold. -/
theorem compactSlackRowVectorsFold_tmPolyTime :
    TMPolyTimeMap
      compactSlackRowVectorsInstructionListEncodedType
      compactSlackRowVectorsAccEncodedType
      (fun xs : List compactSlackRowVectorsInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactSlackRowVectorsStep (acc, instr))
          compactSlackRowVectorsInitAcc) := by
  rcases compactSlackRowVectorsStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      compactSlackRowVectorsInstructionEncodedType
      compactSlackRowVectorsAccEncodedType
      compactSlackRowVectorsStep compactSlackRowVectorsInitAcc hStep
      (Polynomial.C 40)
      (Polynomial.C 4 * Polynomial.X * Polynomial.X +
        Polynomial.C 120 * Polynomial.X + Polynomial.C 1200)
      compactSlackRowVectorsFoldInv ?_ ?_
  · intro xs
    exact compactSlackRowVectorsInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact compactSlackRowVectorsStep_growth source acc instr hInv hInstr

/-- Kernel-audited projection from the inner slack-vector fold accumulator. -/
theorem compactSlackRowVectorsFromInstructions_tmPolyTime :
    TMPolyTimeMap
      compactSlackRowVectorsInstructionListEncodedType
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      compactSlackRowVectorsFromInstructions := by
  let Vec := EncodedType.list EncodedType.binaryNat
  let L := EncodedType.list Vec
  let Tail := EncodedType.prod EncodedType.binaryNat L
  have hTail : TMPolyTimeMap compactSlackRowVectorsAccEncodedType Tail
      (fun acc : CompactSlackRowVectorsAcc => acc.2) := by
    simpa [compactSlackRowVectorsAccEncodedType, Tail, L, Vec] using
      TMPolyTimeMap.snd integerProgrammingBinaryStructuredEncodedType Tail
  have hOut : TMPolyTimeMap Tail L
      (fun tail : Nat × List (List Nat) => tail.2) := by
    simpa [Tail, L, Vec] using
      TMPolyTimeMap.snd EncodedType.binaryNat L
  have hTailComp := TMPolyTimeMap.comp hTail compactSlackRowVectorsFold_tmPolyTime
  have hOutComp := TMPolyTimeMap.comp hOut hTailComp
  simpa [Function.comp, compactSlackRowVectorsFromInstructions, Tail, L, Vec]
    using hOutComp

/-- Kernel-audited executable for one constraint's compact slack-item vectors. -/
theorem compactSlackItemDigitsForConstraintExecutable_tmPolyTime :
    TMPolyTimeMap
      compactSlackRowVectorsInputEncodedType
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      (fun p : IntegerProgrammingInput × Nat × (List Int × Int) =>
        compactSlackItemDigitsForConstraintExecutable p.1 p.2.1 p.2.2) := by
  have hComp := TMPolyTimeMap.comp
    compactSlackRowVectorsFromInstructions_tmPolyTime
    compactSlackRowVectorsInstructions_tm_polytime
  simpa [Function.comp, compactSlackItemDigitsForConstraintExecutable] using hComp

/-- Kernel-audited initial invariant for the outer all-slack-vectors fold. -/
theorem compactSlackAllVectorsInitAcc_bound :
    (xs : List compactSlackAllVectorsInstructionEncodedType.Carrier) →
      compactSlackAllVectorsFoldInv
          (compactSlackAllVectorsInstructionListEncodedType.inputSize xs)
          compactSlackRowVectorsInitAcc ∧
        compactSlackRowVectorsAccEncodedType.inputSize compactSlackRowVectorsInitAcc ≤
          (Polynomial.C 40).eval
            (compactSlackAllVectorsInstructionListEncodedType.inputSize xs) := by
  intro xs
  constructor
  · have hEmpty := compactEmptyIntegerProgrammingInput_inputSize_le
    simpa [compactSlackAllVectorsFoldInv, compactSlackRowVectorsInitAcc] using
      hEmpty.trans (by omega)
  · have hReset := compactSlackAllVectorsResetAcc_inputSize_le
      compactEmptyIntegerProgrammingInput
    have hEmpty := compactEmptyIntegerProgrammingInput_inputSize_le
    simpa [compactSlackRowVectorsInitAcc, Polynomial.eval] using hReset.trans (by omega)

/-- Kernel-audited direct-TM realization of one outer all-slack-vectors step. -/
theorem compactSlackAllVectorsStep_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod compactSlackRowVectorsAccEncodedType
        compactSlackAllVectorsInstructionEncodedType)
      compactSlackRowVectorsAccEncodedType
      compactSlackAllVectorsStep := by
  let Vec := EncodedType.list EncodedType.binaryNat
  let L := EncodedType.list Vec
  let Tail := EncodedType.prod EncodedType.binaryNat L
  let X := EncodedType.prod compactSlackRowVectorsAccEncodedType
    compactSlackAllVectorsInstructionEncodedType
  let A := compactSlackRowVectorsAccEncodedType
  have hAcc : TMPolyTimeMap X A
      (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
        p.1) := by
    simpa [X, A] using
      TMPolyTimeMap.fst compactSlackRowVectorsAccEncodedType
        compactSlackAllVectorsInstructionEncodedType
  have hInstr : TMPolyTimeMap X compactSlackAllVectorsInstructionEncodedType
      (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
        p.2) := by
    simpa [X, A] using
      TMPolyTimeMap.snd compactSlackRowVectorsAccEncodedType
        compactSlackAllVectorsInstructionEncodedType
  have hAccI : TMPolyTimeMap X integerProgrammingBinaryStructuredEncodedType
      (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
        p.1.1) := by
    have hFst := TMPolyTimeMap.fst integerProgrammingBinaryStructuredEncodedType Tail
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, compactSlackRowVectorsAccEncodedType, Tail, X] using hComp
  have hAccTail : TMPolyTimeMap X Tail
      (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
        p.1.2) := by
    have hSnd := TMPolyTimeMap.snd integerProgrammingBinaryStructuredEncodedType Tail
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, compactSlackRowVectorsAccEncodedType, Tail, X] using hComp
  have hAccRow : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
        p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat L
    have hComp := TMPolyTimeMap.comp hFst hAccTail
    simpa [Function.comp, Tail, L, X] using hComp
  have hAccOut : TMPolyTimeMap X L
      (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
        p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat L
    have hComp := TMPolyTimeMap.comp hSnd hAccTail
    simpa [Function.comp, Tail, L, X] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
        p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool
      compactSlackAllVectorsInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, compactSlackAllVectorsInstructionEncodedType, X] using hComp
  have hPayload : TMPolyTimeMap X compactSlackAllVectorsInstructionPayloadEncodedType
      (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
        p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      compactSlackAllVectorsInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, compactSlackAllVectorsInstructionEncodedType, X] using hComp
  have hPayloadI : TMPolyTimeMap X integerProgrammingBinaryStructuredEncodedType
      (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
        p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst integerProgrammingBinaryStructuredEncodedType
      constraintBinaryStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, compactSlackAllVectorsInstructionPayloadEncodedType, X] using hComp
  have hPayloadConstraint : TMPolyTimeMap X constraintBinaryStructuredEncodedType
      (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
        p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd integerProgrammingBinaryStructuredEncodedType
      constraintBinaryStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, compactSlackAllVectorsInstructionPayloadEncodedType, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.binaryNat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have hEmpty : TMPolyTimeMap X L (fun _ : X.Carrier => ([] : List (List Nat))) :=
    TMPolyTimeMap.const X L []
  have hFalseTail : TMPolyTimeMap X Tail
      (fun _ : X.Carrier => ((0 : Nat), ([] : List (List Nat)))) :=
    TMPolyTimeMap.prod_mk hZero hEmpty
  have hFalseBranch : TMPolyTimeMap X A
      (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
        (p.2.2.1, ((0 : Nat), ([] : List (List Nat))))) :=
    TMPolyTimeMap.prod_mk hPayloadI hFalseTail
  have hRowInput :
      TMPolyTimeMap X compactSlackRowVectorsInputEncodedType
        (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
          (p.1.1, (p.1.2.1, p.2.2.2))) := by
    have hTailInput :
        TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat constraintBinaryStructuredEncodedType)
          (fun p : CompactSlackRowVectorsAcc ×
              compactSlackAllVectorsInstructionEncodedType.Carrier =>
            (p.1.2.1, p.2.2.2)) :=
      TMPolyTimeMap.prod_mk hAccRow hPayloadConstraint
    exact TMPolyTimeMap.prod_mk hAccI hTailInput
  have hRowVectors : TMPolyTimeMap X L
      (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
        compactSlackItemDigitsForConstraintExecutable p.1.1 p.1.2.1 p.2.2.2) := by
    have hComp := TMPolyTimeMap.comp
      compactSlackItemDigitsForConstraintExecutable_tmPolyTime hRowInput
    simpa [Function.comp, X, L] using hComp
  have hAppendInput : TMPolyTimeMap X (EncodedType.prod L L)
      (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
        (p.1.2.2,
          compactSlackItemDigitsForConstraintExecutable p.1.1 p.1.2.1 p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAccOut hRowVectors
  have hAppend : TMPolyTimeMap X L
      (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
        p.1.2.2 ++
          compactSlackItemDigitsForConstraintExecutable p.1.1 p.1.2.1 p.2.2.2) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append Vec) hAppendInput
    simpa [Function.comp, L, Vec, X] using hComp
  have hRowSucc : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
        p.1.2.1.succ) := by
    have hComp := TMPolyTimeMap.comp binaryNatSucc_tm_polytime hAccRow
    simpa [Function.comp, X] using hComp
  have hTrueTail : TMPolyTimeMap X Tail
      (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
        (p.1.2.1.succ,
          p.1.2.2 ++
            compactSlackItemDigitsForConstraintExecutable p.1.1 p.1.2.1 p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hRowSucc hAppend
  have hTrueBranch : TMPolyTimeMap X A
      (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
        (p.1.1,
          (p.1.2.1.succ,
            p.1.2.2 ++
              compactSlackItemDigitsForConstraintExecutable p.1.1 p.1.2.1 p.2.2.2))) :=
    TMPolyTimeMap.prod_mk hAccI hTrueTail
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier =>
          (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hDispatch : TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
      (fun p : Bool ×
          (CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier) =>
        match p.1 with
        | true =>
            (p.2.1.1,
              (p.2.1.2.1.succ,
                p.2.1.2.2 ++
                  compactSlackItemDigitsForConstraintExecutable
                    p.2.1.1 p.2.1.2.1 p.2.2.2.2))
        | false => (p.2.2.2.1, ((0 : Nat), ([] : List (List Nat))))) :=
    Clique.boolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : CompactSlackRowVectorsAcc ×
          compactSlackAllVectorsInstructionEncodedType.Carrier =>
        (p.2.2.1, ((0 : Nat), ([] : List (List Nat)))))
      (fTrue := fun p : CompactSlackRowVectorsAcc ×
          compactSlackAllVectorsInstructionEncodedType.Carrier =>
        (p.1.1,
          (p.1.2.1.succ,
            p.1.2.2 ++
              compactSlackItemDigitsForConstraintExecutable p.1.1 p.1.2.1 p.2.2.2)))
      hFalseBranch hTrueBranch
  have hComp := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  rcases instr with ⟨tag, payload⟩
  cases tag <;> rfl

/-- Kernel-audited direct-TM realization of the outer all-slack-vectors fold. -/
theorem compactSlackAllVectorsFold_tmPolyTime :
    TMPolyTimeMap
      compactSlackAllVectorsInstructionListEncodedType
      compactSlackRowVectorsAccEncodedType
      (fun xs : List compactSlackAllVectorsInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactSlackAllVectorsStep (acc, instr))
          compactSlackRowVectorsInitAcc) := by
  rcases compactSlackAllVectorsStep_tmPolyTime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      compactSlackAllVectorsInstructionEncodedType
      compactSlackRowVectorsAccEncodedType
      compactSlackAllVectorsStep compactSlackRowVectorsInitAcc hStep
      (Polynomial.C 40) compactSlackAllVectorsGrowPolynomial
      compactSlackAllVectorsFoldInv ?_ ?_
  · intro xs
    exact compactSlackAllVectorsInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact compactSlackAllVectorsStep_growth source acc instr hInv hInstr

/-- Kernel-audited projection from the outer all-slack-vectors fold accumulator. -/
theorem compactSlackAllVectorsFromInstructions_tmPolyTime :
    TMPolyTimeMap
      compactSlackAllVectorsInstructionListEncodedType
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      compactSlackAllVectorsFromInstructions := by
  let Vec := EncodedType.list EncodedType.binaryNat
  let L := EncodedType.list Vec
  let Tail := EncodedType.prod EncodedType.binaryNat L
  have hTail : TMPolyTimeMap compactSlackRowVectorsAccEncodedType Tail
      (fun acc : CompactSlackRowVectorsAcc => acc.2) := by
    simpa [compactSlackRowVectorsAccEncodedType, Tail, L, Vec] using
      TMPolyTimeMap.snd integerProgrammingBinaryStructuredEncodedType Tail
  have hOut : TMPolyTimeMap Tail L
      (fun tail : Nat × List (List Nat) => tail.2) := by
    simpa [Tail, L, Vec] using
      TMPolyTimeMap.snd EncodedType.binaryNat L
  have hTailComp := TMPolyTimeMap.comp hTail compactSlackAllVectorsFold_tmPolyTime
  have hOutComp := TMPolyTimeMap.comp hOut hTailComp
  simpa [Function.comp, compactSlackAllVectorsFromInstructions, Tail, L, Vec]
    using hOutComp

/-- Kernel-audited executable for all compact slack-item vectors. -/
theorem compactSlackItemDigitVectorsExecutable_tmPolyTime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      compactSlackItemDigitVectorsExecutable := by
  have hComp := TMPolyTimeMap.comp
    compactSlackAllVectorsFromInstructions_tmPolyTime
    compactSlackAllVectorsInstructions_tm_polytime
  simpa [Function.comp, compactSlackItemDigitVectorsExecutable] using hComp

/-- Kernel-audited direct-TM realization of all compact slack-item vectors. -/
theorem compactSlackItemDigitVectors_tmPolyTime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      compactSlackItemDigitVectors := by
  convert compactSlackItemDigitVectorsExecutable_tmPolyTime using 1
  funext I
  exact (compactSlackItemDigitVectorsExecutable_eq I).symm

/-- Assemble CR's full compact item list from the rebuilt variable side and existing slack side. -/
theorem compactItemDigitVectors_tmPolyTime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      compactItemDigitVectors := by
  let X := integerProgrammingBinaryStructuredEncodedType
  let L := EncodedType.list (EncodedType.list EncodedType.binaryNat)
  have hVariable : TMPolyTimeMap X L compactVariableItemDigitVectors := by
    simpa [X, L] using compactVariableItemDigitVectors_tmPolyTime
  have hSlack : TMPolyTimeMap X L compactSlackItemDigitVectors := by
    simpa [X, L] using compactSlackItemDigitVectors_tmPolyTime
  have hPair :
      TMPolyTimeMap X (EncodedType.prod L L)
        (fun I : IntegerProgrammingInput =>
          (compactVariableItemDigitVectors I, compactSlackItemDigitVectors I)) :=
    TMPolyTimeMap.prod_mk hVariable hSlack
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append (EncodedType.list EncodedType.binaryNat)) hPair
  simpa [Function.comp, compactItemDigitVectors, X, L] using hAppend

/-- Kernel-audited code assembly from the rebuilt full item-vector witness. -/
theorem compactItemCodes_tmPolyTime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list EncodedType.binaryNat)
      compactItemCodes :=
  compactItemCodes_tm_polytime_of_item_digit_vectors compactItemDigitVectors_tmPolyTime

/-- Kernel-audited target-code assembly from the rebuilt full item-vector witness. -/
theorem compactTargetCode_tmPolyTime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      EncodedType.binaryNat
      compactTargetCode :=
  compactTargetCode_tm_polytime_of_item_digit_vectors compactItemDigitVectors_tmPolyTime

/-- Standard-axiom direct-TM evidence for CR's exact compact binary map. -/
theorem compactMap_tmPolyTime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      knapsackBinaryStructuredEncodedType
      compactMap :=
  compactMap_tm_polytime_of_binary_arithmetic_witnesses
    rowNegativeShift_tm_polytime
    binaryNatSuccLeBool_tm_polytime
    compactItemCodes_tmPolyTime
    compactTargetCode_tmPolyTime

/-- Compatibility cost is derived from the exact same rebuilt executable. -/
noncomputable def compactMapTMBackedMap :
    TMBackedCostedMap
      integerProgrammingBinaryStructuredEncodedType
      knapsackBinaryStructuredEncodedType
      compactMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      zeroOneIPToKnapsackCompactBinaryStructured_polynomialSizeBound
  tm_polytime := compactMap_tmPolyTime

/-- The canonical V2 binary structured 0-1-IP source hub. -/
abbrev sourceProblem : PresentedProblem :=
  Presentation.ZeroOneIPBinary.binaryStructuredProblem

/-- The canonical V2 binary structured Knapsack target hub. -/
abbrev targetProblem : PresentedProblem :=
  Presentation.KnapsackBinary.structuredProblem

/-- The exact request fixes the full encoder-bound shared-gadget endpoints. -/
abbrev SharedGadgetRequest : Type 2 :=
  Protocol.ComponentRequest .sharedGadget sourceProblem targetProblem

def sharedGadgetRequest : SharedGadgetRequest := .exact

/-- The standard-audited primitive is indexed by CR's exact compact map. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def sharedGadgetPrimitive :
    Primitive sourceProblem.representation targetProblem.representation :=
  Primitive.ofTMPolyTime compactMap compactMap_tmPolyTime

/-- The reusable computation remains one typed primitive atom. -/
noncomputable def sharedGadgetProgram :
    PolyProg sourceProblem.representation targetProblem.representation :=
  .atom sharedGadgetPrimitive

@[simp] theorem sharedGadgetProgram_run (input : sourceProblem.Instance) :
    sharedGadgetProgram.run input = compactMap input :=
  rfl

/-- The semantic iff is indexed by the very same typed primitive executable. -/
theorem sharedGadgetProgram_correct (input : sourceProblem.Instance) :
    sourceProblem.accepts input ↔ targetProblem.accepts (sharedGadgetProgram.run input) := by
  change ZeroOneIntegerProgramming input ↔ Knapsack (sharedGadgetProgram.run input)
  rw [sharedGadgetProgram_run]
  exact compactMap_correct input

/-- The authoritative reusable binary numeric shared-gadget certificate. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def sharedGadget : CertifiedReduction sourceProblem targetProblem where
  program := sharedGadgetProgram
  correct := sharedGadgetProgram_correct

/-- The exact component request is accepted only from this typed certificate. -/
noncomputable def sharedGadgetResolution :
    Protocol.ComponentResolution .sharedGadget sourceProblem targetProblem :=
  Protocol.ComponentResolver.accept sharedGadgetRequest sharedGadget

@[simp] theorem sharedGadgetProgram_eq_atom :
    sharedGadgetProgram = PolyProg.atom sharedGadgetPrimitive :=
  rfl

@[simp] theorem sharedGadget_directTM :
    sharedGadget.directTM = sharedGadget.program.compileTM :=
  CertifiedReduction.directTM_eq_compileTM sharedGadget

@[simp] theorem sharedGadget_compileTM_eq_standardTM :
    sharedGadget.program.compileTM = compactMap_tmPolyTime :=
  rfl

@[simp] theorem sharedGadgetResolution_eq_accepted :
    sharedGadgetResolution = .accepted sharedGadget :=
  rfl

end ZeroOneIPBinaryToKnapsackBinaryStandardTM
end Domain
end ComplexityReduction
