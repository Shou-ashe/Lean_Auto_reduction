import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.SlackVectors

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

/-!
Outer fold for all compact slack-item digit vectors.
-/

def compactEmptyConstraint : List Int × Int :=
  ([], 0)

def compactSlackAllVectorsInstructionPayloadEncodedType : EncodedType :=
  EncodedType.prod integerProgrammingBinaryStructuredEncodedType
    constraintBinaryStructuredEncodedType

def compactSlackAllVectorsInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool compactSlackAllVectorsInstructionPayloadEncodedType

def compactSlackAllVectorsInstructionListEncodedType : EncodedType :=
  EncodedType.list compactSlackAllVectorsInstructionEncodedType

def compactSlackAllVectorsInitInstruction (I : IntegerProgrammingInput) :
    compactSlackAllVectorsInstructionEncodedType.Carrier :=
  (false, (I, compactEmptyConstraint))

def compactSlackAllVectorsTickInstruction (constraint : List Int × Int) :
    compactSlackAllVectorsInstructionEncodedType.Carrier :=
  (true, (compactEmptyIntegerProgrammingInput, constraint))

def compactSlackAllVectorsInstructions (I : IntegerProgrammingInput) :
    List compactSlackAllVectorsInstructionEncodedType.Carrier :=
  compactSlackAllVectorsInitInstruction I ::
    I.constraints.map compactSlackAllVectorsTickInstruction

def compactSlackAllVectorsStep
    (p : CompactSlackRowVectorsAcc × compactSlackAllVectorsInstructionEncodedType.Carrier) :
    CompactSlackRowVectorsAcc :=
  match p.2.1 with
  | false =>
      (p.2.2.1, ((0 : Nat), ([] : List (List Nat))))
  | true =>
      let rowVectors :=
        compactSlackItemDigitsForConstraintExecutable p.1.1 p.1.2.1 p.2.2.2
      (p.1.1, (p.1.2.1.succ, p.1.2.2 ++ rowVectors))

def compactSlackAllVectorsFromInstructions
    (xs : List compactSlackAllVectorsInstructionEncodedType.Carrier) : List (List Nat) :=
  (xs.foldl (fun acc instr => compactSlackAllVectorsStep (acc, instr))
    compactSlackRowVectorsInitAcc).2.2

def compactSlackItemDigitVectorsExecutable (I : IntegerProgrammingInput) : List (List Nat) :=
  compactSlackAllVectorsFromInstructions (compactSlackAllVectorsInstructions I)

theorem compactSlackAllVectorsTick_fold
    (constraints : List (List Int × Int)) (I : IntegerProgrammingInput)
    (rowIndex : Nat) (out : List (List Nat)) :
    ((constraints.map compactSlackAllVectorsTickInstruction).foldl
        (fun acc instr => compactSlackAllVectorsStep (acc, instr))
        (I, (rowIndex, out))).2.2 =
      out ++ compactSlackItemDigitVectorsFrom I rowIndex constraints := by
  induction constraints generalizing rowIndex out with
  | nil =>
      simp [compactSlackAllVectorsStep, compactSlackItemDigitVectorsFrom]
  | cons constraint constraints ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        (((constraints.map compactSlackAllVectorsTickInstruction).foldl
            (fun acc instr => compactSlackAllVectorsStep (acc, instr))
            (I, (rowIndex.succ,
              out ++ compactSlackItemDigitsForConstraintExecutable
                I rowIndex constraint))).2.2) =
          out ++ compactSlackItemDigitVectorsFrom I rowIndex (constraint :: constraints)
      rw [ih rowIndex.succ
        (out ++ compactSlackItemDigitsForConstraintExecutable I rowIndex constraint)]
      rw [compactSlackItemDigitsForConstraintExecutable_eq]
      simp [compactSlackItemDigitVectorsFrom, List.append_assoc, Nat.succ_eq_add_one]

theorem compactSlackItemDigitVectorsExecutable_eq
    (I : IntegerProgrammingInput) :
    compactSlackItemDigitVectorsExecutable I = compactSlackItemDigitVectors I := by
  rw [compactSlackItemDigitVectorsExecutable, compactSlackAllVectorsFromInstructions,
    compactSlackAllVectorsInstructions, compactSlackAllVectorsInitInstruction,
    compactSlackItemDigitVectors]
  change
    (((I.constraints.map compactSlackAllVectorsTickInstruction).foldl
        (fun acc instr => compactSlackAllVectorsStep (acc, instr))
        (I, ((0 : Nat), ([] : List (List Nat))))).2.2) =
      compactSlackItemDigitVectorsFrom I 0 I.constraints
  simpa using compactSlackAllVectorsTick_fold I.constraints I 0 []

theorem compactSlackAllVectorsTickInstruction_tm_polytime :
    TMPolyTimeMap
      constraintBinaryStructuredEncodedType
      compactSlackAllVectorsInstructionEncodedType
      compactSlackAllVectorsTickInstruction := by
  let X := constraintBinaryStructuredEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hEmptyI :
      TMPolyTimeMap X integerProgrammingBinaryStructuredEncodedType
        (fun _ : X.Carrier => compactEmptyIntegerProgrammingInput) :=
    TMPolyTimeMap.const X integerProgrammingBinaryStructuredEncodedType
      compactEmptyIntegerProgrammingInput
  have hPayload :
      TMPolyTimeMap X compactSlackAllVectorsInstructionPayloadEncodedType
        (fun constraint : List Int × Int =>
          (compactEmptyIntegerProgrammingInput, constraint)) :=
    TMPolyTimeMap.prod_mk hEmptyI (TMPolyTimeMap.id X)
  have hOut := TMPolyTimeMap.prod_mk hTag hPayload
  simpa [compactSlackAllVectorsTickInstruction,
    compactSlackAllVectorsInstructionEncodedType, X] using hOut

theorem compactSlackAllVectorsInstructions_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      compactSlackAllVectorsInstructionListEncodedType
      compactSlackAllVectorsInstructions := by
  let X := integerProgrammingBinaryStructuredEncodedType
  have hConstraints :
      TMPolyTimeMap X constraintListBinaryStructuredEncodedType
        (fun I : IntegerProgrammingInput => I.constraints) := by
    simpa [X] using integerProgrammingBinaryConstraints_tm_polytime
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hEmptyConstraint :
      TMPolyTimeMap X constraintBinaryStructuredEncodedType
        (fun _ : X.Carrier => compactEmptyConstraint) :=
    TMPolyTimeMap.const X constraintBinaryStructuredEncodedType compactEmptyConstraint
  have hPayload :
      TMPolyTimeMap X compactSlackAllVectorsInstructionPayloadEncodedType
        (fun I : IntegerProgrammingInput => (I, compactEmptyConstraint)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id X) hEmptyConstraint
  have hInit :
      TMPolyTimeMap X compactSlackAllVectorsInstructionEncodedType
        compactSlackAllVectorsInitInstruction := by
    have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
    simpa [compactSlackAllVectorsInitInstruction,
      compactSlackAllVectorsInstructionEncodedType, X] using hOut
  have hTicks :
      TMPolyTimeMap X compactSlackAllVectorsInstructionListEncodedType
        (fun I : IntegerProgrammingInput =>
          I.constraints.map compactSlackAllVectorsTickInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactSlackAllVectorsTickInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hConstraints
    simpa [Function.comp, compactSlackAllVectorsInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactSlackAllVectorsInstructionEncodedType
          compactSlackAllVectorsInstructionListEncodedType)
        (fun I : IntegerProgrammingInput =>
          (compactSlackAllVectorsInitInstruction I,
            I.constraints.map compactSlackAllVectorsTickInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hTicks
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons compactSlackAllVectorsInstructionEncodedType) hConsInput
  simpa [Function.comp, compactSlackAllVectorsInstructions,
    compactSlackAllVectorsInstructionListEncodedType, X] using hCons

theorem compactSlackAllVectorsStep_tm_polytime :
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
      compactSlackItemDigitsForConstraintExecutable_tm_polytime hRowInput
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

theorem compactSlackAllVectorsInstruction_payload_inputSize_le
    (instr : compactSlackAllVectorsInstructionEncodedType.Carrier) :
    compactSlackAllVectorsInstructionPayloadEncodedType.inputSize instr.2 ≤
      compactSlackAllVectorsInstructionEncodedType.inputSize instr := by
  rcases instr with ⟨tag, payload⟩
  simp [compactSlackAllVectorsInstructionEncodedType, EncodedType.inputSize_prod]

theorem compactSlackAllVectorsResetAcc_inputSize_le
    (I : IntegerProgrammingInput) :
    compactSlackRowVectorsAccEncodedType.inputSize
        (I, ((0 : Nat), ([] : List (List Nat)))) ≤
      integerProgrammingBinaryStructuredEncodedType.inputSize I + 3 := by
  unfold compactSlackRowVectorsAccEncodedType
  rw [EncodedType.inputSize_prod]
  have hTail :
      (EncodedType.prod EncodedType.binaryNat
        (EncodedType.list (EncodedType.list EncodedType.binaryNat))).inputSize
        ((0 : Nat), ([] : List (List Nat))) = 1 := by
    rw [EncodedType.inputSize_prod]
    simp [EncodedType.inputSize, EncodedType.binaryNat, EncodedType.list]
  rw [hTail]
  simp

def compactSlackAllVectorsFoldInv
    (N : Nat) (acc : CompactSlackRowVectorsAcc) : Prop :=
  integerProgrammingBinaryStructuredEncodedType.inputSize acc.1 ≤ N + 20

noncomputable def compactSlackAllVectorsGrowPolynomial : Polynomial Nat :=
  (Polynomial.C 2 * Polynomial.X + Polynomial.C 2) *
      (Polynomial.C 4 * Polynomial.X * Polynomial.X +
        Polynomial.C 120 * Polynomial.X + Polynomial.C 1201) +
    Polynomial.C 20

theorem compactSlackAllVectorsInitAcc_bound
    (xs : List compactSlackAllVectorsInstructionEncodedType.Carrier) :
    compactSlackAllVectorsFoldInv
        (compactSlackAllVectorsInstructionListEncodedType.inputSize xs)
        compactSlackRowVectorsInitAcc ∧
      compactSlackRowVectorsAccEncodedType.inputSize compactSlackRowVectorsInitAcc ≤
        (Polynomial.C 40).eval
          (compactSlackAllVectorsInstructionListEncodedType.inputSize xs) := by
  constructor
  · have hEmpty := compactEmptyIntegerProgrammingInput_inputSize_le
    simpa [compactSlackAllVectorsFoldInv, compactSlackRowVectorsInitAcc] using
      hEmpty.trans (by omega)
  · have hReset := compactSlackAllVectorsResetAcc_inputSize_le
      compactEmptyIntegerProgrammingInput
    have hEmpty := compactEmptyIntegerProgrammingInput_inputSize_le
    simpa [compactSlackRowVectorsInitAcc, Polynomial.eval] using hReset.trans (by omega)

theorem compactSlackAllVectorsStep_growth
    (source : List compactSlackAllVectorsInstructionEncodedType.Carrier)
    (acc : CompactSlackRowVectorsAcc)
    (instr : compactSlackAllVectorsInstructionEncodedType.Carrier)
    (hInv :
      compactSlackAllVectorsFoldInv
        (compactSlackAllVectorsInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      compactSlackAllVectorsInstructionEncodedType.inputSize instr ≤
        compactSlackAllVectorsInstructionListEncodedType.inputSize source) :
    compactSlackAllVectorsFoldInv
        (compactSlackAllVectorsInstructionListEncodedType.inputSize source)
        (compactSlackAllVectorsStep (acc, instr)) ∧
      compactSlackRowVectorsAccEncodedType.inputSize
          (compactSlackAllVectorsStep (acc, instr)) ≤
        compactSlackRowVectorsAccEncodedType.inputSize acc +
          compactSlackAllVectorsGrowPolynomial.eval
            (compactSlackAllVectorsInstructionListEncodedType.inputSize source) := by
  let N := compactSlackAllVectorsInstructionListEncodedType.inputSize source
  rcases acc with ⟨I, rowIndex, out⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨payloadI, payloadConstraint⟩
  have hPayload :
      compactSlackAllVectorsInstructionPayloadEncodedType.inputSize
          (payloadI, payloadConstraint) ≤ N := by
    exact (compactSlackAllVectorsInstruction_payload_inputSize_le
      (tag, payloadI, payloadConstraint)).trans hInstr
  have hPayloadI :
      integerProgrammingBinaryStructuredEncodedType.inputSize payloadI ≤ N := by
    simp [compactSlackAllVectorsInstructionPayloadEncodedType,
      EncodedType.inputSize_prod] at hPayload
    omega
  have hPayloadConstraint :
      constraintBinaryStructuredEncodedType.inputSize payloadConstraint ≤ N := by
    simp [compactSlackAllVectorsInstructionPayloadEncodedType,
      EncodedType.inputSize_prod] at hPayload
    omega
  have hRowSucc := binaryNatAdd_inputSize_le rowIndex 1
  have hOne : EncodedType.binaryNat.inputSize (1 : Nat) = 1 := by
    simp [EncodedType.inputSize, EncodedType.binaryNat]
  have hRowSuccSmall :
      EncodedType.binaryNat.inputSize rowIndex.succ ≤
        EncodedType.binaryNat.inputSize rowIndex + 2 := by
    simpa [Nat.succ_eq_add_one, hOne] using hRowSucc
  cases tag
  · constructor
    · exact hPayloadI.trans (by omega)
    · change compactSlackRowVectorsAccEncodedType.inputSize
          (payloadI, ((0 : Nat), ([] : List (List Nat)))) ≤
        compactSlackRowVectorsAccEncodedType.inputSize (I, (rowIndex, out)) +
          compactSlackAllVectorsGrowPolynomial.eval N
      have hNew :
          compactSlackRowVectorsAccEncodedType.inputSize
              (payloadI, ((0 : Nat), ([] : List (List Nat)))) ≤ N + 3 := by
        exact (compactSlackAllVectorsResetAcc_inputSize_le payloadI).trans (by omega)
      have hBudget :
          N + 3 ≤ compactSlackRowVectorsAccEncodedType.inputSize (I, (rowIndex, out)) +
            compactSlackAllVectorsGrowPolynomial.eval N := by
        have hGrow : N + 3 ≤ compactSlackAllVectorsGrowPolynomial.eval N := by
          simp [compactSlackAllVectorsGrowPolynomial, Polynomial.eval_add,
            Polynomial.eval_mul, Polynomial.eval_X]
          ring_nf
          nlinarith [Nat.zero_le N]
        exact hGrow.trans (Nat.le_add_left _ _)
      exact hNew.trans hBudget
  · have hRowVectors :=
      compactSlackItemDigitsForConstraintExecutable_inputSize_le_of_bound
        (I := I) (rowIndex := rowIndex) (constraint := payloadConstraint) (N := N)
        hInv hPayloadConstraint
    have hAppend :
        (EncodedType.list (EncodedType.list EncodedType.binaryNat)).inputSize
            (out ++
              compactSlackItemDigitsForConstraintExecutable I rowIndex payloadConstraint) =
          (EncodedType.list (EncodedType.list EncodedType.binaryNat)).inputSize out +
            (EncodedType.list (EncodedType.list EncodedType.binaryNat)).inputSize
              (compactSlackItemDigitsForConstraintExecutable I rowIndex payloadConstraint) := by
      exact encodedList_inputSize_append (EncodedType.list EncodedType.binaryNat) out
        (compactSlackItemDigitsForConstraintExecutable I rowIndex payloadConstraint)
    constructor
    · exact hInv
    · simp [compactSlackAllVectorsStep, compactSlackRowVectorsAccEncodedType,
        compactSlackAllVectorsGrowPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, EncodedType.inputSize_prod, hAppend]
      nlinarith

theorem compactSlackAllVectorsFold_tm_polytime :
    TMPolyTimeMap
      compactSlackAllVectorsInstructionListEncodedType
      compactSlackRowVectorsAccEncodedType
      (fun xs : List compactSlackAllVectorsInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactSlackAllVectorsStep (acc, instr))
          compactSlackRowVectorsInitAcc) := by
  rcases compactSlackAllVectorsStep_tm_polytime with ⟨hStep⟩
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

theorem compactSlackAllVectorsFromInstructions_tm_polytime :
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
  have hTailComp := TMPolyTimeMap.comp hTail compactSlackAllVectorsFold_tm_polytime
  have hOutComp := TMPolyTimeMap.comp hOut hTailComp
  simpa [Function.comp, compactSlackAllVectorsFromInstructions, Tail, L, Vec]
    using hOutComp

theorem compactSlackItemDigitVectorsExecutable_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      compactSlackItemDigitVectorsExecutable := by
  have hComp := TMPolyTimeMap.comp
    compactSlackAllVectorsFromInstructions_tm_polytime
    compactSlackAllVectorsInstructions_tm_polytime
  simpa [Function.comp, compactSlackItemDigitVectorsExecutable] using hComp

theorem compactSlackItemDigitVectors_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      compactSlackItemDigitVectors := by
  convert compactSlackItemDigitVectorsExecutable_tm_polytime using 1
  funext I
  exact (compactSlackItemDigitVectorsExecutable_eq I).symm

theorem compactItemDigitVectors_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      compactItemDigitVectors :=
  compactItemDigitVectors_tm_polytime_of_slack_vectors
    compactSlackItemDigitVectors_tm_polytime

theorem compactBase_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      EncodedType.binaryNat
      compactBase :=
  compactBase_tm_polytime_of_slack_vectors compactSlackItemDigitVectors_tm_polytime

theorem compactItemCodes_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list EncodedType.binaryNat)
      compactItemCodes :=
  compactItemCodes_tm_polytime_of_slack_vectors compactSlackItemDigitVectors_tm_polytime

theorem compactTargetCode_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      EncodedType.binaryNat
      compactTargetCode :=
  compactTargetCode_tm_polytime_of_slack_vectors compactSlackItemDigitVectors_tm_polytime

end Knapsack
end Karp21
end ComplexityReduction
