import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.CodeAssembly

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

/-!
Executable generation of the compact truth-item digit vectors.

The fold scans the structural `compactTargetOnes` fuel.  Its accumulator stores
the source instance, the current bounded-variable index, and the generated digit
vectors.  Each tick appends the two truth-item vectors for the current index.
-/

def compactVariableItemDigitsExecutable
    (I : IntegerProgrammingInput) (i : Nat) (b : Bool) : List Nat :=
  compactVariableChoiceDigitsExecutable I i ++
    compactVariableConstraintDigitsExecutable I i b

theorem compactVariableItemDigitsExecutable_eq
    (I : IntegerProgrammingInput) (i : Nat) (b : Bool) :
    compactVariableItemDigitsExecutable I i b =
      compactVariableItemDigits I i b := by
  simp [compactVariableItemDigitsExecutable, compactVariableItemDigits,
    compactVariableChoiceDigitsExecutable_eq,
    compactVariableConstraintDigitsExecutable_eq]

theorem compactVariableItemDigitsExecutable_tm_polytime :
    TMPolyTimeMap
      compactVariableConstraintDigitsExecutableInputEncodedType
      (EncodedType.list EncodedType.binaryNat)
      (fun p : IntegerProgrammingInput × (Nat × Bool) =>
        compactVariableItemDigitsExecutable p.1 p.2.1 p.2.2) := by
  let X := compactVariableConstraintDigitsExecutableInputEncodedType
  let L := EncodedType.list EncodedType.binaryNat
  have hI : TMPolyTimeMap X integerProgrammingBinaryStructuredEncodedType
      (fun p : IntegerProgrammingInput × (Nat × Bool) => p.1) := by
    simpa [X, compactVariableConstraintDigitsExecutableInputEncodedType] using
      TMPolyTimeMap.fst integerProgrammingBinaryStructuredEncodedType
        compactConstraintDigitsInitPayloadEncodedType
  have hPayload :
      TMPolyTimeMap X compactConstraintDigitsInitPayloadEncodedType
        (fun p : IntegerProgrammingInput × (Nat × Bool) => p.2) := by
    simpa [X, compactVariableConstraintDigitsExecutableInputEncodedType] using
      TMPolyTimeMap.snd integerProgrammingBinaryStructuredEncodedType
        compactConstraintDigitsInitPayloadEncodedType
  have hIdx : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : IntegerProgrammingInput × (Nat × Bool) => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, compactConstraintDigitsInitPayloadEncodedType, X] using hComp
  have hChoiceInput :
      TMPolyTimeMap X
        (EncodedType.prod integerProgrammingBinaryStructuredEncodedType EncodedType.binaryNat)
        (fun p : IntegerProgrammingInput × (Nat × Bool) => (p.1, p.2.1)) :=
    TMPolyTimeMap.prod_mk hI hIdx
  have hChoice :
      TMPolyTimeMap X L
        (fun p : IntegerProgrammingInput × (Nat × Bool) =>
          compactVariableChoiceDigitsExecutable p.1 p.2.1) := by
    have hComp := TMPolyTimeMap.comp compactVariableChoiceDigitsExecutable_tm_polytime
      hChoiceInput
    simpa [Function.comp, X, L] using hComp
  have hConstraint :
      TMPolyTimeMap X L
        (fun p : IntegerProgrammingInput × (Nat × Bool) =>
          compactVariableConstraintDigitsExecutable p.1 p.2.1 p.2.2) := by
    simpa [X, L] using compactVariableConstraintDigitsExecutable_tm_polytime
  have hPair :
      TMPolyTimeMap X (EncodedType.prod L L)
        (fun p : IntegerProgrammingInput × (Nat × Bool) =>
          (compactVariableChoiceDigitsExecutable p.1 p.2.1,
            compactVariableConstraintDigitsExecutable p.1 p.2.1 p.2.2)) :=
    TMPolyTimeMap.prod_mk hChoice hConstraint
  have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.binaryNat) hPair
  simpa [Function.comp, compactVariableItemDigitsExecutable, X, L] using hAppend

theorem compactVariableChoiceDigit_inputSize_le_one
    {I : IntegerProgrammingInput} {i digit : Nat}
    (hdigit : digit ∈ compactVariableChoiceDigits I i) :
    EncodedType.binaryNat.inputSize digit ≤ 1 := by
  simp [compactVariableChoiceDigits] at hdigit
  rcases hdigit with ⟨j, _hj, rfl⟩
  split <;> simp [EncodedType.inputSize, EncodedType.binaryNat]

theorem constraintListBinary_inputSize_le_integerProgramming
    (I : IntegerProgrammingInput) :
    constraintListBinaryStructuredEncodedType.inputSize I.constraints ≤
      integerProgrammingBinaryStructuredEncodedType.inputSize I := by
  change constraintListBinaryStructuredEncodedType.inputSize I.constraints ≤
    (EncodedType.prod EncodedType.binaryNat constraintListBinaryStructuredEncodedType).inputSize
      (I.numVariables, I.constraints)
  simp [EncodedType.inputSize_prod]

theorem compactVariableConstraintDigit_inputSize_le
    {I : IntegerProgrammingInput} {i : Nat} {b : Bool} {digit : Nat}
    (hdigit : digit ∈ compactVariableConstraintDigits I i b) :
    EncodedType.binaryNat.inputSize digit ≤
      integerProgrammingBinaryStructuredEncodedType.inputSize I + 4 := by
  rw [compactVariableConstraintDigits] at hdigit
  rw [List.mem_map] at hdigit
  rcases hdigit with ⟨constraint, hconstraint, rfl⟩
  have hContribution :=
    compactCoeffContribution_binaryNat_inputSize_le
      (compactCoeffAt constraint.1 i) b
  have hCoeff := compactCoeffAt_binaryInt_inputSize_le constraint.1 i
  have hConstraintElem :=
    encodedList_element_inputSize_le constraintBinaryStructuredEncodedType hconstraint
  have hConstraintsLe := constraintListBinary_inputSize_le_integerProgramming I
  have hRowLe :
      intRowBinaryStructuredEncodedType.inputSize constraint.1 ≤
        integerProgrammingBinaryStructuredEncodedType.inputSize I := by
    exact (constraint_row_inputSize_le_constraint constraint).trans
      (hConstraintElem.trans hConstraintsLe)
  omega

theorem compactVariableChoiceDigitsExecutable_inputSize_le
    (I : IntegerProgrammingInput) (i : Nat) :
    (EncodedType.list EncodedType.binaryNat).inputSize
        (compactVariableChoiceDigitsExecutable I i) ≤
      2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2 := by
  rw [compactVariableChoiceDigitsExecutable_eq]
  have hList :=
    Clique.encodedList_inputSize_le_length_mul_bound EncodedType.binaryNat
      (compactVariableChoiceDigits I i) 1
      (by
        intro digit hdigit
        exact compactVariableChoiceDigit_inputSize_le_one hdigit)
  have hLen := compactVariableChoiceDigits_length I i
  have hList' :
      (EncodedType.list EncodedType.binaryNat).inputSize
          (compactVariableChoiceDigits I i) ≤ varBound I * 2 := by
    calc
      (EncodedType.list EncodedType.binaryNat).inputSize
          (compactVariableChoiceDigits I i)
          ≤ (compactVariableChoiceDigits I i).length * 2 := by
            simpa using hList
      _ = varBound I * 2 := by
            rw [hLen]
  have hVar := varBound_le_binaryStructured_inputSize I
  nlinarith

theorem compactVariableConstraintDigitsExecutable_inputSize_le
    (I : IntegerProgrammingInput) (i : Nat) (b : Bool) :
    (EncodedType.list EncodedType.binaryNat).inputSize
        (compactVariableConstraintDigitsExecutable I i b) ≤
      integerProgrammingBinaryStructuredEncodedType.inputSize I *
          (integerProgrammingBinaryStructuredEncodedType.inputSize I + 5) := by
  rw [compactVariableConstraintDigitsExecutable_eq]
  have hList :=
    Clique.encodedList_inputSize_le_length_mul_bound EncodedType.binaryNat
      (compactVariableConstraintDigits I i b)
      (integerProgrammingBinaryStructuredEncodedType.inputSize I + 4)
      (by
        intro digit hdigit
        exact compactVariableConstraintDigit_inputSize_le hdigit)
  have hLenDigits := compactVariableConstraintDigits_length I i b
  have hList' :
      (EncodedType.list EncodedType.binaryNat).inputSize
          (compactVariableConstraintDigits I i b) ≤
        I.constraints.length *
          (integerProgrammingBinaryStructuredEncodedType.inputSize I + 5) := by
    calc
      (EncodedType.list EncodedType.binaryNat).inputSize
          (compactVariableConstraintDigits I i b)
          ≤ (compactVariableConstraintDigits I i b).length *
              (integerProgrammingBinaryStructuredEncodedType.inputSize I + 5) := by
            simpa [Nat.add_assoc] using hList
      _ = I.constraints.length *
            (integerProgrammingBinaryStructuredEncodedType.inputSize I + 5) := by
            rw [hLenDigits]
  have hLen :
      I.constraints.length ≤ integerProgrammingBinaryStructuredEncodedType.inputSize I := by
    have hRaw :=
      encodedList_length_le_inputSize constraintBinaryStructuredEncodedType I.constraints
    exact hRaw.trans (constraintListBinary_inputSize_le_integerProgramming I)
  nlinarith

theorem compactVariableItemDigitsExecutable_inputSize_le
    (I : IntegerProgrammingInput) (i : Nat) (b : Bool) :
    (EncodedType.list EncodedType.binaryNat).inputSize
        (compactVariableItemDigitsExecutable I i b) ≤
      integerProgrammingBinaryStructuredEncodedType.inputSize I *
          integerProgrammingBinaryStructuredEncodedType.inputSize I +
        8 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 12 := by
  rw [compactVariableItemDigitsExecutable]
  have hChoice := compactVariableChoiceDigitsExecutable_inputSize_le I i
  have hConstraint := compactVariableConstraintDigitsExecutable_inputSize_le I i b
  calc
    (EncodedType.list EncodedType.binaryNat).inputSize
        (compactVariableChoiceDigitsExecutable I i ++
          compactVariableConstraintDigitsExecutable I i b)
        =
      (EncodedType.list EncodedType.binaryNat).inputSize
          (compactVariableChoiceDigitsExecutable I i) +
        (EncodedType.list EncodedType.binaryNat).inputSize
          (compactVariableConstraintDigitsExecutable I i b) := by
        exact encodedList_inputSize_append EncodedType.binaryNat
          (compactVariableChoiceDigitsExecutable I i)
          (compactVariableConstraintDigitsExecutable I i b)
    _ ≤ integerProgrammingBinaryStructuredEncodedType.inputSize I *
          integerProgrammingBinaryStructuredEncodedType.inputSize I +
        8 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 12 := by
        nlinarith

def compactEmptyIntegerProgrammingInput : IntegerProgrammingInput where
  numVariables := 0
  constraints := []

theorem compactEmptyIntegerProgrammingInput_inputSize_le :
    integerProgrammingBinaryStructuredEncodedType.inputSize
        compactEmptyIntegerProgrammingInput ≤ 20 := by
  native_decide

def compactVariableItemVectorsAccEncodedType : EncodedType :=
  EncodedType.prod integerProgrammingBinaryStructuredEncodedType
    (EncodedType.prod EncodedType.binaryNat
      (EncodedType.list (EncodedType.list EncodedType.binaryNat)))

def compactVariableItemVectorsInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool integerProgrammingBinaryStructuredEncodedType

def compactVariableItemVectorsInstructionListEncodedType : EncodedType :=
  EncodedType.list compactVariableItemVectorsInstructionEncodedType

abbrev CompactVariableItemVectorsAcc :=
  IntegerProgrammingInput × Nat × List (List Nat)

def compactVariableItemVectorsInitAcc : CompactVariableItemVectorsAcc :=
  (compactEmptyIntegerProgrammingInput, (0, []))

theorem compactVariableItemVectorsResetAcc_inputSize_le
    (I : IntegerProgrammingInput) :
    compactVariableItemVectorsAccEncodedType.inputSize
        (I, ((0 : Nat), ([] : List (List Nat)))) ≤
      integerProgrammingBinaryStructuredEncodedType.inputSize I + 3 := by
  unfold compactVariableItemVectorsAccEncodedType
  rw [EncodedType.inputSize_prod]
  have hTail :
      (EncodedType.prod EncodedType.binaryNat
          (EncodedType.list (EncodedType.list EncodedType.binaryNat))).inputSize
          ((0 : Nat), ([] : List (List Nat))) = 1 := by
    rw [EncodedType.inputSize_prod]
    simp [EncodedType.inputSize, EncodedType.binaryNat, EncodedType.list]
  rw [hTail]
  simp

def compactVariableItemVectorsInitInstruction (I : IntegerProgrammingInput) :
    compactVariableItemVectorsInstructionEncodedType.Carrier :=
  (false, I)

def compactVariableItemVectorsTickInstruction (_fuel : Nat) :
    compactVariableItemVectorsInstructionEncodedType.Carrier :=
  (true, compactEmptyIntegerProgrammingInput)

def compactVariableItemVectorsInstructions (I : IntegerProgrammingInput) :
    List compactVariableItemVectorsInstructionEncodedType.Carrier :=
  compactVariableItemVectorsInitInstruction I ::
    (compactTargetOnes I).map compactVariableItemVectorsTickInstruction

def compactVariableItemVectorsStep
    (p :
      CompactVariableItemVectorsAcc ×
        compactVariableItemVectorsInstructionEncodedType.Carrier) :
    CompactVariableItemVectorsAcc :=
  match p.2.1 with
  | false => (p.2.2, (0, []))
  | true =>
      let I := p.1.1
      let idx := p.1.2.1
      let out := p.1.2.2
      (I, (idx.succ,
        out ++ [compactVariableItemDigitsExecutable I idx true,
          compactVariableItemDigitsExecutable I idx false]))

def compactVariableItemDigitVectorsFromInstructions
    (xs : List compactVariableItemVectorsInstructionEncodedType.Carrier) :
    List (List Nat) :=
  (xs.foldl (fun acc instr => compactVariableItemVectorsStep (acc, instr))
    compactVariableItemVectorsInitAcc).2.2

def compactVariableItemDigitVectorsExecutable
    (I : IntegerProgrammingInput) : List (List Nat) :=
  compactVariableItemDigitVectorsFromInstructions
    (compactVariableItemVectorsInstructions I)

theorem compactVariableItemVectorsTick_fold
    (fuel : List Nat) (I : IntegerProgrammingInput) (idx : Nat)
    (out : List (List Nat)) :
    ((fuel.map compactVariableItemVectorsTickInstruction).foldl
        (fun acc instr => compactVariableItemVectorsStep (acc, instr))
        (I, (idx, out))).2.2 =
      out ++ (List.range' idx fuel.length).flatMap fun j =>
        [compactVariableItemDigitsExecutable I j true,
          compactVariableItemDigitsExecutable I j false] := by
  induction fuel generalizing idx out with
  | nil =>
      simp [compactVariableItemVectorsStep]
  | cons _fuel fuel ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        (((fuel.map compactVariableItemVectorsTickInstruction).foldl
            (fun acc instr => compactVariableItemVectorsStep (acc, instr))
            (I, (idx.succ,
              out ++ [compactVariableItemDigitsExecutable I idx true,
                compactVariableItemDigitsExecutable I idx false]))).2.2) =
          out ++ (List.range' idx (_fuel :: fuel).length).flatMap fun j =>
            [compactVariableItemDigitsExecutable I j true,
              compactVariableItemDigitsExecutable I j false]
      rw [ih idx.succ
        (out ++ [compactVariableItemDigitsExecutable I idx true,
          compactVariableItemDigitsExecutable I idx false])]
      simp [List.range'_succ, List.append_assoc, Nat.succ_eq_add_one]

theorem compactVariableItemDigitVectorsExecutable_eq
    (I : IntegerProgrammingInput) :
    compactVariableItemDigitVectorsExecutable I =
      compactVariableItemDigitVectors I := by
  have h := compactVariableItemVectorsTick_fold (compactTargetOnes I) I 0 []
  rw [compactVariableItemDigitVectorsExecutable,
    compactVariableItemDigitVectorsFromInstructions,
    compactVariableItemVectorsInstructions]
  simpa [compactVariableItemVectorsInitInstruction,
    compactVariableItemVectorsInitAcc, compactVariableItemVectorsStep,
    compactTargetOnes_eq_replicate, List.range_eq_range',
    compactVariableItemDigitVectors, compactVariableItemDigitsExecutable_eq] using h

theorem compactVariableItemVectorsInitInstruction_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      compactVariableItemVectorsInstructionEncodedType
      compactVariableItemVectorsInitInstruction := by
  let X := integerProgrammingBinaryStructuredEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun _ : IntegerProgrammingInput => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hOut := TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  simpa [compactVariableItemVectorsInitInstruction,
    compactVariableItemVectorsInstructionEncodedType, X] using hOut

theorem compactVariableItemVectorsTickInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryNat
      compactVariableItemVectorsInstructionEncodedType
      compactVariableItemVectorsTickInstruction := by
  let X := EncodedType.binaryNat
  have hTag : TMPolyTimeMap X EncodedType.bool (fun _ : Nat => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hPayload :
      TMPolyTimeMap X integerProgrammingBinaryStructuredEncodedType
        (fun _ : Nat => compactEmptyIntegerProgrammingInput) :=
    TMPolyTimeMap.const X integerProgrammingBinaryStructuredEncodedType
      compactEmptyIntegerProgrammingInput
  have hOut := TMPolyTimeMap.prod_mk hTag hPayload
  simpa [compactVariableItemVectorsTickInstruction,
    compactVariableItemVectorsInstructionEncodedType, X] using hOut

theorem compactVariableItemVectorsInstructions_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      compactVariableItemVectorsInstructionListEncodedType
      compactVariableItemVectorsInstructions := by
  let X := integerProgrammingBinaryStructuredEncodedType
  have hInit :
      TMPolyTimeMap X compactVariableItemVectorsInstructionEncodedType
        compactVariableItemVectorsInitInstruction := by
    simpa [X] using compactVariableItemVectorsInitInstruction_tm_polytime
  have hFuel :
      TMPolyTimeMap X (EncodedType.list EncodedType.binaryNat) compactTargetOnes := by
    simpa [X] using compactTargetOnes_tm_polytime
  have hTicks :
      TMPolyTimeMap X compactVariableItemVectorsInstructionListEncodedType
        (fun I : IntegerProgrammingInput =>
          (compactTargetOnes I).map compactVariableItemVectorsTickInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactVariableItemVectorsTickInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hFuel
    simpa [Function.comp, compactVariableItemVectorsInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactVariableItemVectorsInstructionEncodedType
          compactVariableItemVectorsInstructionListEncodedType)
        (fun I : IntegerProgrammingInput =>
          (compactVariableItemVectorsInitInstruction I,
            (compactTargetOnes I).map compactVariableItemVectorsTickInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hTicks
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons compactVariableItemVectorsInstructionEncodedType) hConsInput
  simpa [Function.comp, compactVariableItemVectorsInstructions,
    compactVariableItemVectorsInstructionListEncodedType, X] using hCons

theorem compactVariableItemVectorsInstruction_payload_inputSize_le
    (instr : compactVariableItemVectorsInstructionEncodedType.Carrier) :
    integerProgrammingBinaryStructuredEncodedType.inputSize instr.2 ≤
      compactVariableItemVectorsInstructionEncodedType.inputSize instr := by
  rcases instr with ⟨tag, I⟩
  simp [compactVariableItemVectorsInstructionEncodedType, EncodedType.inputSize_prod]

def compactVariableItemVectorsFoldInv
    (N : Nat) (acc : CompactVariableItemVectorsAcc) : Prop :=
  integerProgrammingBinaryStructuredEncodedType.inputSize acc.1 ≤ N + 20

theorem compactVariableItemVectorsInitAcc_bound
    (xs : List compactVariableItemVectorsInstructionEncodedType.Carrier) :
    compactVariableItemVectorsFoldInv
        (compactVariableItemVectorsInstructionListEncodedType.inputSize xs)
        compactVariableItemVectorsInitAcc ∧
      compactVariableItemVectorsAccEncodedType.inputSize compactVariableItemVectorsInitAcc ≤
        (Polynomial.C 30).eval
          (compactVariableItemVectorsInstructionListEncodedType.inputSize xs) := by
  constructor
  · have hEmpty := compactEmptyIntegerProgrammingInput_inputSize_le
    simpa [compactVariableItemVectorsFoldInv, compactVariableItemVectorsInitAcc] using
      hEmpty.trans (by omega)
  · have hReset :=
      compactVariableItemVectorsResetAcc_inputSize_le compactEmptyIntegerProgrammingInput
    have hEmpty := compactEmptyIntegerProgrammingInput_inputSize_le
    simpa [compactVariableItemVectorsInitAcc, Polynomial.eval] using hReset.trans (by omega)

theorem compactVariableItemVectorsStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactVariableItemVectorsAccEncodedType
        compactVariableItemVectorsInstructionEncodedType)
      compactVariableItemVectorsAccEncodedType
      compactVariableItemVectorsStep := by
  let Vec := EncodedType.list EncodedType.binaryNat
  let L := EncodedType.list Vec
  let Tail := EncodedType.prod EncodedType.binaryNat L
  let X := EncodedType.prod compactVariableItemVectorsAccEncodedType
    compactVariableItemVectorsInstructionEncodedType
  let A := compactVariableItemVectorsAccEncodedType
  have hAcc : TMPolyTimeMap X A
      (fun p : CompactVariableItemVectorsAcc ×
          compactVariableItemVectorsInstructionEncodedType.Carrier => p.1) := by
    simpa [X, A] using
      TMPolyTimeMap.fst compactVariableItemVectorsAccEncodedType
        compactVariableItemVectorsInstructionEncodedType
  have hInstr :
      TMPolyTimeMap X compactVariableItemVectorsInstructionEncodedType
        (fun p : CompactVariableItemVectorsAcc ×
          compactVariableItemVectorsInstructionEncodedType.Carrier => p.2) := by
    simpa [X, A] using
      TMPolyTimeMap.snd compactVariableItemVectorsAccEncodedType
        compactVariableItemVectorsInstructionEncodedType
  have hI : TMPolyTimeMap X integerProgrammingBinaryStructuredEncodedType
      (fun p : CompactVariableItemVectorsAcc ×
          compactVariableItemVectorsInstructionEncodedType.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst integerProgrammingBinaryStructuredEncodedType Tail
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, compactVariableItemVectorsAccEncodedType, Tail, X] using hComp
  have hTail : TMPolyTimeMap X Tail
      (fun p : CompactVariableItemVectorsAcc ×
          compactVariableItemVectorsInstructionEncodedType.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd integerProgrammingBinaryStructuredEncodedType Tail
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, compactVariableItemVectorsAccEncodedType, Tail, X] using hComp
  have hIdx : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactVariableItemVectorsAcc ×
          compactVariableItemVectorsInstructionEncodedType.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat L
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, Tail, L, X] using hComp
  have hOut : TMPolyTimeMap X L
      (fun p : CompactVariableItemVectorsAcc ×
          compactVariableItemVectorsInstructionEncodedType.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat L
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, Tail, L, X] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun p : CompactVariableItemVectorsAcc ×
          compactVariableItemVectorsInstructionEncodedType.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool integerProgrammingBinaryStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, compactVariableItemVectorsInstructionEncodedType, X] using hComp
  have hInstrI : TMPolyTimeMap X integerProgrammingBinaryStructuredEncodedType
      (fun p : CompactVariableItemVectorsAcc ×
          compactVariableItemVectorsInstructionEncodedType.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool integerProgrammingBinaryStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, compactVariableItemVectorsInstructionEncodedType, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.binaryNat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have hEmpty : TMPolyTimeMap X L (fun _ : X.Carrier => ([] : L.Carrier)) :=
    TMPolyTimeMap.const X L []
  have hFalseTail : TMPolyTimeMap X Tail
      (fun _ : X.Carrier => ((0 : Nat), ([] : List Vec.Carrier))) :=
    TMPolyTimeMap.prod_mk hZero hEmpty
  have hFalseBranch :
      TMPolyTimeMap X A
        (fun p : CompactVariableItemVectorsAcc ×
            compactVariableItemVectorsInstructionEncodedType.Carrier =>
          (p.2.2, ((0 : Nat), ([] : List Vec.Carrier)))) :=
    TMPolyTimeMap.prod_mk hInstrI hFalseTail
  have hTrueBool : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hFalseBool : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hTruePayload :
      TMPolyTimeMap X compactConstraintDigitsInitPayloadEncodedType
        (fun p : CompactVariableItemVectorsAcc ×
            compactVariableItemVectorsInstructionEncodedType.Carrier => (p.1.2.1, true)) :=
    TMPolyTimeMap.prod_mk hIdx hTrueBool
  have hFalsePayload :
      TMPolyTimeMap X compactConstraintDigitsInitPayloadEncodedType
        (fun p : CompactVariableItemVectorsAcc ×
            compactVariableItemVectorsInstructionEncodedType.Carrier => (p.1.2.1, false)) :=
    TMPolyTimeMap.prod_mk hIdx hFalseBool
  have hTrueInput :
      TMPolyTimeMap X compactVariableConstraintDigitsExecutableInputEncodedType
        (fun p : CompactVariableItemVectorsAcc ×
            compactVariableItemVectorsInstructionEncodedType.Carrier =>
          (p.1.1, (p.1.2.1, true))) :=
    TMPolyTimeMap.prod_mk hI hTruePayload
  have hFalseInput :
      TMPolyTimeMap X compactVariableConstraintDigitsExecutableInputEncodedType
        (fun p : CompactVariableItemVectorsAcc ×
            compactVariableItemVectorsInstructionEncodedType.Carrier =>
          (p.1.1, (p.1.2.1, false))) :=
    TMPolyTimeMap.prod_mk hI hFalsePayload
  have hTrueVec : TMPolyTimeMap X Vec
      (fun p : CompactVariableItemVectorsAcc ×
          compactVariableItemVectorsInstructionEncodedType.Carrier =>
        compactVariableItemDigitsExecutable p.1.1 p.1.2.1 true) := by
    have hComp := TMPolyTimeMap.comp compactVariableItemDigitsExecutable_tm_polytime hTrueInput
    simpa [Function.comp, Vec, X] using hComp
  have hFalseVec : TMPolyTimeMap X Vec
      (fun p : CompactVariableItemVectorsAcc ×
          compactVariableItemVectorsInstructionEncodedType.Carrier =>
        compactVariableItemDigitsExecutable p.1.1 p.1.2.1 false) := by
    have hComp := TMPolyTimeMap.comp compactVariableItemDigitsExecutable_tm_polytime hFalseInput
    simpa [Function.comp, Vec, X] using hComp
  have hFalseSingleton : TMPolyTimeMap X L
      (fun p : CompactVariableItemVectorsAcc ×
          compactVariableItemVectorsInstructionEncodedType.Carrier =>
        [compactVariableItemDigitsExecutable p.1.1 p.1.2.1 false]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton Vec) hFalseVec
    simpa [Function.comp, Vec, L, X] using hComp
  have hBothInput :
      TMPolyTimeMap X (EncodedType.prod Vec L)
        (fun p : CompactVariableItemVectorsAcc ×
            compactVariableItemVectorsInstructionEncodedType.Carrier =>
          (compactVariableItemDigitsExecutable p.1.1 p.1.2.1 true,
            [compactVariableItemDigitsExecutable p.1.1 p.1.2.1 false])) :=
    TMPolyTimeMap.prod_mk hTrueVec hFalseSingleton
  have hBoth : TMPolyTimeMap X L
      (fun p : CompactVariableItemVectorsAcc ×
          compactVariableItemVectorsInstructionEncodedType.Carrier =>
        [compactVariableItemDigitsExecutable p.1.1 p.1.2.1 true,
          compactVariableItemDigitsExecutable p.1.1 p.1.2.1 false]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons Vec) hBothInput
    simpa [Function.comp, Vec, L, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X (EncodedType.prod L L)
        (fun p : CompactVariableItemVectorsAcc ×
            compactVariableItemVectorsInstructionEncodedType.Carrier =>
          (p.1.2.2,
            [compactVariableItemDigitsExecutable p.1.1 p.1.2.1 true,
              compactVariableItemDigitsExecutable p.1.1 p.1.2.1 false])) :=
    TMPolyTimeMap.prod_mk hOut hBoth
  have hAppend : TMPolyTimeMap X L
      (fun p : CompactVariableItemVectorsAcc ×
          compactVariableItemVectorsInstructionEncodedType.Carrier =>
        p.1.2.2 ++
          [compactVariableItemDigitsExecutable p.1.1 p.1.2.1 true,
            compactVariableItemDigitsExecutable p.1.1 p.1.2.1 false]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append Vec) hAppendInput
    simpa [Function.comp, Vec, L, X] using hComp
  have hIdxSucc : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactVariableItemVectorsAcc ×
          compactVariableItemVectorsInstructionEncodedType.Carrier => p.1.2.1.succ) := by
    have hComp := TMPolyTimeMap.comp binaryNatSucc_tm_polytime hIdx
    simpa [Function.comp, X] using hComp
  have hTrueTail : TMPolyTimeMap X Tail
      (fun p : CompactVariableItemVectorsAcc ×
          compactVariableItemVectorsInstructionEncodedType.Carrier =>
        (p.1.2.1.succ,
          p.1.2.2 ++
            [compactVariableItemDigitsExecutable p.1.1 p.1.2.1 true,
              compactVariableItemDigitsExecutable p.1.1 p.1.2.1 false])) :=
    TMPolyTimeMap.prod_mk hIdxSucc hAppend
  have hTrueBranch :
      TMPolyTimeMap X A
        (fun p : CompactVariableItemVectorsAcc ×
            compactVariableItemVectorsInstructionEncodedType.Carrier =>
          (p.1.1,
            (p.1.2.1.succ,
              p.1.2.2 ++
                [compactVariableItemDigitsExecutable p.1.1 p.1.2.1 true,
                  compactVariableItemDigitsExecutable p.1.1 p.1.2.1 false]))) :=
    TMPolyTimeMap.prod_mk hI hTrueTail
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : CompactVariableItemVectorsAcc ×
            compactVariableItemVectorsInstructionEncodedType.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hDispatch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool ×
            (CompactVariableItemVectorsAcc ×
              compactVariableItemVectorsInstructionEncodedType.Carrier) =>
          match p.1 with
          | true =>
              (p.2.1.1,
                (p.2.1.2.1.succ,
                  p.2.1.2.2 ++
                    [compactVariableItemDigitsExecutable p.2.1.1 p.2.1.2.1 true,
                      compactVariableItemDigitsExecutable p.2.1.1 p.2.1.2.1 false]))
          | false => (p.2.2.2, ((0 : Nat), ([] : List Vec.Carrier)))) :=
    Clique.boolProduct_dispatch_tm_polytime X A
      (fFalse := fun p :
          CompactVariableItemVectorsAcc ×
            compactVariableItemVectorsInstructionEncodedType.Carrier =>
        (p.2.2, ((0 : Nat), ([] : List Vec.Carrier))))
      (fTrue := fun p :
          CompactVariableItemVectorsAcc ×
            compactVariableItemVectorsInstructionEncodedType.Carrier =>
        (p.1.1,
          (p.1.2.1.succ,
            p.1.2.2 ++
              [compactVariableItemDigitsExecutable p.1.1 p.1.2.1 true,
                compactVariableItemDigitsExecutable p.1.1 p.1.2.1 false])))
      hFalseBranch hTrueBranch
  have hComp := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  rcases instr with ⟨tag, payload⟩
  cases tag <;> rfl

theorem compactVariableItemVector_inputSize_le_of_bound
    {I : IntegerProgrammingInput} {i : Nat} {b : Bool} {N : Nat}
    (hI :
      integerProgrammingBinaryStructuredEncodedType.inputSize I ≤ N + 20) :
    (EncodedType.list EncodedType.binaryNat).inputSize
        (compactVariableItemDigitsExecutable I i b) ≤
      N * N + 50 * N + 600 := by
  let S := integerProgrammingBinaryStructuredEncodedType.inputSize I
  have hItem := compactVariableItemDigitsExecutable_inputSize_le I i b
  have hSq : S * S ≤ (N + 20) * (N + 20) := by
    exact Nat.mul_le_mul hI hI
  change (EncodedType.list EncodedType.binaryNat).inputSize
      (compactVariableItemDigitsExecutable I i b) ≤ N * N + 50 * N + 600
  nlinarith [hItem, hSq, hI]

theorem compactVariableItemVectorsStep_growth
    (source : List compactVariableItemVectorsInstructionEncodedType.Carrier)
    (acc : CompactVariableItemVectorsAcc)
    (instr : compactVariableItemVectorsInstructionEncodedType.Carrier)
    (hInv :
      compactVariableItemVectorsFoldInv
        (compactVariableItemVectorsInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      compactVariableItemVectorsInstructionEncodedType.inputSize instr ≤
        compactVariableItemVectorsInstructionListEncodedType.inputSize source) :
    compactVariableItemVectorsFoldInv
        (compactVariableItemVectorsInstructionListEncodedType.inputSize source)
        (compactVariableItemVectorsStep (acc, instr)) ∧
      compactVariableItemVectorsAccEncodedType.inputSize
          (compactVariableItemVectorsStep (acc, instr)) ≤
        compactVariableItemVectorsAccEncodedType.inputSize acc +
          ((Polynomial.C 4 * Polynomial.X * Polynomial.X +
              Polynomial.C 200 * Polynomial.X + Polynomial.C 2000).eval
            (compactVariableItemVectorsInstructionListEncodedType.inputSize source)) := by
  let N := compactVariableItemVectorsInstructionListEncodedType.inputSize source
  rcases acc with ⟨I, idx, out⟩
  rcases instr with ⟨tag, payloadI⟩
  have hPayloadI :
      integerProgrammingBinaryStructuredEncodedType.inputSize payloadI ≤ N := by
    exact (compactVariableItemVectorsInstruction_payload_inputSize_le
      (tag, payloadI)).trans hInstr
  have hIdxSucc := binaryNatAdd_inputSize_le idx 1
  have hOne : EncodedType.binaryNat.inputSize (1 : Nat) = 1 := by
    simp [EncodedType.inputSize, EncodedType.binaryNat]
  have hIdxSuccSmall :
      EncodedType.binaryNat.inputSize idx.succ ≤
        EncodedType.binaryNat.inputSize idx + 2 := by
    simpa [Nat.succ_eq_add_one, hOne] using hIdxSucc
  cases tag
  · constructor
    · exact hPayloadI.trans (by omega)
    · change compactVariableItemVectorsAccEncodedType.inputSize
          (payloadI, ((0 : Nat), ([] : List (List Nat)))) ≤
        compactVariableItemVectorsAccEncodedType.inputSize (I, idx, out) +
          ((Polynomial.C 4 * Polynomial.X * Polynomial.X +
              Polynomial.C 200 * Polynomial.X + Polynomial.C 2000).eval N)
      have hNew :
          compactVariableItemVectorsAccEncodedType.inputSize
              (payloadI, ((0 : Nat), ([] : List (List Nat)))) ≤ N + 5 := by
        have hReset := compactVariableItemVectorsResetAcc_inputSize_le payloadI
        exact hReset.trans (by omega)
      have hBudget :
          N + 5 ≤ compactVariableItemVectorsAccEncodedType.inputSize (I, idx, out) +
            ((Polynomial.C 4 * Polynomial.X * Polynomial.X +
                Polynomial.C 200 * Polynomial.X + Polynomial.C 2000).eval N) := by
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        omega
      exact hNew.trans hBudget
  · have hTrueSize :=
      compactVariableItemVector_inputSize_le_of_bound
        (I := I) (i := idx) (b := true) (N := N) hInv
    have hFalseSize :=
      compactVariableItemVector_inputSize_le_of_bound
        (I := I) (i := idx) (b := false) (N := N) hInv
    have hAppend :
        (EncodedType.list (EncodedType.list EncodedType.binaryNat)).inputSize
            (out ++ [compactVariableItemDigitsExecutable I idx true,
              compactVariableItemDigitsExecutable I idx false]) =
          (EncodedType.list (EncodedType.list EncodedType.binaryNat)).inputSize out +
            (EncodedType.list EncodedType.binaryNat).inputSize
              (compactVariableItemDigitsExecutable I idx true) + 1 +
            ((EncodedType.list EncodedType.binaryNat).inputSize
              (compactVariableItemDigitsExecutable I idx false) + 1) := by
      have hRaw := encodedList_inputSize_append
        (EncodedType.list EncodedType.binaryNat) out
        [compactVariableItemDigitsExecutable I idx true,
          compactVariableItemDigitsExecutable I idx false]
      simpa [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_nil,
        Nat.add_assoc] using hRaw
    constructor
    · exact hInv
    · simp [compactVariableItemVectorsStep, compactVariableItemVectorsAccEncodedType,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        EncodedType.inputSize_prod] at hAppend ⊢
      nlinarith

theorem compactVariableItemVectorsFold_tm_polytime :
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

theorem compactVariableItemDigitVectorsFromInstructions_tm_polytime :
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
  have hTailComp := TMPolyTimeMap.comp hTail compactVariableItemVectorsFold_tm_polytime
  have hOutComp := TMPolyTimeMap.comp hOut hTailComp
  simpa [Function.comp, compactVariableItemDigitVectorsFromInstructions, Tail, L, Vec]
    using hOutComp

theorem compactVariableItemDigitVectorsExecutable_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      compactVariableItemDigitVectorsExecutable := by
  have hComp := TMPolyTimeMap.comp
    compactVariableItemDigitVectorsFromInstructions_tm_polytime
    compactVariableItemVectorsInstructions_tm_polytime
  simpa [Function.comp, compactVariableItemDigitVectorsExecutable] using hComp

theorem compactVariableItemDigitVectors_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      compactVariableItemDigitVectors := by
  convert compactVariableItemDigitVectorsExecutable_tm_polytime using 1
  funext I
  exact (compactVariableItemDigitVectorsExecutable_eq I).symm

end Knapsack
end Karp21
end ComplexityReduction
