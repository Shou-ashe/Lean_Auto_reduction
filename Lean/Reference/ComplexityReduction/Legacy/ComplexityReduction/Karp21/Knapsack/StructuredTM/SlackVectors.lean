import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.SlackDigits

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

/-!
Direct generation of compact slack-item digit vectors.

This file first builds the vectors for one constraint row by folding over its
binary slack powers.  The outer fold over all constraints is layered on top of
that row generator.
-/

def compactSlackRowVectorsAccEncodedType : EncodedType :=
  EncodedType.prod integerProgrammingBinaryStructuredEncodedType
    (EncodedType.prod EncodedType.binaryNat
      (EncodedType.list (EncodedType.list EncodedType.binaryNat)))

abbrev CompactSlackRowVectorsAcc :=
  IntegerProgrammingInput × Nat × List (List Nat)

def compactSlackRowVectorsInitAcc : CompactSlackRowVectorsAcc :=
  (compactEmptyIntegerProgrammingInput, (0, []))

def compactSlackRowVectorsInstructionPayloadEncodedType : EncodedType :=
  EncodedType.prod integerProgrammingBinaryStructuredEncodedType
    (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)

def compactSlackRowVectorsInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool compactSlackRowVectorsInstructionPayloadEncodedType

def compactSlackRowVectorsInstructionListEncodedType : EncodedType :=
  EncodedType.list compactSlackRowVectorsInstructionEncodedType

def compactSlackRowVectorsInputEncodedType : EncodedType :=
  EncodedType.prod integerProgrammingBinaryStructuredEncodedType
    (EncodedType.prod EncodedType.binaryNat constraintBinaryStructuredEncodedType)

def compactSlackRowVectorsInitInstruction (I : IntegerProgrammingInput) (rowIndex : Nat) :
    compactSlackRowVectorsInstructionEncodedType.Carrier :=
  (false, (I, (rowIndex, (0 : Nat))))

def compactSlackRowVectorsTickInstruction (power : Nat) :
    compactSlackRowVectorsInstructionEncodedType.Carrier :=
  (true, (compactEmptyIntegerProgrammingInput, ((0 : Nat), power)))

def compactSlackRowVectorsInstructions
    (p : IntegerProgrammingInput × Nat × (List Int × Int)) :
    List compactSlackRowVectorsInstructionEncodedType.Carrier :=
  compactSlackRowVectorsInitInstruction p.1 p.2.1 ::
    (compactSlackPowers p.2.2).map compactSlackRowVectorsTickInstruction

def compactSlackRowVectorsStep
    (p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier) :
    CompactSlackRowVectorsAcc :=
  match p.2.1 with
  | false =>
      let payload := p.2.2
      (payload.1, (payload.2.1, []))
  | true =>
      let power := p.2.2.2.2
      let digits := compactSlackItemDigitsExecutable p.1.1 p.1.2.1 power
      (p.1.1, (p.1.2.1, p.1.2.2 ++ [digits]))

def compactSlackRowVectorsFromInstructions
    (xs : List compactSlackRowVectorsInstructionEncodedType.Carrier) : List (List Nat) :=
  (xs.foldl (fun acc instr => compactSlackRowVectorsStep (acc, instr))
    compactSlackRowVectorsInitAcc).2.2

def compactSlackItemDigitsForConstraintExecutable
    (I : IntegerProgrammingInput) (rowIndex : Nat) (constraint : List Int × Int) :
    List (List Nat) :=
  compactSlackRowVectorsFromInstructions
    (compactSlackRowVectorsInstructions (I, (rowIndex, constraint)))

theorem compactSlackRowVectorsTick_fold
    (powers : List Nat) (I : IntegerProgrammingInput) (rowIndex : Nat)
    (out : List (List Nat)) :
    ((powers.map compactSlackRowVectorsTickInstruction).foldl
        (fun acc instr => compactSlackRowVectorsStep (acc, instr))
        (I, (rowIndex, out))).2.2 =
      out ++ powers.map fun power =>
        compactSlackItemDigitsExecutable I rowIndex power := by
  induction powers generalizing out with
  | nil =>
      simp [compactSlackRowVectorsStep]
  | cons power powers ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        (((powers.map compactSlackRowVectorsTickInstruction).foldl
            (fun acc instr => compactSlackRowVectorsStep (acc, instr))
            (I, (rowIndex,
              out ++ [compactSlackItemDigitsExecutable I rowIndex power]))).2.2) =
          out ++ (power :: powers).map fun power =>
            compactSlackItemDigitsExecutable I rowIndex power
      rw [ih (out ++ [compactSlackItemDigitsExecutable I rowIndex power])]
      simp [List.append_assoc]

theorem compactSlackItemDigitsForConstraintExecutable_eq
    (I : IntegerProgrammingInput) (rowIndex : Nat) (constraint : List Int × Int) :
    compactSlackItemDigitsForConstraintExecutable I rowIndex constraint =
      compactSlackItemDigitsForConstraint I rowIndex constraint := by
  rw [compactSlackItemDigitsForConstraintExecutable, compactSlackRowVectorsFromInstructions,
    compactSlackRowVectorsInstructions, compactSlackRowVectorsInitInstruction]
  change
    (((compactSlackPowers constraint).map compactSlackRowVectorsTickInstruction).foldl
        (fun acc instr => compactSlackRowVectorsStep (acc, instr))
        (I, (rowIndex, ([] : List (List Nat))))).2.2 =
      compactSlackItemDigitsForConstraint I rowIndex constraint
  rw [compactSlackRowVectorsTick_fold]
  simp [compactSlackItemDigitsForConstraint, compactSlackItemDigitsExecutable_eq]

theorem compactSlackItemDigits_digit_inputSize_le
    {I : IntegerProgrammingInput} {rowIndex power digit : Nat}
    (hdigit : digit ∈ compactSlackItemDigits I rowIndex power) :
    EncodedType.binaryNat.inputSize digit ≤
      EncodedType.binaryNat.inputSize power + 1 := by
  rw [compactSlackItemDigits] at hdigit
  rcases List.mem_append.mp hdigit with hPrefix | hTail
  · have hZero : digit = 0 := by
      simpa using (List.mem_replicate.mp hPrefix).2
    subst digit
    simp [EncodedType.inputSize, EncodedType.binaryNat]
  · rw [List.mem_map] at hTail
    rcases hTail with ⟨j, _hj, rfl⟩
    by_cases h : j = rowIndex
    · simp [h]
    · simp [h, EncodedType.inputSize, EncodedType.binaryNat]

theorem compactSlackItemDigitsExecutable_inputSize_le
    (I : IntegerProgrammingInput) (rowIndex power : Nat) :
    (EncodedType.list EncodedType.binaryNat).inputSize
        (compactSlackItemDigitsExecutable I rowIndex power) ≤
      2 * integerProgrammingBinaryStructuredEncodedType.inputSize I *
        (EncodedType.binaryNat.inputSize power + 2) := by
  rw [compactSlackItemDigitsExecutable_eq]
  have hList :=
    Clique.encodedList_inputSize_le_length_mul_bound EncodedType.binaryNat
      (compactSlackItemDigits I rowIndex power)
      (EncodedType.binaryNat.inputSize power + 1)
      (by
        intro digit hdigit
        exact compactSlackItemDigits_digit_inputSize_le hdigit)
  have hLen := compactSlackItemDigits_length I rowIndex power
  have hCount := compactDigitCount_le_two_mul_binaryStructured_inputSize I
  calc
    (EncodedType.list EncodedType.binaryNat).inputSize
        (compactSlackItemDigits I rowIndex power)
        ≤ (compactSlackItemDigits I rowIndex power).length *
            (EncodedType.binaryNat.inputSize power + 2) := by
          simpa [Nat.add_assoc] using hList
    _ = compactDigitCount I * (EncodedType.binaryNat.inputSize power + 2) := by
          rw [hLen]
    _ ≤ 2 * integerProgrammingBinaryStructuredEncodedType.inputSize I *
          (EncodedType.binaryNat.inputSize power + 2) := by
          exact Nat.mul_le_mul_right _ hCount

theorem compactSlackRowVectorsTickInstruction_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryNat
      compactSlackRowVectorsInstructionEncodedType
      compactSlackRowVectorsTickInstruction := by
  let X := EncodedType.binaryNat
  have hTag : TMPolyTimeMap X EncodedType.bool (fun _ : Nat => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hEmptyI :
      TMPolyTimeMap X integerProgrammingBinaryStructuredEncodedType
        (fun _ : Nat => compactEmptyIntegerProgrammingInput) :=
    TMPolyTimeMap.const X integerProgrammingBinaryStructuredEncodedType
      compactEmptyIntegerProgrammingInput
  have hZero : TMPolyTimeMap X EncodedType.binaryNat (fun _ : Nat => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun power : Nat => ((0 : Nat), power)) :=
    TMPolyTimeMap.prod_mk hZero (TMPolyTimeMap.id X)
  have hPayload :
      TMPolyTimeMap X compactSlackRowVectorsInstructionPayloadEncodedType
        (fun power : Nat => (compactEmptyIntegerProgrammingInput, ((0 : Nat), power))) :=
    TMPolyTimeMap.prod_mk hEmptyI hTail
  have hOut := TMPolyTimeMap.prod_mk hTag hPayload
  simpa [compactSlackRowVectorsTickInstruction,
    compactSlackRowVectorsInstructionEncodedType, X] using hOut

theorem compactSlackRowVectorsInstructions_tm_polytime :
    TMPolyTimeMap
      compactSlackRowVectorsInputEncodedType
      compactSlackRowVectorsInstructionListEncodedType
      compactSlackRowVectorsInstructions := by
  let X := compactSlackRowVectorsInputEncodedType
  have hI : TMPolyTimeMap X integerProgrammingBinaryStructuredEncodedType
      (fun p : IntegerProgrammingInput × Nat × (List Int × Int) => p.1) := by
    simpa [X, compactSlackRowVectorsInputEncodedType] using
      TMPolyTimeMap.fst integerProgrammingBinaryStructuredEncodedType
        (EncodedType.prod EncodedType.binaryNat constraintBinaryStructuredEncodedType)
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat constraintBinaryStructuredEncodedType)
        (fun p : IntegerProgrammingInput × Nat × (List Int × Int) => p.2) := by
    simpa [X, compactSlackRowVectorsInputEncodedType] using
      TMPolyTimeMap.snd integerProgrammingBinaryStructuredEncodedType
        (EncodedType.prod EncodedType.binaryNat constraintBinaryStructuredEncodedType)
  have hRow : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : IntegerProgrammingInput × Nat × (List Int × Int) => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat constraintBinaryStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hConstraint : TMPolyTimeMap X constraintBinaryStructuredEncodedType
      (fun p : IntegerProgrammingInput × Nat × (List Int × Int) => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat constraintBinaryStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hZero : TMPolyTimeMap X EncodedType.binaryNat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have hInitTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : IntegerProgrammingInput × Nat × (List Int × Int) =>
          (p.2.1, (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hRow hZero
  have hInitPayload :
      TMPolyTimeMap X compactSlackRowVectorsInstructionPayloadEncodedType
        (fun p : IntegerProgrammingInput × Nat × (List Int × Int) =>
          (p.1, (p.2.1, (0 : Nat)))) :=
    TMPolyTimeMap.prod_mk hI hInitTail
  have hInit :
      TMPolyTimeMap X compactSlackRowVectorsInstructionEncodedType
        (fun p : IntegerProgrammingInput × Nat × (List Int × Int) =>
          compactSlackRowVectorsInitInstruction p.1 p.2.1) := by
    have hOut := TMPolyTimeMap.prod_mk hFalse hInitPayload
    simpa [compactSlackRowVectorsInitInstruction,
      compactSlackRowVectorsInstructionEncodedType, X] using hOut
  have hPowers :
      TMPolyTimeMap X (EncodedType.list EncodedType.binaryNat)
        (fun p : IntegerProgrammingInput × Nat × (List Int × Int) =>
          compactSlackPowers p.2.2) := by
    have hComp := TMPolyTimeMap.comp compactSlackPowers_tm_polytime hConstraint
    simpa [Function.comp, X] using hComp
  have hTicks :
      TMPolyTimeMap X compactSlackRowVectorsInstructionListEncodedType
        (fun p : IntegerProgrammingInput × Nat × (List Int × Int) =>
          (compactSlackPowers p.2.2).map compactSlackRowVectorsTickInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactSlackRowVectorsTickInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hPowers
    simpa [Function.comp, compactSlackRowVectorsInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactSlackRowVectorsInstructionEncodedType
          compactSlackRowVectorsInstructionListEncodedType)
        (fun p : IntegerProgrammingInput × Nat × (List Int × Int) =>
          (compactSlackRowVectorsInitInstruction p.1 p.2.1,
            (compactSlackPowers p.2.2).map compactSlackRowVectorsTickInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hTicks
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons compactSlackRowVectorsInstructionEncodedType) hConsInput
  simpa [Function.comp, compactSlackRowVectorsInstructions,
    compactSlackRowVectorsInstructionListEncodedType, X] using hCons

theorem compactSlackRowVectorsStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactSlackRowVectorsAccEncodedType
        compactSlackRowVectorsInstructionEncodedType)
      compactSlackRowVectorsAccEncodedType
      compactSlackRowVectorsStep := by
  let Vec := EncodedType.list EncodedType.binaryNat
  let L := EncodedType.list Vec
  let Tail := EncodedType.prod EncodedType.binaryNat L
  let PayloadTail := EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat
  let X := EncodedType.prod compactSlackRowVectorsAccEncodedType
    compactSlackRowVectorsInstructionEncodedType
  let A := compactSlackRowVectorsAccEncodedType
  have hAcc : TMPolyTimeMap X A
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        p.1) := by
    simpa [X, A] using
      TMPolyTimeMap.fst compactSlackRowVectorsAccEncodedType
        compactSlackRowVectorsInstructionEncodedType
  have hInstr : TMPolyTimeMap X compactSlackRowVectorsInstructionEncodedType
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        p.2) := by
    simpa [X, A] using
      TMPolyTimeMap.snd compactSlackRowVectorsAccEncodedType
        compactSlackRowVectorsInstructionEncodedType
  have hAccI : TMPolyTimeMap X integerProgrammingBinaryStructuredEncodedType
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        p.1.1) := by
    have hFst := TMPolyTimeMap.fst integerProgrammingBinaryStructuredEncodedType Tail
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, compactSlackRowVectorsAccEncodedType, Tail, X] using hComp
  have hAccTail : TMPolyTimeMap X Tail
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        p.1.2) := by
    have hSnd := TMPolyTimeMap.snd integerProgrammingBinaryStructuredEncodedType Tail
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, compactSlackRowVectorsAccEncodedType, Tail, X] using hComp
  have hAccRow : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat L
    have hComp := TMPolyTimeMap.comp hFst hAccTail
    simpa [Function.comp, Tail, L, X] using hComp
  have hAccOut : TMPolyTimeMap X L
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat L
    have hComp := TMPolyTimeMap.comp hSnd hAccTail
    simpa [Function.comp, Tail, L, X] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool
      compactSlackRowVectorsInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, compactSlackRowVectorsInstructionEncodedType, X] using hComp
  have hPayload : TMPolyTimeMap X compactSlackRowVectorsInstructionPayloadEncodedType
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      compactSlackRowVectorsInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, compactSlackRowVectorsInstructionEncodedType, X] using hComp
  have hPayloadI : TMPolyTimeMap X integerProgrammingBinaryStructuredEncodedType
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst integerProgrammingBinaryStructuredEncodedType PayloadTail
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, compactSlackRowVectorsInstructionPayloadEncodedType,
      PayloadTail, X] using hComp
  have hPayloadTail : TMPolyTimeMap X PayloadTail
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd integerProgrammingBinaryStructuredEncodedType PayloadTail
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, compactSlackRowVectorsInstructionPayloadEncodedType,
      PayloadTail, X] using hComp
  have hPayloadRow : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        p.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hPayloadTail
    simpa [Function.comp, PayloadTail, X] using hComp
  have hPayloadPower : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        p.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hSnd hPayloadTail
    simpa [Function.comp, PayloadTail, X] using hComp
  have hEmpty : TMPolyTimeMap X L (fun _ : X.Carrier => ([] : List (List Nat))) :=
    TMPolyTimeMap.const X L []
  have hFalseTail : TMPolyTimeMap X Tail
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        (p.2.2.2.1, ([] : List (List Nat)))) :=
    TMPolyTimeMap.prod_mk hPayloadRow hEmpty
  have hFalseBranch : TMPolyTimeMap X A
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        (p.2.2.1, (p.2.2.2.1, ([] : List (List Nat))))) :=
    TMPolyTimeMap.prod_mk hPayloadI hFalseTail
  have hItemInput :
      TMPolyTimeMap X compactSlackItemDigitsExecutableInputEncodedType
        (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
          (p.1.1, (p.1.2.1, p.2.2.2.2))) := by
    have hRowPower :
        TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
          (fun p : CompactSlackRowVectorsAcc ×
              compactSlackRowVectorsInstructionEncodedType.Carrier =>
            (p.1.2.1, p.2.2.2.2)) :=
      TMPolyTimeMap.prod_mk hAccRow hPayloadPower
    exact TMPolyTimeMap.prod_mk hAccI hRowPower
  have hItem : TMPolyTimeMap X Vec
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        compactSlackItemDigitsExecutable p.1.1 p.1.2.1 p.2.2.2.2) := by
    have hComp := TMPolyTimeMap.comp compactSlackItemDigitsExecutable_tm_polytime hItemInput
    simpa [Function.comp, X, Vec] using hComp
  have hSingleton : TMPolyTimeMap X L
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        [compactSlackItemDigitsExecutable p.1.1 p.1.2.1 p.2.2.2.2]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton Vec) hItem
    simpa [Function.comp, L, Vec, X] using hComp
  have hAppendInput : TMPolyTimeMap X (EncodedType.prod L L)
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        (p.1.2.2,
          [compactSlackItemDigitsExecutable p.1.1 p.1.2.1 p.2.2.2.2])) :=
    TMPolyTimeMap.prod_mk hAccOut hSingleton
  have hAppend : TMPolyTimeMap X L
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        p.1.2.2 ++
          [compactSlackItemDigitsExecutable p.1.1 p.1.2.1 p.2.2.2.2]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append Vec) hAppendInput
    simpa [Function.comp, L, Vec, X] using hComp
  have hTrueTail : TMPolyTimeMap X Tail
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        (p.1.2.1,
          p.1.2.2 ++
            [compactSlackItemDigitsExecutable p.1.1 p.1.2.1 p.2.2.2.2])) :=
    TMPolyTimeMap.prod_mk hAccRow hAppend
  have hTrueBranch : TMPolyTimeMap X A
      (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
        (p.1.1,
          (p.1.2.1,
            p.1.2.2 ++
              [compactSlackItemDigitsExecutable p.1.1 p.1.2.1 p.2.2.2.2]))) :=
    TMPolyTimeMap.prod_mk hAccI hTrueTail
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier =>
          (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hDispatch : TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
      (fun p : Bool ×
          (CompactSlackRowVectorsAcc × compactSlackRowVectorsInstructionEncodedType.Carrier) =>
        match p.1 with
        | true =>
            (p.2.1.1,
              (p.2.1.2.1,
                p.2.1.2.2 ++
                  [compactSlackItemDigitsExecutable p.2.1.1 p.2.1.2.1 p.2.2.2.2.2]))
        | false => (p.2.2.2.1, (p.2.2.2.2.1, ([] : List (List Nat))))) :=
    Clique.boolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : CompactSlackRowVectorsAcc ×
          compactSlackRowVectorsInstructionEncodedType.Carrier =>
        (p.2.2.1, (p.2.2.2.1, ([] : List (List Nat)))))
      (fTrue := fun p : CompactSlackRowVectorsAcc ×
          compactSlackRowVectorsInstructionEncodedType.Carrier =>
        (p.1.1,
          (p.1.2.1,
            p.1.2.2 ++
              [compactSlackItemDigitsExecutable p.1.1 p.1.2.1 p.2.2.2.2])))
      hFalseBranch hTrueBranch
  have hComp := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  rcases instr with ⟨tag, payload⟩
  cases tag <;> rfl

theorem compactSlackRowVectorsInstruction_payload_inputSize_le
    (instr : compactSlackRowVectorsInstructionEncodedType.Carrier) :
    compactSlackRowVectorsInstructionPayloadEncodedType.inputSize instr.2 ≤
      compactSlackRowVectorsInstructionEncodedType.inputSize instr := by
  rcases instr with ⟨tag, payload⟩
  simp [compactSlackRowVectorsInstructionEncodedType, EncodedType.inputSize_prod]

theorem compactSlackRowVectorsResetAcc_inputSize_le
    (I : IntegerProgrammingInput) (rowIndex power : Nat) :
    compactSlackRowVectorsAccEncodedType.inputSize
        (I, (rowIndex, ([] : List (List Nat)))) ≤
      compactSlackRowVectorsInstructionPayloadEncodedType.inputSize
        (I, (rowIndex, power)) := by
  unfold compactSlackRowVectorsAccEncodedType
    compactSlackRowVectorsInstructionPayloadEncodedType
  simp [EncodedType.prod, EncodedType.inputSize, EncodedType.binaryNat, EncodedType.list]

def compactSlackRowVectorsFoldInv
    (N : Nat) (acc : CompactSlackRowVectorsAcc) : Prop :=
  integerProgrammingBinaryStructuredEncodedType.inputSize acc.1 ≤ N + 20 ∧
    EncodedType.binaryNat.inputSize acc.2.1 ≤ N + 20

theorem compactSlackRowVectorsInitAcc_bound
    (xs : List compactSlackRowVectorsInstructionEncodedType.Carrier) :
    compactSlackRowVectorsFoldInv
        (compactSlackRowVectorsInstructionListEncodedType.inputSize xs)
        compactSlackRowVectorsInitAcc ∧
      compactSlackRowVectorsAccEncodedType.inputSize compactSlackRowVectorsInitAcc ≤
        (Polynomial.C 40).eval
          (compactSlackRowVectorsInstructionListEncodedType.inputSize xs) := by
  constructor
  · constructor
    · have hEmpty := compactEmptyIntegerProgrammingInput_inputSize_le
      simpa [compactSlackRowVectorsInitAcc] using
        hEmpty.trans (by omega)
    · simp [compactSlackRowVectorsInitAcc, EncodedType.inputSize, EncodedType.binaryNat]
  · have hReset :=
      compactSlackRowVectorsResetAcc_inputSize_le compactEmptyIntegerProgrammingInput 0 0
    have hEmpty := compactEmptyIntegerProgrammingInput_inputSize_le
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
      omega
    simpa [compactSlackRowVectorsInitAcc, Polynomial.eval] using hReset.trans hPayload

theorem compactSlackRowVector_inputSize_le_of_bound
    {I : IntegerProgrammingInput} {rowIndex power N : Nat}
    (hI : integerProgrammingBinaryStructuredEncodedType.inputSize I ≤ N + 20)
    (hPower : EncodedType.binaryNat.inputSize power ≤ N) :
    (EncodedType.list EncodedType.binaryNat).inputSize
        (compactSlackItemDigitsExecutable I rowIndex power) ≤
      4 * N * N + 100 * N + 1000 := by
  let S := integerProgrammingBinaryStructuredEncodedType.inputSize I
  let P := EncodedType.binaryNat.inputSize power
  have hItem := compactSlackItemDigitsExecutable_inputSize_le I rowIndex power
  have hS : 2 * S ≤ 2 * (N + 20) := Nat.mul_le_mul_left 2 hI
  have hP : P + 2 ≤ N + 2 := by
    omega
  have hMul : 2 * S * (P + 2) ≤ 2 * (N + 20) * (N + 2) :=
    Nat.mul_le_mul hS hP
  change (EncodedType.list EncodedType.binaryNat).inputSize
      (compactSlackItemDigitsExecutable I rowIndex power) ≤
    4 * N * N + 100 * N + 1000
  nlinarith [hItem, hMul]

theorem constraint_row_length_le_constraint_inputSize
    (constraint : List Int × Int) :
    constraint.1.length ≤ constraintBinaryStructuredEncodedType.inputSize constraint := by
  have hList := encodedList_length_le_inputSize EncodedType.binaryInt constraint.1
  exact hList.trans (constraint_row_binaryStructured_inputSize_le_constraint constraint)

theorem coefficient_binaryInt_inputSize_le_constraint
    {constraint : List Int × Int} {z : Int} (hz : z ∈ constraint.1) :
    EncodedType.binaryInt.inputSize z ≤
      constraintBinaryStructuredEncodedType.inputSize constraint := by
  have hCoeff := encodedList_element_inputSize_le EncodedType.binaryInt hz
  exact hCoeff.trans (constraint_row_binaryStructured_inputSize_le_constraint constraint)

theorem intNegativePart_le_two_pow_constraint
    {constraint : List Int × Int} {z : Int} (hz : z ∈ constraint.1) :
    intNegativePart z ≤ 2 ^ constraintBinaryStructuredEncodedType.inputSize constraint := by
  have hSize := coefficient_binaryInt_inputSize_le_constraint hz
  exact (intNegativePart_le_two_pow_binaryInt_inputSize z).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) hSize)

theorem constraint_bound_positivePart_le_two_pow_constraint
    (constraint : List Int × Int) :
    intPositivePart constraint.2 ≤
      2 ^ constraintBinaryStructuredEncodedType.inputSize constraint := by
  have hSize := constraint_bound_binaryInt_inputSize_le_constraint constraint
  exact (intPositivePart_le_two_pow_binaryInt_inputSize constraint.2).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) hSize)

theorem rowNegativeShift_le_constraint_mul_two_pow_constraint
    (constraint : List Int × Int) :
    rowNegativeShift constraint.1 ≤
      constraintBinaryStructuredEncodedType.inputSize constraint *
        2 ^ constraintBinaryStructuredEncodedType.inputSize constraint := by
  have hrow :
      ∀ z ∈ constraint.1,
        intNegativePart z ≤ 2 ^ constraintBinaryStructuredEncodedType.inputSize constraint := by
    intro z hz
    exact intNegativePart_le_two_pow_constraint hz
  have hShift := rowNegativeShift_le_length_mul_bound hrow
  have hLength := constraint_row_length_le_constraint_inputSize constraint
  exact hShift.trans (Nat.mul_le_mul_right _ hLength)

theorem compactConstraintBound_lt_two_pow_two_mul_constraint_add_two
    (constraint : List Int × Int) :
    compactConstraintBound constraint <
      2 ^ (2 * constraintBinaryStructuredEncodedType.inputSize constraint + 2) := by
  let S := constraintBinaryStructuredEncodedType.inputSize constraint
  have hPos := constraint_bound_positivePart_le_two_pow_constraint constraint
  have hShift := rowNegativeShift_le_constraint_mul_two_pow_constraint constraint
  have hBound := compactConstraintBound_le_posPart_add_shift constraint
  have hLe : compactConstraintBound constraint ≤ (S + 1) * 2 ^ S := by
    calc
      compactConstraintBound constraint
          ≤ intPositivePart constraint.2 + rowNegativeShift constraint.1 := hBound
      _ ≤ 2 ^ S + S * 2 ^ S := by
            simpa [S] using Nat.add_le_add hPos hShift
      _ = (S + 1) * 2 ^ S := by
            rw [Nat.add_mul, one_mul, Nat.add_comm]
  have hSucc : S + 1 ≤ 2 ^ (S + 1) := nat_succ_le_two_pow_succ S
  have hMul : (S + 1) * 2 ^ S ≤ 2 ^ (S + 1) * 2 ^ S :=
    Nat.mul_le_mul_right (2 ^ S) hSucc
  have hPowEq : 2 ^ (S + 1) * 2 ^ S = 2 ^ (2 * S + 1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hPowLt : 2 ^ (2 * S + 1) < 2 ^ (2 * S + 2) := by
    apply Nat.pow_lt_pow_right (by decide : 1 < 2)
    omega
  exact lt_of_le_of_lt (hLe.trans (hMul.trans (le_of_eq hPowEq))) hPowLt

theorem compactSlackBitCount_le_two_mul_constraint_inputSize_add_two
    (constraint : List Int × Int) :
    compactSlackBitCount constraint ≤
      2 * constraintBinaryStructuredEncodedType.inputSize constraint + 2 := by
  unfold compactSlackBitCount
  exact (Nat.digits_length_le_iff (by decide : 1 < 2)
    (compactConstraintBound constraint)).2
      (compactConstraintBound_lt_two_pow_two_mul_constraint_add_two constraint)

theorem compactSlackPowers_inputSize_le_constraint
    {constraint : List Int × Int} {power : Nat}
    (hpower : power ∈ compactSlackPowers constraint) :
    EncodedType.binaryNat.inputSize power ≤
      2 * constraintBinaryStructuredEncodedType.inputSize constraint + 2 := by
  have hlt : power < 2 ^ compactSlackBitCount constraint := by
    simpa [compactSlackPowers] using compactBinaryPowers_entry_lt_two_pow_length hpower
  have hBits := compactSlackBitCount_le_two_mul_constraint_inputSize_add_two constraint
  have hlt' :
      power < 2 ^ (2 * constraintBinaryStructuredEncodedType.inputSize constraint + 2) :=
    lt_of_lt_of_le hlt (pow_two_le_pow_two_of_le hBits)
  exact binaryNat_inputSize_le_of_lt_two_pow hlt'

theorem compactSlackItemDigitsForConstraintExecutable_inputSize_le_of_bound
    {I : IntegerProgrammingInput} {rowIndex : Nat} {constraint : List Int × Int} {N : Nat}
    (hI : integerProgrammingBinaryStructuredEncodedType.inputSize I ≤ N + 20)
    (hConstraint : constraintBinaryStructuredEncodedType.inputSize constraint ≤ N) :
    (EncodedType.list (EncodedType.list EncodedType.binaryNat)).inputSize
        (compactSlackItemDigitsForConstraintExecutable I rowIndex constraint) ≤
      (2 * N + 2) * (4 * N * N + 120 * N + 1201) := by
  rw [compactSlackItemDigitsForConstraintExecutable_eq]
  let Vec := EncodedType.list EncodedType.binaryNat
  let B := 4 * N * N + 120 * N + 1200
  have hVec :
      ∀ digits ∈ compactSlackItemDigitsForConstraint I rowIndex constraint,
        Vec.inputSize digits ≤ B := by
    intro digits hdigits
    rw [compactSlackItemDigitsForConstraint] at hdigits
    rw [List.mem_map] at hdigits
    rcases hdigits with ⟨power, hpower, rfl⟩
    have hPowerC := compactSlackPowers_inputSize_le_constraint hpower
    have hPowerN : EncodedType.binaryNat.inputSize power ≤ 2 * N + 2 := by
      omega
    have hItem := compactSlackItemDigitsExecutable_inputSize_le I rowIndex power
    let S := integerProgrammingBinaryStructuredEncodedType.inputSize I
    let P := EncodedType.binaryNat.inputSize power
    have hS : 2 * S ≤ 2 * (N + 20) := Nat.mul_le_mul_left 2 hI
    have hP : P + 2 ≤ 2 * N + 4 := by
      omega
    have hMul : 2 * S * (P + 2) ≤ 2 * (N + 20) * (2 * N + 4) :=
      Nat.mul_le_mul hS hP
    rw [← compactSlackItemDigitsExecutable_eq]
    change (EncodedType.list EncodedType.binaryNat).inputSize
        (compactSlackItemDigitsExecutable I rowIndex power) ≤ B
    dsimp [B]
    nlinarith [hItem, hMul]
  have hList :=
    Clique.encodedList_inputSize_le_length_mul_bound Vec
      (compactSlackItemDigitsForConstraint I rowIndex constraint) B hVec
  have hLen :
      (compactSlackItemDigitsForConstraint I rowIndex constraint).length ≤ 2 * N + 2 := by
    have hBits := compactSlackBitCount_le_two_mul_constraint_inputSize_add_two constraint
    simp [compactSlackItemDigitsForConstraint, compactSlackPowers_length]
    omega
  calc
    (EncodedType.list Vec).inputSize
        (compactSlackItemDigitsForConstraint I rowIndex constraint)
        ≤ (compactSlackItemDigitsForConstraint I rowIndex constraint).length * (B + 1) :=
          hList
    _ ≤ (2 * N + 2) * (B + 1) := by
          exact Nat.mul_le_mul_right _ hLen
    _ = (2 * N + 2) * (4 * N * N + 120 * N + 1201) := by
          simp [B]

theorem compactSlackRowVectorsStep_growth
    (source : List compactSlackRowVectorsInstructionEncodedType.Carrier)
    (acc : CompactSlackRowVectorsAcc)
    (instr : compactSlackRowVectorsInstructionEncodedType.Carrier)
    (hInv :
      compactSlackRowVectorsFoldInv
        (compactSlackRowVectorsInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      compactSlackRowVectorsInstructionEncodedType.inputSize instr ≤
        compactSlackRowVectorsInstructionListEncodedType.inputSize source) :
    compactSlackRowVectorsFoldInv
        (compactSlackRowVectorsInstructionListEncodedType.inputSize source)
        (compactSlackRowVectorsStep (acc, instr)) ∧
      compactSlackRowVectorsAccEncodedType.inputSize
          (compactSlackRowVectorsStep (acc, instr)) ≤
        compactSlackRowVectorsAccEncodedType.inputSize acc +
          ((Polynomial.C 4 * Polynomial.X * Polynomial.X +
              Polynomial.C 120 * Polynomial.X + Polynomial.C 1200).eval
            (compactSlackRowVectorsInstructionListEncodedType.inputSize source)) := by
  let N := compactSlackRowVectorsInstructionListEncodedType.inputSize source
  rcases acc with ⟨I, rowIndex, out⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨payloadI, payloadRow, payloadPower⟩
  rcases hInv with ⟨hI, hRow⟩
  have hPayload :
      compactSlackRowVectorsInstructionPayloadEncodedType.inputSize
          (payloadI, (payloadRow, payloadPower)) ≤ N := by
    exact (compactSlackRowVectorsInstruction_payload_inputSize_le
      (tag, payloadI, payloadRow, payloadPower)).trans hInstr
  have hPayloadI :
      integerProgrammingBinaryStructuredEncodedType.inputSize payloadI ≤ N := by
    simp [compactSlackRowVectorsInstructionPayloadEncodedType,
      EncodedType.inputSize_prod] at hPayload
    omega
  have hPayloadRow : EncodedType.binaryNat.inputSize payloadRow ≤ N := by
    simp [compactSlackRowVectorsInstructionPayloadEncodedType,
      EncodedType.inputSize_prod] at hPayload
    omega
  have hPayloadPower : EncodedType.binaryNat.inputSize payloadPower ≤ N := by
    simp [compactSlackRowVectorsInstructionPayloadEncodedType,
      EncodedType.inputSize_prod] at hPayload
    omega
  cases tag
  · constructor
    · exact ⟨hPayloadI.trans (by omega), hPayloadRow.trans (by omega)⟩
    · change compactSlackRowVectorsAccEncodedType.inputSize
          (payloadI, (payloadRow, ([] : List (List Nat)))) ≤
        compactSlackRowVectorsAccEncodedType.inputSize (I, (rowIndex, out)) +
          ((Polynomial.C 4 * Polynomial.X * Polynomial.X +
              Polynomial.C 120 * Polynomial.X + Polynomial.C 1200).eval N)
      have hNew :
          compactSlackRowVectorsAccEncodedType.inputSize
              (payloadI, (payloadRow, ([] : List (List Nat)))) ≤ N := by
        exact (compactSlackRowVectorsResetAcc_inputSize_le
          payloadI payloadRow payloadPower).trans hPayload
      have hBudget :
          N ≤ compactSlackRowVectorsAccEncodedType.inputSize (I, (rowIndex, out)) +
            ((Polynomial.C 4 * Polynomial.X * Polynomial.X +
                Polynomial.C 120 * Polynomial.X + Polynomial.C 1200).eval N) := by
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        omega
      exact hNew.trans hBudget
  · have hItemSize :=
      compactSlackRowVector_inputSize_le_of_bound
        (I := I) (rowIndex := rowIndex) (power := payloadPower) (N := N)
        hI hPayloadPower
    have hAppend :
        (EncodedType.list (EncodedType.list EncodedType.binaryNat)).inputSize
            (out ++ [compactSlackItemDigitsExecutable I rowIndex payloadPower]) =
          (EncodedType.list (EncodedType.list EncodedType.binaryNat)).inputSize out +
            (EncodedType.list EncodedType.binaryNat).inputSize
              (compactSlackItemDigitsExecutable I rowIndex payloadPower) + 1 := by
      exact encodedList_inputSize_append_singleton
        (EncodedType.list EncodedType.binaryNat) out
        (compactSlackItemDigitsExecutable I rowIndex payloadPower)
    constructor
    · exact ⟨hI, hRow⟩
    · simp [compactSlackRowVectorsStep, compactSlackRowVectorsAccEncodedType,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        EncodedType.inputSize_prod, hAppend]
      nlinarith

theorem compactSlackRowVectorsFold_tm_polytime :
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

theorem compactSlackRowVectorsFromInstructions_tm_polytime :
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
  have hTailComp := TMPolyTimeMap.comp hTail compactSlackRowVectorsFold_tm_polytime
  have hOutComp := TMPolyTimeMap.comp hOut hTailComp
  simpa [Function.comp, compactSlackRowVectorsFromInstructions, Tail, L, Vec]
    using hOutComp

theorem compactSlackItemDigitsForConstraintExecutable_tm_polytime :
    TMPolyTimeMap
      compactSlackRowVectorsInputEncodedType
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      (fun p : IntegerProgrammingInput × Nat × (List Int × Int) =>
        compactSlackItemDigitsForConstraintExecutable p.1 p.2.1 p.2.2) := by
  have hComp := TMPolyTimeMap.comp
    compactSlackRowVectorsFromInstructions_tm_polytime
    compactSlackRowVectorsInstructions_tm_polytime
  simpa [Function.comp, compactSlackItemDigitsForConstraintExecutable] using hComp

theorem compactSlackItemDigitsForConstraint_tm_polytime :
    TMPolyTimeMap
      compactSlackRowVectorsInputEncodedType
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      (fun p : IntegerProgrammingInput × Nat × (List Int × Int) =>
        compactSlackItemDigitsForConstraint p.1 p.2.1 p.2.2) := by
  convert compactSlackItemDigitsForConstraintExecutable_tm_polytime using 1
  funext p
  exact (compactSlackItemDigitsForConstraintExecutable_eq p.1 p.2.1 p.2.2).symm

end Knapsack
end Karp21
end ComplexityReduction
