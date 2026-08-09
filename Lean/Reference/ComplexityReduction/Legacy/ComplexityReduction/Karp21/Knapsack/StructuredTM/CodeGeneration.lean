import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.ChoiceDigits

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics
theorem compactCoeffContribution_binaryNat_inputSize_le
    (z : Int) (b : Bool) :
    EncodedType.binaryNat.inputSize (compactCoeffContribution z b) ≤
      EncodedType.binaryInt.inputSize z + 3 := by
  cases z with
  | ofNat n =>
      cases b
      · simp [compactCoeffContribution, intNegativePart, rowLookup_binaryNat_inputSize_zero]
      · change EncodedType.binaryNat.inputSize n ≤
          EncodedType.binaryInt.inputSize (Int.ofNat n) + 3
        rw [binaryInt_inputSize_ofNat_payload]
        omega
  | negSucc n =>
      cases b
      · have hSucc := binaryNatAdd_inputSize_le n 1
        have hOne : EncodedType.binaryNat.inputSize (1 : Nat) = 1 := by
          simp [EncodedType.inputSize, EncodedType.binaryNat]
        simp [compactCoeffContribution, intNegativePart] at hSucc ⊢
        omega
      · have hSucc := binaryNatAdd_inputSize_le n 1
        simp [compactCoeffContribution, intPositivePart, rowLookup_binaryNat_inputSize_zero]

theorem compactCoeffAt_binaryInt_inputSize_le
    (row : List Int) (i : Nat) :
    EncodedType.binaryInt.inputSize (compactCoeffAt row i) ≤
      intRowBinaryStructuredEncodedType.inputSize row + 1 := by
  by_cases hi : i < row.length
  · have hget :
        compactCoeffAt row i = row.get ⟨i, hi⟩ := by
      rw [compactCoeffAt, List.getD_eq_getElem (l := row) (d := (0 : Int)) hi]
      rfl
    have hmem : row.get ⟨i, hi⟩ ∈ row := List.get_mem row ⟨i, hi⟩
    rw [hget]
    have hElem := encodedList_element_inputSize_le EncodedType.binaryInt hmem
    simpa [intRowBinaryStructuredEncodedType] using hElem.trans (by omega)
  · have hle : row.length ≤ i := le_of_not_gt hi
    rw [compactCoeffAt, List.getD_eq_default (l := row) (d := (0 : Int)) (n := i) hle]
    simp [rowLookup_binaryInt_inputSize_zero]

def compactConstraintDigitsAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat
    (EncodedType.prod EncodedType.bool (EncodedType.list EncodedType.binaryNat))

abbrev CompactConstraintDigitsAcc := Nat × Bool × List Nat

def compactConstraintDigitsInitPayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat EncodedType.bool

def compactConstraintDigitsInstructionPayloadEncodedType : EncodedType :=
  EncodedType.prod compactConstraintDigitsInitPayloadEncodedType
    constraintBinaryStructuredEncodedType

def compactConstraintDigitsInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool compactConstraintDigitsInstructionPayloadEncodedType

def compactConstraintDigitsInstructionListEncodedType : EncodedType :=
  EncodedType.list compactConstraintDigitsInstructionEncodedType

def compactConstraintDigitsInputEncodedType : EncodedType :=
  EncodedType.prod constraintListBinaryStructuredEncodedType
    compactConstraintDigitsInitPayloadEncodedType

def compactConstraintDigitsInitAcc : CompactConstraintDigitsAcc :=
  ((0 : Nat), (false, ([] : List Nat)))

def compactConstraintDigitsInitInstruction (p : Nat × Bool) :
    compactConstraintDigitsInstructionEncodedType.Carrier :=
  (false, (p, (([] : List Int), (0 : Int))))

def compactConstraintDigitsRowInstruction (constraint : List Int × Int) :
    compactConstraintDigitsInstructionEncodedType.Carrier :=
  (true, (((0 : Nat), false), constraint))

def compactConstraintDigitsInstructions
    (p : List (List Int × Int) × (Nat × Bool)) :
    List compactConstraintDigitsInstructionEncodedType.Carrier :=
  compactConstraintDigitsInitInstruction p.2 ::
    p.1.map compactConstraintDigitsRowInstruction

def compactConstraintDigitsStep
    (p : CompactConstraintDigitsAcc × compactConstraintDigitsInstructionEncodedType.Carrier) :
    CompactConstraintDigitsAcc :=
  match p.2.1 with
  | false =>
      let init := p.2.2.1
      (init.1, (init.2, []))
  | true =>
      let constraint := p.2.2.2
      let i := p.1.1
      let b := p.1.2.1
      let out := p.1.2.2
      let digit := compactCoeffContribution (compactCoeffAt constraint.1 i) b
      (i, (b, out ++ [digit]))

def compactConstraintDigitsFromInstructions
    (xs : List compactConstraintDigitsInstructionEncodedType.Carrier) : List Nat :=
  (xs.foldl (fun acc instr => compactConstraintDigitsStep (acc, instr))
    compactConstraintDigitsInitAcc).2.2

def compactConstraintDigits (p : List (List Int × Int) × (Nat × Bool)) : List Nat :=
  compactConstraintDigitsFromInstructions (compactConstraintDigitsInstructions p)

theorem compactConstraintDigitsRows_fold
    (constraints : List (List Int × Int)) (i : Nat) (b : Bool) (out : List Nat) :
    ((constraints.map compactConstraintDigitsRowInstruction).foldl
        (fun acc instr => compactConstraintDigitsStep (acc, instr))
        (i, (b, out))).2.2 =
      out ++ constraints.map fun constraint =>
        compactCoeffContribution (compactCoeffAt constraint.1 i) b := by
  induction constraints generalizing out with
  | nil =>
      simp
  | cons constraint constraints ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        (((constraints.map compactConstraintDigitsRowInstruction).foldl
              (fun acc instr => compactConstraintDigitsStep (acc, instr))
              (i, (b,
                out ++
                  [compactCoeffContribution (compactCoeffAt constraint.1 i) b]))).2.2) =
          out ++
            (constraint :: constraints).map
              (fun constraint =>
                compactCoeffContribution (compactCoeffAt constraint.1 i) b)
      rw [ih (out ++ [compactCoeffContribution (compactCoeffAt constraint.1 i) b])]
      simp [List.append_assoc]

theorem compactConstraintDigits_eq_map
    (constraints : List (List Int × Int)) (i : Nat) (b : Bool) :
    compactConstraintDigits (constraints, (i, b)) =
      constraints.map fun constraint =>
        compactCoeffContribution (compactCoeffAt constraint.1 i) b := by
  have h := compactConstraintDigitsRows_fold constraints i b []
  simpa [compactConstraintDigits, compactConstraintDigitsFromInstructions,
    compactConstraintDigitsInstructions, compactConstraintDigitsInitInstruction,
    compactConstraintDigitsInitAcc, compactConstraintDigitsStep] using h

def compactVariableConstraintDigitsExecutable
    (I : IntegerProgrammingInput) (i : Nat) (b : Bool) : List Nat :=
  compactConstraintDigits (I.constraints, (i, b))

theorem compactVariableConstraintDigitsExecutable_eq
    (I : IntegerProgrammingInput) (i : Nat) (b : Bool) :
    compactVariableConstraintDigitsExecutable I i b =
      compactVariableConstraintDigits I i b := by
  simp [compactVariableConstraintDigitsExecutable, compactConstraintDigits_eq_map,
    compactVariableConstraintDigits]

theorem compactConstraintDigitsInitInstruction_tm_polytime :
    TMPolyTimeMap
      compactConstraintDigitsInitPayloadEncodedType
      compactConstraintDigitsInstructionEncodedType
      compactConstraintDigitsInitInstruction := by
  let X := compactConstraintDigitsInitPayloadEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun _ : Nat × Bool => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hInit : TMPolyTimeMap X compactConstraintDigitsInitPayloadEncodedType
      (fun p : Nat × Bool => p) :=
    TMPolyTimeMap.id X
  have hEmptyRow : TMPolyTimeMap X intRowBinaryStructuredEncodedType
      (fun _ : Nat × Bool => ([] : List Int)) :=
    TMPolyTimeMap.const X intRowBinaryStructuredEncodedType []
  have hZeroInt : TMPolyTimeMap X EncodedType.binaryInt
      (fun _ : Nat × Bool => (0 : Int)) :=
    TMPolyTimeMap.const X EncodedType.binaryInt (0 : Int)
  have hConstraint : TMPolyTimeMap X constraintBinaryStructuredEncodedType
      (fun _ : Nat × Bool => (([] : List Int), (0 : Int))) :=
    TMPolyTimeMap.prod_mk hEmptyRow hZeroInt
  have hPayload :
      TMPolyTimeMap X compactConstraintDigitsInstructionPayloadEncodedType
        (fun p : Nat × Bool => (p, (([] : List Int), (0 : Int)))) :=
    TMPolyTimeMap.prod_mk hInit hConstraint
  have hOut := TMPolyTimeMap.prod_mk hTag hPayload
  simpa [compactConstraintDigitsInitInstruction,
    compactConstraintDigitsInstructionEncodedType,
    compactConstraintDigitsInstructionPayloadEncodedType, X] using hOut

theorem compactConstraintDigitsRowInstruction_tm_polytime :
    TMPolyTimeMap
      constraintBinaryStructuredEncodedType
      compactConstraintDigitsInstructionEncodedType
      compactConstraintDigitsRowInstruction := by
  let X := constraintBinaryStructuredEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun _ : List Int × Int => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hZeroNat : TMPolyTimeMap X EncodedType.binaryNat
      (fun _ : List Int × Int => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : List Int × Int => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hInit :
      TMPolyTimeMap X compactConstraintDigitsInitPayloadEncodedType
        (fun _ : List Int × Int => ((0 : Nat), false)) :=
    TMPolyTimeMap.prod_mk hZeroNat hFalse
  have hPayload :
      TMPolyTimeMap X compactConstraintDigitsInstructionPayloadEncodedType
        (fun constraint : List Int × Int => (((0 : Nat), false), constraint)) :=
    TMPolyTimeMap.prod_mk hInit (TMPolyTimeMap.id X)
  have hOut := TMPolyTimeMap.prod_mk hTag hPayload
  simpa [compactConstraintDigitsRowInstruction,
    compactConstraintDigitsInstructionEncodedType,
    compactConstraintDigitsInstructionPayloadEncodedType, X] using hOut

theorem compactConstraintDigitsInstructions_tm_polytime :
    TMPolyTimeMap
      compactConstraintDigitsInputEncodedType
      compactConstraintDigitsInstructionListEncodedType
      compactConstraintDigitsInstructions := by
  let X := compactConstraintDigitsInputEncodedType
  have hConstraints :
      TMPolyTimeMap X constraintListBinaryStructuredEncodedType
        (fun p : List (List Int × Int) × (Nat × Bool) => p.1) := by
    simpa [X, compactConstraintDigitsInputEncodedType] using
      TMPolyTimeMap.fst constraintListBinaryStructuredEncodedType
        compactConstraintDigitsInitPayloadEncodedType
  have hInitPayload :
      TMPolyTimeMap X compactConstraintDigitsInitPayloadEncodedType
        (fun p : List (List Int × Int) × (Nat × Bool) => p.2) := by
    simpa [X, compactConstraintDigitsInputEncodedType] using
      TMPolyTimeMap.snd constraintListBinaryStructuredEncodedType
        compactConstraintDigitsInitPayloadEncodedType
  have hInit :
      TMPolyTimeMap X compactConstraintDigitsInstructionEncodedType
        (fun p : List (List Int × Int) × (Nat × Bool) =>
          compactConstraintDigitsInitInstruction p.2) := by
    have hComp := TMPolyTimeMap.comp compactConstraintDigitsInitInstruction_tm_polytime
      hInitPayload
    simpa [Function.comp, X] using hComp
  have hRows :
      TMPolyTimeMap X compactConstraintDigitsInstructionListEncodedType
        (fun p : List (List Int × Int) × (Nat × Bool) =>
          p.1.map compactConstraintDigitsRowInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactConstraintDigitsRowInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hConstraints
    simpa [Function.comp, compactConstraintDigitsInstructionListEncodedType,
      constraintListBinaryStructuredEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactConstraintDigitsInstructionEncodedType
          compactConstraintDigitsInstructionListEncodedType)
        (fun p : List (List Int × Int) × (Nat × Bool) =>
          (compactConstraintDigitsInitInstruction p.2,
            p.1.map compactConstraintDigitsRowInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hRows
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons compactConstraintDigitsInstructionEncodedType) hConsInput
  simpa [Function.comp, compactConstraintDigitsInstructions,
    compactConstraintDigitsInstructionListEncodedType, X] using hOut

theorem compactConstraintDigitsStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactConstraintDigitsAccEncodedType
        compactConstraintDigitsInstructionEncodedType)
      compactConstraintDigitsAccEncodedType
      compactConstraintDigitsStep := by
  let X := EncodedType.prod compactConstraintDigitsAccEncodedType
    compactConstraintDigitsInstructionEncodedType
  let A := compactConstraintDigitsAccEncodedType
  let Tail := EncodedType.prod EncodedType.bool (EncodedType.list EncodedType.binaryNat)
  let L := EncodedType.list EncodedType.binaryNat
  have hAcc : TMPolyTimeMap X A
      (fun p : CompactConstraintDigitsAcc ×
          compactConstraintDigitsInstructionEncodedType.Carrier => p.1) := by
    simpa [X, A] using TMPolyTimeMap.fst A compactConstraintDigitsInstructionEncodedType
  have hInstr : TMPolyTimeMap X compactConstraintDigitsInstructionEncodedType
      (fun p : CompactConstraintDigitsAcc ×
          compactConstraintDigitsInstructionEncodedType.Carrier => p.2) := by
    simpa [X, A] using TMPolyTimeMap.snd A compactConstraintDigitsInstructionEncodedType
  have hI : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactConstraintDigitsAcc ×
          compactConstraintDigitsInstructionEncodedType.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat Tail
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, compactConstraintDigitsAccEncodedType, Tail, X] using hComp
  have hTail : TMPolyTimeMap X Tail
      (fun p : CompactConstraintDigitsAcc ×
          compactConstraintDigitsInstructionEncodedType.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat Tail
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, compactConstraintDigitsAccEncodedType, Tail, X] using hComp
  have hB : TMPolyTimeMap X EncodedType.bool
      (fun p : CompactConstraintDigitsAcc ×
          compactConstraintDigitsInstructionEncodedType.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool L
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, Tail, L, X] using hComp
  have hOutList : TMPolyTimeMap X L
      (fun p : CompactConstraintDigitsAcc ×
          compactConstraintDigitsInstructionEncodedType.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool L
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, Tail, L, X] using hComp
  have hInitBranch :
      TMPolyTimeMap compactConstraintDigitsInitPayloadEncodedType A
        (fun init : Nat × Bool => (init.1, (init.2, ([] : List Nat)))) := by
    have hIdx :
        TMPolyTimeMap compactConstraintDigitsInitPayloadEncodedType EncodedType.binaryNat
          (fun init : Nat × Bool => init.1) := by
      simpa [compactConstraintDigitsInitPayloadEncodedType] using
        TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.bool
    have hBool :
        TMPolyTimeMap compactConstraintDigitsInitPayloadEncodedType EncodedType.bool
          (fun init : Nat × Bool => init.2) := by
      simpa [compactConstraintDigitsInitPayloadEncodedType] using
        TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.bool
    have hEmpty :
        TMPolyTimeMap compactConstraintDigitsInitPayloadEncodedType L
          (fun _ : Nat × Bool => ([] : List Nat)) :=
      TMPolyTimeMap.const compactConstraintDigitsInitPayloadEncodedType L []
    have hTailOut : TMPolyTimeMap compactConstraintDigitsInitPayloadEncodedType Tail
        (fun init : Nat × Bool => (init.2, ([] : List Nat))) :=
      TMPolyTimeMap.prod_mk hBool hEmpty
    exact TMPolyTimeMap.prod_mk hIdx hTailOut
  have hRowBranch :
      TMPolyTimeMap
        (EncodedType.prod A constraintBinaryStructuredEncodedType)
        A
        (fun p : CompactConstraintDigitsAcc × (List Int × Int) =>
          (p.1.1, (p.1.2.1,
            p.1.2.2 ++
              [compactCoeffContribution (compactCoeffAt p.2.1 p.1.1) p.1.2.1]))) := by
    let Y := EncodedType.prod A constraintBinaryStructuredEncodedType
    have hAccY : TMPolyTimeMap Y A (fun p : CompactConstraintDigitsAcc × (List Int × Int) => p.1) := by
      simpa [Y] using TMPolyTimeMap.fst A constraintBinaryStructuredEncodedType
    have hConstraint :
        TMPolyTimeMap Y constraintBinaryStructuredEncodedType
          (fun p : CompactConstraintDigitsAcc × (List Int × Int) => p.2) := by
      simpa [Y] using TMPolyTimeMap.snd A constraintBinaryStructuredEncodedType
    have hIY : TMPolyTimeMap Y EncodedType.binaryNat
        (fun p : CompactConstraintDigitsAcc × (List Int × Int) => p.1.1) := by
      have hFst := TMPolyTimeMap.fst EncodedType.binaryNat Tail
      have hComp := TMPolyTimeMap.comp hFst hAccY
      simpa [Function.comp, A, compactConstraintDigitsAccEncodedType, Tail, Y] using hComp
    have hTailY : TMPolyTimeMap Y Tail
        (fun p : CompactConstraintDigitsAcc × (List Int × Int) => p.1.2) := by
      have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat Tail
      have hComp := TMPolyTimeMap.comp hSnd hAccY
      simpa [Function.comp, A, compactConstraintDigitsAccEncodedType, Tail, Y] using hComp
    have hBY : TMPolyTimeMap Y EncodedType.bool
        (fun p : CompactConstraintDigitsAcc × (List Int × Int) => p.1.2.1) := by
      have hFst := TMPolyTimeMap.fst EncodedType.bool L
      have hComp := TMPolyTimeMap.comp hFst hTailY
      simpa [Function.comp, Tail, L, Y] using hComp
    have hOutY : TMPolyTimeMap Y L
        (fun p : CompactConstraintDigitsAcc × (List Int × Int) => p.1.2.2) := by
      have hSnd := TMPolyTimeMap.snd EncodedType.bool L
      have hComp := TMPolyTimeMap.comp hSnd hTailY
      simpa [Function.comp, Tail, L, Y] using hComp
    have hRow : TMPolyTimeMap Y intRowBinaryStructuredEncodedType
        (fun p : CompactConstraintDigitsAcc × (List Int × Int) => p.2.1) := by
      have hFst := TMPolyTimeMap.fst intRowBinaryStructuredEncodedType
        EncodedType.binaryInt
      have hComp := TMPolyTimeMap.comp hFst hConstraint
      simpa [Function.comp, constraintBinaryStructuredEncodedType, Y] using hComp
    have hLookupInput :
        TMPolyTimeMap Y (EncodedType.prod intRowBinaryStructuredEncodedType EncodedType.binaryNat)
          (fun p : CompactConstraintDigitsAcc × (List Int × Int) => (p.2.1, p.1.1)) :=
      TMPolyTimeMap.prod_mk hRow hIY
    have hCoeff : TMPolyTimeMap Y EncodedType.binaryInt
        (fun p : CompactConstraintDigitsAcc × (List Int × Int) =>
          compactCoeffAt p.2.1 p.1.1) := by
      have hComp := TMPolyTimeMap.comp compactCoeffAt_tm_polytime hLookupInput
      simpa [Function.comp, Y] using hComp
    have hContributionInput :
        TMPolyTimeMap Y compactCoeffContributionInputEncodedType
          (fun p : CompactConstraintDigitsAcc × (List Int × Int) =>
            (compactCoeffAt p.2.1 p.1.1, p.1.2.1)) :=
      TMPolyTimeMap.prod_mk hCoeff hBY
    have hDigit : TMPolyTimeMap Y EncodedType.binaryNat
        (fun p : CompactConstraintDigitsAcc × (List Int × Int) =>
          compactCoeffContribution (compactCoeffAt p.2.1 p.1.1) p.1.2.1) := by
      have hComp := TMPolyTimeMap.comp compactCoeffContribution_tm_polytime
        hContributionInput
      simpa [Function.comp, Y] using hComp
    have hAppendInput :
        TMPolyTimeMap Y (EncodedType.prod L EncodedType.binaryNat)
          (fun p : CompactConstraintDigitsAcc × (List Int × Int) =>
            (p.1.2.2,
              compactCoeffContribution (compactCoeffAt p.2.1 p.1.1) p.1.2.1)) :=
      TMPolyTimeMap.prod_mk hOutY hDigit
    have hAppend : TMPolyTimeMap Y L
        (fun p : CompactConstraintDigitsAcc × (List Int × Int) =>
          p.1.2.2 ++
            [compactCoeffContribution (compactCoeffAt p.2.1 p.1.1) p.1.2.1]) := by
      have hComp := TMPolyTimeMap.comp binaryNatListAppendSingleton_tm_polytime
        hAppendInput
      simpa [Function.comp, Y, L] using hComp
    have hTailOut : TMPolyTimeMap Y Tail
        (fun p : CompactConstraintDigitsAcc × (List Int × Int) =>
          (p.1.2.1,
            p.1.2.2 ++
              [compactCoeffContribution (compactCoeffAt p.2.1 p.1.1) p.1.2.1])) :=
      TMPolyTimeMap.prod_mk hBY hAppend
    exact TMPolyTimeMap.prod_mk hIY hTailOut
  have hInstrTag : TMPolyTimeMap X EncodedType.bool
      (fun p : CompactConstraintDigitsAcc ×
          compactConstraintDigitsInstructionEncodedType.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool
      compactConstraintDigitsInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, compactConstraintDigitsInstructionEncodedType, X] using hComp
  have hInstrPayload :
      TMPolyTimeMap X compactConstraintDigitsInstructionPayloadEncodedType
        (fun p : CompactConstraintDigitsAcc ×
            compactConstraintDigitsInstructionEncodedType.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool
      compactConstraintDigitsInstructionPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, compactConstraintDigitsInstructionEncodedType, X] using hComp
  have hInitPayloadX :
      TMPolyTimeMap X compactConstraintDigitsInitPayloadEncodedType
        (fun p : CompactConstraintDigitsAcc ×
            compactConstraintDigitsInstructionEncodedType.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst compactConstraintDigitsInitPayloadEncodedType
      constraintBinaryStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstrPayload
    simpa [Function.comp, compactConstraintDigitsInstructionPayloadEncodedType, X] using hComp
  have hConstraintPayloadX :
      TMPolyTimeMap X constraintBinaryStructuredEncodedType
        (fun p : CompactConstraintDigitsAcc ×
            compactConstraintDigitsInstructionEncodedType.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd compactConstraintDigitsInitPayloadEncodedType
      constraintBinaryStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstrPayload
    simpa [Function.comp, compactConstraintDigitsInstructionPayloadEncodedType, X] using hComp
  have hFalseX : TMPolyTimeMap X A
      (fun p : CompactConstraintDigitsAcc ×
          compactConstraintDigitsInstructionEncodedType.Carrier =>
        (p.2.2.1.1, (p.2.2.1.2, ([] : List Nat)))) := by
    have hComp := TMPolyTimeMap.comp hInitBranch hInitPayloadX
    simpa [Function.comp, X] using hComp
  have hRowInputX :
      TMPolyTimeMap X (EncodedType.prod A constraintBinaryStructuredEncodedType)
        (fun p : CompactConstraintDigitsAcc ×
            compactConstraintDigitsInstructionEncodedType.Carrier =>
          (p.1, p.2.2.2)) :=
    TMPolyTimeMap.prod_mk hAcc hConstraintPayloadX
  have hTrueX : TMPolyTimeMap X A
      (fun p : CompactConstraintDigitsAcc ×
          compactConstraintDigitsInstructionEncodedType.Carrier =>
        (p.1.1, (p.1.2.1,
          p.1.2.2 ++
            [compactCoeffContribution (compactCoeffAt p.2.2.2.1 p.1.1) p.1.2.1]))) := by
    have hComp := TMPolyTimeMap.comp hRowBranch hRowInputX
    simpa [Function.comp, X] using hComp
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : CompactConstraintDigitsAcc ×
            compactConstraintDigitsInstructionEncodedType.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hInstrTag (TMPolyTimeMap.id X)
  have hDispatch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
        (fun p : Bool ×
            (CompactConstraintDigitsAcc × compactConstraintDigitsInstructionEncodedType.Carrier) =>
          match p.1 with
          | true =>
              (p.2.1.1, (p.2.1.2.1,
                p.2.1.2.2 ++
                  [compactCoeffContribution (compactCoeffAt p.2.2.2.2.1 p.2.1.1)
                    p.2.1.2.1]))
          | false => (p.2.2.2.1.1, (p.2.2.2.1.2, ([] : List Nat)))) :=
    Clique.boolProduct_dispatch_tm_polytime X A
      (fFalse := fun p :
          CompactConstraintDigitsAcc × compactConstraintDigitsInstructionEncodedType.Carrier =>
        (p.2.2.1.1, (p.2.2.1.2, ([] : List Nat))))
      (fTrue := fun p :
          CompactConstraintDigitsAcc × compactConstraintDigitsInstructionEncodedType.Carrier =>
        (p.1.1, (p.1.2.1,
          p.1.2.2 ++
            [compactCoeffContribution (compactCoeffAt p.2.2.2.1 p.1.1) p.1.2.1])))
      hFalseX hTrueX
  have hOut := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hOut using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases h : instr.1 <;> simp [Function.comp, compactConstraintDigitsStep, h]
  all_goals rfl

theorem compactConstraintDigitsInitAcc_bound
    (xs : List compactConstraintDigitsInstructionEncodedType.Carrier) :
    compactConstraintDigitsAccEncodedType.inputSize compactConstraintDigitsInitAcc ≤
      (Polynomial.C 20).eval (compactConstraintDigitsInstructionListEncodedType.inputSize xs) := by
  simp [compactConstraintDigitsInitAcc, compactConstraintDigitsAccEncodedType,
    EncodedType.inputSize_prod]

theorem compactConstraintDigitsInstruction_initIdx_inputSize_le
    (instr : compactConstraintDigitsInstructionEncodedType.Carrier) :
    EncodedType.binaryNat.inputSize instr.2.1.1 ≤
      compactConstraintDigitsInstructionEncodedType.inputSize instr := by
  rcases instr with ⟨tag, init, constraint⟩
  rcases init with ⟨i, b⟩
  rcases constraint with ⟨row, bound⟩
  simp [compactConstraintDigitsInstructionEncodedType,
    compactConstraintDigitsInstructionPayloadEncodedType,
    compactConstraintDigitsInitPayloadEncodedType,
    constraintBinaryStructuredEncodedType, EncodedType.inputSize_prod]
  omega

theorem compactConstraintDigitsInstruction_row_inputSize_le
    (instr : compactConstraintDigitsInstructionEncodedType.Carrier) :
    intRowBinaryStructuredEncodedType.inputSize instr.2.2.1 ≤
      compactConstraintDigitsInstructionEncodedType.inputSize instr := by
  rcases instr with ⟨tag, init, constraint⟩
  rcases init with ⟨i, b⟩
  rcases constraint with ⟨row, bound⟩
  simp [compactConstraintDigitsInstructionEncodedType,
    compactConstraintDigitsInstructionPayloadEncodedType,
    compactConstraintDigitsInitPayloadEncodedType,
    constraintBinaryStructuredEncodedType, EncodedType.inputSize_prod]
  omega

theorem compactConstraintDigitsStep_growth
    (source : List compactConstraintDigitsInstructionEncodedType.Carrier)
    (acc : compactConstraintDigitsAccEncodedType.Carrier)
    (instr : compactConstraintDigitsInstructionEncodedType.Carrier)
    (hInstr :
      compactConstraintDigitsInstructionEncodedType.inputSize instr ≤
        compactConstraintDigitsInstructionListEncodedType.inputSize source) :
    compactConstraintDigitsAccEncodedType.inputSize
        (compactConstraintDigitsStep (acc, instr)) ≤
      compactConstraintDigitsAccEncodedType.inputSize acc +
        (Polynomial.C 50 * Polynomial.X + Polynomial.C 100).eval
          (compactConstraintDigitsInstructionListEncodedType.inputSize source) := by
  change CompactConstraintDigitsAcc at acc
  rcases acc with ⟨i, b, out⟩
  rcases instr with ⟨tag, init, constraint⟩
  rcases init with ⟨initIdx, initBool⟩
  rcases constraint with ⟨row, bound⟩
  have hInitIdx :
      EncodedType.binaryNat.inputSize initIdx ≤
        compactConstraintDigitsInstructionListEncodedType.inputSize source :=
    (compactConstraintDigitsInstruction_initIdx_inputSize_le
      (tag, (initIdx, initBool), (row, bound))).trans hInstr
  have hRow :
      intRowBinaryStructuredEncodedType.inputSize row ≤
        compactConstraintDigitsInstructionListEncodedType.inputSize source :=
    (compactConstraintDigitsInstruction_row_inputSize_le
      (tag, (initIdx, initBool), (row, bound))).trans hInstr
  let digit := compactCoeffContribution (compactCoeffAt row i) b
  have hCoeff := compactCoeffAt_binaryInt_inputSize_le row i
  have hDigitRaw := compactCoeffContribution_binaryNat_inputSize_le (compactCoeffAt row i) b
  have hDigitSize :
      EncodedType.binaryNat.inputSize digit ≤
        compactConstraintDigitsInstructionListEncodedType.inputSize source + 10 := by
    dsimp [digit] at hDigitRaw ⊢
    omega
  have hAppend :
      (EncodedType.list EncodedType.binaryNat).inputSize (out ++ [digit]) =
        (EncodedType.list EncodedType.binaryNat).inputSize out +
          EncodedType.binaryNat.inputSize digit + 1 :=
    encodedList_inputSize_append_singleton EncodedType.binaryNat out digit
  cases tag
  · simp [compactConstraintDigitsStep, compactConstraintDigitsAccEncodedType,
      EncodedType.inputSize_prod, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X]
    omega
  · simp [compactConstraintDigitsStep, compactConstraintDigitsAccEncodedType,
      EncodedType.inputSize_prod, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, hAppend, digit] at hAppend ⊢
    omega

theorem compactConstraintDigitsFold_tm_polytime :
    TMPolyTimeMap
      compactConstraintDigitsInstructionListEncodedType
      compactConstraintDigitsAccEncodedType
      (fun xs : List compactConstraintDigitsInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactConstraintDigitsStep (acc, instr))
          compactConstraintDigitsInitAcc) := by
  rcases compactConstraintDigitsStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      compactConstraintDigitsInstructionEncodedType compactConstraintDigitsAccEncodedType
      compactConstraintDigitsStep compactConstraintDigitsInitAcc hStep
      (Polynomial.C 20) (Polynomial.C 50 * Polynomial.X + Polynomial.C 100) ?_ ?_
  · intro xs
    exact compactConstraintDigitsInitAcc_bound xs
  · intro source acc instr hInstr
    exact compactConstraintDigitsStep_growth source acc instr hInstr

theorem compactConstraintDigitsFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactConstraintDigitsInstructionListEncodedType
      (EncodedType.list EncodedType.binaryNat)
      compactConstraintDigitsFromInstructions := by
  let Tail := EncodedType.prod EncodedType.bool (EncodedType.list EncodedType.binaryNat)
  have hTail : TMPolyTimeMap compactConstraintDigitsAccEncodedType Tail
      (fun acc : CompactConstraintDigitsAcc => acc.2) := by
    simpa [compactConstraintDigitsAccEncodedType, Tail] using
      TMPolyTimeMap.snd EncodedType.binaryNat Tail
  have hOut : TMPolyTimeMap Tail (EncodedType.list EncodedType.binaryNat)
      (fun tail : Bool × List Nat => tail.2) := by
    simpa [Tail] using
      TMPolyTimeMap.snd EncodedType.bool (EncodedType.list EncodedType.binaryNat)
  have hTailComp := TMPolyTimeMap.comp hTail compactConstraintDigitsFold_tm_polytime
  have hOutComp := TMPolyTimeMap.comp hOut hTailComp
  simpa [Function.comp, compactConstraintDigitsFromInstructions, Tail] using hOutComp

theorem compactConstraintDigits_tm_polytime :
    TMPolyTimeMap
      compactConstraintDigitsInputEncodedType
      (EncodedType.list EncodedType.binaryNat)
      compactConstraintDigits := by
  have hComp := TMPolyTimeMap.comp compactConstraintDigitsFromInstructions_tm_polytime
    compactConstraintDigitsInstructions_tm_polytime
  simpa [Function.comp, compactConstraintDigits] using hComp

def compactVariableConstraintDigitsExecutableInputEncodedType : EncodedType :=
  EncodedType.prod integerProgrammingBinaryStructuredEncodedType
    compactConstraintDigitsInitPayloadEncodedType

theorem compactVariableConstraintDigitsExecutable_tm_polytime :
    TMPolyTimeMap
      compactVariableConstraintDigitsExecutableInputEncodedType
      (EncodedType.list EncodedType.binaryNat)
      (fun p : IntegerProgrammingInput × (Nat × Bool) =>
        compactVariableConstraintDigitsExecutable p.1 p.2.1 p.2.2) := by
  let X := compactVariableConstraintDigitsExecutableInputEncodedType
  have hI : TMPolyTimeMap X integerProgrammingBinaryStructuredEncodedType
      (fun p : IntegerProgrammingInput × (Nat × Bool) => p.1) := by
    simpa [X, compactVariableConstraintDigitsExecutableInputEncodedType] using
      TMPolyTimeMap.fst integerProgrammingBinaryStructuredEncodedType
        compactConstraintDigitsInitPayloadEncodedType
  have hInitPayload :
      TMPolyTimeMap X compactConstraintDigitsInitPayloadEncodedType
        (fun p : IntegerProgrammingInput × (Nat × Bool) => p.2) := by
    simpa [X, compactVariableConstraintDigitsExecutableInputEncodedType] using
      TMPolyTimeMap.snd integerProgrammingBinaryStructuredEncodedType
        compactConstraintDigitsInitPayloadEncodedType
  have hConstraints :
      TMPolyTimeMap X constraintListBinaryStructuredEncodedType
        (fun p : IntegerProgrammingInput × (Nat × Bool) => p.1.constraints) := by
    have hComp := TMPolyTimeMap.comp
      integerProgrammingBinaryConstraints_tm_polytime hI
    simpa [Function.comp, X] using hComp
  have hInput :
      TMPolyTimeMap X compactConstraintDigitsInputEncodedType
        (fun p : IntegerProgrammingInput × (Nat × Bool) =>
          (p.1.constraints, p.2)) :=
    TMPolyTimeMap.prod_mk hConstraints hInitPayload
  have hComp := TMPolyTimeMap.comp compactConstraintDigits_tm_polytime hInput
  simpa [Function.comp, compactVariableConstraintDigitsExecutable,
    compactConstraintDigitsInputEncodedType, X] using hComp


end Knapsack
end Karp21
end ComplexityReduction
