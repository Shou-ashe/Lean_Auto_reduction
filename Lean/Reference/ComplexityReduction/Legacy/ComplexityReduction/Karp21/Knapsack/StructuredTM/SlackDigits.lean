import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.ItemVectorAssembly

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

/-!
Direct generation of one compact slack-item digit vector.

A slack item has a zero prefix over variable-choice digits and a selector over
constraint rows, carrying `power` exactly at `rowIndex`.
-/

def compactZeroDigits (fuel : List Nat) : List Nat :=
  fuel.map fun _ => (0 : Nat)

theorem compactZeroDigits_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list EncodedType.binaryNat)
      (EncodedType.list EncodedType.binaryNat)
      compactZeroDigits := by
  have hZero :
      TMPolyTimeMap EncodedType.binaryNat EncodedType.binaryNat
        (fun _ : Nat => (0 : Nat)) :=
    TMPolyTimeMap.const EncodedType.binaryNat EncodedType.binaryNat (0 : Nat)
  have hMap := TMPolyTimeMap.list_map hZero
  simpa [compactZeroDigits] using hMap

def compactSlackSelectorAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat
    (EncodedType.prod EncodedType.binaryNat
      (EncodedType.prod EncodedType.binaryNat
        (EncodedType.list EncodedType.binaryNat)))

abbrev CompactSlackSelectorAcc := Nat × Nat × Nat × List Nat

def compactSlackSelectorInitPayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat

def compactSlackSelectorInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool compactSlackSelectorInitPayloadEncodedType

def compactSlackSelectorInstructionListEncodedType : EncodedType :=
  EncodedType.list compactSlackSelectorInstructionEncodedType

def compactSlackSelectorInputEncodedType : EncodedType :=
  EncodedType.prod constraintListBinaryStructuredEncodedType
    compactSlackSelectorInitPayloadEncodedType

def compactSlackSelectorInitAcc : CompactSlackSelectorAcc :=
  (0, (0, (0, [])))

def compactSlackSelectorInitInstruction (p : Nat × Nat) :
    compactSlackSelectorInstructionEncodedType.Carrier :=
  (false, p)

def compactSlackSelectorTickInstruction (_constraint : List Int × Int) :
    compactSlackSelectorInstructionEncodedType.Carrier :=
  (true, ((0 : Nat), (0 : Nat)))

def compactSlackSelectorInstructions
    (p : List (List Int × Int) × (Nat × Nat)) :
    List compactSlackSelectorInstructionEncodedType.Carrier :=
  compactSlackSelectorInitInstruction p.2 ::
    p.1.map compactSlackSelectorTickInstruction

def compactSlackSelectorStep
    (p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier) :
    CompactSlackSelectorAcc :=
  match p.2.1 with
  | false =>
      let init := p.2.2
      (init.1, (init.2, (0, [])))
  | true =>
      let rowIndex := p.1.1
      let power := p.1.2.1
      let idx := p.1.2.2.1
      let out := p.1.2.2.2
      let digit := if idx = rowIndex then power else 0
      (rowIndex, (power, (idx.succ, out ++ [digit])))

def compactSlackSelectorFromInstructions
    (xs : List compactSlackSelectorInstructionEncodedType.Carrier) : List Nat :=
  (xs.foldl (fun acc instr => compactSlackSelectorStep (acc, instr))
    compactSlackSelectorInitAcc).2.2.2

def compactSlackSelectorDigits
    (p : List (List Int × Int) × (Nat × Nat)) : List Nat :=
  compactSlackSelectorFromInstructions (compactSlackSelectorInstructions p)

def compactSlackItemDigitsExecutable
    (I : IntegerProgrammingInput) (rowIndex power : Nat) : List Nat :=
  compactZeroDigits (compactTargetOnes I) ++
    compactSlackSelectorDigits (I.constraints, (rowIndex, power))

theorem compactSlackSelectorTick_fold
    (constraints : List (List Int × Int)) (rowIndex power idx : Nat) (out : List Nat) :
    ((constraints.map compactSlackSelectorTickInstruction).foldl
        (fun acc instr => compactSlackSelectorStep (acc, instr))
        (rowIndex, (power, (idx, out)))).2.2.2 =
      out ++ (List.range' idx constraints.length).map fun j =>
        if j = rowIndex then power else 0 := by
  induction constraints generalizing idx out with
  | nil =>
      simp [compactSlackSelectorStep]
  | cons constraint constraints ih =>
      rw [List.map_cons, List.foldl_cons]
      change
        (((constraints.map compactSlackSelectorTickInstruction).foldl
            (fun acc instr => compactSlackSelectorStep (acc, instr))
            (rowIndex, (power,
              (idx.succ, out ++ [if idx = rowIndex then power else 0])))).2.2.2) =
          out ++ (List.range' idx (constraint :: constraints).length).map fun j =>
            if j = rowIndex then power else 0
      rw [ih idx.succ (out ++ [if idx = rowIndex then power else 0])]
      simp [List.range'_succ, List.append_assoc, Nat.succ_eq_add_one]

theorem compactSlackSelectorDigits_eq
    (constraints : List (List Int × Int)) (rowIndex power : Nat) :
    compactSlackSelectorDigits (constraints, (rowIndex, power)) =
      (List.range constraints.length).map fun j =>
        if j = rowIndex then power else 0 := by
  have h := compactSlackSelectorTick_fold constraints rowIndex power 0 []
  simpa [compactSlackSelectorDigits, compactSlackSelectorFromInstructions,
    compactSlackSelectorInstructions, compactSlackSelectorInitInstruction,
    compactSlackSelectorInitAcc, compactSlackSelectorStep, List.range_eq_range'] using h

theorem compactZeroDigits_eq_replicate (fuel : List Nat) :
    compactZeroDigits fuel = List.replicate fuel.length 0 := by
  induction fuel with
  | nil =>
      simp [compactZeroDigits]
  | cons x xs ih =>
      simp [compactZeroDigits, List.replicate_succ]

theorem compactSlackItemDigitsExecutable_eq
    (I : IntegerProgrammingInput) (rowIndex power : Nat) :
    compactSlackItemDigitsExecutable I rowIndex power =
      compactSlackItemDigits I rowIndex power := by
  rw [compactSlackItemDigitsExecutable, compactSlackItemDigits,
    compactSlackSelectorDigits_eq, compactZeroDigits_eq_replicate,
    compactTargetOnes_eq_replicate]
  simp [List.length_replicate]

theorem compactSlackSelectorInitInstruction_tm_polytime :
    TMPolyTimeMap
      compactSlackSelectorInitPayloadEncodedType
      compactSlackSelectorInstructionEncodedType
      compactSlackSelectorInitInstruction := by
  let X := compactSlackSelectorInitPayloadEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hOut := TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  simpa [compactSlackSelectorInitInstruction, compactSlackSelectorInstructionEncodedType, X]
    using hOut

theorem compactSlackSelectorTickInstruction_tm_polytime :
    TMPolyTimeMap
      constraintBinaryStructuredEncodedType
      compactSlackSelectorInstructionEncodedType
      compactSlackSelectorTickInstruction := by
  let X := constraintBinaryStructuredEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hZero : TMPolyTimeMap X EncodedType.binaryNat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have hPayload :
      TMPolyTimeMap X compactSlackSelectorInitPayloadEncodedType
        (fun _ : X.Carrier => ((0 : Nat), (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hZero hZero
  have hOut := TMPolyTimeMap.prod_mk hTag hPayload
  simpa [compactSlackSelectorTickInstruction, compactSlackSelectorInstructionEncodedType, X]
    using hOut

theorem compactSlackSelectorInstructions_tm_polytime :
    TMPolyTimeMap
      compactSlackSelectorInputEncodedType
      compactSlackSelectorInstructionListEncodedType
      compactSlackSelectorInstructions := by
  let X := compactSlackSelectorInputEncodedType
  have hConstraints :
      TMPolyTimeMap X constraintListBinaryStructuredEncodedType
        (fun p : List (List Int × Int) × (Nat × Nat) => p.1) := by
    simpa [X, compactSlackSelectorInputEncodedType] using
      TMPolyTimeMap.fst constraintListBinaryStructuredEncodedType
        compactSlackSelectorInitPayloadEncodedType
  have hPayload :
      TMPolyTimeMap X compactSlackSelectorInitPayloadEncodedType
        (fun p : List (List Int × Int) × (Nat × Nat) => p.2) := by
    simpa [X, compactSlackSelectorInputEncodedType] using
      TMPolyTimeMap.snd constraintListBinaryStructuredEncodedType
        compactSlackSelectorInitPayloadEncodedType
  have hInit :
      TMPolyTimeMap X compactSlackSelectorInstructionEncodedType
        (fun p : List (List Int × Int) × (Nat × Nat) =>
          compactSlackSelectorInitInstruction p.2) := by
    have hComp := TMPolyTimeMap.comp compactSlackSelectorInitInstruction_tm_polytime hPayload
    simpa [Function.comp, X] using hComp
  have hTicks :
      TMPolyTimeMap X compactSlackSelectorInstructionListEncodedType
        (fun p : List (List Int × Int) × (Nat × Nat) =>
          p.1.map compactSlackSelectorTickInstruction) := by
    have hMap := TMPolyTimeMap.list_map compactSlackSelectorTickInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hConstraints
    simpa [Function.comp, compactSlackSelectorInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod compactSlackSelectorInstructionEncodedType
          compactSlackSelectorInstructionListEncodedType)
        (fun p : List (List Int × Int) × (Nat × Nat) =>
          (compactSlackSelectorInitInstruction p.2,
            p.1.map compactSlackSelectorTickInstruction)) :=
    TMPolyTimeMap.prod_mk hInit hTicks
  have hCons := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons compactSlackSelectorInstructionEncodedType) hConsInput
  simpa [Function.comp, compactSlackSelectorInstructions,
    compactSlackSelectorInstructionListEncodedType, X] using hCons

theorem compactSlackSelectorStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod compactSlackSelectorAccEncodedType
        compactSlackSelectorInstructionEncodedType)
      compactSlackSelectorAccEncodedType
      compactSlackSelectorStep := by
  let L := EncodedType.list EncodedType.binaryNat
  let IdxOut := EncodedType.prod EncodedType.binaryNat L
  let PowerTail := EncodedType.prod EncodedType.binaryNat IdxOut
  let X := EncodedType.prod compactSlackSelectorAccEncodedType
    compactSlackSelectorInstructionEncodedType
  let A := compactSlackSelectorAccEncodedType
  have hAcc : TMPolyTimeMap X A
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        p.1) := by
    simpa [X, A] using
      TMPolyTimeMap.fst compactSlackSelectorAccEncodedType
        compactSlackSelectorInstructionEncodedType
  have hInstr : TMPolyTimeMap X compactSlackSelectorInstructionEncodedType
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        p.2) := by
    simpa [X, A] using
      TMPolyTimeMap.snd compactSlackSelectorAccEncodedType
        compactSlackSelectorInstructionEncodedType
  have hRow : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat PowerTail
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, compactSlackSelectorAccEncodedType, PowerTail, X] using hComp
  have hPowerTail : TMPolyTimeMap X PowerTail
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat PowerTail
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, compactSlackSelectorAccEncodedType, PowerTail, X] using hComp
  have hPower : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat IdxOut
    have hComp := TMPolyTimeMap.comp hFst hPowerTail
    simpa [Function.comp, PowerTail, IdxOut, X] using hComp
  have hIdxOut : TMPolyTimeMap X IdxOut
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat IdxOut
    have hComp := TMPolyTimeMap.comp hSnd hPowerTail
    simpa [Function.comp, PowerTail, IdxOut, X] using hComp
  have hIdx : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        p.1.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat L
    have hComp := TMPolyTimeMap.comp hFst hIdxOut
    simpa [Function.comp, IdxOut, L, X] using hComp
  have hOutList : TMPolyTimeMap X L
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat L
    have hComp := TMPolyTimeMap.comp hSnd hIdxOut
    simpa [Function.comp, IdxOut, L, X] using hComp
  have hTag : TMPolyTimeMap X EncodedType.bool
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool compactSlackSelectorInitPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, compactSlackSelectorInstructionEncodedType, X] using hComp
  have hPayload : TMPolyTimeMap X compactSlackSelectorInitPayloadEncodedType
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool compactSlackSelectorInitPayloadEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, compactSlackSelectorInstructionEncodedType, X] using hComp
  have hPayloadRow : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, compactSlackSelectorInitPayloadEncodedType, X] using hComp
  have hPayloadPower : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, compactSlackSelectorInitPayloadEncodedType, X] using hComp
  have hZero : TMPolyTimeMap X EncodedType.binaryNat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have hEmpty : TMPolyTimeMap X L (fun _ : X.Carrier => ([] : List Nat)) :=
    TMPolyTimeMap.const X L []
  have hFalseIdxOut : TMPolyTimeMap X IdxOut
      (fun _ : X.Carrier => ((0 : Nat), ([] : List Nat))) :=
    TMPolyTimeMap.prod_mk hZero hEmpty
  have hFalseTail : TMPolyTimeMap X PowerTail
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        (p.2.2.2, ((0 : Nat), ([] : List Nat)))) :=
    TMPolyTimeMap.prod_mk hPayloadPower hFalseIdxOut
  have hFalseBranch : TMPolyTimeMap X A
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        (p.2.2.1, (p.2.2.2, ((0 : Nat), ([] : List Nat))))) :=
    TMPolyTimeMap.prod_mk hPayloadRow hFalseTail
  have hEqInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
          (p.1.2.2.1, p.1.1)) :=
    TMPolyTimeMap.prod_mk hIdx hRow
  have hEq : TMPolyTimeMap X EncodedType.bool
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        binaryNatEqBool (p.1.2.2.1, p.1.1)) := by
    have hComp := TMPolyTimeMap.comp binaryNatEqBool_tm_polytime hEqInput
    simpa [Function.comp, X] using hComp
  let D := EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat
  have hDigitPayload : TMPolyTimeMap X D
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        ((0 : Nat), p.1.2.1)) :=
    TMPolyTimeMap.prod_mk hZero hPower
  have hDigitBranchInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool D)
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        (binaryNatEqBool (p.1.2.2.1, p.1.1), ((0 : Nat), p.1.2.1))) :=
    TMPolyTimeMap.prod_mk hEq hDigitPayload
  have hDigitFalse : TMPolyTimeMap D EncodedType.binaryNat (fun p : Nat × Nat => p.1) := by
    simpa [D] using TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
  have hDigitTrue : TMPolyTimeMap D EncodedType.binaryNat (fun p : Nat × Nat => p.2) := by
    simpa [D] using TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
  have hDigitDispatch :
      TMPolyTimeMap (EncodedType.prod EncodedType.bool D) EncodedType.binaryNat
        (fun p : Bool × (Nat × Nat) =>
          match p.1 with
          | true => p.2.2
          | false => p.2.1) :=
    Clique.boolProduct_dispatch_tm_polytime D EncodedType.binaryNat
      (fFalse := fun p : Nat × Nat => p.1)
      (fTrue := fun p : Nat × Nat => p.2)
      hDigitFalse hDigitTrue
  have hDigit := TMPolyTimeMap.comp hDigitDispatch hDigitBranchInput
  have hDigit' : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        if p.1.2.2.1 = p.1.1 then p.1.2.1 else (0 : Nat)) := by
    convert hDigit using 1
    funext p
    rw [Function.comp_apply]
    by_cases h : p.1.2.2.1 = p.1.1
    · have hTrue : binaryNatEqBool (p.1.2.2.1, p.1.1) = true :=
        (binaryNatEqBool_eq_true_iff _).mpr h
      have hTrueSelf : binaryNatEqBool (p.1.1, p.1.1) = true :=
        (binaryNatEqBool_eq_true_iff _).mpr rfl
      simp [h, hTrueSelf]
    · have hFalse : binaryNatEqBool (p.1.2.2.1, p.1.1) = false := by
        exact Bool.eq_false_iff.mpr ((binaryNatEqBool_eq_true_iff _).not.mpr h)
      simp [h, hFalse]
  have hSingleton : TMPolyTimeMap X L
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        [if p.1.2.2.1 = p.1.1 then p.1.2.1 else (0 : Nat)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton EncodedType.binaryNat) hDigit'
    simpa [Function.comp, L, X] using hComp
  have hAppendInput : TMPolyTimeMap X (EncodedType.prod L L)
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        (p.1.2.2.2, [if p.1.2.2.1 = p.1.1 then p.1.2.1 else (0 : Nat)])) :=
    TMPolyTimeMap.prod_mk hOutList hSingleton
  have hAppend : TMPolyTimeMap X L
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        p.1.2.2.2 ++ [if p.1.2.2.1 = p.1.1 then p.1.2.1 else (0 : Nat)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.binaryNat)
      hAppendInput
    simpa [Function.comp, L, X] using hComp
  have hIdxSucc : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        p.1.2.2.1.succ) := by
    have hComp := TMPolyTimeMap.comp binaryNatSucc_tm_polytime hIdx
    simpa [Function.comp, X] using hComp
  have hTrueIdxOut : TMPolyTimeMap X IdxOut
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        (p.1.2.2.1.succ,
          p.1.2.2.2 ++ [if p.1.2.2.1 = p.1.1 then p.1.2.1 else (0 : Nat)])) :=
    TMPolyTimeMap.prod_mk hIdxSucc hAppend
  have hTrueTail : TMPolyTimeMap X PowerTail
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        (p.1.2.1,
          (p.1.2.2.1.succ,
            p.1.2.2.2 ++
              [if p.1.2.2.1 = p.1.1 then p.1.2.1 else (0 : Nat)]))) :=
    TMPolyTimeMap.prod_mk hPower hTrueIdxOut
  have hTrueBranch : TMPolyTimeMap X A
      (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
        (p.1.1,
          (p.1.2.1,
            (p.1.2.2.1.succ,
              p.1.2.2.2 ++
                [if p.1.2.2.1 = p.1.1 then p.1.2.1 else (0 : Nat)])))) :=
    TMPolyTimeMap.prod_mk hRow hTrueTail
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier =>
          (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hDispatch : TMPolyTimeMap (EncodedType.prod EncodedType.bool X) A
      (fun p : Bool ×
          (CompactSlackSelectorAcc × compactSlackSelectorInstructionEncodedType.Carrier) =>
        match p.1 with
        | true =>
            (p.2.1.1,
              (p.2.1.2.1,
                (p.2.1.2.2.1.succ,
                  p.2.1.2.2.2 ++
                    [if p.2.1.2.2.1 = p.2.1.1 then p.2.1.2.1 else (0 : Nat)])))
        | false => (p.2.2.2.1, (p.2.2.2.2, ((0 : Nat), [])))) :=
    Clique.boolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : CompactSlackSelectorAcc ×
          compactSlackSelectorInstructionEncodedType.Carrier =>
        (p.2.2.1, (p.2.2.2, ((0 : Nat), []))))
      (fTrue := fun p : CompactSlackSelectorAcc ×
          compactSlackSelectorInstructionEncodedType.Carrier =>
        (p.1.1,
          (p.1.2.1,
            (p.1.2.2.1.succ,
              p.1.2.2.2 ++
                [if p.1.2.2.1 = p.1.1 then p.1.2.1 else (0 : Nat)]))))
      hFalseBranch hTrueBranch
  have hComp := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  rcases instr with ⟨tag, payload⟩
  cases tag <;> rfl

theorem compactSlackSelectorInstruction_payload_inputSize_le
    (instr : compactSlackSelectorInstructionEncodedType.Carrier) :
    compactSlackSelectorInitPayloadEncodedType.inputSize instr.2 ≤
      compactSlackSelectorInstructionEncodedType.inputSize instr := by
  rcases instr with ⟨tag, payload⟩
  simp [compactSlackSelectorInstructionEncodedType, EncodedType.inputSize_prod]

def compactSlackSelectorFoldInv (N : Nat) (acc : CompactSlackSelectorAcc) : Prop :=
  EncodedType.binaryNat.inputSize acc.1 ≤ N ∧
    EncodedType.binaryNat.inputSize acc.2.1 ≤ N

theorem compactSlackSelectorResetAcc_inputSize_le (rowIndex power : Nat) :
    compactSlackSelectorAccEncodedType.inputSize
        (rowIndex, (power, ((0 : Nat), ([] : List Nat)))) ≤
      compactSlackSelectorInitPayloadEncodedType.inputSize (rowIndex, power) + 2 := by
  unfold compactSlackSelectorAccEncodedType compactSlackSelectorInitPayloadEncodedType
  simp [EncodedType.prod, EncodedType.inputSize, EncodedType.binaryNat, EncodedType.list]
  omega

theorem compactSlackSelectorInitAcc_bound
    (xs : List compactSlackSelectorInstructionEncodedType.Carrier) :
    compactSlackSelectorFoldInv
        (compactSlackSelectorInstructionListEncodedType.inputSize xs)
        compactSlackSelectorInitAcc ∧
      compactSlackSelectorAccEncodedType.inputSize compactSlackSelectorInitAcc ≤
        (Polynomial.C 10).eval
          (compactSlackSelectorInstructionListEncodedType.inputSize xs) := by
  constructor
  · constructor <;> simp [compactSlackSelectorInitAcc,
      EncodedType.inputSize, EncodedType.binaryNat]
  · simp [compactSlackSelectorAccEncodedType, compactSlackSelectorInitAcc,
      EncodedType.inputSize, EncodedType.prod, EncodedType.binaryNat, EncodedType.list]

theorem compactSlackSelectorStep_growth
    (source : List compactSlackSelectorInstructionEncodedType.Carrier)
    (acc : CompactSlackSelectorAcc)
    (instr : compactSlackSelectorInstructionEncodedType.Carrier)
    (hInv :
      compactSlackSelectorFoldInv
        (compactSlackSelectorInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      compactSlackSelectorInstructionEncodedType.inputSize instr ≤
        compactSlackSelectorInstructionListEncodedType.inputSize source) :
    compactSlackSelectorFoldInv
        (compactSlackSelectorInstructionListEncodedType.inputSize source)
        (compactSlackSelectorStep (acc, instr)) ∧
      compactSlackSelectorAccEncodedType.inputSize (compactSlackSelectorStep (acc, instr)) ≤
        compactSlackSelectorAccEncodedType.inputSize acc +
          ((Polynomial.C 4 * Polynomial.X + Polynomial.C 20).eval
            (compactSlackSelectorInstructionListEncodedType.inputSize source)) := by
  let N := compactSlackSelectorInstructionListEncodedType.inputSize source
  rcases acc with ⟨rowIndex, power, idx, out⟩
  rcases instr with ⟨tag, payload⟩
  rcases payload with ⟨payloadRow, payloadPower⟩
  rcases hInv with ⟨hRow, hPower⟩
  have hPayload :
      compactSlackSelectorInitPayloadEncodedType.inputSize (payloadRow, payloadPower) ≤ N := by
    exact (compactSlackSelectorInstruction_payload_inputSize_le
      (tag, payloadRow, payloadPower)).trans hInstr
  have hPayloadRow : EncodedType.binaryNat.inputSize payloadRow ≤ N := by
    simp [compactSlackSelectorInitPayloadEncodedType, EncodedType.inputSize_prod] at hPayload
    omega
  have hPayloadPower : EncodedType.binaryNat.inputSize payloadPower ≤ N := by
    simp [compactSlackSelectorInitPayloadEncodedType, EncodedType.inputSize_prod] at hPayload
    omega
  have hIdxSucc := binaryNatAdd_inputSize_le idx 1
  have hOne : EncodedType.binaryNat.inputSize (1 : Nat) = 1 := by
    simp [EncodedType.inputSize, EncodedType.binaryNat]
  have hIdxSuccSmall :
      EncodedType.binaryNat.inputSize idx.succ ≤ EncodedType.binaryNat.inputSize idx + 2 := by
    simpa [Nat.succ_eq_add_one, hOne] using hIdxSucc
  cases tag
  · constructor
    · exact ⟨hPayloadRow, hPayloadPower⟩
    · change compactSlackSelectorAccEncodedType.inputSize
          (payloadRow, (payloadPower, ((0 : Nat), ([] : List Nat)))) ≤
        compactSlackSelectorAccEncodedType.inputSize (rowIndex, (power, (idx, out))) +
          ((Polynomial.C 4 * Polynomial.X + Polynomial.C 20).eval N)
      have hNew :
          compactSlackSelectorAccEncodedType.inputSize
              (payloadRow, (payloadPower, ((0 : Nat), ([] : List Nat)))) ≤ N + 2 := by
        exact (compactSlackSelectorResetAcc_inputSize_le payloadRow payloadPower).trans
          (by omega)
      have hBudget :
          N + 2 ≤ compactSlackSelectorAccEncodedType.inputSize
              (rowIndex, (power, (idx, out))) +
            ((Polynomial.C 4 * Polynomial.X + Polynomial.C 20).eval N) := by
        simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
        omega
      exact hNew.trans hBudget
  · have hDigit :
        EncodedType.binaryNat.inputSize
            (if idx = rowIndex then power else (0 : Nat)) ≤ N := by
      by_cases h : idx = rowIndex
      · simpa [N, h] using hPower
      · simp [N, h, EncodedType.inputSize, EncodedType.binaryNat]
    have hAppend :
          (EncodedType.list EncodedType.binaryNat).inputSize
              (out ++ [if idx = rowIndex then power else (0 : Nat)]) =
            (EncodedType.list EncodedType.binaryNat).inputSize out +
              EncodedType.binaryNat.inputSize
                (if idx = rowIndex then power else (0 : Nat)) + 1 := by
        exact encodedList_inputSize_append_singleton EncodedType.binaryNat out
          (if idx = rowIndex then power else (0 : Nat))
    constructor
    · exact ⟨hRow, hPower⟩
    · simp [compactSlackSelectorStep, compactSlackSelectorAccEncodedType,
        EncodedType.inputSize_prod, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, hAppend]
      omega

theorem compactSlackSelectorFold_tm_polytime :
    TMPolyTimeMap
      compactSlackSelectorInstructionListEncodedType
      compactSlackSelectorAccEncodedType
      (fun xs : List compactSlackSelectorInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => compactSlackSelectorStep (acc, instr))
          compactSlackSelectorInitAcc) := by
  rcases compactSlackSelectorStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      compactSlackSelectorInstructionEncodedType compactSlackSelectorAccEncodedType
      compactSlackSelectorStep compactSlackSelectorInitAcc hStep
      (Polynomial.C 10) (Polynomial.C 4 * Polynomial.X + Polynomial.C 20)
      compactSlackSelectorFoldInv ?_ ?_
  · intro xs
    exact compactSlackSelectorInitAcc_bound xs
  · intro source acc instr hInv hInstr
    exact compactSlackSelectorStep_growth source acc instr hInv hInstr

theorem compactSlackSelectorFromInstructions_tm_polytime :
    TMPolyTimeMap
      compactSlackSelectorInstructionListEncodedType
      (EncodedType.list EncodedType.binaryNat)
      compactSlackSelectorFromInstructions := by
  let L := EncodedType.list EncodedType.binaryNat
  let IdxOut := EncodedType.prod EncodedType.binaryNat L
  let PowerTail := EncodedType.prod EncodedType.binaryNat IdxOut
  have hTail : TMPolyTimeMap compactSlackSelectorAccEncodedType PowerTail
      (fun acc : CompactSlackSelectorAcc => acc.2) := by
    simpa [compactSlackSelectorAccEncodedType, PowerTail] using
      TMPolyTimeMap.snd EncodedType.binaryNat PowerTail
  have hIdxOut : TMPolyTimeMap PowerTail IdxOut
      (fun tail : Nat × (Nat × List Nat) => tail.2) := by
    simpa [PowerTail, IdxOut] using
      TMPolyTimeMap.snd EncodedType.binaryNat IdxOut
  have hOut : TMPolyTimeMap IdxOut L
      (fun tail : Nat × List Nat => tail.2) := by
    simpa [IdxOut, L] using
      TMPolyTimeMap.snd EncodedType.binaryNat L
  have hTailComp := TMPolyTimeMap.comp hTail compactSlackSelectorFold_tm_polytime
  have hIdxComp := TMPolyTimeMap.comp hIdxOut hTailComp
  have hOutComp := TMPolyTimeMap.comp hOut hIdxComp
  simpa [Function.comp, compactSlackSelectorFromInstructions, PowerTail, IdxOut, L]
    using hOutComp

theorem compactSlackSelectorDigits_tm_polytime :
    TMPolyTimeMap
      compactSlackSelectorInputEncodedType
      (EncodedType.list EncodedType.binaryNat)
      compactSlackSelectorDigits := by
  have hComp := TMPolyTimeMap.comp compactSlackSelectorFromInstructions_tm_polytime
    compactSlackSelectorInstructions_tm_polytime
  simpa [Function.comp, compactSlackSelectorDigits] using hComp

def compactSlackItemDigitsExecutableInputEncodedType : EncodedType :=
  EncodedType.prod integerProgrammingBinaryStructuredEncodedType
    (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)

theorem compactSlackItemDigitsExecutable_tm_polytime :
    TMPolyTimeMap
      compactSlackItemDigitsExecutableInputEncodedType
      (EncodedType.list EncodedType.binaryNat)
      (fun p : IntegerProgrammingInput × (Nat × Nat) =>
        compactSlackItemDigitsExecutable p.1 p.2.1 p.2.2) := by
  let X := compactSlackItemDigitsExecutableInputEncodedType
  let L := EncodedType.list EncodedType.binaryNat
  have hI : TMPolyTimeMap X integerProgrammingBinaryStructuredEncodedType
      (fun p : IntegerProgrammingInput × (Nat × Nat) => p.1) := by
    simpa [X, compactSlackItemDigitsExecutableInputEncodedType] using
      TMPolyTimeMap.fst integerProgrammingBinaryStructuredEncodedType
        (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
  have hPayload :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : IntegerProgrammingInput × (Nat × Nat) => p.2) := by
    simpa [X, compactSlackItemDigitsExecutableInputEncodedType] using
      TMPolyTimeMap.snd integerProgrammingBinaryStructuredEncodedType
        (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
  have hConstraints : TMPolyTimeMap X constraintListBinaryStructuredEncodedType
      (fun p : IntegerProgrammingInput × (Nat × Nat) => p.1.constraints) := by
    have hComp := TMPolyTimeMap.comp integerProgrammingBinaryConstraints_tm_polytime hI
    simpa [Function.comp, X] using hComp
  have hFuel : TMPolyTimeMap X L
      (fun p : IntegerProgrammingInput × (Nat × Nat) => compactTargetOnes p.1) := by
    have hComp := TMPolyTimeMap.comp compactTargetOnes_tm_polytime hI
    simpa [Function.comp, X, L] using hComp
  have hZeros : TMPolyTimeMap X L
      (fun p : IntegerProgrammingInput × (Nat × Nat) =>
        compactZeroDigits (compactTargetOnes p.1)) := by
    have hComp := TMPolyTimeMap.comp compactZeroDigits_tm_polytime hFuel
    simpa [Function.comp, X, L] using hComp
  have hSelectorInput :
      TMPolyTimeMap X compactSlackSelectorInputEncodedType
        (fun p : IntegerProgrammingInput × (Nat × Nat) =>
          (p.1.constraints, p.2)) :=
    TMPolyTimeMap.prod_mk hConstraints hPayload
  have hSelector : TMPolyTimeMap X L
      (fun p : IntegerProgrammingInput × (Nat × Nat) =>
        compactSlackSelectorDigits (p.1.constraints, p.2)) := by
    have hComp := TMPolyTimeMap.comp compactSlackSelectorDigits_tm_polytime hSelectorInput
    simpa [Function.comp, X, L] using hComp
  have hPair :
      TMPolyTimeMap X (EncodedType.prod L L)
        (fun p : IntegerProgrammingInput × (Nat × Nat) =>
          (compactZeroDigits (compactTargetOnes p.1),
            compactSlackSelectorDigits (p.1.constraints, p.2))) :=
    TMPolyTimeMap.prod_mk hZeros hSelector
  have hAppend := TMPolyTimeMap.comp (TMPolyTimeMap.list_append EncodedType.binaryNat) hPair
  simpa [Function.comp, compactSlackItemDigitsExecutable, X, L] using hAppend

theorem compactSlackItemDigits_tm_polytime :
    TMPolyTimeMap
      compactSlackItemDigitsExecutableInputEncodedType
      (EncodedType.list EncodedType.binaryNat)
      (fun p : IntegerProgrammingInput × (Nat × Nat) =>
        compactSlackItemDigits p.1 p.2.1 p.2.2) := by
  convert compactSlackItemDigitsExecutable_tm_polytime using 1
  funext p
  exact (compactSlackItemDigitsExecutable_eq p.1 p.2.1 p.2.2).symm

end Knapsack
end Karp21
end ComplexityReduction
