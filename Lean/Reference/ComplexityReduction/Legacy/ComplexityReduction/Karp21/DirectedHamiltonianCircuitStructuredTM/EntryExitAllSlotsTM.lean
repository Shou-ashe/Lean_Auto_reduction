/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitBoundaryExitSemantics

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! TM-backed all-slot runner for entry boundary arcs. -/

def dhcAllSlotsPayloadEncodedType : EncodedType :=
  dhcIndexedIncidenceListWithBudgetEncodedType

def dhcAllSlotsAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod dhcIndexedIncidenceListEncodedType edgeListStructuredEncodedType)

def dhcAllSlotsInstructionEncodedType : EncodedType :=
  EncodedType.sum dhcAllSlotsPayloadEncodedType EncodedType.nat

def dhcAllSlotsInstructionListEncodedType : EncodedType :=
  EncodedType.list dhcAllSlotsInstructionEncodedType

def dhcAllSlotsFoldInit : dhcAllSlotsAccEncodedType.Carrier :=
  ((0 : Nat), (([] : List dhcIndexedIncidenceEncodedType.Carrier), ([] : List (Nat × Nat))))

def dhcAllSlotsFoldLeftStep
    (payload : dhcAllSlotsPayloadEncodedType.Carrier) :
    dhcAllSlotsAccEncodedType.Carrier :=
  (payload.1, (payload.2, ([] : List (Nat × Nat))))

def dhcAllSlotsInstructions
    (p : dhcIndexedIncidenceListWithBudgetRaw) :
    dhcAllSlotsInstructionListEncodedType.Carrier :=
  Sum.inl (p.1, p.2) :: (List.range p.1).map Sum.inr

theorem dhcAllSlotsFoldLeftStep_tm_polytime :
    TMPolyTimeMap dhcAllSlotsPayloadEncodedType dhcAllSlotsAccEncodedType
      dhcAllSlotsFoldLeftStep := by
  let X := dhcAllSlotsPayloadEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcAllSlotsPayloadEncodedType, dhcIndexedIncidenceListWithBudgetEncodedType]
      using TMPolyTimeMap.fst EncodedType.nat dhcIndexedIncidenceListEncodedType
  have hSource :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcAllSlotsPayloadEncodedType, dhcIndexedIncidenceListWithBudgetEncodedType]
      using TMPolyTimeMap.snd EncodedType.nat dhcIndexedIncidenceListEncodedType
  have hEmpty :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun _ : X.Carrier => ([] : List (Nat × Nat))) :=
    TMPolyTimeMap.const X edgeListStructuredEncodedType []
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceListEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier => (p.2, ([] : List (Nat × Nat)))) :=
    TMPolyTimeMap.prod_mk hSource hEmpty
  have hOut := TMPolyTimeMap.prod_mk hBudget hTail
  simpa [dhcAllSlotsFoldLeftStep, dhcAllSlotsAccEncodedType,
    dhcAllSlotsPayloadEncodedType, X] using hOut

theorem dhcAllSlotsInstructions_tm_polytime :
    TMPolyTimeMap dhcIndexedIncidenceListWithBudgetEncodedType
      dhcAllSlotsInstructionListEncodedType
      dhcAllSlotsInstructions := by
  let X := dhcIndexedIncidenceListWithBudgetEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcIndexedIncidenceListWithBudgetEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat dhcIndexedIncidenceListEncodedType
  have hSource :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcIndexedIncidenceListWithBudgetEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat dhcIndexedIncidenceListEncodedType
  have hPayload :
      TMPolyTimeMap X dhcAllSlotsPayloadEncodedType
        (fun p : X.Carrier => (p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hBudget hSource
  have hInit :
      TMPolyTimeMap X dhcAllSlotsInstructionEncodedType
        (fun p : X.Carrier => Sum.inl (p.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl dhcAllSlotsPayloadEncodedType EncodedType.nat) hPayload
    simpa [Function.comp, dhcAllSlotsInstructionEncodedType, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X dhcAllSlotsInstructionListEncodedType
        (fun p : X.Carrier => [Sum.inl (p.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton dhcAllSlotsInstructionEncodedType) hInit
    simpa [Function.comp, dhcAllSlotsInstructionListEncodedType, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => List.range p.1) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hBudget
    simpa [Function.comp, X] using hComp
  have hSlotInstruction :
      TMPolyTimeMap EncodedType.nat dhcAllSlotsInstructionEncodedType
        (fun slot : Nat => Sum.inr slot) := by
    simpa [dhcAllSlotsInstructionEncodedType] using
      TMPolyTimeMap.inr dhcAllSlotsPayloadEncodedType EncodedType.nat
  have hSlotInstrs :
      TMPolyTimeMap X dhcAllSlotsInstructionListEncodedType
        (fun p : X.Carrier => (List.range p.1).map Sum.inr) := by
    have hMap := TMPolyTimeMap.list_map hSlotInstruction
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, dhcAllSlotsInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod dhcAllSlotsInstructionListEncodedType
          dhcAllSlotsInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([Sum.inl (p.1, p.2)], (List.range p.1).map Sum.inr)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hSlotInstrs
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append dhcAllSlotsInstructionEncodedType) hAppendInput
  simpa [Function.comp, dhcAllSlotsInstructions, dhcAllSlotsInstructionListEncodedType,
    X, dhcIndexedIncidenceListWithBudgetEncodedType] using hAppend

def dhcEntryAllSlotsFoldRightStep
    (p : dhcAllSlotsAccEncodedType.Carrier × EncodedType.nat.Carrier) :
    dhcAllSlotsAccEncodedType.Carrier :=
  (p.1.1,
    (p.1.2.1,
      (show List (Nat × Nat) from p.1.2.2) ++
        dhcEntryArcsForSlotFromBoundaryIndexedExecutable (p.1.1, (p.2, p.1.2.1))))

def dhcEntryAllSlotsFoldStep
    (p : dhcAllSlotsAccEncodedType.Carrier × dhcAllSlotsInstructionEncodedType.Carrier) :
    dhcAllSlotsAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl payload => dhcAllSlotsFoldLeftStep payload
  | Sum.inr slot => dhcEntryAllSlotsFoldRightStep (p.1, slot)

def dhcEntryAllSlotsFoldResult
    (instrs : dhcAllSlotsInstructionListEncodedType.Carrier) :
    List (Nat × Nat) :=
  (instrs.foldl (fun acc instr => dhcEntryAllSlotsFoldStep (acc, instr))
    dhcAllSlotsFoldInit).2.2

def dhcEntryAllSlotsExecutableFromIndexed
    (p : dhcIndexedIncidenceListWithBudgetRaw) : List (Nat × Nat) :=
  dhcEntryAllSlotsFoldResult (dhcAllSlotsInstructions p)

theorem dhcEntryAllSlotsFoldRightStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcAllSlotsAccEncodedType EncodedType.nat)
      dhcAllSlotsAccEncodedType
      dhcEntryAllSlotsFoldRightStep := by
  let X := EncodedType.prod dhcAllSlotsAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X dhcAllSlotsAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst dhcAllSlotsAccEncodedType EncodedType.nat
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod dhcIndexedIncidenceListEncodedType edgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, dhcAllSlotsAccEncodedType, X] using hComp
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceListEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod dhcIndexedIncidenceListEncodedType edgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, dhcAllSlotsAccEncodedType, X] using hComp
  have hSource :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst dhcIndexedIncidenceListEncodedType
      edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hOutEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd dhcIndexedIncidenceListEncodedType
      edgeListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hSlot : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd dhcAllSlotsAccEncodedType EncodedType.nat
  have hSlotSource :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
        (fun p : X.Carrier => (p.2, p.1.2.1)) :=
    TMPolyTimeMap.prod_mk hSlot hSource
  have hRowInput :
      TMPolyTimeMap X dhcSlotIndexedIncidenceListEncodedType
        (fun p : X.Carrier => (p.1.1, (p.2, p.1.2.1))) :=
    TMPolyTimeMap.prod_mk hBudget hSlotSource
  have hRow :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          dhcEntryArcsForSlotFromBoundaryIndexedExecutable (p.1.1, (p.2, p.1.2.1))) := by
    have hComp := TMPolyTimeMap.comp
      dhcEntryArcsForSlotFromBoundaryIndexedExecutable_tm_polytime hRowInput
    simpa [Function.comp, dhcSlotIndexedIncidenceListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          (p.1.2.2,
            dhcEntryArcsForSlotFromBoundaryIndexedExecutable
              (p.1.1, (p.2, p.1.2.1)))) :=
    TMPolyTimeMap.prod_mk hOutEdges hRow
  have hAppend :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List (Nat × Nat) from p.1.2.2) ++
            dhcEntryArcsForSlotFromBoundaryIndexedExecutable
              (p.1.1, (p.2, p.1.2.1))) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append edgeStructuredEncodedType) hAppendInput
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hTailOut :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceListEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          (p.1.2.1,
            (show List (Nat × Nat) from p.1.2.2) ++
              dhcEntryArcsForSlotFromBoundaryIndexedExecutable
                (p.1.1, (p.2, p.1.2.1)))) :=
    TMPolyTimeMap.prod_mk hSource hAppend
  have hOut := TMPolyTimeMap.prod_mk hBudget hTailOut
  simpa [dhcEntryAllSlotsFoldRightStep, dhcAllSlotsAccEncodedType, X] using hOut

theorem dhcEntryAllSlotsFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcAllSlotsAccEncodedType dhcAllSlotsInstructionEncodedType)
      dhcAllSlotsAccEncodedType
      dhcEntryAllSlotsFoldStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      dhcAllSlotsAccEncodedType dhcAllSlotsPayloadEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim dhcAllSlotsFoldLeftStep_tm_polytime
      dhcEntryAllSlotsFoldRightStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def dhcAllSlotsFoldAccBound (N : Nat) (acc : dhcAllSlotsAccEncodedType.Carrier) :
    Prop :=
  EncodedType.nat.inputSize acc.1 ≤ N + 1 ∧
    dhcIndexedIncidenceListEncodedType.inputSize acc.2.1 ≤ N + 1

noncomputable def dhcAllSlotsFoldGrowPolynomial : Polynomial Nat :=
  Polynomial.C 1000 * Polynomial.X * Polynomial.X +
    Polynomial.C 5000 * Polynomial.X + Polynomial.C 5000

theorem dhcAllSlotsFoldGrowPolynomial_eval (N : Nat) :
    dhcAllSlotsFoldGrowPolynomial.eval N =
      1000 * N * N + 5000 * N + 5000 := by
  simp [dhcAllSlotsFoldGrowPolynomial, Polynomial.eval_add, Polynomial.eval_mul]

theorem dhcEntryArcsForSlotFromPrevIndexed_inputSize_le
    (M budget slot : Nat) (prev : dhcIndexedIncidenceEncodedType.Carrier)
    (xs : List dhcIndexedIncidenceEncodedType.Carrier)
    (hBudget : EncodedType.nat.inputSize budget ≤ M + 1)
    (hSlot : EncodedType.nat.inputSize slot ≤ M + 1)
    (hXs : dhcIndexedIncidenceListEncodedType.inputSize xs ≤ M + 1) :
    edgeListStructuredEncodedType.inputSize
        (dhcEntryArcsForSlotFromPrevIndexed budget slot prev xs) ≤
      dhcIndexedIncidenceListEncodedType.inputSize xs * (120 * M + 200) := by
  induction xs generalizing prev with
  | nil =>
      have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
        exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
      simp [dhcEntryArcsForSlotFromPrevIndexed, hNil, dhcIndexedIncidenceListEncodedType]
  | cons inc rest ih =>
      have hConsSize :
          dhcIndexedIncidenceListEncodedType.inputSize (inc :: rest) =
            dhcIndexedIncidenceEncodedType.inputSize inc + 1 +
              dhcIndexedIncidenceListEncodedType.inputSize rest := by
        simp [dhcIndexedIncidenceListEncodedType, EncodedType.inputSize_list_cons]
      have hInc : dhcIndexedIncidenceEncodedType.inputSize inc ≤ M + 5 := by
        have h := hConsSize ▸ hXs
        omega
      have hRest : dhcIndexedIncidenceListEncodedType.inputSize rest ≤ M + 1 := by
        have h := hConsSize ▸ hXs
        omega
      let block : List (Nat × Nat) :=
        if dhcBoundarySameSourceBool prev inc then []
        else dhcEntryArcForSlotBlockFromIndexed budget slot inc
      let tail : List (Nat × Nat) :=
        dhcEntryArcsForSlotFromPrevIndexed budget slot inc rest
      have hAppend :
          edgeListStructuredEncodedType.inputSize (block ++ tail) =
            edgeListStructuredEncodedType.inputSize block +
              edgeListStructuredEncodedType.inputSize tail := by
        simpa [edgeListStructuredEncodedType, block, tail] using
          Clique.encodedList_inputSize_append edgeStructuredEncodedType block tail
      have hBlock : edgeListStructuredEncodedType.inputSize block ≤ 120 * M + 200 := by
        by_cases hSame :
            dhcBoundaryIncidenceSource prev = dhcBoundaryIncidenceSource inc
        · have hSameRaw : (prev.1.1 : Nat) = (inc.1.1 : Nat) := by
            simpa [dhcBoundaryIncidenceSource] using hSame
          have hBeq : dhcBoundarySameSourceBool prev inc = true := by
            rw [dhcBoundarySameSourceBool, dhcBoundaryIncidenceSource, Nat.beq_eq]
            exact hSameRaw
          have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
            exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
          simp [block, hBeq, hNil]
        · have hSameRaw : ¬(prev.1.1 : Nat) = (inc.1.1 : Nat) := by
            simpa [dhcBoundaryIncidenceSource] using hSame
          have hBeq : dhcBoundarySameSourceBool prev inc = false := by
            rw [dhcBoundarySameSourceBool, dhcBoundaryIncidenceSource, ← Bool.not_eq_true,
              Nat.beq_eq]
            exact hSameRaw
          simpa [block, hBeq] using
            dhcEntryArcForSlotBlockFromIndexed_inputSize_le M budget slot inc
              hBudget hSlot hInc
      have hTail :
          edgeListStructuredEncodedType.inputSize tail ≤
            dhcIndexedIncidenceListEncodedType.inputSize rest * (120 * M + 200) := by
        simpa [tail] using ih inc hRest
      have hMain : edgeListStructuredEncodedType.inputSize (block ++ tail) ≤
          dhcIndexedIncidenceListEncodedType.inputSize (inc :: rest) *
            (120 * M + 200) := by
        rw [hAppend, hConsSize]
        nlinarith [hBlock, hTail,
          Nat.zero_le (dhcIndexedIncidenceEncodedType.inputSize inc),
          Nat.zero_le (dhcIndexedIncidenceListEncodedType.inputSize rest)]
      have hUnfold :
          dhcEntryArcsForSlotFromPrevIndexed budget slot prev (inc :: rest) =
            block ++ tail := by
        by_cases hSame :
            dhcBoundaryIncidenceSource prev = dhcBoundaryIncidenceSource inc
        · have hSameRaw : (prev.1.1 : Nat) = (inc.1.1 : Nat) := by
            simpa [dhcBoundaryIncidenceSource] using hSame
          have hBeq : dhcBoundarySameSourceBool prev inc = true := by
            rw [dhcBoundarySameSourceBool, dhcBoundaryIncidenceSource, Nat.beq_eq]
            exact hSameRaw
          simp [dhcEntryArcsForSlotFromPrevIndexed, block, tail, hSameRaw, hBeq]
        · have hSameRaw : ¬(prev.1.1 : Nat) = (inc.1.1 : Nat) := by
            simpa [dhcBoundaryIncidenceSource] using hSame
          have hBeq : dhcBoundarySameSourceBool prev inc = false := by
            rw [dhcBoundarySameSourceBool, dhcBoundaryIncidenceSource, ← Bool.not_eq_true,
              Nat.beq_eq]
            exact hSameRaw
          simp [dhcEntryArcsForSlotFromPrevIndexed, block, tail, hBeq]
          intro hEq
          exact False.elim (hSameRaw hEq)
      have hInputSize :=
        congrArg edgeListStructuredEncodedType.inputSize hUnfold
      exact le_of_eq_of_le hInputSize hMain

theorem dhcEntryArcsForSlotFromBoundaryIndexed_inputSize_le
    (M budget slot : Nat) (xs : List dhcIndexedIncidenceEncodedType.Carrier)
    (hBudget : EncodedType.nat.inputSize budget ≤ M + 1)
    (hSlot : EncodedType.nat.inputSize slot ≤ M + 1)
    (hXs : dhcIndexedIncidenceListEncodedType.inputSize xs ≤ M + 1) :
    edgeListStructuredEncodedType.inputSize
        (dhcEntryArcsForSlotFromBoundaryIndexed budget slot xs) ≤
      dhcIndexedIncidenceListEncodedType.inputSize xs * (120 * M + 200) := by
  cases xs with
  | nil =>
      have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
        exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
      simp [dhcEntryArcsForSlotFromBoundaryIndexed, hNil, dhcIndexedIncidenceListEncodedType]
  | cons inc rest =>
      have hConsSize :
          dhcIndexedIncidenceListEncodedType.inputSize (inc :: rest) =
            dhcIndexedIncidenceEncodedType.inputSize inc + 1 +
              dhcIndexedIncidenceListEncodedType.inputSize rest := by
        simp [dhcIndexedIncidenceListEncodedType, EncodedType.inputSize_list_cons]
      have hInc : dhcIndexedIncidenceEncodedType.inputSize inc ≤ M + 5 := by
        have h := hConsSize ▸ hXs
        omega
      have hRest : dhcIndexedIncidenceListEncodedType.inputSize rest ≤ M + 1 := by
        have h := hConsSize ▸ hXs
        omega
      let block : List (Nat × Nat) := dhcEntryArcForSlotBlockFromIndexed budget slot inc
      let tail : List (Nat × Nat) := dhcEntryArcsForSlotFromPrevIndexed budget slot inc rest
      have hAppend :
          edgeListStructuredEncodedType.inputSize (block ++ tail) =
            edgeListStructuredEncodedType.inputSize block +
              edgeListStructuredEncodedType.inputSize tail := by
        simpa [edgeListStructuredEncodedType, block, tail] using
          Clique.encodedList_inputSize_append edgeStructuredEncodedType block tail
      have hBlock : edgeListStructuredEncodedType.inputSize block ≤ 120 * M + 200 := by
        simpa [block] using
          dhcEntryArcForSlotBlockFromIndexed_inputSize_le M budget slot inc
            hBudget hSlot hInc
      have hTail :
          edgeListStructuredEncodedType.inputSize tail ≤
            dhcIndexedIncidenceListEncodedType.inputSize rest * (120 * M + 200) := by
        simpa [tail] using
          dhcEntryArcsForSlotFromPrevIndexed_inputSize_le M budget slot inc rest
            hBudget hSlot hRest
      change edgeListStructuredEncodedType.inputSize (block ++ tail) ≤
        dhcIndexedIncidenceListEncodedType.inputSize (inc :: rest) * (120 * M + 200)
      rw [hAppend, hConsSize]
      nlinarith [hBlock, hTail,
        Nat.zero_le (dhcIndexedIncidenceEncodedType.inputSize inc),
        Nat.zero_le (dhcIndexedIncidenceListEncodedType.inputSize rest)]

theorem dhcEntryArcsForSlotFromBoundaryIndexedExecutable_inputSize_le
    (M budget slot : Nat) (xs : List dhcIndexedIncidenceEncodedType.Carrier)
    (hBudget : EncodedType.nat.inputSize budget ≤ M + 1)
    (hSlot : EncodedType.nat.inputSize slot ≤ M + 1)
    (hXs : dhcIndexedIncidenceListEncodedType.inputSize xs ≤ M + 1) :
    edgeListStructuredEncodedType.inputSize
        (dhcEntryArcsForSlotFromBoundaryIndexedExecutable (budget, (slot, xs))) ≤
      dhcIndexedIncidenceListEncodedType.inputSize xs * (120 * M + 200) := by
  rw [dhcEntryArcsForSlotFromBoundaryIndexedExecutable_eq]
  exact dhcEntryArcsForSlotFromBoundaryIndexed_inputSize_le M budget slot xs
    hBudget hSlot hXs

theorem dhcEntryAllSlotsFoldStep_growth
    (source : List dhcAllSlotsInstructionEncodedType.Carrier)
    (acc : dhcAllSlotsAccEncodedType.Carrier)
    (instr : dhcAllSlotsInstructionEncodedType.Carrier)
    (hAcc :
      dhcAllSlotsFoldAccBound
        (dhcAllSlotsInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      dhcAllSlotsInstructionEncodedType.inputSize instr ≤
        dhcAllSlotsInstructionListEncodedType.inputSize source) :
    dhcAllSlotsFoldAccBound
        (dhcAllSlotsInstructionListEncodedType.inputSize source)
        (dhcEntryAllSlotsFoldStep (acc, instr)) ∧
      dhcAllSlotsAccEncodedType.inputSize (dhcEntryAllSlotsFoldStep (acc, instr)) ≤
        dhcAllSlotsAccEncodedType.inputSize acc +
          dhcAllSlotsFoldGrowPolynomial.eval
            (dhcAllSlotsInstructionListEncodedType.inputSize source) := by
  let N := dhcAllSlotsInstructionListEncodedType.inputSize source
  cases instr with
  | inl payload =>
      rcases payload with ⟨budget, xs⟩
      change Nat at budget
      have hPayloadInput : dhcAllSlotsPayloadEncodedType.inputSize (budget, xs) ≤ N := by
        have hTagged : dhcAllSlotsPayloadEncodedType.inputSize (budget, xs) + 1 ≤ N := by
          simpa [dhcAllSlotsInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
        omega
      have hBudgetPayload :
          EncodedType.nat.inputSize budget ≤
            dhcAllSlotsPayloadEncodedType.inputSize (budget, xs) := by
        simp [dhcAllSlotsPayloadEncodedType, dhcIndexedIncidenceListWithBudgetEncodedType,
          EncodedType.inputSize_prod]
        omega
      have hSourcePayload :
          dhcIndexedIncidenceListEncodedType.inputSize xs ≤
            dhcAllSlotsPayloadEncodedType.inputSize (budget, xs) := by
        simp [dhcAllSlotsPayloadEncodedType, dhcIndexedIncidenceListWithBudgetEncodedType,
          EncodedType.inputSize_prod]
      have hBudget : EncodedType.nat.inputSize budget ≤ N + 1 :=
        (hBudgetPayload.trans hPayloadInput).trans (Nat.le_succ N)
      have hSource : dhcIndexedIncidenceListEncodedType.inputSize xs ≤ N + 1 :=
        (hSourcePayload.trans hPayloadInput).trans (Nat.le_succ N)
      constructor
      · exact ⟨hBudget, hSource⟩
      · have hNilEdges :
            edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
          exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
        simp [dhcEntryAllSlotsFoldStep, dhcAllSlotsFoldLeftStep, dhcAllSlotsAccEncodedType,
          EncodedType.inputSize_prod, hNilEdges, dhcAllSlotsFoldGrowPolynomial_eval]
        have hBudgetNat : budget ≤ N := by
          simpa [EncodedType.inputSize_nat] using hBudget
        nlinarith
  | inr slot =>
      have hBudget : EncodedType.nat.inputSize acc.1 ≤ N + 1 := by
        simpa [dhcAllSlotsFoldAccBound, N] using hAcc.1
      have hSource : dhcIndexedIncidenceListEncodedType.inputSize acc.2.1 ≤ N + 1 := by
        simpa [dhcAllSlotsFoldAccBound, N] using hAcc.2
      have hSlotInput : EncodedType.nat.inputSize slot ≤ N := by
        have hTagged : EncodedType.nat.inputSize slot + 1 ≤ N := by
          simpa [dhcAllSlotsInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
        omega
      have hSlot : EncodedType.nat.inputSize slot ≤ (N + 1) + 1 := by
        omega
      let out : List (Nat × Nat) := acc.2.2
      let row : List (Nat × Nat) :=
        dhcEntryArcsForSlotFromBoundaryIndexedExecutable (acc.1, (slot, acc.2.1))
      have hAppend :
          edgeListStructuredEncodedType.inputSize (out ++ row) =
            edgeListStructuredEncodedType.inputSize out +
              edgeListStructuredEncodedType.inputSize row := by
        simpa [edgeListStructuredEncodedType, row] using
          Clique.encodedList_inputSize_append edgeStructuredEncodedType out row
      have hRowRaw :
          edgeListStructuredEncodedType.inputSize row ≤
            dhcIndexedIncidenceListEncodedType.inputSize acc.2.1 *
              (120 * (N + 1) + 200) := by
        have hBudget' : EncodedType.nat.inputSize acc.1 ≤ (N + 1) + 1 := by omega
        have hSource' : dhcIndexedIncidenceListEncodedType.inputSize acc.2.1 ≤
            (N + 1) + 1 := by omega
        simpa [row] using
          dhcEntryArcsForSlotFromBoundaryIndexedExecutable_inputSize_le
            (N + 1) acc.1 slot acc.2.1 hBudget' hSlot hSource'
      have hRow :
          edgeListStructuredEncodedType.inputSize row ≤
            dhcAllSlotsFoldGrowPolynomial.eval N := by
        rw [dhcAllSlotsFoldGrowPolynomial_eval]
        nlinarith [hRowRaw, hSource]
      constructor
      · exact ⟨hBudget, hSource⟩
      · simp [dhcEntryAllSlotsFoldStep, dhcEntryAllSlotsFoldRightStep,
          dhcAllSlotsAccEncodedType, EncodedType.inputSize_prod,
          dhcAllSlotsFoldGrowPolynomial_eval]
        have hAppend' :
            edgeListStructuredEncodedType.inputSize
                ((show List (Nat × Nat) from acc.2.2) ++
                  dhcEntryArcsForSlotFromBoundaryIndexedExecutable
                    (acc.1, (slot, acc.2.1))) =
              edgeListStructuredEncodedType.inputSize acc.2.2 +
                edgeListStructuredEncodedType.inputSize
                  (dhcEntryArcsForSlotFromBoundaryIndexedExecutable
                    (acc.1, (slot, acc.2.1))) := by
          simpa [out, row] using hAppend
        have hRow' :
            edgeListStructuredEncodedType.inputSize
                (dhcEntryArcsForSlotFromBoundaryIndexedExecutable
                  (acc.1, (slot, acc.2.1))) ≤
              1000 * dhcAllSlotsInstructionListEncodedType.inputSize source *
                  dhcAllSlotsInstructionListEncodedType.inputSize source +
                5000 * dhcAllSlotsInstructionListEncodedType.inputSize source +
              5000 := by
          simpa [row, N, dhcAllSlotsFoldGrowPolynomial_eval] using hRow
        rw [hAppend']
        nlinarith

theorem dhcEntryAllSlotsFold_tm_polytime :
    TMPolyTimeMap
      dhcAllSlotsInstructionListEncodedType
      dhcAllSlotsAccEncodedType
      (fun xs : List dhcAllSlotsInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => dhcEntryAllSlotsFoldStep (acc, instr))
          dhcAllSlotsFoldInit) := by
  rcases dhcEntryAllSlotsFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      dhcAllSlotsInstructionEncodedType dhcAllSlotsAccEncodedType
      dhcEntryAllSlotsFoldStep dhcAllSlotsFoldInit hStep
      (Polynomial.C 20) dhcAllSlotsFoldGrowPolynomial
      dhcAllSlotsFoldAccBound ?_ ?_
  · intro xs
    constructor
    · constructor
      · simp [dhcAllSlotsFoldInit, EncodedType.inputSize_nat]
      · have hNil :
            dhcIndexedIncidenceListEncodedType.inputSize
                ([] : List dhcIndexedIncidenceEncodedType.Carrier) = 0 := by
          exact EncodedType.inputSize_list_nil dhcIndexedIncidenceEncodedType
        simp [dhcAllSlotsFoldInit, hNil]
    · have hNilEdges :
          edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
        exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
      have hNilSource :
          dhcIndexedIncidenceListEncodedType.inputSize
              ([] : List dhcIndexedIncidenceEncodedType.Carrier) = 0 := by
        exact EncodedType.inputSize_list_nil dhcIndexedIncidenceEncodedType
      simp [dhcAllSlotsFoldInit, dhcAllSlotsAccEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_nat, hNilEdges, hNilSource]
  · intro source acc instr hAcc hInstr
    simpa [dhcAllSlotsInstructionListEncodedType] using
      dhcEntryAllSlotsFoldStep_growth source acc instr hAcc hInstr

theorem dhcEntryAllSlotsFoldResult_tm_polytime :
    TMPolyTimeMap
      dhcAllSlotsInstructionListEncodedType
      edgeListStructuredEncodedType
      dhcEntryAllSlotsFoldResult := by
  have hTail := TMPolyTimeMap.snd dhcIndexedIncidenceListEncodedType edgeListStructuredEncodedType
  have hAccTail :
      TMPolyTimeMap dhcAllSlotsAccEncodedType
        (EncodedType.prod dhcIndexedIncidenceListEncodedType edgeListStructuredEncodedType)
        (fun acc : dhcAllSlotsAccEncodedType.Carrier => acc.2) := by
    simpa [dhcAllSlotsAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod dhcIndexedIncidenceListEncodedType edgeListStructuredEncodedType)
  have hEdges :
      TMPolyTimeMap dhcAllSlotsAccEncodedType edgeListStructuredEncodedType
        (fun acc : dhcAllSlotsAccEncodedType.Carrier => acc.2.2) := by
    have hComp := TMPolyTimeMap.comp hTail hAccTail
    simpa [Function.comp] using hComp
  have hComp := TMPolyTimeMap.comp hEdges dhcEntryAllSlotsFold_tm_polytime
  simpa [Function.comp, dhcEntryAllSlotsFoldResult] using hComp

theorem dhcEntryAllSlotsExecutableFromIndexed_tm_polytime :
    TMPolyTimeMap dhcIndexedIncidenceListWithBudgetEncodedType
      edgeListStructuredEncodedType
      dhcEntryAllSlotsExecutableFromIndexed := by
  have hComp :=
    TMPolyTimeMap.comp dhcEntryAllSlotsFoldResult_tm_polytime
      dhcAllSlotsInstructions_tm_polytime
  simpa [Function.comp, dhcEntryAllSlotsExecutableFromIndexed] using hComp

theorem dhcEntryAllSlotsFold_map_invariant
    (budget : Nat) (source : List dhcIndexedIncidenceEncodedType.Carrier)
    (slots : List Nat) (out : List (Nat × Nat)) :
    (slots.map Sum.inr).foldl
        (fun acc instr => dhcEntryAllSlotsFoldStep (acc, instr))
        (budget, (source, out)) =
      (budget,
        (source,
          out ++
            (slots.map fun slot =>
              dhcEntryArcsForSlotFromBoundaryIndexedExecutable
                (budget, (slot, source))).flatten)) := by
  induction slots generalizing out with
  | nil =>
      simp only [List.map_nil, List.flatten_nil, List.append_nil]
      rfl
  | cons slot slots ih =>
      change
        (slots.map Sum.inr).foldl
            (fun acc instr => dhcEntryAllSlotsFoldStep (acc, instr))
            (dhcEntryAllSlotsFoldStep ((budget, (source, out)), Sum.inr slot)) =
          (budget,
            (source,
              out ++
                (dhcEntryArcsForSlotFromBoundaryIndexedExecutable (budget, (slot, source)) ::
                  slots.map fun slot =>
                    dhcEntryArcsForSlotFromBoundaryIndexedExecutable
                      (budget, (slot, source))).flatten))
      rw [show dhcEntryAllSlotsFoldStep ((budget, (source, out)), Sum.inr slot) =
          (budget,
            (source,
              out ++
                dhcEntryArcsForSlotFromBoundaryIndexedExecutable (budget, (slot, source)))) by
        rfl]
      calc
        (slots.map Sum.inr).foldl
            (fun acc instr => dhcEntryAllSlotsFoldStep (acc, instr))
            (budget,
              (source,
                out ++
                  dhcEntryArcsForSlotFromBoundaryIndexedExecutable (budget, (slot, source))))
            =
          (budget,
            (source,
              (out ++
                  dhcEntryArcsForSlotFromBoundaryIndexedExecutable (budget, (slot, source))) ++
                (slots.map fun slot =>
                  dhcEntryArcsForSlotFromBoundaryIndexedExecutable
                    (budget, (slot, source))).flatten)) :=
            ih (out ++ dhcEntryArcsForSlotFromBoundaryIndexedExecutable (budget, (slot, source)))
        _ =
          (budget,
            (source,
              out ++
                (dhcEntryArcsForSlotFromBoundaryIndexedExecutable (budget, (slot, source)) ::
                  slots.map fun slot =>
                    dhcEntryArcsForSlotFromBoundaryIndexedExecutable
                      (budget, (slot, source))).flatten)) := by
            simp [List.append_assoc]

theorem dhcEntryAllSlotsExecutableFromIndexed_eq
    (p : dhcIndexedIncidenceListWithBudgetRaw) :
    dhcEntryAllSlotsExecutableFromIndexed p =
      dhcEntryArcsExecutableFromIndexed p := by
  rcases p with ⟨budget, source⟩
  rw [dhcEntryAllSlotsExecutableFromIndexed, dhcEntryAllSlotsFoldResult,
    dhcAllSlotsInstructions]
  rw [List.foldl_cons]
  rw [show
      dhcEntryAllSlotsFoldStep (dhcAllSlotsFoldInit, Sum.inl (budget, source)) =
        (budget, (source, ([] : List (Nat × Nat)))) by
    rfl]
  change
    (List.foldl (fun acc instr => dhcEntryAllSlotsFoldStep (acc, instr))
      (budget, (source, [])) (List.map Sum.inr (List.range budget))).2.2 =
      dhcEntryArcsExecutableFromIndexed (budget, source)
  have hFold :=
    congrArg (fun acc : dhcAllSlotsAccEncodedType.Carrier => acc.2.2)
      (dhcEntryAllSlotsFold_map_invariant budget source (List.range budget)
        ([] : List (Nat × Nat)))
  calc
    (List.foldl (fun acc instr => dhcEntryAllSlotsFoldStep (acc, instr))
        (budget, (source, [])) (List.map Sum.inr (List.range budget))).2.2
        =
      ((List.range budget).map fun slot =>
        dhcEntryArcsForSlotFromBoundaryIndexedExecutable
          (budget, (slot, source))).flatten := by
        simpa using hFold
    _ = dhcEntryArcsExecutableFromIndexed (budget, source) := by
        simp [dhcEntryArcsExecutableFromIndexed,
          dhcEntryArcsForSlotFromBoundaryIndexedExecutable_eq]

theorem dhcEntryArcsExecutableFromIndexed_tm_polytime :
    TMPolyTimeMap dhcIndexedIncidenceListWithBudgetEncodedType
      edgeListStructuredEncodedType
      dhcEntryArcsExecutableFromIndexed := by
  convert dhcEntryAllSlotsExecutableFromIndexed_tm_polytime using 1
  funext p
  exact (dhcEntryAllSlotsExecutableFromIndexed_eq p).symm

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
