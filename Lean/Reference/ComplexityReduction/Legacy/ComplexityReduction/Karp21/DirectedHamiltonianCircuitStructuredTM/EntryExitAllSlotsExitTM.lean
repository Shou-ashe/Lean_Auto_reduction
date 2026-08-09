/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitAllSlotsTM

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! TM-backed all-slot runner for exit boundary arcs. -/

def dhcExitAllSlotsFoldRightStep
    (p : dhcAllSlotsAccEncodedType.Carrier × EncodedType.nat.Carrier) :
    dhcAllSlotsAccEncodedType.Carrier :=
  (p.1.1,
    (p.1.2.1,
      (show List (Nat × Nat) from p.1.2.2) ++
        dhcExitArcsForSlotFromBoundaryIndexedExecutable (p.1.1, (p.2, p.1.2.1))))

def dhcExitAllSlotsFoldStep
    (p : dhcAllSlotsAccEncodedType.Carrier × dhcAllSlotsInstructionEncodedType.Carrier) :
    dhcAllSlotsAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl payload => dhcAllSlotsFoldLeftStep payload
  | Sum.inr slot => dhcExitAllSlotsFoldRightStep (p.1, slot)

def dhcExitAllSlotsFoldResult
    (instrs : dhcAllSlotsInstructionListEncodedType.Carrier) :
    List (Nat × Nat) :=
  (instrs.foldl (fun acc instr => dhcExitAllSlotsFoldStep (acc, instr))
    dhcAllSlotsFoldInit).2.2

def dhcExitAllSlotsExecutableFromIndexed
    (p : dhcIndexedIncidenceListWithBudgetRaw) : List (Nat × Nat) :=
  dhcExitAllSlotsFoldResult (dhcAllSlotsInstructions p)

theorem dhcExitAllSlotsFoldRightStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcAllSlotsAccEncodedType EncodedType.nat)
      dhcAllSlotsAccEncodedType
      dhcExitAllSlotsFoldRightStep := by
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
          dhcExitArcsForSlotFromBoundaryIndexedExecutable (p.1.1, (p.2, p.1.2.1))) := by
    have hComp := TMPolyTimeMap.comp
      dhcExitArcsForSlotFromBoundaryIndexedExecutable_tm_polytime hRowInput
    simpa [Function.comp, dhcSlotIndexedIncidenceListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          (p.1.2.2,
            dhcExitArcsForSlotFromBoundaryIndexedExecutable
              (p.1.1, (p.2, p.1.2.1)))) :=
    TMPolyTimeMap.prod_mk hOutEdges hRow
  have hAppend :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List (Nat × Nat) from p.1.2.2) ++
            dhcExitArcsForSlotFromBoundaryIndexedExecutable
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
              dhcExitArcsForSlotFromBoundaryIndexedExecutable
                (p.1.1, (p.2, p.1.2.1)))) :=
    TMPolyTimeMap.prod_mk hSource hAppend
  have hOut := TMPolyTimeMap.prod_mk hBudget hTailOut
  simpa [dhcExitAllSlotsFoldRightStep, dhcAllSlotsAccEncodedType, X] using hOut

theorem dhcExitAllSlotsFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcAllSlotsAccEncodedType dhcAllSlotsInstructionEncodedType)
      dhcAllSlotsAccEncodedType
      dhcExitAllSlotsFoldStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      dhcAllSlotsAccEncodedType dhcAllSlotsPayloadEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim dhcAllSlotsFoldLeftStep_tm_polytime
      dhcExitAllSlotsFoldRightStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem dhcExitArcsForSlotFromPrevIndexed_inputSize_le
    (M budget slot : Nat) (prev : dhcIndexedIncidenceEncodedType.Carrier)
    (xs : List dhcIndexedIncidenceEncodedType.Carrier)
    (hBudget : EncodedType.nat.inputSize budget ≤ M + 1)
    (hSlot : EncodedType.nat.inputSize slot ≤ M + 1)
    (hPrev : dhcIndexedIncidenceEncodedType.inputSize prev ≤ M + 5)
    (hXs : dhcIndexedIncidenceListEncodedType.inputSize xs ≤ M + 1) :
    edgeListStructuredEncodedType.inputSize
        (dhcExitArcsForSlotFromPrevIndexed budget slot prev xs) ≤
      (dhcIndexedIncidenceListEncodedType.inputSize xs + 1) * (120 * M + 200) := by
  induction xs generalizing prev with
  | nil =>
      have hNil :
          dhcIndexedIncidenceListEncodedType.inputSize
              ([] : List dhcIndexedIncidenceEncodedType.Carrier) = 0 := by
        exact EncodedType.inputSize_list_nil dhcIndexedIncidenceEncodedType
      have hBlock :=
        dhcExitArcForSlotBlockFromIndexed_inputSize_le M budget slot prev
          hBudget hSlot hPrev
      simpa [dhcExitArcsForSlotFromPrevIndexed, hNil] using hBlock
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
        else dhcExitArcForSlotBlockFromIndexed budget slot prev
      let tail : List (Nat × Nat) :=
        dhcExitArcsForSlotFromPrevIndexed budget slot inc rest
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
            dhcExitArcForSlotBlockFromIndexed_inputSize_le M budget slot prev
              hBudget hSlot hPrev
      have hTail :
          edgeListStructuredEncodedType.inputSize tail ≤
            (dhcIndexedIncidenceListEncodedType.inputSize rest + 1) * (120 * M + 200) := by
        simpa [tail] using ih inc hInc hRest
      have hMain : edgeListStructuredEncodedType.inputSize (block ++ tail) ≤
          (dhcIndexedIncidenceListEncodedType.inputSize (inc :: rest) + 1) *
            (120 * M + 200) := by
        rw [hAppend, hConsSize]
        nlinarith [hBlock, hTail,
          Nat.zero_le (dhcIndexedIncidenceEncodedType.inputSize inc),
          Nat.zero_le (dhcIndexedIncidenceListEncodedType.inputSize rest)]
      have hUnfold :
          dhcExitArcsForSlotFromPrevIndexed budget slot prev (inc :: rest) =
            block ++ tail := by
        by_cases hSame :
            dhcBoundaryIncidenceSource prev = dhcBoundaryIncidenceSource inc
        · have hSameRaw : (prev.1.1 : Nat) = (inc.1.1 : Nat) := by
            simpa [dhcBoundaryIncidenceSource] using hSame
          have hBeq : dhcBoundarySameSourceBool prev inc = true := by
            rw [dhcBoundarySameSourceBool, dhcBoundaryIncidenceSource, Nat.beq_eq]
            exact hSameRaw
          simp [dhcExitArcsForSlotFromPrevIndexed, block, tail, hSameRaw, hBeq]
        · have hSameRaw : ¬(prev.1.1 : Nat) = (inc.1.1 : Nat) := by
            simpa [dhcBoundaryIncidenceSource] using hSame
          have hBeq : dhcBoundarySameSourceBool prev inc = false := by
            rw [dhcBoundarySameSourceBool, dhcBoundaryIncidenceSource, ← Bool.not_eq_true,
              Nat.beq_eq]
            exact hSameRaw
          simp [dhcExitArcsForSlotFromPrevIndexed, block, tail, hBeq]
          intro hEq
          exact False.elim (hSameRaw hEq)
      have hInputSize :=
        congrArg edgeListStructuredEncodedType.inputSize hUnfold
      exact le_of_eq_of_le hInputSize hMain

theorem dhcExitArcsForSlotFromBoundaryIndexed_inputSize_le
    (M budget slot : Nat) (xs : List dhcIndexedIncidenceEncodedType.Carrier)
    (hBudget : EncodedType.nat.inputSize budget ≤ M + 1)
    (hSlot : EncodedType.nat.inputSize slot ≤ M + 1)
    (hXs : dhcIndexedIncidenceListEncodedType.inputSize xs ≤ M + 1) :
    edgeListStructuredEncodedType.inputSize
        (dhcExitArcsForSlotFromBoundaryIndexed budget slot xs) ≤
      (dhcIndexedIncidenceListEncodedType.inputSize xs + 1) * (120 * M + 200) := by
  cases xs with
  | nil =>
      have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
        exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
      simp [dhcExitArcsForSlotFromBoundaryIndexed, hNil]
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
      have hTail :
          edgeListStructuredEncodedType.inputSize
              (dhcExitArcsForSlotFromPrevIndexed budget slot inc rest) ≤
            (dhcIndexedIncidenceListEncodedType.inputSize rest + 1) *
              (120 * M + 200) := by
        exact dhcExitArcsForSlotFromPrevIndexed_inputSize_le M budget slot inc rest
          hBudget hSlot hInc hRest
      change edgeListStructuredEncodedType.inputSize
          (dhcExitArcsForSlotFromPrevIndexed budget slot inc rest) ≤
        (dhcIndexedIncidenceListEncodedType.inputSize (inc :: rest) + 1) *
          (120 * M + 200)
      rw [hConsSize]
      nlinarith [hTail, Nat.zero_le (dhcIndexedIncidenceEncodedType.inputSize inc)]

theorem dhcExitArcsForSlotFromBoundaryIndexedExecutable_inputSize_le
    (M budget slot : Nat) (xs : List dhcIndexedIncidenceEncodedType.Carrier)
    (hBudget : EncodedType.nat.inputSize budget ≤ M + 1)
    (hSlot : EncodedType.nat.inputSize slot ≤ M + 1)
    (hXs : dhcIndexedIncidenceListEncodedType.inputSize xs ≤ M + 1) :
    edgeListStructuredEncodedType.inputSize
        (dhcExitArcsForSlotFromBoundaryIndexedExecutable (budget, (slot, xs))) ≤
      (dhcIndexedIncidenceListEncodedType.inputSize xs + 1) * (120 * M + 200) := by
  rw [dhcExitArcsForSlotFromBoundaryIndexedExecutable_eq]
  exact dhcExitArcsForSlotFromBoundaryIndexed_inputSize_le M budget slot xs
    hBudget hSlot hXs

theorem dhcExitAllSlotsFoldStep_growth
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
        (dhcExitAllSlotsFoldStep (acc, instr)) ∧
      dhcAllSlotsAccEncodedType.inputSize (dhcExitAllSlotsFoldStep (acc, instr)) ≤
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
        simp [dhcExitAllSlotsFoldStep, dhcAllSlotsFoldLeftStep, dhcAllSlotsAccEncodedType,
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
        dhcExitArcsForSlotFromBoundaryIndexedExecutable (acc.1, (slot, acc.2.1))
      have hAppend :
          edgeListStructuredEncodedType.inputSize (out ++ row) =
            edgeListStructuredEncodedType.inputSize out +
              edgeListStructuredEncodedType.inputSize row := by
        simpa [edgeListStructuredEncodedType, row] using
          Clique.encodedList_inputSize_append edgeStructuredEncodedType out row
      have hRowRaw :
          edgeListStructuredEncodedType.inputSize row ≤
            (dhcIndexedIncidenceListEncodedType.inputSize acc.2.1 + 1) *
              (120 * (N + 1) + 200) := by
        have hBudget' : EncodedType.nat.inputSize acc.1 ≤ (N + 1) + 1 := by omega
        have hSource' : dhcIndexedIncidenceListEncodedType.inputSize acc.2.1 ≤
            (N + 1) + 1 := by omega
        simpa [row] using
          dhcExitArcsForSlotFromBoundaryIndexedExecutable_inputSize_le
            (N + 1) acc.1 slot acc.2.1 hBudget' hSlot hSource'
      have hRow :
          edgeListStructuredEncodedType.inputSize row ≤
            dhcAllSlotsFoldGrowPolynomial.eval N := by
        rw [dhcAllSlotsFoldGrowPolynomial_eval]
        nlinarith [hRowRaw, hSource]
      constructor
      · exact ⟨hBudget, hSource⟩
      · simp [dhcExitAllSlotsFoldStep, dhcExitAllSlotsFoldRightStep,
          dhcAllSlotsAccEncodedType, EncodedType.inputSize_prod,
          dhcAllSlotsFoldGrowPolynomial_eval]
        have hAppend' :
            edgeListStructuredEncodedType.inputSize
                ((show List (Nat × Nat) from acc.2.2) ++
                  dhcExitArcsForSlotFromBoundaryIndexedExecutable
                    (acc.1, (slot, acc.2.1))) =
              edgeListStructuredEncodedType.inputSize acc.2.2 +
                edgeListStructuredEncodedType.inputSize
                  (dhcExitArcsForSlotFromBoundaryIndexedExecutable
                    (acc.1, (slot, acc.2.1))) := by
          simpa [out, row] using hAppend
        have hRow' :
            edgeListStructuredEncodedType.inputSize
                (dhcExitArcsForSlotFromBoundaryIndexedExecutable
                  (acc.1, (slot, acc.2.1))) ≤
              1000 * dhcAllSlotsInstructionListEncodedType.inputSize source *
                  dhcAllSlotsInstructionListEncodedType.inputSize source +
                5000 * dhcAllSlotsInstructionListEncodedType.inputSize source +
              5000 := by
          simpa [row, N, dhcAllSlotsFoldGrowPolynomial_eval] using hRow
        rw [hAppend']
        nlinarith

theorem dhcExitAllSlotsFold_tm_polytime :
    TMPolyTimeMap
      dhcAllSlotsInstructionListEncodedType
      dhcAllSlotsAccEncodedType
      (fun xs : List dhcAllSlotsInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => dhcExitAllSlotsFoldStep (acc, instr))
          dhcAllSlotsFoldInit) := by
  rcases dhcExitAllSlotsFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      dhcAllSlotsInstructionEncodedType dhcAllSlotsAccEncodedType
      dhcExitAllSlotsFoldStep dhcAllSlotsFoldInit hStep
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
      dhcExitAllSlotsFoldStep_growth source acc instr hAcc hInstr

theorem dhcExitAllSlotsFoldResult_tm_polytime :
    TMPolyTimeMap
      dhcAllSlotsInstructionListEncodedType
      edgeListStructuredEncodedType
      dhcExitAllSlotsFoldResult := by
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
  have hComp := TMPolyTimeMap.comp hEdges dhcExitAllSlotsFold_tm_polytime
  simpa [Function.comp, dhcExitAllSlotsFoldResult] using hComp

theorem dhcExitAllSlotsExecutableFromIndexed_tm_polytime :
    TMPolyTimeMap dhcIndexedIncidenceListWithBudgetEncodedType
      edgeListStructuredEncodedType
      dhcExitAllSlotsExecutableFromIndexed := by
  have hComp :=
    TMPolyTimeMap.comp dhcExitAllSlotsFoldResult_tm_polytime
      dhcAllSlotsInstructions_tm_polytime
  simpa [Function.comp, dhcExitAllSlotsExecutableFromIndexed] using hComp

theorem dhcExitAllSlotsFold_map_invariant
    (budget : Nat) (source : List dhcIndexedIncidenceEncodedType.Carrier)
    (slots : List Nat) (out : List (Nat × Nat)) :
    (slots.map Sum.inr).foldl
        (fun acc instr => dhcExitAllSlotsFoldStep (acc, instr))
        (budget, (source, out)) =
      (budget,
        (source,
          out ++
            (slots.map fun slot =>
              dhcExitArcsForSlotFromBoundaryIndexedExecutable
                (budget, (slot, source))).flatten)) := by
  induction slots generalizing out with
  | nil =>
      simp only [List.map_nil, List.flatten_nil, List.append_nil]
      rfl
  | cons slot slots ih =>
      change
        (slots.map Sum.inr).foldl
            (fun acc instr => dhcExitAllSlotsFoldStep (acc, instr))
            (dhcExitAllSlotsFoldStep ((budget, (source, out)), Sum.inr slot)) =
          (budget,
            (source,
              out ++
                (dhcExitArcsForSlotFromBoundaryIndexedExecutable (budget, (slot, source)) ::
                  slots.map fun slot =>
                    dhcExitArcsForSlotFromBoundaryIndexedExecutable
                      (budget, (slot, source))).flatten))
      rw [show dhcExitAllSlotsFoldStep ((budget, (source, out)), Sum.inr slot) =
          (budget,
            (source,
              out ++
                dhcExitArcsForSlotFromBoundaryIndexedExecutable (budget, (slot, source)))) by
        rfl]
      calc
        (slots.map Sum.inr).foldl
            (fun acc instr => dhcExitAllSlotsFoldStep (acc, instr))
            (budget,
              (source,
                out ++
                  dhcExitArcsForSlotFromBoundaryIndexedExecutable (budget, (slot, source))))
            =
          (budget,
            (source,
              (out ++
                  dhcExitArcsForSlotFromBoundaryIndexedExecutable (budget, (slot, source))) ++
                (slots.map fun slot =>
                  dhcExitArcsForSlotFromBoundaryIndexedExecutable
                    (budget, (slot, source))).flatten)) :=
            ih (out ++ dhcExitArcsForSlotFromBoundaryIndexedExecutable (budget, (slot, source)))
        _ =
          (budget,
            (source,
              out ++
                (dhcExitArcsForSlotFromBoundaryIndexedExecutable (budget, (slot, source)) ::
                  slots.map fun slot =>
                    dhcExitArcsForSlotFromBoundaryIndexedExecutable
                      (budget, (slot, source))).flatten)) := by
            simp [List.append_assoc]

theorem dhcExitAllSlotsExecutableFromIndexed_eq
    (p : dhcIndexedIncidenceListWithBudgetRaw) :
    dhcExitAllSlotsExecutableFromIndexed p =
      dhcExitArcsExecutableFromIndexed p := by
  rcases p with ⟨budget, source⟩
  rw [dhcExitAllSlotsExecutableFromIndexed, dhcExitAllSlotsFoldResult,
    dhcAllSlotsInstructions]
  rw [List.foldl_cons]
  rw [show
      dhcExitAllSlotsFoldStep (dhcAllSlotsFoldInit, Sum.inl (budget, source)) =
        (budget, (source, ([] : List (Nat × Nat)))) by
    rfl]
  change
    (List.foldl (fun acc instr => dhcExitAllSlotsFoldStep (acc, instr))
      (budget, (source, [])) (List.map Sum.inr (List.range budget))).2.2 =
      dhcExitArcsExecutableFromIndexed (budget, source)
  have hFold :=
    congrArg (fun acc : dhcAllSlotsAccEncodedType.Carrier => acc.2.2)
      (dhcExitAllSlotsFold_map_invariant budget source (List.range budget)
        ([] : List (Nat × Nat)))
  calc
    (List.foldl (fun acc instr => dhcExitAllSlotsFoldStep (acc, instr))
        (budget, (source, [])) (List.map Sum.inr (List.range budget))).2.2
        =
      ((List.range budget).map fun slot =>
        dhcExitArcsForSlotFromBoundaryIndexedExecutable
          (budget, (slot, source))).flatten := by
        simpa using hFold
    _ = dhcExitArcsExecutableFromIndexed (budget, source) := by
        simp [dhcExitArcsExecutableFromIndexed,
          dhcExitArcsForSlotFromBoundaryIndexedExecutable_eq]

theorem dhcExitArcsExecutableFromIndexed_tm_polytime :
    TMPolyTimeMap dhcIndexedIncidenceListWithBudgetEncodedType
      edgeListStructuredEncodedType
      dhcExitArcsExecutableFromIndexed := by
  convert dhcExitAllSlotsExecutableFromIndexed_tm_polytime using 1
  funext p
  exact (dhcExitAllSlotsExecutableFromIndexed_eq p).symm

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
