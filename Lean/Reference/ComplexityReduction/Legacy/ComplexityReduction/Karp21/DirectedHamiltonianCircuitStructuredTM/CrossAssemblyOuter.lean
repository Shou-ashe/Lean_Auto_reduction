/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.CrossAssembly

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! ### Outer executable fold for all cross arcs -/

def dhcCrossArcsPayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType

def dhcCrossArcsAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod dhcIndexedIncidenceListEncodedType edgeListStructuredEncodedType)

def dhcCrossArcsInstructionEncodedType : EncodedType :=
  EncodedType.sum dhcCrossArcsPayloadEncodedType dhcIndexedIncidenceEncodedType

def dhcCrossArcsInstructionListEncodedType : EncodedType :=
  EncodedType.list dhcCrossArcsInstructionEncodedType

def dhcCrossArcsFoldInit : dhcCrossArcsAccEncodedType.Carrier :=
  ((0 : Nat), (([] : List ((Nat × Nat) × Nat)), ([] : List (Nat × Nat))))

def dhcCrossArcsFoldLeftStep
    (payload : dhcCrossArcsPayloadEncodedType.Carrier) :
    dhcCrossArcsAccEncodedType.Carrier :=
  (payload.1, (payload.2, ([] : List (Nat × Nat))))

def dhcCrossArcsFoldRightStep
    (p : dhcCrossArcsAccEncodedType.Carrier × dhcIndexedIncidenceEncodedType.Carrier) :
    dhcCrossArcsAccEncodedType.Carrier :=
  (p.1.1,
    (p.1.2.1,
      (show List (Nat × Nat) from p.1.2.2) ++
        dhcCrossRowArcsExecutable (p.1.1, (p.2, p.1.2.1))))

def dhcCrossArcsFoldStep
    (p : dhcCrossArcsAccEncodedType.Carrier ×
      dhcCrossArcsInstructionEncodedType.Carrier) :
    dhcCrossArcsAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl payload => dhcCrossArcsFoldLeftStep payload
  | Sum.inr left => dhcCrossArcsFoldRightStep (p.1, left)

def dhcCrossArcsInstructions
    (p : dhcIndexedIncidenceListWithBudgetRaw) :
    dhcCrossArcsInstructionListEncodedType.Carrier :=
  Sum.inl (p.1, p.2) :: p.2.map Sum.inr

def dhcCrossArcsFoldResult
    (instrs : dhcCrossArcsInstructionListEncodedType.Carrier) :
    List (Nat × Nat) :=
  (instrs.foldl (fun acc instr => dhcCrossArcsFoldStep (acc, instr))
    dhcCrossArcsFoldInit).2.2

def dhcCrossArcsExecutableFromIndexed
    (p : dhcIndexedIncidenceListWithBudgetRaw) : List (Nat × Nat) :=
  dhcCrossArcsFoldResult (dhcCrossArcsInstructions p)

def dhcCrossArcsFromIndexedBlocks
    (p : dhcIndexedIncidenceListWithBudgetRaw) : List (Nat × Nat) :=
  (p.2.map fun left => dhcCrossRowArcsFromIndexed p.1 left p.2).flatten

def dhcCrossArcsExecutableFromInput (I : VertexCoverInput) : List (Nat × Nat) :=
  dhcCrossArcsExecutableFromIndexed (I.k, dhcIndexedSourceIncidencesFromInput I)

theorem dhcCrossArcsFoldLeftStep_tm_polytime :
    TMPolyTimeMap dhcCrossArcsPayloadEncodedType dhcCrossArcsAccEncodedType
      dhcCrossArcsFoldLeftStep := by
  let X := dhcCrossArcsPayloadEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcCrossArcsPayloadEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat dhcIndexedIncidenceListEncodedType
  have hSource :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcCrossArcsPayloadEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat dhcIndexedIncidenceListEncodedType
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
  simpa [dhcCrossArcsFoldLeftStep, dhcCrossArcsAccEncodedType,
    dhcCrossArcsPayloadEncodedType, X] using hOut

theorem dhcCrossArcsFoldRightStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcCrossArcsAccEncodedType dhcIndexedIncidenceEncodedType)
      dhcCrossArcsAccEncodedType
      dhcCrossArcsFoldRightStep := by
  let X := EncodedType.prod dhcCrossArcsAccEncodedType dhcIndexedIncidenceEncodedType
  have hAcc : TMPolyTimeMap X dhcCrossArcsAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst dhcCrossArcsAccEncodedType
      dhcIndexedIncidenceEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat
      (EncodedType.prod dhcIndexedIncidenceListEncodedType edgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, dhcCrossArcsAccEncodedType, X] using hComp
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceListEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat
      (EncodedType.prod dhcIndexedIncidenceListEncodedType edgeListStructuredEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, dhcCrossArcsAccEncodedType, X] using hComp
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
  have hLeft :
      TMPolyTimeMap X dhcIndexedIncidenceEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd dhcCrossArcsAccEncodedType
      dhcIndexedIncidenceEncodedType
  have hRowTail :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceEncodedType dhcIndexedIncidenceListEncodedType)
        (fun p : X.Carrier => (p.2, p.1.2.1)) :=
    TMPolyTimeMap.prod_mk hLeft hSource
  have hRowInput :
      TMPolyTimeMap X dhcCrossRowInputEncodedType
        (fun p : X.Carrier => (p.1.1, (p.2, p.1.2.1))) :=
    TMPolyTimeMap.prod_mk hBudget hRowTail
  have hRow :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => dhcCrossRowArcsExecutable (p.1.1, (p.2, p.1.2.1))) := by
    have hComp := TMPolyTimeMap.comp dhcCrossRowArcsExecutable_tm_polytime hRowInput
    simpa [Function.comp, dhcCrossRowInputEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          (p.1.2.2, dhcCrossRowArcsExecutable (p.1.1, (p.2, p.1.2.1)))) :=
    TMPolyTimeMap.prod_mk hOutEdges hRow
  have hAppend :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List (Nat × Nat) from p.1.2.2) ++
            dhcCrossRowArcsExecutable (p.1.1, (p.2, p.1.2.1))) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append edgeStructuredEncodedType) hAppendInput
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hOutTail :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceListEncodedType edgeListStructuredEncodedType)
        (fun p : X.Carrier =>
          (p.1.2.1,
            (show List (Nat × Nat) from p.1.2.2) ++
              dhcCrossRowArcsExecutable (p.1.1, (p.2, p.1.2.1)))) :=
    TMPolyTimeMap.prod_mk hSource hAppend
  have hOut := TMPolyTimeMap.prod_mk hBudget hOutTail
  simpa [dhcCrossArcsFoldRightStep, dhcCrossArcsAccEncodedType, X] using hOut

theorem dhcCrossArcsFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcCrossArcsAccEncodedType dhcCrossArcsInstructionEncodedType)
      dhcCrossArcsAccEncodedType
      dhcCrossArcsFoldStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      dhcCrossArcsAccEncodedType dhcCrossArcsPayloadEncodedType
      dhcIndexedIncidenceEncodedType
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim dhcCrossArcsFoldLeftStep_tm_polytime
      dhcCrossArcsFoldRightStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem dhcCrossArcsInstructions_tm_polytime :
    TMPolyTimeMap dhcIndexedIncidenceListWithBudgetEncodedType
      dhcCrossArcsInstructionListEncodedType
      dhcCrossArcsInstructions := by
  let X := dhcIndexedIncidenceListWithBudgetEncodedType
  have hBudget : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcIndexedIncidenceListWithBudgetEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat dhcIndexedIncidenceListEncodedType
  have hSource :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcIndexedIncidenceListWithBudgetEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat dhcIndexedIncidenceListEncodedType
  have hPayload :
      TMPolyTimeMap X dhcCrossArcsPayloadEncodedType
        (fun p : X.Carrier => (p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hBudget hSource
  have hInit :
      TMPolyTimeMap X dhcCrossArcsInstructionEncodedType
        (fun p : X.Carrier => Sum.inl (p.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl dhcCrossArcsPayloadEncodedType dhcIndexedIncidenceEncodedType)
      hPayload
    simpa [Function.comp, dhcCrossArcsInstructionEncodedType, X] using hComp
  have hElemInstrs :
      TMPolyTimeMap X dhcCrossArcsInstructionListEncodedType
        (fun p : X.Carrier => p.2.map Sum.inr) := by
    have hMap :=
      TMPolyTimeMap.list_map
        (TMPolyTimeMap.inr dhcCrossArcsPayloadEncodedType dhcIndexedIncidenceEncodedType)
    have hComp := TMPolyTimeMap.comp hMap hSource
    simpa [Function.comp, dhcIndexedIncidenceListEncodedType,
      dhcCrossArcsInstructionListEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod dhcCrossArcsInstructionEncodedType
          dhcCrossArcsInstructionListEncodedType)
        (fun p : X.Carrier => (Sum.inl (p.1, p.2), p.2.map Sum.inr)) :=
    TMPolyTimeMap.prod_mk hInit hElemInstrs
  have hOut :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons dhcCrossArcsInstructionEncodedType)
      hConsInput
  simpa [Function.comp, dhcCrossArcsInstructions, dhcCrossArcsInstructionListEncodedType,
    X, dhcIndexedIncidenceListWithBudgetEncodedType] using hOut

def dhcCrossArcsFoldAccBound
    (N : Nat) (acc : dhcCrossArcsAccEncodedType.Carrier) : Prop :=
  EncodedType.nat.inputSize acc.1 ≤ N + 1 ∧
    dhcIndexedIncidenceListEncodedType.inputSize acc.2.1 ≤ N + 1

noncomputable def dhcCrossArcsFoldGrowPolynomial : Polynomial Nat :=
  Polynomial.C 1000 * Polynomial.X * Polynomial.X +
    Polynomial.C 5000 * Polynomial.X + Polynomial.C 5000

theorem dhcCrossArcsFoldGrowPolynomial_eval (N : Nat) :
    dhcCrossArcsFoldGrowPolynomial.eval N =
      1000 * N * N + 5000 * N + 5000 := by
  simp [dhcCrossArcsFoldGrowPolynomial, Polynomial.eval_add, Polynomial.eval_mul]

theorem dhcCrossRowArcsFromIndexed_inputSize_le_aux
    (M budget : Nat) (left : (Nat × Nat) × Nat)
    (xs : List ((Nat × Nat) × Nat))
    (hBudget : EncodedType.nat.inputSize budget ≤ M + 1)
    (hLeft : dhcIndexedIncidenceEncodedType.inputSize left ≤ M + 5)
    (hXs : dhcIndexedIncidenceListEncodedType.inputSize xs ≤ M + 1) :
    edgeListStructuredEncodedType.inputSize
        (dhcCrossRowArcsFromIndexed budget left xs) ≤
      dhcIndexedIncidenceListEncodedType.inputSize xs * (120 * M + 200) := by
  induction xs with
  | nil =>
      have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
        exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
      simp [dhcCrossRowArcsFromIndexed, hNil, dhcIndexedIncidenceListEncodedType]
  | cons right xs ih =>
      have hConsSize :
          dhcIndexedIncidenceListEncodedType.inputSize (right :: xs) =
            dhcIndexedIncidenceEncodedType.inputSize right + 1 +
              dhcIndexedIncidenceListEncodedType.inputSize xs := by
        simp [dhcIndexedIncidenceListEncodedType, EncodedType.inputSize_list_cons]
      have hXsCons :
          dhcIndexedIncidenceEncodedType.inputSize right + 1 +
              dhcIndexedIncidenceListEncodedType.inputSize xs ≤ M + 1 := by
        exact hConsSize ▸ hXs
      have hRightInput :
          dhcIndexedIncidenceEncodedType.inputSize right ≤ M + 1 := by
        omega
      have hRight : dhcIndexedIncidenceEncodedType.inputSize right ≤ M + 5 := by
        omega
      have hTail : dhcIndexedIncidenceListEncodedType.inputSize xs ≤ M + 1 := by
        omega
      let block : List (Nat × Nat) := dhcCrossArcBlockFromIndexed (budget, (left, right))
      let rest : List (Nat × Nat) := dhcCrossRowArcsFromIndexed budget left xs
      have hAppend :
          edgeListStructuredEncodedType.inputSize (block ++ rest) =
            edgeListStructuredEncodedType.inputSize block +
              edgeListStructuredEncodedType.inputSize rest := by
        simpa [edgeListStructuredEncodedType, block, rest] using
          Clique.encodedList_inputSize_append edgeStructuredEncodedType block rest
      have hBlock :
          edgeListStructuredEncodedType.inputSize block ≤ 120 * M + 200 := by
        simpa [block] using dhcCrossArcBlock_inputSize_le M budget left right
          hBudget hLeft hRight
      have hRest :
          edgeListStructuredEncodedType.inputSize rest ≤
            dhcIndexedIncidenceListEncodedType.inputSize xs * (120 * M + 200) := by
        simpa [rest] using ih hTail
      change edgeListStructuredEncodedType.inputSize (block ++ rest) ≤
        dhcIndexedIncidenceListEncodedType.inputSize (right :: xs) * (120 * M + 200)
      rw [hAppend]
      rw [hConsSize]
      nlinarith [hBlock, hRest,
        Nat.zero_le (dhcIndexedIncidenceEncodedType.inputSize right),
        Nat.zero_le (dhcIndexedIncidenceListEncodedType.inputSize xs)]

theorem dhcCrossRowArcsExecutable_inputSize_le
    (M budget : Nat) (left : (Nat × Nat) × Nat)
    (xs : List ((Nat × Nat) × Nat))
    (hBudget : EncodedType.nat.inputSize budget ≤ M + 1)
    (hLeft : dhcIndexedIncidenceEncodedType.inputSize left ≤ M + 5)
    (hXs : dhcIndexedIncidenceListEncodedType.inputSize xs ≤ M + 1) :
    edgeListStructuredEncodedType.inputSize
        (dhcCrossRowArcsExecutable (budget, (left, xs))) ≤
      dhcIndexedIncidenceListEncodedType.inputSize xs * (120 * M + 200) := by
  rw [dhcCrossRowArcsExecutable_eq]
  exact dhcCrossRowArcsFromIndexed_inputSize_le_aux M budget left xs hBudget hLeft hXs

theorem dhcCrossArcsFoldStep_growth
    (source : List dhcCrossArcsInstructionEncodedType.Carrier)
    (acc : dhcCrossArcsAccEncodedType.Carrier)
    (instr : dhcCrossArcsInstructionEncodedType.Carrier)
    (hAcc :
      dhcCrossArcsFoldAccBound
        (dhcCrossArcsInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      dhcCrossArcsInstructionEncodedType.inputSize instr ≤
        dhcCrossArcsInstructionListEncodedType.inputSize source) :
    dhcCrossArcsFoldAccBound
        (dhcCrossArcsInstructionListEncodedType.inputSize source)
        (dhcCrossArcsFoldStep (acc, instr)) ∧
      dhcCrossArcsAccEncodedType.inputSize (dhcCrossArcsFoldStep (acc, instr)) ≤
        dhcCrossArcsAccEncodedType.inputSize acc +
          dhcCrossArcsFoldGrowPolynomial.eval
            (dhcCrossArcsInstructionListEncodedType.inputSize source) := by
  let N := dhcCrossArcsInstructionListEncodedType.inputSize source
  cases instr with
  | inl payload =>
      rcases payload with ⟨budget, xs⟩
      change Nat at budget
      have hPayloadInput :
          dhcCrossArcsPayloadEncodedType.inputSize (budget, xs) ≤ N := by
        have hTagged :
            dhcCrossArcsPayloadEncodedType.inputSize (budget, xs) + 1 ≤ N := by
          simpa [dhcCrossArcsInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
        omega
      have hBudgetPayload :
          EncodedType.nat.inputSize budget ≤
            dhcCrossArcsPayloadEncodedType.inputSize (budget, xs) := by
        simp [dhcCrossArcsPayloadEncodedType, EncodedType.inputSize_prod]
        omega
      have hSourcePayload :
          dhcIndexedIncidenceListEncodedType.inputSize xs ≤
            dhcCrossArcsPayloadEncodedType.inputSize (budget, xs) := by
        simp [dhcCrossArcsPayloadEncodedType, EncodedType.inputSize_prod]
      have hBudget : EncodedType.nat.inputSize budget ≤ N + 1 :=
        (hBudgetPayload.trans hPayloadInput).trans (Nat.le_succ N)
      have hSource : dhcIndexedIncidenceListEncodedType.inputSize xs ≤ N + 1 :=
        (hSourcePayload.trans hPayloadInput).trans (Nat.le_succ N)
      constructor
      · exact ⟨hBudget, hSource⟩
      · have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
          exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
        simp [dhcCrossArcsFoldStep, dhcCrossArcsFoldLeftStep, dhcCrossArcsAccEncodedType,
          EncodedType.inputSize_prod, hNil, dhcCrossArcsFoldGrowPolynomial_eval]
        have hBudgetNat : budget ≤ N := by
          simpa [EncodedType.inputSize_nat] using hBudget
        nlinarith
  | inr left =>
      have hBudget : EncodedType.nat.inputSize acc.1 ≤ N + 1 := by
        simpa [dhcCrossArcsFoldAccBound, N] using hAcc.1
      have hSource : dhcIndexedIncidenceListEncodedType.inputSize acc.2.1 ≤ N + 1 := by
        simpa [dhcCrossArcsFoldAccBound, N] using hAcc.2
      have hLeftInput : dhcIndexedIncidenceEncodedType.inputSize left ≤ N := by
        have hTagged : dhcIndexedIncidenceEncodedType.inputSize left + 1 ≤ N := by
          simpa [dhcCrossArcsInstructionEncodedType, EncodedType.inputSize,
            EncodedType.sum, N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
        omega
      have hLeft : dhcIndexedIncidenceEncodedType.inputSize left ≤ (N + 1) + 5 := by
        omega
      let out : List (Nat × Nat) := acc.2.2
      let row : List (Nat × Nat) := dhcCrossRowArcsExecutable (acc.1, (left, acc.2.1))
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
        have hBudget' : EncodedType.nat.inputSize acc.1 ≤ (N + 1) + 1 := by
          omega
        have hSource' : dhcIndexedIncidenceListEncodedType.inputSize acc.2.1 ≤
            (N + 1) + 1 := by
          omega
        simpa [row] using
          dhcCrossRowArcsExecutable_inputSize_le (N + 1) acc.1 left acc.2.1
            hBudget' hLeft hSource'
      have hRow :
          edgeListStructuredEncodedType.inputSize row ≤
            dhcCrossArcsFoldGrowPolynomial.eval N := by
        rw [dhcCrossArcsFoldGrowPolynomial_eval]
        nlinarith [hRowRaw, hSource]
      constructor
      · exact ⟨hBudget, hSource⟩
      · simp [dhcCrossArcsFoldStep, dhcCrossArcsFoldRightStep,
          dhcCrossArcsAccEncodedType, EncodedType.inputSize_prod,
          dhcCrossArcsFoldGrowPolynomial_eval]
        have hAppend' :
            edgeListStructuredEncodedType.inputSize
                ((show List (Nat × Nat) from acc.2.2) ++
                  dhcCrossRowArcsExecutable (acc.1, (left, acc.2.1))) =
              edgeListStructuredEncodedType.inputSize acc.2.2 +
                edgeListStructuredEncodedType.inputSize
                  (dhcCrossRowArcsExecutable (acc.1, (left, acc.2.1))) := by
          simpa [out, row] using hAppend
        have hRow' :
            edgeListStructuredEncodedType.inputSize
                (dhcCrossRowArcsExecutable (acc.1, (left, acc.2.1))) ≤
              1000 * dhcCrossArcsInstructionListEncodedType.inputSize source *
                  dhcCrossArcsInstructionListEncodedType.inputSize source +
                5000 * dhcCrossArcsInstructionListEncodedType.inputSize source +
              5000 := by
          simpa [row, N, dhcCrossArcsFoldGrowPolynomial_eval] using hRow
        rw [hAppend']
        nlinarith

theorem dhcCrossArcsFold_tm_polytime :
    TMPolyTimeMap
      dhcCrossArcsInstructionListEncodedType
      dhcCrossArcsAccEncodedType
      (fun xs : List dhcCrossArcsInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => dhcCrossArcsFoldStep (acc, instr))
          dhcCrossArcsFoldInit) := by
  rcases dhcCrossArcsFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      dhcCrossArcsInstructionEncodedType dhcCrossArcsAccEncodedType
      dhcCrossArcsFoldStep dhcCrossArcsFoldInit hStep
      (Polynomial.C 20) dhcCrossArcsFoldGrowPolynomial
      dhcCrossArcsFoldAccBound ?_ ?_
  · intro xs
    constructor
    · constructor
      · simp [dhcCrossArcsFoldInit, EncodedType.inputSize_nat]
      · have hNil :
            dhcIndexedIncidenceListEncodedType.inputSize
                ([] : List ((Nat × Nat) × Nat)) = 0 := by
          exact EncodedType.inputSize_list_nil dhcIndexedIncidenceEncodedType
        simp [dhcCrossArcsFoldInit, hNil]
    · have hNilEdges :
          edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
        exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
      have hNilSource :
          dhcIndexedIncidenceListEncodedType.inputSize
              ([] : List ((Nat × Nat) × Nat)) = 0 := by
        exact EncodedType.inputSize_list_nil dhcIndexedIncidenceEncodedType
      simp [dhcCrossArcsFoldInit, dhcCrossArcsAccEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_nat, hNilEdges, hNilSource]
  · intro source acc instr hAcc hInstr
    simpa [dhcCrossArcsInstructionListEncodedType] using
      dhcCrossArcsFoldStep_growth source acc instr hAcc hInstr

theorem dhcCrossArcsFoldResult_tm_polytime :
    TMPolyTimeMap
      dhcCrossArcsInstructionListEncodedType
      edgeListStructuredEncodedType
      dhcCrossArcsFoldResult := by
  have hTail := TMPolyTimeMap.snd dhcIndexedIncidenceListEncodedType edgeListStructuredEncodedType
  have hAccTail :
      TMPolyTimeMap dhcCrossArcsAccEncodedType
        (EncodedType.prod dhcIndexedIncidenceListEncodedType edgeListStructuredEncodedType)
        (fun acc : dhcCrossArcsAccEncodedType.Carrier => acc.2) := by
    simpa [dhcCrossArcsAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod dhcIndexedIncidenceListEncodedType edgeListStructuredEncodedType)
  have hEdges :
      TMPolyTimeMap dhcCrossArcsAccEncodedType edgeListStructuredEncodedType
        (fun acc : dhcCrossArcsAccEncodedType.Carrier => acc.2.2) := by
    have hComp := TMPolyTimeMap.comp hTail hAccTail
    simpa [Function.comp] using hComp
  have hComp := TMPolyTimeMap.comp hEdges dhcCrossArcsFold_tm_polytime
  simpa [Function.comp, dhcCrossArcsFoldResult] using hComp

theorem dhcCrossArcsExecutableFromIndexed_tm_polytime :
    TMPolyTimeMap dhcIndexedIncidenceListWithBudgetEncodedType
      edgeListStructuredEncodedType
      dhcCrossArcsExecutableFromIndexed := by
  have hComp :=
    TMPolyTimeMap.comp dhcCrossArcsFoldResult_tm_polytime
      dhcCrossArcsInstructions_tm_polytime
  simpa [Function.comp, dhcCrossArcsExecutableFromIndexed] using hComp

theorem dhcCrossArcsFold_map_invariant
    (budget : Nat) (source : List ((Nat × Nat) × Nat)) (xs : List ((Nat × Nat) × Nat))
    (out : List (Nat × Nat)) :
    (xs.map Sum.inr).foldl
        (fun acc instr => dhcCrossArcsFoldStep (acc, instr))
        (budget, (source, out)) =
      (budget,
        (source,
          out ++
            (xs.map fun left => dhcCrossRowArcsExecutable (budget, (left, source))).flatten)) := by
  induction xs generalizing out with
  | nil =>
      change (budget, (source, out)) =
        (budget, (source, out ++ ([] : List (Nat × Nat))))
      simp
  | cons left xs ih =>
      change
        (xs.map Sum.inr).foldl
            (fun acc instr => dhcCrossArcsFoldStep (acc, instr))
            (dhcCrossArcsFoldStep ((budget, (source, out)), Sum.inr left)) =
          (budget,
            (source,
              out ++
                (dhcCrossRowArcsExecutable (budget, (left, source)) ::
                  xs.map fun left => dhcCrossRowArcsExecutable (budget, (left, source))).flatten))
      rw [show dhcCrossArcsFoldStep ((budget, (source, out)), Sum.inr left) =
          (budget,
            (source, out ++ dhcCrossRowArcsExecutable (budget, (left, source)))) by
        rfl]
      calc
        (xs.map Sum.inr).foldl
            (fun acc instr => dhcCrossArcsFoldStep (acc, instr))
            (budget,
              (source, out ++ dhcCrossRowArcsExecutable (budget, (left, source))))
            =
          (budget,
            (source,
              (out ++ dhcCrossRowArcsExecutable (budget, (left, source))) ++
                (xs.map fun left => dhcCrossRowArcsExecutable (budget, (left, source))).flatten)) :=
            ih (out ++ dhcCrossRowArcsExecutable (budget, (left, source)))
        _ =
          (budget,
            (source,
              out ++
                (dhcCrossRowArcsExecutable (budget, (left, source)) ::
                  xs.map fun left => dhcCrossRowArcsExecutable (budget, (left, source))).flatten)) := by
            simp [List.append_assoc]

theorem dhcCrossArcsExecutableFromIndexed_eq
    (p : dhcIndexedIncidenceListWithBudgetRaw) :
    dhcCrossArcsExecutableFromIndexed p =
      dhcCrossArcsFromIndexedBlocks p := by
  rcases p with ⟨budget, xs⟩
  rw [dhcCrossArcsExecutableFromIndexed, dhcCrossArcsFoldResult,
    dhcCrossArcsInstructions]
  rw [List.foldl_cons]
  rw [show dhcCrossArcsFoldStep (dhcCrossArcsFoldInit, Sum.inl (budget, xs)) =
      (budget, (xs, ([] : List (Nat × Nat)))) by
    rfl]
  change
    (List.foldl (fun acc instr => dhcCrossArcsFoldStep (acc, instr))
      (budget, (xs, [])) (List.map Sum.inr xs)).2.2 =
      dhcCrossArcsFromIndexedBlocks (budget, xs)
  have hFold :=
    congrArg (fun acc : dhcCrossArcsAccEncodedType.Carrier => acc.2.2)
      (dhcCrossArcsFold_map_invariant budget xs xs ([] : List (Nat × Nat)))
  calc
    (List.foldl (fun acc instr => dhcCrossArcsFoldStep (acc, instr))
        (budget, (xs, [])) (List.map Sum.inr xs)).2.2
        =
      (xs.map fun left => dhcCrossRowArcsExecutable (budget, (left, xs))).flatten := by
        simpa using hFold
    _ = dhcCrossArcsFromIndexedBlocks (budget, xs) := by
        simp [dhcCrossArcsFromIndexedBlocks, dhcCrossRowArcsExecutable_eq]

/-! ### Bridge from carried indices back to source-list/textbook semantics -/

def dhcCrossArcPairBlockFromSourceList
    (budget : Nat) (source : List (Nat × Nat)) (pair : (Nat × Nat) × (Nat × Nat)) :
    List (Nat × Nat) :=
  [ (dhcIncidenceVertexFromSourceList budget source pair.1 0,
      dhcIncidenceVertexFromSourceList budget source pair.2 0)
  , (dhcIncidenceVertexFromSourceList budget source pair.1 1,
      dhcIncidenceVertexFromSourceList budget source pair.2 1)
  ]

theorem list_flatten_map_if_bool_filter {α β : Type*}
    (xs : List α) (p : α → Bool) (f : α → List β) :
    (xs.map fun x => if p x then f x else []).flatten =
      ((xs.filter p).map f).flatten := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      cases h : p x <;> simp [h, ih]

theorem list_product_map_fst {α β : Type*}
    (xs ys : List (α × β)) :
    (xs.product ys).map (fun pair => (pair.1.1, pair.2.1)) =
      (xs.map Prod.fst).product (ys.map Prod.fst) := by
  induction xs with
  | nil =>
      simp [List.product]
  | cons x xs ih =>
      simp [List.product, List.map_append, List.map_map]
      have hHead :
          List.map ((fun pair => (pair.1.1, pair.2.1)) ∘ Prod.mk x) ys =
            List.map (Prod.mk x.1 ∘ Prod.fst) ys := by
        apply List.map_congr_left
        intro y _hy
        rfl
      have hTail :
          List.map (fun pair => (pair.1.1, pair.2.1))
              (List.flatMap (fun a => List.map (Prod.mk a) ys) xs) =
            List.flatMap (fun a => List.map (Prod.mk a ∘ Prod.fst) ys)
              (List.map Prod.fst xs) := by
        simpa [List.product] using ih
      rw [hHead, hTail]

theorem list_flatten_product_map_fst {α β γ : Type*}
    (xs ys : List (α × β)) (f : α × α → List γ) :
    ((xs.product ys).map fun pair => f (pair.1.1, pair.2.1)).flatten =
      (((xs.map Prod.fst).product (ys.map Prod.fst)).map f).flatten := by
  simpa [List.map_map, Function.comp] using
    congrArg (fun zs : List (α × α) => (zs.map f).flatten)
      (list_product_map_fst xs ys)

theorem dhcZipIdx_mem_idx_eq
    {source : List (Nat × Nat)} (hNodup : source.Nodup)
    {ui : Nat × Nat} {idx : Nat}
    (hMem : (ui, idx) ∈ source.zipIdx) :
    idx = source.idxOf ui := by
  rcases List.mem_zipIdx' hMem with ⟨hIdxLt, hGet⟩
  have hIdxOf := hNodup.idxOf_getElem idx hIdxLt
  have hIdxOf' : source.idxOf ui = idx := by
    simpa [hGet.symm] using hIdxOf
  exact hIdxOf'.symm

theorem dhcCrossArcBlockFromIndexed_eq_sourceListBlock_of_zipIdx_mem
    (budget : Nat) (source : List (Nat × Nat)) (hNodup : source.Nodup)
    {left right : (Nat × Nat) × Nat}
    (hLeft : left ∈ source.zipIdx) (hRight : right ∈ source.zipIdx) :
    dhcCrossArcBlockFromIndexed (budget, (left, right)) =
      if decide (left.1.2 = right.1.2 ∧ left.1.1 ≠ right.1.1) then
        dhcCrossArcPairBlockFromSourceList budget source (left.1, right.1)
      else [] := by
  have hLeftIdx : left.2 = source.idxOf left.1 :=
    dhcZipIdx_mem_idx_eq hNodup hLeft
  have hRightIdx : right.2 = source.idxOf right.1 :=
    dhcZipIdx_mem_idx_eq hNodup hRight
  by_cases hPred : left.1.2 = right.1.2 ∧ left.1.1 ≠ right.1.1
  · have hKeep : dhcCrossArcCandidateBool (left, right) = true :=
      (dhcCrossArcCandidateBool_eq_true_iff (left, right)).2 hPred
    simp [dhcCrossArcBlockFromIndexed, hKeep, hPred, dhcCrossArcPairBlock,
      dhcCrossArcPairBlockFromSourceList, dhcCrossArcFromIndexedBitRaw,
      dhcIncidenceVertexFromSourceList, dhcCrossArcLeftIncidenceIndex,
      dhcCrossArcRightIncidenceIndex, hLeftIdx, hRightIdx]
  · have hKeep : dhcCrossArcCandidateBool (left, right) = false := by
      cases h : dhcCrossArcCandidateBool (left, right)
      · rfl
      · exact False.elim (hPred ((dhcCrossArcCandidateBool_eq_true_iff (left, right)).1 h))
    simp [dhcCrossArcBlockFromIndexed, hKeep, hPred]

theorem dhcCrossRowsFromIndexed_eq_product
    (budget : Nat) (lefts rights : List ((Nat × Nat) × Nat)) :
    (lefts.map fun left => dhcCrossRowArcsFromIndexed budget left rights).flatten =
      ((lefts.product rights).map fun pair =>
        dhcCrossArcBlockFromIndexed (budget, pair)).flatten := by
  induction lefts with
  | nil =>
      simp
  | cons left xs ih =>
      calc
        ((left :: xs).map fun left => dhcCrossRowArcsFromIndexed budget left rights).flatten
            =
          dhcCrossRowArcsFromIndexed budget left rights ++
            (xs.map fun left => dhcCrossRowArcsFromIndexed budget left rights).flatten := by
            simp
        _ =
          (rights.map fun right => dhcCrossArcBlockFromIndexed (budget, (left, right))).flatten ++
            ((xs.product rights).map fun pair =>
              dhcCrossArcBlockFromIndexed (budget, pair)).flatten := by
            rw [ih]
            simp [dhcCrossRowArcsFromIndexed]
        _ =
          (((left :: xs).product rights).map fun pair =>
            dhcCrossArcBlockFromIndexed (budget, pair)).flatten := by
            simp [List.product, List.map_append, List.flatten_append]
            apply congrArg List.flatten
            apply List.map_congr_left
            intro right _hright
            rfl

theorem dhcCrossArcsFromIndexedBlocks_eq_product
    (budget : Nat) (xs : List ((Nat × Nat) × Nat)) :
    dhcCrossArcsFromIndexedBlocks (budget, xs) =
      ((xs.product xs).map fun pair => dhcCrossArcBlockFromIndexed (budget, pair)).flatten := by
  simpa [dhcCrossArcsFromIndexedBlocks] using
    dhcCrossRowsFromIndexed_eq_product budget xs xs

theorem dhcCrossArcsFromIndexedBlocks_zipIdx_eq_sourceList
    (budget : Nat) (source : List (Nat × Nat)) (hNodup : source.Nodup) :
    dhcCrossArcsFromIndexedBlocks (budget, source.zipIdx) =
      dhcCrossArcsFromSourceList budget source := by
  rw [dhcCrossArcsFromIndexedBlocks_eq_product]
  have hBlockMap :
      ((source.zipIdx.product source.zipIdx).map
          fun pair => dhcCrossArcBlockFromIndexed (budget, pair)).flatten =
        ((source.zipIdx.product source.zipIdx).map
          fun pair =>
            if decide (pair.1.1.2 = pair.2.1.2 ∧ pair.1.1.1 ≠ pair.2.1.1) then
              dhcCrossArcPairBlockFromSourceList budget source (pair.1.1, pair.2.1)
            else []).flatten := by
    apply congrArg List.flatten
    apply List.map_congr_left
    intro pair hPair
    have hLeft : pair.1 ∈ source.zipIdx := (List.mem_product.mp hPair).1
    have hRight : pair.2 ∈ source.zipIdx := (List.mem_product.mp hPair).2
    simpa using
      dhcCrossArcBlockFromIndexed_eq_sourceListBlock_of_zipIdx_mem
        budget source hNodup hLeft hRight
  rw [hBlockMap]
  rw [show
      ((source.zipIdx.product source.zipIdx).map
          fun pair =>
            if decide (pair.1.1.2 = pair.2.1.2 ∧ pair.1.1.1 ≠ pair.2.1.1) then
              dhcCrossArcPairBlockFromSourceList budget source (pair.1.1, pair.2.1)
            else []).flatten =
        ((source.zipIdx.product source.zipIdx).map
          fun pair =>
            (fun q : (Nat × Nat) × (Nat × Nat) =>
              if decide (q.1.2 = q.2.2 ∧ q.1.1 ≠ q.2.1) then
                dhcCrossArcPairBlockFromSourceList budget source q
              else []) (pair.1.1, pair.2.1)).flatten by
    rfl]
  rw [list_flatten_product_map_fst (source.zipIdx) (source.zipIdx)
    (fun q : (Nat × Nat) × (Nat × Nat) =>
      if decide (q.1.2 = q.2.2 ∧ q.1.1 ≠ q.2.1) then
        dhcCrossArcPairBlockFromSourceList budget source q
      else [])]
  have hMapFst : (source.zipIdx.map Prod.fst) = source := by
    simp
  rw [hMapFst]
  rw [list_flatten_map_if_bool_filter]
  change
    (List.map (fun pair => dhcCrossArcPairBlockFromSourceList budget source pair)
        (List.filter
          (fun q => decide (q.1.2 = q.2.2 ∧ q.1.1 ≠ q.2.1))
          (source.product source))).flatten =
      dhcCrossArcsFromSourceList budget source
  simp [dhcCrossArcsFromSourceList, dhcCrossArcPairBlockFromSourceList]

theorem dhcCrossArcsExecutableFromInput_eq_dhcCrossArcsFromInput
    (I : VertexCoverInput) :
    dhcCrossArcsExecutableFromInput I = dhcCrossArcsFromInput I := by
  rw [dhcCrossArcsExecutableFromInput, dhcCrossArcsExecutableFromIndexed_eq,
    dhcCrossArcsFromInput, dhcCrossArcsFromIndexed]
  rw [dhcIndexedSourceIncidencesFromInput,
    dhcIndexedSourceIncidencesFromInput_eq_zipIdx_sourceIncidences]
  simpa [dhcSourceIncidencesFromIndexed] using
    dhcCrossArcsFromIndexedBlocks_zipIdx_eq_sourceList I.k (sourceIncidences I)
      (sourceIncidences_nodup I)

theorem dhcCrossArcsExecutableFromInput_eq_textbookCrossArcs
    (I : VertexCoverInput) :
    dhcCrossArcsExecutableFromInput I = textbookCrossArcs I := by
  rw [dhcCrossArcsExecutableFromInput_eq_dhcCrossArcsFromInput,
    dhcCrossArcsFromInput_eq_textbookCrossArcs]

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
