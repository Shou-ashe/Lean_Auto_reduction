/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.FoldTM

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! ### Outer row scan over all source vertices -/

def dhcRowsAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod edgeListStructuredEncodedType
      (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType))

def dhcRowsInitPayloadEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat edgeListStructuredEncodedType

def dhcRowsInstructionEncodedType : EncodedType :=
  EncodedType.sum dhcRowsInitPayloadEncodedType EncodedType.nat

def dhcRowsInstructionListEncodedType : EncodedType :=
  EncodedType.list dhcRowsInstructionEncodedType

def dhcRowsInputEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat edgeListStructuredEncodedType

def dhcRowsFoldInit : dhcRowsAccEncodedType.Carrier :=
  ((0 : Nat),
    (([] : List (Nat × Nat)),
      ((0 : Nat), ([] : List ((Nat × Nat) × Nat)))))

def dhcRowsFoldLeftStep
    (p : dhcRowsInitPayloadEncodedType.Carrier) :
    dhcRowsAccEncodedType.Carrier :=
  (p.1, (p.2, ((0 : Nat), ([] : List ((Nat × Nat) × Nat)))))

def dhcRowsFoldRightStep
    (p : dhcRowsAccEncodedType.Carrier × Nat) :
    dhcRowsAccEncodedType.Carrier :=
  let acc := p.1
  let u := p.2
  let row := dhcRowScanResult acc.1 u acc.2.2.1 acc.2.1
  (acc.1,
    (acc.2.1,
      (row.2.2.2.1,
        (show List ((Nat × Nat) × Nat) from acc.2.2.2) ++
          (show List ((Nat × Nat) × Nat) from row.2.2.2.2))))

def dhcRowsFoldStep
    (p : dhcRowsAccEncodedType.Carrier × dhcRowsInstructionEncodedType.Carrier) :
    dhcRowsAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl payload => dhcRowsFoldLeftStep payload
  | Sum.inr u => dhcRowsFoldRightStep (p.1, u)

def dhcRowsInstructions (vertices : Nat) (edges : List (Nat × Nat)) :
    dhcRowsInstructionListEncodedType.Carrier :=
  Sum.inl (vertices, edges) :: (List.range vertices).map Sum.inr

def dhcRowsFoldResult (vertices : Nat) (edges : List (Nat × Nat)) :
    dhcRowsAccEncodedType.Carrier :=
  (dhcRowsInstructions vertices edges).foldl
    (fun acc instr => dhcRowsFoldStep (acc, instr))
    dhcRowsFoldInit

def dhcIndexedSourceIncidencesFromGraphData
    (p : dhcRowsInputEncodedType.Carrier) : List ((Nat × Nat) × Nat) :=
  (dhcRowsFoldResult p.1 p.2).2.2.2

theorem dhcRowsFold_map_inr
    (us : List Nat) (acc : dhcRowsAccEncodedType.Carrier) :
    (us.map Sum.inr).foldl
        (fun acc instr => dhcRowsFoldStep (acc, instr)) acc =
      us.foldl (fun acc u => dhcRowsFoldRightStep (acc, u)) acc := by
  induction us generalizing acc with
  | nil =>
      rfl
  | cons u us ih =>
      simpa [dhcRowsFoldStep] using ih (dhcRowsFoldRightStep (acc, u))

theorem dhcRowsFoldResult_eq_rangeFold (vertices : Nat) (edges : List (Nat × Nat)) :
    dhcRowsFoldResult vertices edges =
      (List.range vertices).foldl
        (fun acc u => dhcRowsFoldRightStep (acc, u))
        (vertices, (edges, ((0 : Nat), ([] : List ((Nat × Nat) × Nat))))) := by
  unfold dhcRowsFoldResult dhcRowsInstructions
  rw [List.foldl_cons]
  have h :=
    dhcRowsFold_map_inr (List.range vertices)
      (dhcRowsFoldStep (dhcRowsFoldInit, Sum.inl (vertices, edges)))
  simpa [dhcRowsFoldStep, dhcRowsFoldLeftStep, dhcRowsFoldInit] using h

theorem dhcIndexedSourceIncidencesFromGraphData_eq_rangeFold
    (vertices : Nat) (edges : List (Nat × Nat)) :
    dhcIndexedSourceIncidencesFromGraphData (vertices, edges) =
      ((List.range vertices).foldl
        (fun acc u => dhcRowsFoldRightStep (acc, u))
        (vertices, (edges, ((0 : Nat), ([] : List ((Nat × Nat) × Nat)))))).2.2.2 := by
  simp [dhcIndexedSourceIncidencesFromGraphData, dhcRowsFoldResult_eq_rangeFold]

theorem dhcRowsFoldLeftStep_tm_polytime :
    TMPolyTimeMap
      dhcRowsInitPayloadEncodedType
      dhcRowsAccEncodedType
      dhcRowsFoldLeftStep := by
  let X := dhcRowsInitPayloadEncodedType
  have hVertices : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcRowsInitPayloadEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat edgeListStructuredEncodedType
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcRowsInitPayloadEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat edgeListStructuredEncodedType
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hEmpty :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType
        (fun _ : X.Carrier => ([] : List ((Nat × Nat) × Nat))) :=
    TMPolyTimeMap.const X dhcIndexedIncidenceListEncodedType []
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
        (fun _ : X.Carrier => ((0 : Nat), ([] : List ((Nat × Nat) × Nat)))) :=
    TMPolyTimeMap.prod_mk hZero hEmpty
  have hEdgesTail :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType
          (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType))
        (fun p : X.Carrier =>
          (p.2, ((0 : Nat), ([] : List ((Nat × Nat) × Nat))))) :=
    TMPolyTimeMap.prod_mk hEdges hTail
  have hOut := TMPolyTimeMap.prod_mk hVertices hEdgesTail
  simpa [dhcRowsFoldLeftStep, dhcRowsAccEncodedType, dhcRowsInitPayloadEncodedType, X]
    using hOut

theorem dhcRowsFoldRightStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcRowsAccEncodedType EncodedType.nat)
      dhcRowsAccEncodedType
      dhcRowsFoldRightStep := by
  let X := EncodedType.prod dhcRowsAccEncodedType EncodedType.nat
  have hAcc : TMPolyTimeMap X dhcRowsAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst dhcRowsAccEncodedType EncodedType.nat
  have hU : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd dhcRowsAccEncodedType EncodedType.nat
  have hVertices : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst :=
      TMPolyTimeMap.fst EncodedType.nat
        (EncodedType.prod edgeListStructuredEncodedType
          (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType))
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, dhcRowsAccEncodedType, X] using hComp
  have hTail :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType
          (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType))
        (fun p : X.Carrier => p.1.2) := by
    have hSnd :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod edgeListStructuredEncodedType
          (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType))
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, dhcRowsAccEncodedType, X] using hComp
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.1.2.1) := by
    have hFst :=
      TMPolyTimeMap.fst edgeListStructuredEncodedType
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
    have hComp := TMPolyTimeMap.comp hFst hTail
    simpa [Function.comp, X] using hComp
  have hState :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
        (fun p : X.Carrier => p.1.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd edgeListStructuredEncodedType
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hTail
    simpa [Function.comp, X] using hComp
  have hNext : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat dhcIndexedIncidenceListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hState
    simpa [Function.comp, X] using hComp
  have hOut :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType
        (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat dhcIndexedIncidenceListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hState
    simpa [Function.comp, X] using hComp
  have hRowInput :
      TMPolyTimeMap X dhcRowScanInputEncodedType
        (fun p : X.Carrier => (p.1.1, (p.2, (p.1.2.2.1, p.1.2.1)))) :=
    TMPolyTimeMap.prod_mk hVertices (TMPolyTimeMap.prod_mk hU (TMPolyTimeMap.prod_mk hNext hEdges))
  have hRow :
      TMPolyTimeMap X dhcRowScanAccEncodedType
        (fun p : X.Carrier => dhcRowScanResult p.1.1 p.2 p.1.2.2.1 p.1.2.1) := by
    have hComp := TMPolyTimeMap.comp dhcRowScanFromInput_tm_polytime hRowInput
    simpa [Function.comp, dhcRowScanFromInput, dhcRowScanResult, X] using hComp
  have hRowState :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
        (fun p : X.Carrier =>
          (dhcRowScanResult p.1.1 p.2 p.1.2.2.1 p.1.2.1).2.2.2) := by
    have hSnd₁ :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat
            (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)))
    have hSnd₂ :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType))
    have hSnd₃ :=
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
    have hComp₁ := TMPolyTimeMap.comp hSnd₁ hRow
    have hComp₂ := TMPolyTimeMap.comp hSnd₂ hComp₁
    have hComp₃ := TMPolyTimeMap.comp hSnd₃ hComp₂
    simpa [Function.comp, dhcRowScanAccEncodedType, X] using hComp₃
  have hRowNext :
      TMPolyTimeMap X EncodedType.nat
        (fun p : X.Carrier =>
          (dhcRowScanResult p.1.1 p.2 p.1.2.2.1 p.1.2.1).2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat dhcIndexedIncidenceListEncodedType
    have hComp := TMPolyTimeMap.comp hFst hRowState
    simpa [Function.comp, X] using hComp
  have hRowOut :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType
        (fun p : X.Carrier =>
          (dhcRowScanResult p.1.1 p.2 p.1.2.2.1 p.1.2.1).2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat dhcIndexedIncidenceListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hRowState
    simpa [Function.comp, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod dhcIndexedIncidenceListEncodedType dhcIndexedIncidenceListEncodedType)
        (fun p : X.Carrier =>
          (p.1.2.2.2,
            (dhcRowScanResult p.1.1 p.2 p.1.2.2.1 p.1.2.1).2.2.2.2)) :=
    TMPolyTimeMap.prod_mk hOut hRowOut
  have hAppend :
      TMPolyTimeMap X dhcIndexedIncidenceListEncodedType
        (fun p : X.Carrier =>
          (show List ((Nat × Nat) × Nat) from p.1.2.2.2) ++
            (show List ((Nat × Nat) × Nat) from
              (dhcRowScanResult p.1.1 p.2 p.1.2.2.1 p.1.2.1).2.2.2.2)) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append dhcIndexedIncidenceEncodedType) hAppendInput
    simpa [Function.comp, dhcIndexedIncidenceListEncodedType, X] using hComp
  have hNewState :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
        (fun p : X.Carrier =>
          ((dhcRowScanResult p.1.1 p.2 p.1.2.2.1 p.1.2.1).2.2.2.1,
            (show List ((Nat × Nat) × Nat) from p.1.2.2.2) ++
              (show List ((Nat × Nat) × Nat) from
                (dhcRowScanResult p.1.1 p.2 p.1.2.2.1 p.1.2.1).2.2.2.2))) :=
    TMPolyTimeMap.prod_mk hRowNext hAppend
  have hEdgesState :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType
          (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType))
        (fun p : X.Carrier =>
          (p.1.2.1,
            ((dhcRowScanResult p.1.1 p.2 p.1.2.2.1 p.1.2.1).2.2.2.1,
              (show List ((Nat × Nat) × Nat) from p.1.2.2.2) ++
                (show List ((Nat × Nat) × Nat) from
                  (dhcRowScanResult p.1.1 p.2 p.1.2.2.1 p.1.2.1).2.2.2.2)))) :=
    TMPolyTimeMap.prod_mk hEdges hNewState
  have hResult := TMPolyTimeMap.prod_mk hVertices hEdgesState
  simpa [dhcRowsFoldRightStep, dhcRowsAccEncodedType, X] using hResult

theorem dhcRowsFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod dhcRowsAccEncodedType dhcRowsInstructionEncodedType)
      dhcRowsAccEncodedType
      dhcRowsFoldStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      dhcRowsAccEncodedType dhcRowsInitPayloadEncodedType EncodedType.nat
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim dhcRowsFoldLeftStep_tm_polytime
      dhcRowsFoldRightStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

theorem dhcRowsInstructions_tm_polytime :
    TMPolyTimeMap
      dhcRowsInputEncodedType
      dhcRowsInstructionListEncodedType
      (fun p : dhcRowsInputEncodedType.Carrier => dhcRowsInstructions p.1 p.2) := by
  let X := dhcRowsInputEncodedType
  have hVertices : TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, dhcRowsInputEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat edgeListStructuredEncodedType
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, dhcRowsInputEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat edgeListStructuredEncodedType
  have hInitPayload :
      TMPolyTimeMap X dhcRowsInitPayloadEncodedType
        (fun p : X.Carrier => (p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hVertices hEdges
  have hInit :
      TMPolyTimeMap X dhcRowsInstructionEncodedType
        (fun p : X.Carrier => Sum.inl (p.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl dhcRowsInitPayloadEncodedType EncodedType.nat)
      hInitPayload
    simpa [Function.comp, dhcRowsInstructionEncodedType, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X dhcRowsInstructionListEncodedType
        (fun p : X.Carrier => [Sum.inl (p.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton dhcRowsInstructionEncodedType) hInit
    simpa [Function.comp, dhcRowsInstructionListEncodedType, X] using hComp
  have hRange :
      TMPolyTimeMap X (EncodedType.list EncodedType.nat)
        (fun p : X.Carrier => List.range p.1) := by
    have hComp := TMPolyTimeMap.comp natRange_tm_polytime hVertices
    simpa [Function.comp, X] using hComp
  have hRowInstruction :
      TMPolyTimeMap EncodedType.nat dhcRowsInstructionEncodedType
        (fun u : Nat => Sum.inr u) := by
    simpa [dhcRowsInstructionEncodedType] using
      TMPolyTimeMap.inr dhcRowsInitPayloadEncodedType EncodedType.nat
  have hRows :
      TMPolyTimeMap X dhcRowsInstructionListEncodedType
        (fun p : X.Carrier => (List.range p.1).map Sum.inr) := by
    have hMap := TMPolyTimeMap.list_map hRowInstruction
    have hComp := TMPolyTimeMap.comp hMap hRange
    simpa [Function.comp, dhcRowsInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod dhcRowsInstructionListEncodedType dhcRowsInstructionListEncodedType)
        (fun p : X.Carrier => ([Sum.inl (p.1, p.2)], (List.range p.1).map Sum.inr)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hRows
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append dhcRowsInstructionEncodedType) hAppendInput
  simpa [Function.comp, dhcRowsInstructions, dhcRowsInstructionListEncodedType, X] using hAppend

/-! ### Typed outer fold with reachable accumulator bounds -/

abbrev dhcRowsAccRaw :=
  Nat × (List (Nat × Nat) × (Nat × List ((Nat × Nat) × Nat)))

def dhcRowsIndexedIncidenceBound (N processed : Nat) (x : ((Nat × Nat) × Nat)) :
    Prop :=
  x.1.1 ≤ N ∧ x.1.2 ≤ N ∧ x.2 ≤ processed * N

def dhcRowsAccBound (N processed : Nat) (acc : dhcRowsAccRaw) :
    Prop :=
  acc.1 ≤ N ∧
    edgeListStructuredEncodedType.inputSize acc.2.1 ≤ N ∧
      acc.2.2.1 ≤ processed * N ∧
        (∀ x ∈ acc.2.2.2, dhcRowsIndexedIncidenceBound N processed x) ∧
          acc.2.2.2.length ≤ processed * N

theorem dhcRowsIndexedIncidenceBound_mono {N processed processed' : Nat}
    {x : ((Nat × Nat) × Nat)}
    (hProcessed : processed ≤ processed')
    (hBound : dhcRowsIndexedIncidenceBound N processed x) :
    dhcRowsIndexedIncidenceBound N processed' x := by
  rcases hBound with ⟨hU, hEdgeIndex, hNextIndex⟩
  exact ⟨hU, hEdgeIndex, by nlinarith⟩

theorem dhcIndexedRowFromEdgeIndices_length
    (u nextIndex : Nat) (indices : List Nat) :
    (dhcIndexedRowFromEdgeIndices u nextIndex indices).length = indices.length := by
  induction indices generalizing nextIndex with
  | nil =>
      simp [dhcIndexedRowFromEdgeIndices]
  | cons i is ih =>
      simp [dhcIndexedRowFromEdgeIndices, ih]

theorem dhcIndexedRowFromEdgeIndices_mem_bound {N processed u nextIndex : Nat}
    {indices : List Nat}
    (hU : u ≤ N)
    (hIndices : ∀ i ∈ indices, i ≤ N)
    (hNext : nextIndex + indices.length ≤ processed * N) :
    ∀ x ∈ dhcIndexedRowFromEdgeIndices u nextIndex indices,
      dhcRowsIndexedIncidenceBound N processed x := by
  induction indices generalizing nextIndex with
  | nil =>
      intro x hx
      simp [dhcIndexedRowFromEdgeIndices] at hx
  | cons i is ih =>
      intro x hx
      simp [dhcIndexedRowFromEdgeIndices] at hx
      rcases hx with hx | hx
      · subst x
        have hi : i ≤ N := hIndices i (by simp)
        exact ⟨hU, hi, by omega⟩
      · have hTailIndices : ∀ j ∈ is, j ≤ N := by
          intro j hj
          exact hIndices j (by simp [hj])
        have hTailNext : nextIndex + 1 + is.length ≤ processed * N := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hNext
        exact ih hTailIndices hTailNext x hx

theorem dhcRowsFoldStep_bound {N processed : Nat}
    {acc : dhcRowsAccRaw}
    {instr : dhcRowsInstructionEncodedType.Carrier}
    (hAcc : dhcRowsAccBound N processed acc)
    (hInstr : dhcRowsInstructionEncodedType.inputSize instr ≤ N) :
    dhcRowsAccBound N (processed + 1) (dhcRowsFoldStep (acc, instr)) := by
  rcases acc with ⟨vertices, edges, nextIndex, out⟩
  rcases hAcc with ⟨hVertices, hEdgesSize, hNextIndex, hOut, hOutLen⟩
  change vertices ≤ N at hVertices
  change edgeListStructuredEncodedType.inputSize edges ≤ N at hEdgesSize
  change nextIndex ≤ processed * N at hNextIndex
  change (∀ x ∈ out, dhcRowsIndexedIncidenceBound N processed x) at hOut
  change out.length ≤ processed * N at hOutLen
  cases instr with
  | inl payload =>
      rcases payload with ⟨vertices', edges'⟩
      change Nat at vertices'
      have hVertices' : vertices' ≤ N := by
        simp [dhcRowsInstructionEncodedType, dhcRowsInitPayloadEncodedType,
          EncodedType.inputSize, EncodedType.sum, EncodedType.prod, EncodedType.nat] at hInstr
        omega
      have hEdges' : edgeListStructuredEncodedType.inputSize edges' ≤ N := by
        change (edgeListStructuredEncodedType.encode edges').length ≤ N
        simp [dhcRowsInstructionEncodedType, dhcRowsInitPayloadEncodedType,
          EncodedType.inputSize, EncodedType.sum, EncodedType.prod, EncodedType.nat] at hInstr
        omega
      change dhcRowsAccBound N (processed + 1)
        (vertices', (edges', ((0 : Nat), ([] : List ((Nat × Nat) × Nat)))))
      simp [dhcRowsAccBound, hVertices', hEdges']
  | inr u =>
      change Nat at u
      let hits := edges.findIdxs (fun edge => dhcSourceIncidentBool (vertices, (u, edge))) 0
      have hU : u ≤ N := by
        simp [dhcRowsInstructionEncodedType, EncodedType.inputSize, EncodedType.sum,
          EncodedType.nat] at hInstr
        omega
      have hEdgesLen : edges.length ≤ N := by
        have hLen := SetCovering.incidentEncodedList_length_le_inputSize
          edgeStructuredEncodedType edges
        have hLen' : edges.length ≤ edgeListStructuredEncodedType.inputSize edges := by
          simpa [edgeListStructuredEncodedType] using hLen
        exact hLen'.trans hEdgesSize
      have hHitsLenEdges : hits.length ≤ edges.length := by
        dsimp [hits]
        simpa using
          (List.countP_le_length (l := edges)
            (p := fun edge : Nat × Nat => dhcSourceIncidentBool (vertices, (u, edge))))
      have hHitsLenN : hits.length ≤ N := hHitsLenEdges.trans hEdgesLen
      have hHitIndex : ∀ i ∈ hits, i ≤ N := by
        intro i hi
        have hiLt : i < edges.length := by
          dsimp [hits] at hi
          rcases (List.mem_findIdxs_iff_exists_getElem_pos (xs := edges)
              (p := fun edge : Nat × Nat => dhcSourceIncidentBool (vertices, (u, edge)))).1
              hi with
            ⟨hiLt, _hPred⟩
          exact hiLt
        omega
      have hNextNew : nextIndex + hits.length ≤ (processed + 1) * N := by
        nlinarith
      have hOutOld :
          ∀ x ∈ out, dhcRowsIndexedIncidenceBound N (processed + 1) x := by
        intro x hx
        exact dhcRowsIndexedIncidenceBound_mono (by omega) (hOut x hx)
      have hOutNew :
          ∀ x ∈ dhcIndexedRowFromEdgeIndices u nextIndex hits,
            dhcRowsIndexedIncidenceBound N (processed + 1) x :=
        dhcIndexedRowFromEdgeIndices_mem_bound hU hHitIndex hNextNew
      have hOutAppend :
          ∀ x ∈ out ++ dhcIndexedRowFromEdgeIndices u nextIndex hits,
            dhcRowsIndexedIncidenceBound N (processed + 1) x := by
        intro x hx
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact hOutOld x hx
        · exact hOutNew x hx
      have hOutLenNew :
          (out ++ dhcIndexedRowFromEdgeIndices u nextIndex hits).length ≤
            (processed + 1) * N := by
        rw [List.length_append, dhcIndexedRowFromEdgeIndices_length]
        nlinarith
      change dhcRowsAccBound N (processed + 1)
        (vertices,
          (edges,
            ((dhcRowScanResult vertices u nextIndex edges).2.2.2.1,
              out ++
                (show List ((Nat × Nat) × Nat) from
                  (dhcRowScanResult vertices u nextIndex edges).2.2.2.2))))
      rw [dhcRowScanResult_findIdxs]
      change dhcRowsAccBound N (processed + 1)
        (vertices, (edges,
          (nextIndex + hits.length, out ++ dhcIndexedRowFromEdgeIndices u nextIndex hits)))
      exact ⟨hVertices, hEdgesSize, hNextNew, hOutAppend, hOutLenNew⟩

theorem dhcRowsFold_bound_aux
    {N processed : Nat}
    (xs : List dhcRowsInstructionEncodedType.Carrier)
    (acc : dhcRowsAccRaw)
    (hAcc : dhcRowsAccBound N processed acc)
    (hLen : processed + xs.length ≤ N)
    (hInstr : ∀ instr ∈ xs, dhcRowsInstructionEncodedType.inputSize instr ≤ N) :
    dhcRowsAccBound N (processed + xs.length)
      (xs.foldl (fun acc instr => dhcRowsFoldStep (acc, instr)) acc) := by
  induction xs generalizing processed acc with
  | nil =>
      simpa using hAcc
  | cons instr xs ih =>
      have hStep := dhcRowsFoldStep_bound hAcc (hInstr instr (by simp))
      have hTailLen : (processed + 1) + xs.length ≤ N := by
        simp only [List.length_cons] at hLen
        omega
      have hTailInstr :
          ∀ instr ∈ xs, dhcRowsInstructionEncodedType.inputSize instr ≤ N := by
        intro instr hin
        exact hInstr instr (by simp [hin])
      have hTail :=
        ih (processed := processed + 1)
          (acc := dhcRowsFoldStep (acc, instr)) hStep hTailLen hTailInstr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hTail

theorem dhcRowsFold_bound_of_inputSize_le
    {N : Nat} (xs : List dhcRowsInstructionEncodedType.Carrier)
    (hSize : dhcRowsInstructionListEncodedType.inputSize xs ≤ N) :
    dhcRowsAccBound N xs.length
      (xs.foldl (fun acc instr => dhcRowsFoldStep (acc, instr)) dhcRowsFoldInit) := by
  have hInit : dhcRowsAccBound N 0 dhcRowsFoldInit := by
    have hNil : edgeListStructuredEncodedType.inputSize ([] : List (Nat × Nat)) = 0 := by
      exact EncodedType.inputSize_list_nil edgeStructuredEncodedType
    simp [dhcRowsAccBound, dhcRowsFoldInit, hNil]
  have hLen : 0 + xs.length ≤ N := by
    have hLenInput :=
      SetCovering.incidentEncodedList_length_le_inputSize dhcRowsInstructionEncodedType xs
    have hLenInput' : xs.length ≤ dhcRowsInstructionListEncodedType.inputSize xs := by
      simpa [dhcRowsInstructionListEncodedType] using hLenInput
    omega
  have hInstr :
      ∀ instr ∈ xs, dhcRowsInstructionEncodedType.inputSize instr ≤ N := by
    intro instr hin
    have hElem :=
      SetCovering.incidentEncodedList_element_inputSize_le
        (X := dhcRowsInstructionEncodedType) (x := instr) (xs := xs) hin
    have hElem' : dhcRowsInstructionEncodedType.inputSize instr ≤
        dhcRowsInstructionListEncodedType.inputSize xs := by
      simpa [dhcRowsInstructionListEncodedType] using hElem
    omega
  have h :=
    dhcRowsFold_bound_aux (N := N) (processed := 0) xs dhcRowsFoldInit
      hInit hLen hInstr
  simpa using h

noncomputable def dhcRowsFoldAccBoundPolynomial : Polynomial Nat :=
  Polynomial.C 100000 *
      (((Polynomial.X * Polynomial.X) * (Polynomial.X * Polynomial.X)) +
        ((Polynomial.X * Polynomial.X) * Polynomial.X) +
        (Polynomial.X * Polynomial.X) + Polynomial.X + Polynomial.C 1) +
    Polynomial.C 100000

@[simp] theorem dhcRowsFoldAccBoundPolynomial_eval (N : Nat) :
    dhcRowsFoldAccBoundPolynomial.eval N =
      100000 * (((N * N) * (N * N)) + ((N * N) * N) + (N * N) + N + 1) +
        100000 := by
  simp [dhcRowsFoldAccBoundPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X]

theorem dhcRowsIndexedIncidenceBound_inputSize_le {N processed : Nat}
    {x : ((Nat × Nat) × Nat)}
    (hBound : dhcRowsIndexedIncidenceBound N processed x)
    (hProcessed : processed ≤ N) :
    dhcIndexedIncidenceEncodedType.inputSize x ≤
      (N * N) + 2 * N + 5 := by
  rcases x with ⟨⟨u, edgeIndex⟩, nextIndex⟩
  rcases hBound with ⟨hU, hEdgeIndex, hNextIndex⟩
  have hNextN : nextIndex ≤ N * N := by nlinarith
  simp [dhcIndexedIncidenceEncodedType, vertexPairEncodedType, EncodedType.inputSize_prod,
    EncodedType.inputSize_nat]
  nlinarith

theorem dhcRowsAccBound_inputSize_le {N processed : Nat}
    {acc : dhcRowsAccRaw}
    (hAcc : dhcRowsAccBound N processed acc)
    (hProcessed : processed ≤ N) :
    dhcRowsAccEncodedType.inputSize acc ≤
      dhcRowsFoldAccBoundPolynomial.eval N := by
  rcases acc with ⟨vertices, edges, nextIndex, out⟩
  rcases hAcc with ⟨hVertices, hEdgesSize, hNextIndex, hOut, hOutLen⟩
  change vertices ≤ N at hVertices
  change edgeListStructuredEncodedType.inputSize edges ≤ N at hEdgesSize
  change nextIndex ≤ processed * N at hNextIndex
  change (∀ x ∈ out, dhcRowsIndexedIncidenceBound N processed x) at hOut
  change out.length ≤ processed * N at hOutLen
  have hNextN : nextIndex ≤ N * N := by nlinarith
  have hOutLenN : out.length ≤ N * N := by nlinarith
  have hOutSize :
      dhcIndexedIncidenceListEncodedType.inputSize out ≤
        out.length * ((N * N) + 2 * N + 6) := by
    have hElems :
        ∀ x ∈ out, dhcIndexedIncidenceEncodedType.inputSize x ≤
          (N * N) + 2 * N + 5 := by
      intro x hx
      exact dhcRowsIndexedIncidenceBound_inputSize_le (hOut x hx) hProcessed
    simpa [dhcIndexedIncidenceListEncodedType] using
      VertexCover.encodedList_inputSize_le_length_mul_bound
        dhcIndexedIncidenceEncodedType out ((N * N) + 2 * N + 5) hElems
  have hOutSizeN :
      dhcIndexedIncidenceListEncodedType.inputSize out ≤
        (N * N) * ((N * N) + 2 * N + 6) :=
    hOutSize.trans (Nat.mul_le_mul_right ((N * N) + 2 * N + 6) hOutLenN)
  have hOutSizeN' :
      dhcIndexedIncidenceEncodedType.list.inputSize out ≤
        (N * N) * ((N * N) + 2 * N + 6) := by
    simpa [dhcIndexedIncidenceListEncodedType] using hOutSizeN
  simp [dhcRowsAccEncodedType, dhcIndexedIncidenceListEncodedType,
    EncodedType.inputSize_prod, EncodedType.inputSize_nat]
  calc
    vertices + 1 + 1 +
        (edgeListStructuredEncodedType.inputSize edges + 1 +
          (nextIndex + 1 + 1 + dhcIndexedIncidenceEncodedType.list.inputSize out)) ≤
        N + 1 + 1 +
          (N + 1 +
            ((N * N) + 1 + 1 +
              (N * N) * ((N * N) + 2 * N + 6))) := by
          nlinarith
    _ ≤
        100000 * (((N * N) * (N * N)) + ((N * N) * N) + (N * N) + N + 1) +
          100000 := by
          nlinarith [sq_nonneg (N : Int)]

noncomputable def dhcRowsFoldTimePolynomial
    (hStep :
      Turing.TM2ComputableInPolyTime
        (EncodedType.prod dhcRowsAccEncodedType
          dhcRowsInstructionEncodedType).encode
        dhcRowsAccEncodedType.encode
        dhcRowsFoldStep) : Polynomial Nat :=
  TM2Programs.listFoldBoundedTimePolynomial hStep.tm dhcRowsFoldAccBoundPolynomial
    (hStep.time.comp
      (dhcRowsFoldAccBoundPolynomial + Polynomial.X + Polynomial.C 5))

theorem dhcRowsFold_tm_polytime :
    TMPolyTimeMap
      dhcRowsInstructionListEncodedType
      dhcRowsAccEncodedType
      (fun xs : List dhcRowsInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => dhcRowsFoldStep (acc, instr)) dhcRowsFoldInit) := by
  rcases dhcRowsFoldStep_tm_polytime with ⟨hStep⟩
  let time := dhcRowsFoldTimePolynomial hStep
  refine
    TMPolyTimeMap.list_foldl_typed
      dhcRowsInstructionEncodedType dhcRowsAccEncodedType
      dhcRowsFoldStep dhcRowsFoldInit hStep time ?_
  intro source
  let N := dhcRowsInstructionListEncodedType.inputSize source
  let B := dhcRowsFoldAccBoundPolynomial.eval N
  let T := hStep.time.eval (B + N + 5)
  let C := TM2Programs.listFoldBlockTimeCoeff hStep.tm B T
  have hSourceLenN : source.length ≤ N := by
    have hLen :=
      SetCovering.incidentEncodedList_length_le_inputSize dhcRowsInstructionEncodedType source
    simpa [N, dhcRowsInstructionListEncodedType] using hLen
  have hLoopAux :
      ∀ (pref rest : List dhcRowsInstructionEncodedType.Carrier),
        source = pref ++ rest →
          TM2Programs.listFoldTypedLoopTime
              dhcRowsInstructionEncodedType dhcRowsAccEncodedType
              dhcRowsFoldStep hStep
              (pref.foldl (fun acc instr => dhcRowsFoldStep (acc, instr)) dhcRowsFoldInit)
              rest ≤
            C * (EncodedType.list dhcRowsInstructionEncodedType).inputSize rest := by
    intro pref rest
    induction rest generalizing pref with
    | nil =>
        intro _hEq
        simp [TM2Programs.listFoldTypedLoopTime]
    | cons instr rest ih =>
        intro hEq
        have hInstrMemSource : instr ∈ source := by
          rw [hEq]
          simp
        have hInstrN : dhcRowsInstructionEncodedType.inputSize instr ≤ N := by
          have hElem :=
            SetCovering.incidentEncodedList_element_inputSize_le
              (X := dhcRowsInstructionEncodedType) (x := instr) (xs := source)
              hInstrMemSource
          simpa [N, dhcRowsInstructionListEncodedType] using hElem
        have hPrefixSize : dhcRowsInstructionListEncodedType.inputSize pref ≤ N := by
          have hEqSize :
              dhcRowsInstructionListEncodedType.inputSize source =
                dhcRowsInstructionListEncodedType.inputSize pref +
                  dhcRowsInstructionListEncodedType.inputSize (instr :: rest) := by
            rw [hEq]
            exact SetCovering.incidentEncodedList_inputSize_append
              dhcRowsInstructionEncodedType pref (instr :: rest)
          omega
        have hPrefixBound :=
          dhcRowsFold_bound_of_inputSize_le (N := N) pref hPrefixSize
        have hPrefixLenN : pref.length ≤ N := by
          have hLen :=
            SetCovering.incidentEncodedList_length_le_inputSize
              dhcRowsInstructionEncodedType pref
          have hLen' : pref.length ≤ dhcRowsInstructionListEncodedType.inputSize pref := by
            simpa [dhcRowsInstructionListEncodedType] using hLen
          omega
        have hAccSize :
            dhcRowsAccEncodedType.inputSize
                (pref.foldl (fun acc instr => dhcRowsFoldStep (acc, instr))
                  dhcRowsFoldInit) ≤ B := by
          simpa [B] using
            dhcRowsAccBound_inputSize_le hPrefixBound hPrefixLenN
        have hStepProcessed : pref.length + 1 ≤ N := by
          have hLenEq : source.length = pref.length + (instr :: rest).length := by
            rw [hEq, List.length_append]
          simp only [List.length_cons] at hLenEq
          omega
        have hStepBound :=
          dhcRowsFoldStep_bound hPrefixBound hInstrN
        have hStepSize :
            dhcRowsAccEncodedType.inputSize
                (dhcRowsFoldStep
                  (pref.foldl (fun acc instr => dhcRowsFoldStep (acc, instr))
                    dhcRowsFoldInit, instr)) ≤ B := by
          simpa [B] using
            dhcRowsAccBound_inputSize_le hStepBound hStepProcessed
        have hStepTime :
            hStep.time.eval
                ((EncodedType.prod dhcRowsAccEncodedType
                  dhcRowsInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => dhcRowsFoldStep (acc, instr))
                    dhcRowsFoldInit, instr)) ≤ T := by
          have hArg :
              (EncodedType.prod dhcRowsAccEncodedType
                dhcRowsInstructionEncodedType).inputSize
                  (pref.foldl (fun acc instr => dhcRowsFoldStep (acc, instr))
                    dhcRowsFoldInit, instr) ≤ B + N + 5 := by
            rw [EncodedType.inputSize_prod]
            change
              dhcRowsAccEncodedType.inputSize
                    (pref.foldl (fun acc instr => dhcRowsFoldStep (acc, instr))
                      dhcRowsFoldInit) +
                  1 + dhcRowsInstructionEncodedType.inputSize instr ≤ B + N + 5
            omega
          exact TM2Programs.polynomialNat_eval_mono hStep.time hArg
        have hBlock :
            TM2Programs.listFoldBlockTime hStep.tm
                (dhcRowsInstructionEncodedType.encode instr).length
                (dhcRowsAccEncodedType.encode
                  (pref.foldl (fun acc instr => dhcRowsFoldStep (acc, instr))
                    dhcRowsFoldInit)).length
                (dhcRowsAccEncodedType.encode
                  (dhcRowsFoldStep
                    (pref.foldl (fun acc instr => dhcRowsFoldStep (acc, instr))
                      dhcRowsFoldInit, instr))).length
                (hStep.time.eval
                  ((EncodedType.prod dhcRowsAccEncodedType
                    dhcRowsInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => dhcRowsFoldStep (acc, instr))
                      dhcRowsFoldInit, instr))) ≤
              C * (dhcRowsInstructionEncodedType.inputSize instr + 1) := by
          exact
            TM2Programs.listFoldBlockTime_le_linear_payload hStep.tm B T
              (by simpa [EncodedType.inputSize] using hAccSize)
              (by simpa [EncodedType.inputSize] using hStepSize)
              hStepTime
        have hEqTail : source = (pref ++ [instr]) ++ rest := by
          rw [hEq]
          simp [List.append_assoc]
        have hTailRaw := ih (pref := pref ++ [instr]) hEqTail
        have hTail :
            TM2Programs.listFoldTypedLoopTime
                dhcRowsInstructionEncodedType dhcRowsAccEncodedType
                dhcRowsFoldStep hStep
                (dhcRowsFoldStep
                  (pref.foldl (fun acc instr => dhcRowsFoldStep (acc, instr))
                    dhcRowsFoldInit, instr)) rest ≤
              C * (EncodedType.list dhcRowsInstructionEncodedType).inputSize rest := by
          have hFoldPref :
              (pref ++ [instr]).foldl
                  (fun acc instr => dhcRowsFoldStep (acc, instr)) dhcRowsFoldInit =
                dhcRowsFoldStep
                  (pref.foldl (fun acc instr => dhcRowsFoldStep (acc, instr))
                    dhcRowsFoldInit, instr) := by
            exact
              List.foldl_concat
                (fun acc instr => dhcRowsFoldStep (acc, instr)) dhcRowsFoldInit instr pref
          convert hTailRaw using 1
          exact congrArg
            (fun acc =>
              TM2Programs.listFoldTypedLoopTime
                dhcRowsInstructionEncodedType dhcRowsAccEncodedType
                dhcRowsFoldStep hStep acc rest)
            hFoldPref.symm
        calc
          TM2Programs.listFoldTypedLoopTime
              dhcRowsInstructionEncodedType dhcRowsAccEncodedType
              dhcRowsFoldStep hStep
              (pref.foldl (fun acc instr => dhcRowsFoldStep (acc, instr)) dhcRowsFoldInit)
              (instr :: rest)
              =
            TM2Programs.listFoldTypedLoopTime
                dhcRowsInstructionEncodedType dhcRowsAccEncodedType
                dhcRowsFoldStep hStep
                (dhcRowsFoldStep
                  (pref.foldl (fun acc instr => dhcRowsFoldStep (acc, instr))
                    dhcRowsFoldInit, instr)) rest +
              TM2Programs.listFoldBlockTime hStep.tm
                (dhcRowsInstructionEncodedType.encode instr).length
                (dhcRowsAccEncodedType.encode
                  (pref.foldl (fun acc instr => dhcRowsFoldStep (acc, instr))
                    dhcRowsFoldInit)).length
                (dhcRowsAccEncodedType.encode
                  (dhcRowsFoldStep
                    (pref.foldl (fun acc instr => dhcRowsFoldStep (acc, instr))
                      dhcRowsFoldInit, instr))).length
                (hStep.time.eval
                  ((EncodedType.prod dhcRowsAccEncodedType
                    dhcRowsInstructionEncodedType).inputSize
                    (pref.foldl (fun acc instr => dhcRowsFoldStep (acc, instr))
                      dhcRowsFoldInit, instr))) := by
                rfl
          _ ≤
              C * (EncodedType.list dhcRowsInstructionEncodedType).inputSize rest +
                C * (dhcRowsInstructionEncodedType.inputSize instr + 1) :=
                Nat.add_le_add hTail hBlock
          _ ≤ C * (EncodedType.list dhcRowsInstructionEncodedType).inputSize
              (instr :: rest) := by
                rw [EncodedType.inputSize_list_cons]
                nlinarith
  have hLoop :
      TM2Programs.listFoldTypedLoopTime
          dhcRowsInstructionEncodedType dhcRowsAccEncodedType
          dhcRowsFoldStep hStep dhcRowsFoldInit source ≤ C * N := by
    have h := hLoopAux [] source (by simp)
    simpa [N, dhcRowsInstructionListEncodedType] using h
  have hTimeEval : time.eval N = (C + 2) * (N + 1) := by
    simp [time, dhcRowsFoldTimePolynomial, B, T, C,
      TM2Programs.listFoldBoundedTimePolynomial_eval, TM2Programs.listFoldBlockTimeCoeff,
      Polynomial.eval_add, Polynomial.eval_comp]
  change 2 +
      TM2Programs.listFoldTypedLoopTime
        dhcRowsInstructionEncodedType dhcRowsAccEncodedType
        dhcRowsFoldStep hStep dhcRowsFoldInit source ≤ time.eval N
  rw [hTimeEval]
  nlinarith [hLoop, Nat.zero_le C, Nat.zero_le N]

theorem dhcRowsFoldResult_tm_polytime :
    TMPolyTimeMap
      dhcRowsInputEncodedType
      dhcRowsAccEncodedType
      (fun p : dhcRowsInputEncodedType.Carrier => dhcRowsFoldResult p.1 p.2) := by
  have hComp := TMPolyTimeMap.comp dhcRowsFold_tm_polytime dhcRowsInstructions_tm_polytime
  simpa [Function.comp, dhcRowsFoldResult] using hComp

theorem dhcIndexedSourceIncidencesFromGraphData_tm_polytime :
    TMPolyTimeMap
      dhcRowsInputEncodedType
      dhcIndexedIncidenceListEncodedType
      dhcIndexedSourceIncidencesFromGraphData := by
  have hTail₁ :
      TMPolyTimeMap dhcRowsAccEncodedType
        (EncodedType.prod edgeListStructuredEncodedType
          (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType))
        (fun acc : dhcRowsAccEncodedType.Carrier => acc.2) := by
    simpa [dhcRowsAccEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat
        (EncodedType.prod edgeListStructuredEncodedType
          (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType))
  have hTail₂ :
      TMPolyTimeMap dhcRowsAccEncodedType
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
        (fun acc : dhcRowsAccEncodedType.Carrier => acc.2.2) := by
    have hSnd :=
      TMPolyTimeMap.snd edgeListStructuredEncodedType
        (EncodedType.prod EncodedType.nat dhcIndexedIncidenceListEncodedType)
    have hComp := TMPolyTimeMap.comp hSnd hTail₁
    simpa [Function.comp] using hComp
  have hOut :
      TMPolyTimeMap dhcRowsAccEncodedType
        dhcIndexedIncidenceListEncodedType
        (fun acc : dhcRowsAccEncodedType.Carrier => acc.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat dhcIndexedIncidenceListEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTail₂
    simpa [Function.comp] using hComp
  have hComp := TMPolyTimeMap.comp hOut dhcRowsFoldResult_tm_polytime
  simpa [Function.comp, dhcIndexedSourceIncidencesFromGraphData] using hComp

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
