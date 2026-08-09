/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.OuterRows

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! ### Source-incidence semantics for the indexed DHC runner -/

def dhcIndexedSourceIncidencePairsFromGraphData
    (p : dhcRowsInputEncodedType.Carrier) : List (Nat × Nat) :=
  (dhcIndexedSourceIncidencesFromGraphData p).map Prod.fst

theorem dhcIndexedRowFromEdgeIndices_eq_zipIdx
    (u nextIndex : Nat) (indices : List Nat) :
    dhcIndexedRowFromEdgeIndices u nextIndex indices =
      (indices.map fun i => (u, i)).zipIdx nextIndex := by
  induction indices generalizing nextIndex with
  | nil =>
      simp [dhcIndexedRowFromEdgeIndices]
  | cons i indices ih =>
      simp [dhcIndexedRowFromEdgeIndices, ih]

theorem dhcIndexedRowFromEdgeIndices_map_fst
    (u nextIndex : Nat) (indices : List Nat) :
    (dhcIndexedRowFromEdgeIndices u nextIndex indices).map Prod.fst =
      indices.map fun i => (u, i) := by
  rw [dhcIndexedRowFromEdgeIndices_eq_zipIdx]
  simp

theorem mem_dhcFindIdxs_source_iff
    (I : VertexCoverInput) (u i : Nat) :
    i ∈ I.graph.edges.findIdxs
        (fun edge => dhcSourceIncidentBool (I.graph.vertices, (u, edge))) ↔
      SourceIncidentAt I u i := by
  constructor
  · intro hi
    rcases (List.mem_findIdxs_iff_exists_getElem_pos (xs := I.graph.edges)
        (p := fun edge : Nat × Nat =>
          dhcSourceIncidentBool (I.graph.vertices, (u, edge)))).1 hi with
      ⟨hiLt, hBool⟩
    have hBoolTrue :
        dhcSourceIncidentBool (I.graph.vertices, (u, I.graph.edges[i]'hiLt)) = true := by
      simpa using hBool
    rcases (dhcSourceIncidentBool_eq_true_iff
        (I.graph.vertices, (u, I.graph.edges[i]'hiLt))).1 hBoolTrue with
      ⟨hu, hEndpoint⟩
    refine ⟨hiLt, hu, ?_⟩
    rcases hEndpoint with hLeft | hRight
    · left
      simpa [List.getD_getElem?, hiLt] using hLeft
    · right
      simpa [List.getD_getElem?, hiLt] using hRight
  · intro hSource
    rcases hSource with ⟨hiLt, hu, hEndpoint⟩
    refine (List.mem_findIdxs_iff_exists_getElem_pos (xs := I.graph.edges)
        (p := fun edge : Nat × Nat =>
          dhcSourceIncidentBool (I.graph.vertices, (u, edge)))).2 ?_
    refine ⟨hiLt, ?_⟩
    have hEndpoint' :
        (I.graph.edges[i]'hiLt).1 = u ∨ (I.graph.edges[i]'hiLt).2 = u := by
      rcases hEndpoint with hLeft | hRight
      · left
        simpa [List.getD_getElem?, hiLt] using hLeft
      · right
        simpa [List.getD_getElem?, hiLt] using hRight
    have hBool :
        dhcSourceIncidentBool (I.graph.vertices, (u, I.graph.edges[i]'hiLt)) = true :=
      (dhcSourceIncidentBool_eq_true_iff
        (I.graph.vertices, (u, I.graph.edges[i]'hiLt))).2 ⟨hu, hEndpoint'⟩
    simpa using hBool

theorem mem_dhcIndexedRowFromEdgeIndices_map_fst_iff
    (u nextIndex : Nat) (indices : List Nat) (ui : Nat × Nat) :
    ui ∈ (dhcIndexedRowFromEdgeIndices u nextIndex indices).map Prod.fst ↔
      ui.1 = u ∧ ui.2 ∈ indices := by
  rw [dhcIndexedRowFromEdgeIndices_map_fst]
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨i, hi, hui⟩
    exact ⟨by simpa using congrArg Prod.fst hui.symm,
      by simpa using congrArg Prod.snd hui.symm ▸ hi⟩
  · intro h
    exact List.mem_map.mpr ⟨ui.2, h.2, by ext <;> simp [h.1]⟩

theorem dhcRowScanResult_out_eq_zipIdx
    (vertices u nextIndex : Nat) (edges : List (Nat × Nat)) :
    (show List ((Nat × Nat) × Nat) from
        (dhcRowScanResult vertices u nextIndex edges).2.2.2.2) =
      ((edges.findIdxs fun edge => dhcSourceIncidentBool (vertices, (u, edge))).map
          fun i => (u, i)).zipIdx nextIndex := by
  rw [dhcRowScanResult_findIdxs]
  simp [dhcIndexedRowFromEdgeIndices_eq_zipIdx]

theorem dhcRowsFoldRightStep_eq_zipIdx
    (vertices nextIndex u : Nat) (edges : List (Nat × Nat))
    (out : List ((Nat × Nat) × Nat)) :
    dhcRowsFoldRightStep ((vertices, (edges, (nextIndex, out))), u) =
      (vertices,
        (edges,
          (nextIndex +
              ((edges.findIdxs fun edge => dhcSourceIncidentBool (vertices, (u, edge))).map
                fun i => (u, i)).length,
            out ++
              ((edges.findIdxs fun edge => dhcSourceIncidentBool (vertices, (u, edge))).map
                fun i => (u, i)).zipIdx nextIndex))) := by
  simp [dhcRowsFoldRightStep, dhcRowScanResult_findIdxs,
    dhcIndexedRowFromEdgeIndices_eq_zipIdx]
  rfl

theorem dhcRowsFoldRightStep_nextIndex_eq
    (vertices nextIndex u : Nat) (edges : List (Nat × Nat))
    (out : List ((Nat × Nat) × Nat)) :
    (dhcRowsFoldRightStep
        ((vertices, (edges, (nextIndex, out))), u)).2.2.1 =
      nextIndex +
        ((edges.findIdxs fun edge => dhcSourceIncidentBool (vertices, (u, edge))).map
          fun i => (u, i)).length := by
  simp [dhcRowsFoldRightStep, dhcRowScanResult_findIdxs]

theorem dhcRowsFoldRightStep_out_eq_zipIdx
    (vertices nextIndex u : Nat) (edges : List (Nat × Nat))
    (out : List ((Nat × Nat) × Nat)) :
    (dhcRowsFoldRightStep
        ((vertices, (edges, (nextIndex, out))), u)).2.2.2 =
      out ++
        ((edges.findIdxs fun edge => dhcSourceIncidentBool (vertices, (u, edge))).map
          fun i => (u, i)).zipIdx nextIndex := by
  simp [dhcRowsFoldRightStep, dhcRowScanResult_findIdxs,
    dhcIndexedRowFromEdgeIndices_eq_zipIdx]

theorem dhcRowsFoldRange_out_eq_zipIdx
    (rows : List Nat) (vertices nextIndex : Nat) (edges : List (Nat × Nat))
    (out : List ((Nat × Nat) × Nat)) :
    (rows.foldl
        (fun acc u => dhcRowsFoldRightStep (acc, u))
        (vertices, (edges, (nextIndex, out)))).2.2.2 =
      out ++
        (rows.flatMap fun u =>
          (edges.findIdxs fun edge => dhcSourceIncidentBool (vertices, (u, edge))).map
            fun i => (u, i)).zipIdx nextIndex := by
  induction rows generalizing nextIndex out with
  | nil =>
      simp
  | cons u rows ih =>
      rw [List.foldl_cons]
      rw [dhcRowsFoldRightStep_eq_zipIdx]
      let rowPairs :=
        (edges.findIdxs fun edge => dhcSourceIncidentBool (vertices, (u, edge))).map
          fun i => (u, i)
      let tailPairs :=
        rows.flatMap fun u =>
          (edges.findIdxs fun edge => dhcSourceIncidentBool (vertices, (u, edge))).map
            fun i => (u, i)
      change
        (List.foldl
            (fun acc u => dhcRowsFoldRightStep (acc, u))
            (vertices, (edges,
              (nextIndex + rowPairs.length, out ++ rowPairs.zipIdx nextIndex)))
            rows).2.2.2 =
          out ++ (rowPairs ++ tailPairs).zipIdx nextIndex
      calc
        (List.foldl
            (fun acc u => dhcRowsFoldRightStep (acc, u))
            (vertices, (edges,
              (nextIndex + rowPairs.length, out ++ rowPairs.zipIdx nextIndex)))
            rows).2.2.2
            = (out ++ rowPairs.zipIdx nextIndex) ++
                tailPairs.zipIdx (nextIndex + rowPairs.length) := by
              exact ih (nextIndex + rowPairs.length) (out ++ rowPairs.zipIdx nextIndex)
        _ = out ++
              (rowPairs.zipIdx nextIndex ++ tailPairs.zipIdx (nextIndex + rowPairs.length)) := by
              rw [List.append_assoc]
        _ = out ++ (rowPairs ++ tailPairs).zipIdx nextIndex := by
              rw [List.zipIdx_append]

theorem dhcIndexedSourceIncidencesFromGraphData_eq_zipIdx
    (vertices : Nat) (edges : List (Nat × Nat)) :
    dhcIndexedSourceIncidencesFromGraphData (vertices, edges) =
      ((List.range vertices).flatMap fun u =>
        (edges.findIdxs fun edge => dhcSourceIncidentBool (vertices, (u, edge))).map
          fun i => (u, i)).zipIdx := by
  rw [dhcIndexedSourceIncidencesFromGraphData_eq_rangeFold]
  simpa using
    dhcRowsFoldRange_out_eq_zipIdx (List.range vertices) vertices 0 edges
      ([] : List ((Nat × Nat) × Nat))

theorem dhcIndexedSourceIncidencePairsFromGraphData_eq_bind_findIdxs
    (vertices : Nat) (edges : List (Nat × Nat)) :
    dhcIndexedSourceIncidencePairsFromGraphData (vertices, edges) =
      (List.range vertices).flatMap fun u =>
        (edges.findIdxs fun edge => dhcSourceIncidentBool (vertices, (u, edge))).map
          fun i => (u, i) := by
  rw [dhcIndexedSourceIncidencePairsFromGraphData,
    dhcIndexedSourceIncidencesFromGraphData_eq_zipIdx]
  simp

theorem mem_dhcFindIdxs_source_map_iff
    (I : VertexCoverInput) (u : Nat) (ui : Nat × Nat) :
    ui ∈
        (I.graph.edges.findIdxs
          (fun edge => dhcSourceIncidentBool (I.graph.vertices, (u, edge)))).map
            (fun i => (u, i)) ↔
      ui ∈ incidencesOfVertex I u := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨i, hi, hui⟩
    have hSource : SourceIncidentAt I u i :=
      (mem_dhcFindIdxs_source_iff I u i).1 hi
    cases hui
    exact (mem_incidencesOfVertex_iff I u (u, i)).2
      ⟨(mem_sourceIncidences_iff I (u, i)).2 hSource, rfl⟩
  · intro h
    have hData := (mem_incidencesOfVertex_iff I u ui).1 h
    have hSource : SourceIncidentAt I ui.1 ui.2 :=
      (mem_sourceIncidences_iff I ui).1 hData.1
    have hSourceU : SourceIncidentAt I u ui.2 := by
      simpa [hData.2] using hSource
    exact List.mem_map.mpr
      ⟨ui.2, (mem_dhcFindIdxs_source_iff I u ui.2).2 hSourceU,
        by ext <;> simp [hData.2]⟩

theorem dhcFindIdxs_source_map_pairwise_edge_lt
    (I : VertexCoverInput) (u : Nat) :
    ((I.graph.edges.findIdxs
      (fun edge => dhcSourceIncidentBool (I.graph.vertices, (u, edge)))).map
        (fun i => (u, i))).Pairwise fun ui uj => ui.2 < uj.2 := by
  have hPair :
      (I.graph.edges.findIdxs
        (fun edge => dhcSourceIncidentBool (I.graph.vertices, (u, edge)))).Pairwise
          fun i j => i < j := by
    exact List.pairwise_findIdxs
  simp [List.pairwise_map] at hPair ⊢

theorem dhcFindIdxs_source_map_eq_incidencesOfVertex
    (I : VertexCoverInput) (u : Nat) :
    (I.graph.edges.findIdxs
      (fun edge => dhcSourceIncidentBool (I.graph.vertices, (u, edge)))).map
        (fun i => (u, i)) =
      incidencesOfVertex I u := by
  let r : Nat × Nat → Nat × Nat → Prop := fun ui uj => ui.2 < uj.2
  haveI : Std.Irrefl r := ⟨by
    intro ui
    exact Nat.lt_irrefl ui.2⟩
  haveI : Std.Antisymm r := ⟨by
    intro ui uj hui hju
    exact False.elim (Nat.lt_asymm hui hju)⟩
  have hLeft :
      ((I.graph.edges.findIdxs
        (fun edge => dhcSourceIncidentBool (I.graph.vertices, (u, edge)))).map
          (fun i => (u, i))).Pairwise r := by
    simpa [r] using dhcFindIdxs_source_map_pairwise_edge_lt I u
  have hRight : (incidencesOfVertex I u).Pairwise r := by
    simpa [r] using incidencesOfVertex_pairwise_edge_lt I u
  exact hLeft.eq_of_mem_iff hRight (mem_dhcFindIdxs_source_map_iff I u)

theorem sourceIncidences_eq_flatMap_incidencesOfVertex
    (I : VertexCoverInput) :
    sourceIncidences I =
      (List.range I.graph.vertices).flatMap fun u => incidencesOfVertex I u := by
  classical
  simp [sourceIncidences, incidencesOfVertex, List.product, List.filter_flatMap,
    List.filter_map, Function.comp_def]

theorem dhcIndexedSourceIncidencePairsFromInput_eq
    (I : VertexCoverInput) :
    dhcIndexedSourceIncidencePairsFromGraphData
        (I.graph.vertices, I.graph.edges) =
      sourceIncidences I := by
  rw [dhcIndexedSourceIncidencePairsFromGraphData_eq_bind_findIdxs,
    sourceIncidences_eq_flatMap_incidencesOfVertex]
  exact List.flatMap_congr
    (fun u _hu => dhcFindIdxs_source_map_eq_incidencesOfVertex I u)

theorem dhcIndexedSourceIncidencePairsFromInput_nodup
    (I : VertexCoverInput) :
    (dhcIndexedSourceIncidencePairsFromGraphData
        (I.graph.vertices, I.graph.edges)).Nodup := by
  rw [dhcIndexedSourceIncidencePairsFromInput_eq]
  exact sourceIncidences_nodup I

theorem dhcIndexedSourceIncidencesFromInput_eq_zipIdx_sourceIncidences
    (I : VertexCoverInput) :
    dhcIndexedSourceIncidencesFromGraphData
        (I.graph.vertices, I.graph.edges) =
      (sourceIncidences I).zipIdx := by
  rw [dhcIndexedSourceIncidencesFromGraphData_eq_zipIdx]
  rw [show
      (List.range I.graph.vertices).flatMap
          (fun u =>
            (I.graph.edges.findIdxs
              (fun edge => dhcSourceIncidentBool (I.graph.vertices, (u, edge)))).map
                fun i => (u, i)) =
        sourceIncidences I from
      (dhcIndexedSourceIncidencePairsFromGraphData_eq_bind_findIdxs
          I.graph.vertices I.graph.edges).symm.trans
        (dhcIndexedSourceIncidencePairsFromInput_eq I)]

theorem dhcIndexedSourceIncidencesFromInput_idx_eq
    (I : VertexCoverInput) {u i idx : Nat}
    (hMem :
      ((u, i), idx) ∈
        dhcIndexedSourceIncidencesFromGraphData
          (I.graph.vertices, I.graph.edges)) :
    idx = (sourceIncidences I).idxOf (u, i) := by
  have hZip :
      ((u, i), idx) ∈ (sourceIncidences I).zipIdx := by
    simpa [dhcIndexedSourceIncidencesFromInput_eq_zipIdx_sourceIncidences I] using hMem
  rcases List.mem_zipIdx' hZip with ⟨hIdxLt, hGet⟩
  have hIdxOf :=
    (sourceIncidences_nodup I).idxOf_getElem idx hIdxLt
  have hIdxOf' : (sourceIncidences I).idxOf (u, i) = idx := by
    simpa [hGet.symm] using hIdxOf
  exact hIdxOf'.symm

theorem dhcIncidenceVertexCode_eq_textbookIncidenceVertex_of_mem
    (I : VertexCoverInput) {u i idx bit : Nat}
    (hMem :
      ((u, i), idx) ∈
        dhcIndexedSourceIncidencesFromGraphData
          (I.graph.vertices, I.graph.edges)) :
    dhcIncidenceVertexCode (I.k, (idx, bit)) =
      textbookIncidenceVertex I u i bit := by
  have hIdx := dhcIndexedSourceIncidencesFromInput_idx_eq I hMem
  simp [dhcIncidenceVertexCode, textbookIncidenceVertex, natDouble, hIdx]
  omega

theorem mem_dhcRowScanResult_out_map_fst_iff
    (vertices u nextIndex : Nat) (edges : List (Nat × Nat)) (ui : Nat × Nat) :
    ui ∈ (dhcRowScanResult vertices u nextIndex edges).2.2.2.2.map Prod.fst ↔
      ui.1 = u ∧
        ui.2 ∈ edges.findIdxs (fun edge => dhcSourceIncidentBool (vertices, (u, edge))) := by
  rw [dhcRowScanResult_findIdxs]
  exact mem_dhcIndexedRowFromEdgeIndices_map_fst_iff u nextIndex
    (edges.findIdxs (fun edge => dhcSourceIncidentBool (vertices, (u, edge)))) ui

theorem mem_dhcRowsFoldRightStep_out_map_fst_iff
    (vertices nextIndex u : Nat) (edges : List (Nat × Nat))
    (out : List ((Nat × Nat) × Nat)) (ui : Nat × Nat) :
    ui ∈
        (dhcRowsFoldRightStep
          ((vertices, (edges, (nextIndex, out))), u)).2.2.2.map Prod.fst ↔
      ui ∈ out.map Prod.fst ∨
        ui.1 = u ∧
          ui.2 ∈ edges.findIdxs
            (fun edge => dhcSourceIncidentBool (vertices, (u, edge))) := by
  change ui ∈
      (out ++
        (show List ((Nat × Nat) × Nat) from
          (dhcRowScanResult vertices u nextIndex edges).2.2.2.2)).map Prod.fst ↔
    ui ∈ out.map Prod.fst ∨
      ui.1 = u ∧
        ui.2 ∈ edges.findIdxs
          (fun edge => dhcSourceIncidentBool (vertices, (u, edge)))
  rw [List.map_append, List.mem_append]
  have hRow :
      ui ∈
          (show List ((Nat × Nat) × Nat) from
            (dhcRowScanResult vertices u nextIndex edges).2.2.2.2).map Prod.fst ↔
        ui.1 = u ∧
          ui.2 ∈ edges.findIdxs
            (fun edge => dhcSourceIncidentBool (vertices, (u, edge))) := by
    exact mem_dhcRowScanResult_out_map_fst_iff vertices u nextIndex edges ui
  exact or_congr_right hRow

theorem mem_dhcRowsFoldRange_out_map_fst_iff
    (rows : List Nat) (vertices nextIndex : Nat) (edges : List (Nat × Nat))
    (out : List ((Nat × Nat) × Nat)) (ui : Nat × Nat) :
    ui ∈
        ((rows.foldl
          (fun acc u => dhcRowsFoldRightStep (acc, u))
          (vertices, (edges, (nextIndex, out)))).2.2.2.map Prod.fst) ↔
      ui ∈ out.map Prod.fst ∨
        ∃ u ∈ rows,
          ui.1 = u ∧
            ui.2 ∈ edges.findIdxs
              (fun edge => dhcSourceIncidentBool (vertices, (u, edge))) := by
  induction rows generalizing nextIndex out with
  | nil =>
      constructor
      · intro h
        exact Or.inl h
      · intro h
        rcases h with h | h
        · exact h
        · rcases h with ⟨u, hu, _hData⟩
          simp at hu
  | cons u rows ih =>
      rw [List.foldl_cons]
      have hStep :=
        mem_dhcRowsFoldRightStep_out_map_fst_iff vertices nextIndex u edges out ui
      have hTail :=
        ih
          (dhcRowsFoldRightStep ((vertices, (edges, (nextIndex, out))), u)).2.2.1
          (dhcRowsFoldRightStep ((vertices, (edges, (nextIndex, out))), u)).2.2.2
      change ui ∈
          List.map Prod.fst
            (List.foldl (fun acc u => dhcRowsFoldRightStep (acc, u))
              (vertices,
                (edges,
                  ((dhcRowsFoldRightStep
                      ((vertices, (edges, (nextIndex, out))), u)).2.2.1,
                    (dhcRowsFoldRightStep
                      ((vertices, (edges, (nextIndex, out))), u)).2.2.2)))
              rows).2.2.2 ↔
        ui ∈ out.map Prod.fst ∨
          ∃ u_1 ∈ u :: rows,
            ui.1 = u_1 ∧
              ui.2 ∈ edges.findIdxs
                (fun edge => dhcSourceIncidentBool (vertices, (u_1, edge)))
      rw [hTail]
      constructor
      · intro h
        rcases h with hStepMem | hRows
        · rcases hStep.1 hStepMem with hOld | hRow
          · exact Or.inl hOld
          · exact Or.inr ⟨u, by simp, hRow⟩
        · rcases hRows with ⟨v, hvRows, hvData⟩
          exact Or.inr ⟨v, by simp [hvRows], hvData⟩
      · intro h
        rcases h with hOld | hRows
        · exact Or.inl (hStep.2 (Or.inl hOld))
        · rcases hRows with ⟨v, hvRows, hvData⟩
          by_cases hvEq : v = u
          · subst v
            exact Or.inl (hStep.2 (Or.inr hvData))
          · have hvTail : v ∈ rows := by
              simpa [hvEq] using hvRows
            exact Or.inr ⟨v, hvTail, hvData⟩

theorem mem_dhcIndexedSourceIncidencePairsFromGraphData_iff
    (vertices : Nat) (edges : List (Nat × Nat)) (ui : Nat × Nat) :
    ui ∈ dhcIndexedSourceIncidencePairsFromGraphData (vertices, edges) ↔
      ui.1 < vertices ∧
        ui.2 ∈ edges.findIdxs
          (fun edge => dhcSourceIncidentBool (vertices, (ui.1, edge))) := by
  rw [dhcIndexedSourceIncidencePairsFromGraphData,
    dhcIndexedSourceIncidencesFromGraphData_eq_rangeFold]
  have hRange :=
    mem_dhcRowsFoldRange_out_map_fst_iff (List.range vertices) vertices 0 edges
      ([] : List ((Nat × Nat) × Nat)) ui
  change ui ∈
      List.map Prod.fst
        (List.foldl (fun acc u => dhcRowsFoldRightStep (acc, u))
          (vertices, (edges, ((0 : Nat), ([] : List ((Nat × Nat) × Nat)))))
          (List.range vertices)).2.2.2 ↔
    ui.1 < vertices ∧
      ui.2 ∈ edges.findIdxs
        (fun edge => dhcSourceIncidentBool (vertices, (ui.1, edge)))
  rw [hRange]
  constructor
  · intro h
    rcases h with hEmpty | hRows
    · simp at hEmpty
    · rcases hRows with ⟨u, huRange, hui, hi⟩
      have huLt : u < vertices := by
        simpa using huRange
      exact ⟨by simpa [hui] using huLt, by simpa [hui] using hi⟩
  · intro h
    rcases h with ⟨hu, hi⟩
    exact Or.inr ⟨ui.1, by simpa using hu, rfl, hi⟩

theorem mem_dhcIndexedSourceIncidencePairsFromInput_iff
    (I : VertexCoverInput) (ui : Nat × Nat) :
    ui ∈ dhcIndexedSourceIncidencePairsFromGraphData
        (I.graph.vertices, I.graph.edges) ↔
      ui ∈ sourceIncidences I := by
  rw [mem_dhcIndexedSourceIncidencePairsFromGraphData_iff,
    mem_sourceIncidences_iff]
  constructor
  · intro h
    exact (mem_dhcFindIdxs_source_iff I ui.1 ui.2).1 h.2
  · intro h
    have hSource := (mem_dhcFindIdxs_source_iff I ui.1 ui.2).2 h
    exact ⟨h.2.1, hSource⟩

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
