/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitAssembly

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

/-! ### Product/filter entry and exit arcs agree with row-boundary track arcs -/

theorem sourceIncidences_filter_firstIncident_map_eq_trackRows
    (I : VertexCoverInput) (slot : Nat) :
    (by
      classical
      exact
        (((sourceIncidences I).filter fun ui =>
            decide (FirstIncident I ui.1 ui.2)).map fun ui =>
          (textbookSelectorVertex slot, textbookIncidenceVertex I ui.1 ui.2 0)) =
          ((List.range I.graph.vertices).map fun u =>
            match (incidencesOfVertex I u).head? with
            | none => []
            | some ui =>
                [(textbookSelectorVertex slot,
                  textbookIncidenceVertex I ui.1 ui.2 0)]).flatten) := by
  classical
  rw [sourceIncidences_eq_flatMap_incidencesOfVertex I]
  change
    (((((List.range I.graph.vertices).map fun u => incidencesOfVertex I u).flatten).filter
        fun ui => decide (FirstIncident I ui.1 ui.2)).map fun ui =>
      (textbookSelectorVertex slot, textbookIncidenceVertex I ui.1 ui.2 0)) =
      ((List.range I.graph.vertices).map fun u =>
        match (incidencesOfVertex I u).head? with
        | none => []
        | some ui =>
            [(textbookSelectorVertex slot,
              textbookIncidenceVertex I ui.1 ui.2 0)]).flatten
  rw [list_filter_map_flatten]
  simp only [List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro u _hu
  change
    (((incidencesOfVertex I u).filter fun ui =>
      decide (FirstIncident I ui.1 ui.2)).map fun ui =>
      (textbookSelectorVertex slot, textbookIncidenceVertex I ui.1 ui.2 0)) =
      match (incidencesOfVertex I u).head? with
      | none => []
      | some ui =>
          [(textbookSelectorVertex slot,
            textbookIncidenceVertex I ui.1 ui.2 0)]
  rw [incidencesOfVertex_filter_firstIncident_eq_head I u]
  cases hHead : (incidencesOfVertex I u).head? <;> simp

theorem sourceIncidences_filter_lastIncident_map_eq_trackRows
    (I : VertexCoverInput) (slot : Nat) :
    (by
      classical
      exact
        (((sourceIncidences I).filter fun ui =>
            decide (LastIncident I ui.1 ui.2)).map fun ui =>
          (textbookIncidenceVertex I ui.1 ui.2 1,
            textbookSelectorVertex (textbookNextSelector I slot))) =
          ((List.range I.graph.vertices).map fun u =>
            match (incidencesOfVertex I u).getLast? with
            | none => []
            | some ui =>
                [(textbookIncidenceVertex I ui.1 ui.2 1,
                  textbookSelectorVertex (textbookNextSelector I slot))]).flatten) := by
  classical
  rw [sourceIncidences_eq_flatMap_incidencesOfVertex I]
  change
    (((((List.range I.graph.vertices).map fun u => incidencesOfVertex I u).flatten).filter
        fun ui => decide (LastIncident I ui.1 ui.2)).map fun ui =>
      (textbookIncidenceVertex I ui.1 ui.2 1,
        textbookSelectorVertex (textbookNextSelector I slot))) =
      ((List.range I.graph.vertices).map fun u =>
        match (incidencesOfVertex I u).getLast? with
        | none => []
        | some ui =>
            [(textbookIncidenceVertex I ui.1 ui.2 1,
              textbookSelectorVertex (textbookNextSelector I slot))]).flatten
  rw [list_filter_map_flatten]
  simp only [List.map_map]
  apply congrArg List.flatten
  apply List.map_congr_left
  intro u _hu
  change
    (((incidencesOfVertex I u).filter fun ui =>
      decide (LastIncident I ui.1 ui.2)).map fun ui =>
      (textbookIncidenceVertex I ui.1 ui.2 1,
        textbookSelectorVertex (textbookNextSelector I slot))) =
      match (incidencesOfVertex I u).getLast? with
      | none => []
      | some ui =>
          [(textbookIncidenceVertex I ui.1 ui.2 1,
            textbookSelectorVertex (textbookNextSelector I slot))]
  rw [incidencesOfVertex_filter_lastIncident_eq_getLast I u]
  cases hLast : (incidencesOfVertex I u).getLast? <;> simp

theorem textbookEntryArcs_eq_textbookTrackEntryArcs
    (I : VertexCoverInput) :
    textbookEntryArcs I = textbookTrackEntryArcs I := by
  classical
  calc
    textbookEntryArcs I
        =
      ((List.range I.k).map fun slot =>
        ((sourceIncidences I).filter fun ui =>
          decide (FirstIncident I ui.1 ui.2)).map fun ui =>
          (textbookSelectorVertex slot, textbookIncidenceVertex I ui.1 ui.2 0)).flatten := by
        simpa [textbookEntryArcs] using
          list_product_filter_map_right (List.range I.k) (sourceIncidences I)
            (fun ui : Nat × Nat => FirstIncident I ui.1 ui.2)
            (fun pair : Nat × (Nat × Nat) =>
              (textbookSelectorVertex pair.1,
                textbookIncidenceVertex I pair.2.1 pair.2.2 0))
    _ =
      ((List.range I.k).map fun slot =>
        ((List.range I.graph.vertices).map fun u =>
          match (incidencesOfVertex I u).head? with
          | none => []
          | some ui =>
              [(textbookSelectorVertex slot,
                textbookIncidenceVertex I ui.1 ui.2 0)]).flatten).flatten := by
        apply congrArg List.flatten
        apply List.map_congr_left
        intro slot _hslot
        exact sourceIncidences_filter_firstIncident_map_eq_trackRows I slot
    _ = textbookTrackEntryArcs I := by
        rw [list_flatten_map_flatten_eq_product_flatMap]
        rfl

theorem textbookExitArcs_eq_textbookTrackExitArcs
    (I : VertexCoverInput) :
    textbookExitArcs I = textbookTrackExitArcs I := by
  classical
  calc
    textbookExitArcs I
        =
      ((List.range I.k).map fun slot =>
        ((sourceIncidences I).filter fun ui =>
          decide (LastIncident I ui.1 ui.2)).map fun ui =>
          (textbookIncidenceVertex I ui.1 ui.2 1,
            textbookSelectorVertex (textbookNextSelector I slot))).flatten := by
        simpa [textbookExitArcs] using
          list_product_filter_map_right (List.range I.k) (sourceIncidences I)
            (fun ui : Nat × Nat => LastIncident I ui.1 ui.2)
            (fun pair : Nat × (Nat × Nat) =>
              (textbookIncidenceVertex I pair.2.1 pair.2.2 1,
                textbookSelectorVertex (textbookNextSelector I pair.1)))
    _ =
      ((List.range I.k).map fun slot =>
        ((List.range I.graph.vertices).map fun u =>
          match (incidencesOfVertex I u).getLast? with
          | none => []
          | some ui =>
              [(textbookIncidenceVertex I ui.1 ui.2 1,
                textbookSelectorVertex (textbookNextSelector I slot))]).flatten).flatten := by
        apply congrArg List.flatten
        apply List.map_congr_left
        intro slot _hslot
        exact sourceIncidences_filter_lastIncident_map_eq_trackRows I slot
    _ = textbookTrackExitArcs I := by
        rw [list_flatten_map_flatten_eq_product_flatMap]
        rfl

theorem dhcEntryArcsExecutableFromInput_eq_textbookEntryArcs
    (I : VertexCoverInput) :
    dhcEntryArcsExecutableFromIndexed
        (I.k, dhcIndexedSourceIncidencesFromInput I) =
      textbookEntryArcs I := by
  rw [dhcEntryArcsExecutableFromInput_eq_textbookTrackEntryArcs]
  rw [textbookEntryArcs_eq_textbookTrackEntryArcs]

theorem dhcExitArcsExecutableFromInput_eq_textbookExitArcs
    (I : VertexCoverInput) :
    dhcExitArcsExecutableFromIndexed
        (I.k, dhcIndexedSourceIncidencesFromInput I) =
      textbookExitArcs I := by
  rw [dhcExitArcsExecutableFromInput_eq_textbookTrackExitArcs]
  rw [textbookExitArcs_eq_textbookTrackExitArcs]

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
