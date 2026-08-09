/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.EntryExitAllSlotsExitTM

/-!
Input-level executable wrappers for the DHC edge-family runners.

The earlier files prove the indexed executable emitters.  This file supplies the
structured `VertexCoverInput` projections needed to run those emitters directly
from the source instance and proves that the track aliases in `EdgeAssembly`
are backed by the same executable lists.
-/

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

def dhcIndexedSourceIncidenceBudgetFromInput
    (I : VertexCoverInput) : dhcIndexedIncidenceListWithBudgetRaw :=
  (I.k, dhcIndexedSourceIncidencesFromInput I)

theorem dhcIndexedSourceIncidencesFromInput_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      dhcIndexedIncidenceListEncodedType
      dhcIndexedSourceIncidencesFromInput := by
  let X := vertexCoverStructuredEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun I : VertexCoverInput => I.graph) := by
    simpa [X] using vertexCoverGraphTMBackedMap.tm_polytime
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : VertexCoverInput => graphPayloadOfGraph I.graph) := by
    have hComp := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : VertexCoverInput => I.graph.edges) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X] using hComp
  have hVertices :
      TMPolyTimeMap X EncodedType.nat
        (fun I : VertexCoverInput => I.graph.vertices) := by
    have hComp := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hRowsInput :
      TMPolyTimeMap X dhcRowsInputEncodedType
        (fun I : VertexCoverInput => (I.graph.vertices, I.graph.edges)) :=
    TMPolyTimeMap.prod_mk hVertices hEdges
  have hComp := TMPolyTimeMap.comp
    dhcIndexedSourceIncidencesFromGraphData_tm_polytime hRowsInput
  simpa [Function.comp, dhcIndexedSourceIncidencesFromInput, dhcRowsInputEncodedType, X]
    using hComp

theorem dhcIndexedSourceIncidenceBudgetFromInput_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      dhcIndexedIncidenceListWithBudgetEncodedType
      dhcIndexedSourceIncidenceBudgetFromInput := by
  let X := vertexCoverStructuredEncodedType
  have hBudget :
      TMPolyTimeMap X EncodedType.nat
        (fun I : VertexCoverInput => I.k) := by
    simpa [X] using vertexCoverBudgetTMBackedMap.tm_polytime
  have hOut :=
    TMPolyTimeMap.prod_mk hBudget dhcIndexedSourceIncidencesFromInput_tm_polytime
  simpa [dhcIndexedSourceIncidenceBudgetFromInput,
    dhcIndexedIncidenceListWithBudgetEncodedType, X] using hOut

def dhcIncidenceArcsExecutableFromInput (I : VertexCoverInput) : List (Nat × Nat) :=
  dhcIncidenceArcsExecutableFromIndexed (dhcIndexedSourceIncidenceBudgetFromInput I)

def dhcChainArcsExecutableFromInputDirect (I : VertexCoverInput) : List (Nat × Nat) :=
  dhcChainArcsExecutableFromIndexed (dhcIndexedSourceIncidenceBudgetFromInput I)

def dhcEntryArcsExecutableFromInputDirect (I : VertexCoverInput) : List (Nat × Nat) :=
  dhcEntryArcsExecutableFromIndexed (dhcIndexedSourceIncidenceBudgetFromInput I)

def dhcExitArcsExecutableFromInputDirect (I : VertexCoverInput) : List (Nat × Nat) :=
  dhcExitArcsExecutableFromIndexed (dhcIndexedSourceIncidenceBudgetFromInput I)

def dhcTrackChainArcsExecutableFromInput (I : VertexCoverInput) : List (Nat × Nat) :=
  dhcChainArcsExecutableFromIndexed (dhcIndexedSourceIncidenceBudgetFromInput I)

def dhcTrackEntryArcsExecutableFromInput (I : VertexCoverInput) : List (Nat × Nat) :=
  dhcEntryArcsExecutableFromIndexed (dhcIndexedSourceIncidenceBudgetFromInput I)

def dhcTrackExitArcsExecutableFromInput (I : VertexCoverInput) : List (Nat × Nat) :=
  dhcExitArcsExecutableFromIndexed (dhcIndexedSourceIncidenceBudgetFromInput I)

theorem dhcIncidenceArcsExecutableFromInput_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      edgeListStructuredEncodedType
      dhcIncidenceArcsExecutableFromInput := by
  have hComp := TMPolyTimeMap.comp
    dhcIncidenceArcsExecutableFromIndexed_tm_polytime
    dhcIndexedSourceIncidenceBudgetFromInput_tm_polytime
  simpa [Function.comp, dhcIncidenceArcsExecutableFromInput] using hComp

theorem dhcCrossArcsExecutableFromInput_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      edgeListStructuredEncodedType
      dhcCrossArcsExecutableFromInput := by
  have hComp := TMPolyTimeMap.comp
    dhcCrossArcsExecutableFromIndexed_tm_polytime
    dhcIndexedSourceIncidenceBudgetFromInput_tm_polytime
  simpa [Function.comp, dhcCrossArcsExecutableFromInput,
    dhcIndexedSourceIncidenceBudgetFromInput] using hComp

theorem dhcChainArcsExecutableFromInputDirect_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      edgeListStructuredEncodedType
      dhcChainArcsExecutableFromInputDirect := by
  have hComp := TMPolyTimeMap.comp
    dhcChainArcsExecutableFromIndexed_tm_polytime
    dhcIndexedSourceIncidenceBudgetFromInput_tm_polytime
  simpa [Function.comp, dhcChainArcsExecutableFromInputDirect] using hComp

theorem dhcEntryArcsExecutableFromInputDirect_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      edgeListStructuredEncodedType
      dhcEntryArcsExecutableFromInputDirect := by
  have hComp := TMPolyTimeMap.comp
    dhcEntryArcsExecutableFromIndexed_tm_polytime
    dhcIndexedSourceIncidenceBudgetFromInput_tm_polytime
  simpa [Function.comp, dhcEntryArcsExecutableFromInputDirect] using hComp

theorem dhcExitArcsExecutableFromInputDirect_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      edgeListStructuredEncodedType
      dhcExitArcsExecutableFromInputDirect := by
  have hComp := TMPolyTimeMap.comp
    dhcExitArcsExecutableFromIndexed_tm_polytime
    dhcIndexedSourceIncidenceBudgetFromInput_tm_polytime
  simpa [Function.comp, dhcExitArcsExecutableFromInputDirect] using hComp

theorem dhcTrackChainArcsExecutableFromInput_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      edgeListStructuredEncodedType
      dhcTrackChainArcsExecutableFromInput :=
  dhcChainArcsExecutableFromInputDirect_tm_polytime

theorem dhcTrackEntryArcsExecutableFromInput_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      edgeListStructuredEncodedType
      dhcTrackEntryArcsExecutableFromInput :=
  dhcEntryArcsExecutableFromInputDirect_tm_polytime

theorem dhcTrackExitArcsExecutableFromInput_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      edgeListStructuredEncodedType
      dhcTrackExitArcsExecutableFromInput :=
  dhcExitArcsExecutableFromInputDirect_tm_polytime

theorem dhcIncidenceArcsExecutableFromInput_eq_dhcIncidenceArcsFromInput
    (I : VertexCoverInput) :
    dhcIncidenceArcsExecutableFromInput I = dhcIncidenceArcsFromInput I := by
  simp [dhcIncidenceArcsExecutableFromInput, dhcIncidenceArcsFromInput,
    dhcIndexedSourceIncidenceBudgetFromInput, dhcIncidenceArcsExecutableFromIndexed_eq]

theorem dhcChainArcsExecutableFromInputDirect_eq_dhcChainArcsFromInput
    (I : VertexCoverInput) :
    dhcChainArcsExecutableFromInputDirect I = dhcChainArcsFromInput I := by
  calc
    dhcChainArcsExecutableFromInputDirect I =
        textbookChainArcs I := by
          simpa [dhcChainArcsExecutableFromInputDirect,
            dhcIndexedSourceIncidenceBudgetFromInput] using
            dhcChainArcsExecutableFromInput_eq_textbookChainArcs I
    _ = dhcChainArcsFromInput I :=
        (dhcChainArcsFromInput_eq_textbookChainArcs I).symm

theorem dhcEntryArcsExecutableFromInputDirect_eq_dhcEntryArcsFromInput
    (I : VertexCoverInput) :
    dhcEntryArcsExecutableFromInputDirect I = dhcEntryArcsFromInput I := by
  calc
    dhcEntryArcsExecutableFromInputDirect I =
        textbookEntryArcs I := by
          simpa [dhcEntryArcsExecutableFromInputDirect,
            dhcIndexedSourceIncidenceBudgetFromInput] using
            dhcEntryArcsExecutableFromInput_eq_textbookEntryArcs I
    _ = dhcEntryArcsFromInput I :=
        (dhcEntryArcsFromInput_eq_textbookEntryArcs I).symm

theorem dhcExitArcsExecutableFromInputDirect_eq_dhcExitArcsFromInput
    (I : VertexCoverInput) :
    dhcExitArcsExecutableFromInputDirect I = dhcExitArcsFromInput I := by
  calc
    dhcExitArcsExecutableFromInputDirect I =
        textbookExitArcs I := by
          simpa [dhcExitArcsExecutableFromInputDirect,
            dhcIndexedSourceIncidenceBudgetFromInput] using
            dhcExitArcsExecutableFromInput_eq_textbookExitArcs I
    _ = dhcExitArcsFromInput I :=
        (dhcExitArcsFromInput_eq_textbookExitArcs I).symm

theorem dhcTrackChainArcsExecutableFromInput_eq_dhcTrackChainArcsFromInput
    (I : VertexCoverInput) :
    dhcTrackChainArcsExecutableFromInput I = dhcTrackChainArcsFromInput I := by
  calc
    dhcTrackChainArcsExecutableFromInput I =
        textbookTrackChainArcs I := by
          simpa [dhcTrackChainArcsExecutableFromInput,
            dhcIndexedSourceIncidenceBudgetFromInput] using
            dhcChainArcsExecutableFromInput_eq_textbookTrackChainArcs I
    _ = dhcTrackChainArcsFromInput I :=
        (dhcTrackChainArcsFromInput_eq_textbookTrackChainArcs I).symm

theorem dhcTrackEntryArcsExecutableFromInput_eq_dhcTrackEntryArcsFromInput
    (I : VertexCoverInput) :
    dhcTrackEntryArcsExecutableFromInput I = dhcTrackEntryArcsFromInput I := by
  calc
    dhcTrackEntryArcsExecutableFromInput I =
        textbookTrackEntryArcs I := by
          simpa [dhcTrackEntryArcsExecutableFromInput,
            dhcIndexedSourceIncidenceBudgetFromInput] using
            dhcEntryArcsExecutableFromInput_eq_textbookTrackEntryArcs I
    _ = dhcTrackEntryArcsFromInput I :=
        (dhcTrackEntryArcsFromInput_eq_textbookTrackEntryArcs I).symm

theorem dhcTrackExitArcsExecutableFromInput_eq_dhcTrackExitArcsFromInput
    (I : VertexCoverInput) :
    dhcTrackExitArcsExecutableFromInput I = dhcTrackExitArcsFromInput I := by
  calc
    dhcTrackExitArcsExecutableFromInput I =
        textbookTrackExitArcs I := by
          simpa [dhcTrackExitArcsExecutableFromInput,
            dhcIndexedSourceIncidenceBudgetFromInput] using
            dhcExitArcsExecutableFromInput_eq_textbookTrackExitArcs I
    _ = dhcTrackExitArcsFromInput I :=
        (dhcTrackExitArcsFromInput_eq_textbookTrackExitArcs I).symm

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
