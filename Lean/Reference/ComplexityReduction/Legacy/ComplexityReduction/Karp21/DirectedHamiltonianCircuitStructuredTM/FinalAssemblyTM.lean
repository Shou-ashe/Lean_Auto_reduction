/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.DirectedHamiltonianCircuitStructuredTM.SelectorSkipTM

/-!
Final executable edge-list append tree for the DHC selector/path gadget.
-/

namespace ComplexityReduction
namespace Karp21
namespace DirectedHamiltonianCircuit

open ComplexityReduction.Combinatorics.Graph

def dhcEdgeListExecutableFromInput (I : VertexCoverInput) : List (Nat × Nat) :=
  dhcIncidenceArcsExecutableFromInput I ++
    (dhcCrossArcsExecutableFromInput I ++
      (dhcChainArcsExecutableFromInputDirect I ++
        (dhcTrackChainArcsExecutableFromInput I ++
          (dhcSelectorSkipArcsExecutableFromInput I ++
            (dhcEntryArcsExecutableFromInputDirect I ++
              (dhcExitArcsExecutableFromInputDirect I ++
                (dhcTrackEntryArcsExecutableFromInput I ++
                  dhcTrackExitArcsExecutableFromInput I)))))))

theorem dhcEdgeListAppend_tm_polytime
    {X : EncodedType} {f g : X.Carrier → List (Nat × Nat)}
    (hf : TMPolyTimeMap X edgeListStructuredEncodedType f)
    (hg : TMPolyTimeMap X edgeListStructuredEncodedType g) :
    TMPolyTimeMap X edgeListStructuredEncodedType (fun x => f x ++ g x) := by
  have hPair :
      TMPolyTimeMap X
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun x => (f x, g x)) :=
    TMPolyTimeMap.prod_mk hf hg
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append edgeStructuredEncodedType) hPair
  simpa [Function.comp, edgeListStructuredEncodedType] using hAppend

theorem dhcEdgeListExecutableFromInput_tm_polytime :
    TMPolyTimeMap
      vertexCoverStructuredEncodedType
      edgeListStructuredEncodedType
      dhcEdgeListExecutableFromInput := by
  let X := vertexCoverStructuredEncodedType
  have hTrackEntryExit :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : VertexCoverInput =>
          dhcTrackEntryArcsExecutableFromInput I ++
            dhcTrackExitArcsExecutableFromInput I) :=
    dhcEdgeListAppend_tm_polytime
      dhcTrackEntryArcsExecutableFromInput_tm_polytime
      dhcTrackExitArcsExecutableFromInput_tm_polytime
  have hExitTail :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : VertexCoverInput =>
          dhcExitArcsExecutableFromInputDirect I ++
            (dhcTrackEntryArcsExecutableFromInput I ++
              dhcTrackExitArcsExecutableFromInput I)) :=
    dhcEdgeListAppend_tm_polytime
      dhcExitArcsExecutableFromInputDirect_tm_polytime hTrackEntryExit
  have hEntryTail :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : VertexCoverInput =>
          dhcEntryArcsExecutableFromInputDirect I ++
            (dhcExitArcsExecutableFromInputDirect I ++
              (dhcTrackEntryArcsExecutableFromInput I ++
                dhcTrackExitArcsExecutableFromInput I))) :=
    dhcEdgeListAppend_tm_polytime
      dhcEntryArcsExecutableFromInputDirect_tm_polytime hExitTail
  have hSelectorTail :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : VertexCoverInput =>
          dhcSelectorSkipArcsExecutableFromInput I ++
            (dhcEntryArcsExecutableFromInputDirect I ++
              (dhcExitArcsExecutableFromInputDirect I ++
                (dhcTrackEntryArcsExecutableFromInput I ++
                  dhcTrackExitArcsExecutableFromInput I)))) :=
    dhcEdgeListAppend_tm_polytime
      dhcSelectorSkipArcsExecutableFromInput_tm_polytime hEntryTail
  have hTrackChainTail :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : VertexCoverInput =>
          dhcTrackChainArcsExecutableFromInput I ++
            (dhcSelectorSkipArcsExecutableFromInput I ++
              (dhcEntryArcsExecutableFromInputDirect I ++
                (dhcExitArcsExecutableFromInputDirect I ++
                  (dhcTrackEntryArcsExecutableFromInput I ++
                    dhcTrackExitArcsExecutableFromInput I))))) :=
    dhcEdgeListAppend_tm_polytime
      dhcTrackChainArcsExecutableFromInput_tm_polytime hSelectorTail
  have hChainTail :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : VertexCoverInput =>
          dhcChainArcsExecutableFromInputDirect I ++
            (dhcTrackChainArcsExecutableFromInput I ++
              (dhcSelectorSkipArcsExecutableFromInput I ++
                (dhcEntryArcsExecutableFromInputDirect I ++
                  (dhcExitArcsExecutableFromInputDirect I ++
                    (dhcTrackEntryArcsExecutableFromInput I ++
                      dhcTrackExitArcsExecutableFromInput I)))))) :=
    dhcEdgeListAppend_tm_polytime
      dhcChainArcsExecutableFromInputDirect_tm_polytime hTrackChainTail
  have hCrossTail :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : VertexCoverInput =>
          dhcCrossArcsExecutableFromInput I ++
            (dhcChainArcsExecutableFromInputDirect I ++
              (dhcTrackChainArcsExecutableFromInput I ++
                (dhcSelectorSkipArcsExecutableFromInput I ++
                  (dhcEntryArcsExecutableFromInputDirect I ++
                    (dhcExitArcsExecutableFromInputDirect I ++
                      (dhcTrackEntryArcsExecutableFromInput I ++
                        dhcTrackExitArcsExecutableFromInput I))))))) :=
    dhcEdgeListAppend_tm_polytime
      dhcCrossArcsExecutableFromInput_tm_polytime hChainTail
  have hAll :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : VertexCoverInput =>
          dhcIncidenceArcsExecutableFromInput I ++
            (dhcCrossArcsExecutableFromInput I ++
              (dhcChainArcsExecutableFromInputDirect I ++
                (dhcTrackChainArcsExecutableFromInput I ++
                  (dhcSelectorSkipArcsExecutableFromInput I ++
                    (dhcEntryArcsExecutableFromInputDirect I ++
                      (dhcExitArcsExecutableFromInputDirect I ++
                        (dhcTrackEntryArcsExecutableFromInput I ++
                          dhcTrackExitArcsExecutableFromInput I)))))))) :=
    dhcEdgeListAppend_tm_polytime
      dhcIncidenceArcsExecutableFromInput_tm_polytime hCrossTail
  simpa [dhcEdgeListExecutableFromInput, X] using hAll

theorem dhcEdgeListExecutableFromInput_eq_dhcEdgeListFromInput
    (I : VertexCoverInput) :
    dhcEdgeListExecutableFromInput I = dhcEdgeListFromInput I := by
  simp [dhcEdgeListExecutableFromInput, dhcEdgeListFromInput,
    dhcIncidenceArcsExecutableFromInput_eq_dhcIncidenceArcsFromInput,
    dhcCrossArcsExecutableFromInput_eq_dhcCrossArcsFromInput,
    dhcChainArcsExecutableFromInputDirect_eq_dhcChainArcsFromInput,
    dhcTrackChainArcsExecutableFromInput_eq_dhcTrackChainArcsFromInput,
    dhcSelectorSkipArcsExecutableFromInput_eq_dhcSelectorSkipArcsFromInput,
    dhcEntryArcsExecutableFromInputDirect_eq_dhcEntryArcsFromInput,
    dhcExitArcsExecutableFromInputDirect_eq_dhcExitArcsFromInput,
    dhcTrackEntryArcsExecutableFromInput_eq_dhcTrackEntryArcsFromInput,
    dhcTrackExitArcsExecutableFromInput_eq_dhcTrackExitArcsFromInput]

theorem dhcEdgeListExecutableFromInput_eq_textbookEdgeList
    (I : VertexCoverInput) :
    dhcEdgeListExecutableFromInput I = textbookEdgeList I := by
  rw [dhcEdgeListExecutableFromInput_eq_dhcEdgeListFromInput]
  exact dhcEdgeListFromInput_eq_textbookEdgeList I

end DirectedHamiltonianCircuit
end Karp21
end ComplexityReduction
