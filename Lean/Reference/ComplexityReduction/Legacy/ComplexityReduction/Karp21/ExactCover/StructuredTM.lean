import ComplexityReduction.Legacy.ComplexityReduction.Karp21.CliqueCover
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.StructuredTM.EdgeCode
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.Literals

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
TM-facing support for the compact Chromatic-Number-to-Exact-Cover route.

The semantic route in `Part3` is now guarded only by the executable self-loop
test.  This file collects the direct finite-alphabet witnesses used by the
eventual public `TMBackedCostedReduction`.
-/

theorem colorSelfLoopBool_tm_polytime :
    TMPolyTimeMap edgeStructuredEncodedType EncodedType.bool colorSelfLoopBool := by
  simpa [colorSelfLoopBool, CliqueCover.edgeSelfLoopBool] using
    CliqueCover.edgeSelfLoopBool_tm_polytime

theorem colorGraphHasSelfLoopBool_eq_boolListOr_map (I : ChromaticNumberInput) :
    colorGraphHasSelfLoopBool I =
      CliqueCover.boolListOr (I.graph.edges.map colorSelfLoopBool) := by
  have hMap :
      CliqueCover.boolListOr (I.graph.edges.map colorSelfLoopBool) = true ↔
        colorGraphHasSelfLoop I := by
    rw [CliqueCover.boolListOr_eq_true_iff]
    constructor
    · intro h
      rcases List.mem_map.mp h with ⟨e, he, hEq⟩
      exact ⟨e, he, (colorSelfLoopBool_eq_true_iff e).1 hEq⟩
    · rintro ⟨e, he, hLoop⟩
      exact List.mem_map.mpr ⟨e, he, (colorSelfLoopBool_eq_true_iff e).2 hLoop⟩
  by_cases hLoop : colorGraphHasSelfLoop I
  · have hLeft := (colorGraphHasSelfLoopBool_eq_true_iff I).2 hLoop
    have hRight := hMap.2 hLoop
    simp [hLeft, hRight]
  · have hLeft : colorGraphHasSelfLoopBool I = false := by
      cases h : colorGraphHasSelfLoopBool I
      · rfl
      · exact (hLoop ((colorGraphHasSelfLoopBool_eq_true_iff I).1 h)).elim
    have hRight :
        CliqueCover.boolListOr (I.graph.edges.map colorSelfLoopBool) = false := by
      cases h : CliqueCover.boolListOr (I.graph.edges.map colorSelfLoopBool)
      · rfl
      · exact (hLoop (hMap.1 h)).elim
    simp [hLeft, hRight]

theorem colorGraphHasSelfLoopBool_tm_polytime :
    TMPolyTimeMap
      chromaticNumberStructuredEncodedType
      EncodedType.bool
      colorGraphHasSelfLoopBool := by
  let X := chromaticNumberStructuredEncodedType
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun I : ChromaticNumberInput => I.graph) := by
    simpa [X] using chromaticNumberGraphTMBackedMap.tm_polytime
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : ChromaticNumberInput => graphPayloadOfGraph I.graph) := by
    have hComp := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : ChromaticNumberInput => I.graph.edges) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X] using hComp
  have hEdgeBools :
      TMPolyTimeMap X (EncodedType.list EncodedType.bool)
        (fun I : ChromaticNumberInput => I.graph.edges.map colorSelfLoopBool) := by
    have hMap := TMPolyTimeMap.list_map colorSelfLoopBool_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hEdges
    simpa [Function.comp, edgeListStructuredEncodedType, X] using hComp
  have hOut := TMPolyTimeMap.comp CliqueCover.boolListOr_tm_polytime hEdgeBools
  convert hOut using 1
  funext I
  exact colorGraphHasSelfLoopBool_eq_boolListOr_map I

def colorIncidentInputEncodedType : EncodedType :=
  EncodedType.prod chromaticNumberStructuredEncodedType EncodedType.nat

theorem colorIncidentEdgeIndices_eq_incidentEdgeIndicesFromEdges
    (I : ChromaticNumberInput) (v : Nat) :
    colorIncidentEdgeIndices I v =
      SetCovering.incidentEdgeIndicesFromEdges (I.graph.edges, v) := by
  simpa [colorIncidentEdgeIndices] using
    (SetCovering.incidentEdgeIndicesFromEdges_eq_incidentEdgeIndices
      ({ graph := I.graph, k := 0 } : VertexCoverInput) v).symm

theorem colorIncidentEdgeIndices_tm_polytime :
    TMPolyTimeMap
      colorIncidentInputEncodedType
      (EncodedType.list EncodedType.nat)
      (fun p : ChromaticNumberInput × Nat => colorIncidentEdgeIndices p.1 p.2) := by
  let X := colorIncidentInputEncodedType
  have hSource :
      TMPolyTimeMap X chromaticNumberStructuredEncodedType
        (fun p : X.Carrier => p.1) := by
    simpa [X, colorIncidentInputEncodedType] using
      TMPolyTimeMap.fst chromaticNumberStructuredEncodedType EncodedType.nat
  have hVertex :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2) := by
    simpa [X, colorIncidentInputEncodedType] using
      TMPolyTimeMap.snd chromaticNumberStructuredEncodedType EncodedType.nat
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        (fun p : X.Carrier => p.1.graph) := by
    have hComp := TMPolyTimeMap.comp chromaticNumberGraphTMBackedMap.tm_polytime hSource
    simpa [Function.comp, X] using hComp
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun p : X.Carrier => graphPayloadOfGraph p.1.graph) := by
    have hComp := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime hGraph
    simpa [Function.comp, X] using hComp
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun p : X.Carrier => p.1.graph.edges) := by
    have hFst := TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X] using hComp
  have hInput :
      TMPolyTimeMap X SetCovering.incidentEdgeInstructionInputEncodedType
        (fun p : X.Carrier => (p.1.graph.edges, p.2)) := by
    simpa [SetCovering.incidentEdgeInstructionInputEncodedType] using
      TMPolyTimeMap.prod_mk hEdges hVertex
  have hOut :=
    TMPolyTimeMap.comp SetCovering.incidentEdgeIndicesFromEdges_tm_polytime hInput
  convert hOut using 1
  funext p
  exact colorIncidentEdgeIndices_eq_incidentEdgeIndicesFromEdges p.1 p.2

def exactCoverInputFromSystem (S : SetSystemInput) : ExactCoverInput where
  system := S

theorem exactCoverInputFromSystem_encode (S : SetSystemInput) :
    exactCoverStructuredEncodedType.encode (exactCoverInputFromSystem S) =
      setSystemStructuredEncodedType.encode S := by
  cases S
  rfl

noncomputable def exactCoverInputFromSystemTMBackedMap :
    TMBackedCostedMap
      setSystemStructuredEncodedType
      exactCoverStructuredEncodedType
      exactCoverInputFromSystem :=
  TMBackedCostedMap.ofEncodingEquiv
    setSystemStructuredEncodedType
    exactCoverStructuredEncodedType
    exactCoverInputFromSystem
    (Equiv.refl setSystemStructuredEncodedType.Symbol)
    (by
      intro S
      change exactCoverStructuredEncodedType.encode (exactCoverInputFromSystem S) =
        (setSystemStructuredEncodedType.encode S).map id
      simp [exactCoverInputFromSystem_encode])

end ExactCover
end Karp21
end ComplexityReduction
