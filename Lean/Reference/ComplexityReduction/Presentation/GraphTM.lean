/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Presentation.Graph
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.Part1

/-!
Route-independent direct-TM structural API for the public `GraphInput` codec.

The graph presentation is intentionally user-locked, so the canonical product
program constructors do not apply to it definitionally.  These lemmas expose
only the encoder-preserving unwrap/wrap and field-wise construction operations;
they contain no reduction, semantic theorem, benchmark direction, or case
specific gadget.
-/

namespace ComplexityReduction
namespace Presentation
namespace GraphTM

open ComplexityReduction.Combinatorics.Graph

/-- Unwrap the custom graph carrier to the exact tuple encoded by its codec. -/
theorem toTuple :
    TMPolyTimeMap graphStructuredEncodedType graphTupleStructuredEncodedType
      (fun graph : GraphInput => (graph.vertices, (graph.edges, graph.directed))) := by
  exact TMPolyTimeMap.of_encodingEquiv
    graphStructuredEncodedType graphTupleStructuredEncodedType _
    (Equiv.refl graphStructuredEncodedType.Symbol) (by
      intro graph
      change graphTupleStructuredEncodedType.encode
          (graph.vertices, (graph.edges, graph.directed)) =
        List.map id (graphTupleStructuredEncodedType.encode
          (graph.vertices, (graph.edges, graph.directed)))
      rw [List.map_id])

/-- Rewrap the exact graph tuple as the custom public graph carrier. -/
theorem ofTuple :
    TMPolyTimeMap graphTupleStructuredEncodedType graphStructuredEncodedType
      (fun input : Nat × (List (Nat × Nat) × Bool) =>
        { vertices := input.1, edges := input.2.1, directed := input.2.2 }) := by
  exact TMPolyTimeMap.of_encodingEquiv
    graphTupleStructuredEncodedType graphStructuredEncodedType _
    (Equiv.refl graphTupleStructuredEncodedType.Symbol) (by
      intro input
      rcases input with ⟨vertices, edges, directed⟩
      change graphTupleStructuredEncodedType.encode
          (vertices, (edges, directed)) =
        List.map id (graphTupleStructuredEncodedType.encode
          (vertices, (edges, directed)))
      rw [List.map_id])

/-- Vertex-count projection at the custom graph encoding. -/
theorem vertices :
    TMPolyTimeMap graphStructuredEncodedType EncodedType.nat GraphInput.vertices := by
  have composed := TMPolyTimeMap.comp
    (TMPolyTimeMap.fst EncodedType.nat graphPayloadStructuredEncodedType) toTuple
  simpa [Function.comp] using composed

/-- Edge-list projection at the custom graph encoding. -/
theorem edges :
    TMPolyTimeMap graphStructuredEncodedType edgeListStructuredEncodedType GraphInput.edges := by
  have payload := TMPolyTimeMap.comp
    (TMPolyTimeMap.snd EncodedType.nat graphPayloadStructuredEncodedType) toTuple
  have composed := TMPolyTimeMap.comp
    (TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool) payload
  simpa [Function.comp] using composed

/-- Directedness projection at the custom graph encoding. -/
theorem directed :
    TMPolyTimeMap graphStructuredEncodedType EncodedType.bool GraphInput.directed := by
  have payload := TMPolyTimeMap.comp
    (TMPolyTimeMap.snd EncodedType.nat graphPayloadStructuredEncodedType) toTuple
  have composed := TMPolyTimeMap.comp
    (TMPolyTimeMap.snd edgeListStructuredEncodedType EncodedType.bool) payload
  simpa [Function.comp] using composed

/-- Swap the two endpoints of one structurally encoded edge. -/
theorem edgeSwap :
    TMPolyTimeMap edgeStructuredEncodedType edgeStructuredEncodedType
      (fun edge : Nat × Nat => (edge.2, edge.1)) := by
  exact TMPolyTimeMap.prod_mk
    (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat)
    (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat)

/-- Append a list to the result of mapping one direct-TM edge operation over it. -/
theorem appendMapEdges {transform : (Nat × Nat) → (Nat × Nat)}
    (transformTM :
      TMPolyTimeMap edgeStructuredEncodedType edgeStructuredEncodedType transform) :
    TMPolyTimeMap edgeListStructuredEncodedType edgeListStructuredEncodedType
      (fun edgeList : List (Nat × Nat) => edgeList ++ edgeList.map transform) := by
  have mapped :
      TMPolyTimeMap edgeListStructuredEncodedType edgeListStructuredEncodedType
        (fun edgeList => edgeList.map transform) :=
    TMPolyTimeMap.list_map transformTM
  have paired :
      TMPolyTimeMap edgeListStructuredEncodedType
        (EncodedType.prod edgeListStructuredEncodedType edgeListStructuredEncodedType)
        (fun edgeList => (edgeList, edgeList.map transform)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id edgeListStructuredEncodedType) mapped
  have composed := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append edgeStructuredEncodedType) paired
  simpa [Function.comp] using composed

/-- Assemble a custom encoded graph from three direct-TM-computable fields. -/
theorem mk {X : EncodedType}
    {vertexCount : X.Carrier → Nat}
    {edgeList : X.Carrier → List (Nat × Nat)}
    {isDirected : X.Carrier → Bool}
    (vertexTM : TMPolyTimeMap X EncodedType.nat vertexCount)
    (edgesTM : TMPolyTimeMap X edgeListStructuredEncodedType edgeList)
    (directedTM : TMPolyTimeMap X EncodedType.bool isDirected) :
    TMPolyTimeMap X graphStructuredEncodedType
      (fun input =>
        { vertices := vertexCount input
          edges := edgeList input
          directed := isDirected input }) := by
  have payloadTM :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun input => (edgeList input, isDirected input)) :=
    TMPolyTimeMap.prod_mk edgesTM directedTM
  have tupleTM :
      TMPolyTimeMap X graphTupleStructuredEncodedType
        (fun input => (vertexCount input, (edgeList input, isDirected input))) :=
    TMPolyTimeMap.prod_mk vertexTM payloadTM
  have composed := TMPolyTimeMap.comp ofTuple tupleTM
  simpa [Function.comp] using composed

end GraphTM
end Presentation
end ComplexityReduction
