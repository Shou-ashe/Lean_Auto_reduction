/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.AxiomGate
import ComplexityReduction.Domain.RectangularCoordinates
import ComplexityReduction.Domain.VertexCoverToMostNeighborsCore
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatArithmetic
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatMul
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatRange
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ListLookupTM
import ComplexityReduction.Problems.Karp21.GraphAtoms
import ComplexityReduction.Program.ContextListMap
import Mathlib.Tactic

/-!
Public Clique-to-Most-Neighbors reduction packet.

The semantic core is the robust Vertex-Cover gadget.  The executable used for
the direct TM stores the same two endpoint edges in separate rectangular
passes.  It is semantically identical on the always-well-formed output of the
standard Clique-to-Vertex-Cover map, while its exact list construction is a
composition of reusable direct-TM range, rectangle, context-map, lookup, and
arithmetic components.
-/

namespace ComplexityReduction
namespace Domain
namespace VertexCoverToMostNeighbors

open Encoding
open Certificate
open Program
open ComplexityReduction.Combinatorics.Graph

abbrev source : PresentedProblem :=
  Problems.Karp21.GraphAtoms.cliqueStructuredProblem

abbrev target : PresentedProblem :=
  Presentation.MostNeighbors.presentedProblem

/-- Ordered `(raw edge index, copy index)` coordinates. -/
def coordinates (input : VertexCoverInput) : List (Nat × Nat) :=
  RectangularCoordinates.familyExecutable
    (input.graph.edges.length, VertexCoverToMostNeighborsCore.copyCount input)

theorem coordinates_eq (input : VertexCoverInput) :
    coordinates input =
      (List.range input.graph.edges.length).flatMap fun edgeIndex =>
        (List.range (VertexCoverToMostNeighborsCore.copyCount input)).map fun copyIndex =>
          (edgeIndex, copyIndex) := by
  simpa [coordinates, RectangularCoordinates.coordinateOfRow] using
    RectangularCoordinates.familyExecutable_eq_flatMap
      (input.graph.edges.length, VertexCoverToMostNeighborsCore.copyCount input)

theorem mem_coordinates_iff (input : VertexCoverInput) (coordinate : Nat × Nat) :
    coordinate ∈ coordinates input ↔
      coordinate.1 < input.graph.edges.length ∧
        coordinate.2 < VertexCoverToMostNeighborsCore.copyCount input := by
  rw [coordinates_eq]
  constructor
  · intro member
    rcases List.mem_flatMap.mp member with ⟨edgeIndex, edgeMember, coordinateMember⟩
    rcases List.mem_map.mp coordinateMember with ⟨copyIndex, copyMember, equality⟩
    have edgeBound := List.mem_range.mp edgeMember
    have copyBound := List.mem_range.mp copyMember
    rw [← equality]
    exact ⟨edgeBound, copyBound⟩
  · intro bounds
    exact List.mem_flatMap.mpr
      ⟨coordinate.1, List.mem_range.mpr bounds.1,
        List.mem_map.mpr
          ⟨coordinate.2, List.mem_range.mpr bounds.2, by simp⟩⟩

/-- One endpoint edge at a rectangular coordinate. -/
def endpointEdgeAt (rightEndpoint : Bool)
    (input : VertexCoverInput × (Nat × Nat)) : Nat × Nat :=
  let sourceEdge := input.1.graph.edges.getD input.2.1 (0, 0)
  let endpoint := if rightEndpoint then sourceEdge.2 else sourceEdge.1
  (endpoint,
    VertexCoverToMostNeighborsCore.constraintVertex input.1 input.2.1 input.2.2)

/-- Two fixed-width passes over the same rectangle, one for each endpoint. -/
def fullConstraintEdges (input : VertexCoverInput) : List (Nat × Nat) :=
  ((coordinates input).map fun coordinate => endpointEdgeAt false (input, coordinate)) ++
    ((coordinates input).map fun coordinate => endpointEdgeAt true (input, coordinate))

def fullGadgetEdges (input : VertexCoverInput) : List (Nat × Nat) :=
  fullConstraintEdges input ++ VertexCoverToMostNeighborsCore.rootEdges input ++
    [(VertexCoverToMostNeighborsCore.rootVertex input,
      VertexCoverToMostNeighborsCore.leafVertex input)]

def fullGraph (input : VertexCoverInput) : GraphInput where
  vertices := VertexCoverToMostNeighborsCore.vertexCount input
  edges := fullGadgetEdges input
  directed := false

def fullExecutable (input : VertexCoverInput) : target.Instance where
  graph := fullGraph input
  threshold := VertexCoverToMostNeighborsCore.vertexCount input - (input.k + 1)

theorem mem_fullConstraintEdges_iff (input : VertexCoverInput) (edge : Nat × Nat) :
    edge ∈ fullConstraintEdges input ↔
      ∃ edgeIndex copyIndex,
        edgeIndex < input.graph.edges.length ∧
          copyIndex < VertexCoverToMostNeighborsCore.copyCount input ∧
          (edge = ((input.graph.edges.getD edgeIndex (0, 0)).1,
              VertexCoverToMostNeighborsCore.constraintVertex input edgeIndex copyIndex) ∨
            edge = ((input.graph.edges.getD edgeIndex (0, 0)).2,
              VertexCoverToMostNeighborsCore.constraintVertex input edgeIndex copyIndex)) := by
  constructor
  · intro member
    rcases List.mem_append.mp member with leftMember | rightMember
    · rcases List.mem_map.mp leftMember with ⟨coordinate, coordinateMember, equality⟩
      have bounds := (mem_coordinates_iff input coordinate).1 coordinateMember
      exact ⟨coordinate.1, coordinate.2, bounds.1, bounds.2,
        Or.inl (by simpa [endpointEdgeAt] using equality.symm)⟩
    · rcases List.mem_map.mp rightMember with ⟨coordinate, coordinateMember, equality⟩
      have bounds := (mem_coordinates_iff input coordinate).1 coordinateMember
      exact ⟨coordinate.1, coordinate.2, bounds.1, bounds.2,
        Or.inr (by simpa [endpointEdgeAt] using equality.symm)⟩
  · rintro ⟨edgeIndex, copyIndex, edgeBound, copyBound, left | right⟩
    · apply List.mem_append_left
      exact List.mem_map.mpr
        ⟨(edgeIndex, copyIndex),
          (mem_coordinates_iff input _).2 ⟨edgeBound, copyBound⟩,
          by simpa [endpointEdgeAt] using left.symm⟩
    · apply List.mem_append_right
      exact List.mem_map.mpr
        ⟨(edgeIndex, copyIndex),
          (mem_coordinates_iff input _).2 ⟨edgeBound, copyBound⟩,
          by simpa [endpointEdgeAt] using right.symm⟩

theorem constraintEdges_membership_iff_of_wellFormed (input : VertexCoverInput)
    (sourceWellFormed : WellFormed input.graph) (edge : Nat × Nat) :
    edge ∈ fullConstraintEdges input ↔
      edge ∈ VertexCoverToMostNeighborsCore.constraintEdges input := by
  constructor
  · intro member
    rcases (mem_fullConstraintEdges_iff input edge).1 member with
      ⟨edgeIndex, copyIndex, edgeBound, copyBound, localEdge⟩
    have sourceEdgeMember :=
      VertexCoverToMostNeighborsCore.edge_getD_mem input.graph.edges edgeBound
    have endpointBounds := sourceWellFormed _ sourceEdgeMember
    apply (VertexCoverToMostNeighborsCore.mem_constraintEdges_iff input edge).2
    refine ⟨edgeIndex, copyIndex, edgeBound, copyBound, ?_⟩
    rcases localEdge with left | right
    · exact Or.inl ⟨endpointBounds.1, left⟩
    · exact Or.inr ⟨endpointBounds.2, right⟩
  · intro member
    rcases (VertexCoverToMostNeighborsCore.mem_constraintEdges_iff input edge).1 member with
      ⟨edgeIndex, copyIndex, edgeBound, copyBound, localEdge⟩
    apply (mem_fullConstraintEdges_iff input edge).2
    refine ⟨edgeIndex, copyIndex, edgeBound, copyBound, ?_⟩
    rcases localEdge with ⟨_bound, left⟩ | ⟨_bound, right⟩
    · exact Or.inl left
    · exact Or.inr right

theorem gadgetEdges_membership_iff_of_wellFormed (input : VertexCoverInput)
    (sourceWellFormed : WellFormed input.graph) (edge : Nat × Nat) :
    edge ∈ fullGadgetEdges input ↔
      edge ∈ VertexCoverToMostNeighborsCore.gadgetEdges input := by
  simp only [fullGadgetEdges, VertexCoverToMostNeighborsCore.gadgetEdges, List.mem_append,
    List.mem_singleton]
  rw [constraintEdges_membership_iff_of_wellFormed input sourceWellFormed edge]

theorem adjacency_iff_of_wellFormed (input : VertexCoverInput)
    (sourceWellFormed : WellFormed input.graph) (left right : Nat) :
    HasUndirectedEdge (fullGraph input) left right ↔
      HasUndirectedEdge (VertexCoverToMostNeighborsCore.gadgetGraph input) left right := by
  unfold HasUndirectedEdge fullGraph VertexCoverToMostNeighborsCore.gadgetGraph
  rw [gadgetEdges_membership_iff_of_wellFormed input sourceWellFormed,
    gadgetEdges_membership_iff_of_wellFormed input sourceWellFormed]

theorem fullGraph_wellFormed (input : VertexCoverInput)
    (sourceWellFormed : WellFormed input.graph) :
    WellFormed (fullGraph input) := by
  intro edge member
  apply VertexCoverToMostNeighborsCore.graph_wellFormed input edge
  exact (gadgetEdges_membership_iff_of_wellFormed input sourceWellFormed edge).1 member

@[simp] theorem outsideVertices_fullExecutable (input : VertexCoverInput)
    (assignment : List Nat) :
    Presentation.MostNeighbors.outsideVertices (fullExecutable input) assignment =
      Presentation.MostNeighbors.outsideVertices
        (VertexCoverToMostNeighborsCore.executable input) assignment :=
  rfl

theorem outsideSupported_iff_of_wellFormed (input : VertexCoverInput)
    (sourceWellFormed : WellFormed input.graph) (assignment : List Nat) (vertex : Nat) :
    Presentation.MostNeighbors.OutsideSupported
        (fullExecutable input) assignment vertex ↔
      Presentation.MostNeighbors.OutsideSupported
        (VertexCoverToMostNeighborsCore.executable input) assignment vertex := by
  unfold Presentation.MostNeighbors.OutsideSupported
  constructor
  · rintro ⟨selected, selectedBound, selectedValue, adjacent⟩
    refine ⟨selected, selectedBound, selectedValue, ?_⟩
    exact (adjacency_iff_of_wellFormed input sourceWellFormed selected vertex).1 adjacent
  · rintro ⟨selected, selectedBound, selectedValue, adjacent⟩
    refine ⟨selected, selectedBound, selectedValue, ?_⟩
    exact (adjacency_iff_of_wellFormed input sourceWellFormed selected vertex).2 adjacent

theorem witness_iff_of_wellFormed (input : VertexCoverInput)
    (sourceWellFormed : WellFormed input.graph) (assignment : List Nat) :
    Presentation.MostNeighbors.Witness (fullExecutable input) assignment ↔
      Presentation.MostNeighbors.Witness
        (VertexCoverToMostNeighborsCore.executable input) assignment := by
  constructor
  · rintro ⟨length, values, threshold, supported⟩
    refine ⟨length, values, by simpa using threshold, ?_⟩
    intro vertex vertexBound outsideValue
    apply (outsideSupported_iff_of_wellFormed input sourceWellFormed assignment vertex).1
    exact supported vertex vertexBound outsideValue
  · rintro ⟨length, values, threshold, supported⟩
    refine ⟨length, values, by simpa using threshold, ?_⟩
    intro vertex vertexBound outsideValue
    apply (outsideSupported_iff_of_wellFormed input sourceWellFormed assignment vertex).2
    exact supported vertex vertexBound outsideValue

theorem fullExecutable_isYes_iff_core (input : VertexCoverInput)
    (sourceWellFormed : WellFormed input.graph) :
    Presentation.MostNeighbors.IsYes (fullExecutable input) ↔
      Presentation.MostNeighbors.IsYes
        (VertexCoverToMostNeighborsCore.executable input) := by
  constructor
  · rintro ⟨_undirected, _wellFormed, assignment, witness⟩
    exact ⟨rfl, VertexCoverToMostNeighborsCore.graph_wellFormed input, assignment,
      (witness_iff_of_wellFormed input sourceWellFormed assignment).1 witness⟩
  · rintro ⟨_undirected, _wellFormed, assignment, witness⟩
    exact ⟨rfl, fullGraph_wellFormed input sourceWellFormed, assignment,
      (witness_iff_of_wellFormed input sourceWellFormed assignment).2 witness⟩

theorem fullExecutable_correct_of_wellFormed (input : VertexCoverInput)
    (sourceWellFormed : WellFormed input.graph) :
    VertexCover input ↔ Presentation.MostNeighbors.IsYes (fullExecutable input) := by
  rw [fullExecutable_isYes_iff_core input sourceWellFormed]
  exact VertexCoverToMostNeighborsCore.executableCorrect input

/-- Exact composed production executable from the standard Clique endpoint. -/
noncomputable def executable (input : source.Instance) : target.Instance :=
  fullExecutable (ComplexityReduction.Karp21.VertexCover.map input)

theorem mappedVertexCover_wellFormed (input : CliqueInput) :
    WellFormed (ComplexityReduction.Karp21.VertexCover.map input).graph := by
  unfold ComplexityReduction.Karp21.VertexCover.map
  split
  · exact ComplexityReduction.Karp21.VertexCover.complementGraph_wellFormed input.graph
  · intro edge member
    change edge ∈ [(0, 1)] at member
    simp only [List.mem_singleton] at member
    subst edge
    change (0 : Nat) < 2 ∧ (1 : Nat) < 2
    exact ⟨by omega, by omega⟩

/-- Mathematical correctness of the exact public executable. -/
theorem executableCorrect :
    Agent.Hardness.Authoring.ExecutableSemanticProof source target executable := by
  intro input
  change Clique input ↔ Presentation.MostNeighbors.IsYes (executable input)
  rw [show Clique input ↔
      VertexCover (ComplexityReduction.Karp21.VertexCover.map input) by
    simpa [ComplexityReduction.Combinatorics.Graph.cliqueDecisionProblem] using
      ComplexityReduction.Karp21.VertexCover.map_correct input]
  exact fullExecutable_correct_of_wellFormed _ (mappedVertexCover_wellFormed input)

/-! ### Direct-TM realization of the exact production executable -/

abbrev edgeEncodedType : EncodedType :=
  ComplexityReduction.Combinatorics.Graph.edgeStructuredEncodedType

abbrev edgeListEncodedType : EncodedType :=
  ComplexityReduction.Combinatorics.Graph.edgeListStructuredEncodedType

abbrev vertexCoverEncodedType : EncodedType :=
  ComplexityReduction.Combinatorics.Graph.vertexCoverStructuredEncodedType

abbrev endpointContextEncodedType : EncodedType :=
  EncodedType.prod vertexCoverEncodedType RectangularCoordinates.coordinateEncodedType

private theorem copyCount_tmPolyTime :
    TMPolyTimeMap vertexCoverEncodedType EncodedType.nat
      VertexCoverToMostNeighborsCore.copyCount := by
  have budget : TMPolyTimeMap vertexCoverEncodedType EncodedType.nat
      (fun input : VertexCoverInput => input.k) := by
    simpa [vertexCoverEncodedType] using
      Problems.Karp21.GraphAtoms.vertexCoverBudgetPrimitive_directTM
  have successor := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime budget
  have successorTwice := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime successor
  simpa [Function.comp, VertexCoverToMostNeighborsCore.copyCount,
    Nat.succ_eq_add_one, Nat.add_assoc] using successorTwice

private theorem endpointEdgeAt_tmPolyTime (rightEndpoint : Bool) :
    TMPolyTimeMap endpointContextEncodedType edgeEncodedType
      (endpointEdgeAt rightEndpoint) := by
  let X := endpointContextEncodedType
  have sourceInput : TMPolyTimeMap X vertexCoverEncodedType
      (fun input : VertexCoverInput × (Nat × Nat) => input.1) := by
    simpa [X, endpointContextEncodedType] using
      TMPolyTimeMap.fst vertexCoverEncodedType RectangularCoordinates.coordinateEncodedType
  have coordinate : TMPolyTimeMap X RectangularCoordinates.coordinateEncodedType
      (fun input : VertexCoverInput × (Nat × Nat) => input.2) := by
    simpa [X, endpointContextEncodedType] using
      TMPolyTimeMap.snd vertexCoverEncodedType RectangularCoordinates.coordinateEncodedType
  have graph : TMPolyTimeMap X graphStructuredEncodedType
      (fun input : VertexCoverInput × (Nat × Nat) => input.1.graph) := by
    have composed := TMPolyTimeMap.comp
      Problems.Karp21.GraphAtoms.vertexCoverGraphPrimitive_directTM sourceInput
    simpa [Function.comp, X, vertexCoverEncodedType] using composed
  have vertices : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput × (Nat × Nat) => input.1.graph.vertices) := by
    have composed := TMPolyTimeMap.comp
      Problems.Karp21.GraphAtoms.graphVerticesPrimitive_directTM graph
    simpa [Function.comp, X] using composed
  have graphPayload : TMPolyTimeMap X graphPayloadStructuredEncodedType
      (fun input : VertexCoverInput × (Nat × Nat) =>
        ComplexityReduction.Karp21.graphPayloadOfGraph input.1.graph) := by
    have composed := TMPolyTimeMap.comp
      Problems.Karp21.GraphAtoms.graphPayloadPrimitive_directTM graph
    simpa [Function.comp, X] using composed
  have edges : TMPolyTimeMap X edgeListEncodedType
      (fun input : VertexCoverInput × (Nat × Nat) => input.1.graph.edges) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst edgeListEncodedType EncodedType.bool) graphPayload
    simpa [Function.comp, ComplexityReduction.Karp21.graphPayloadOfGraph,
      graphPayloadStructuredEncodedType, X]
      using composed
  have edgeIndex : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput × (Nat × Nat) => input.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) coordinate
    simpa [Function.comp, RectangularCoordinates.coordinateEncodedType, X] using composed
  have copyIndex : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput × (Nat × Nat) => input.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat) coordinate
    simpa [Function.comp, RectangularCoordinates.coordinateEncodedType, X] using composed
  have lookupInput : TMPolyTimeMap X
      (EncodedType.prod edgeListEncodedType EncodedType.nat)
      (fun input : VertexCoverInput × (Nat × Nat) =>
        (input.1.graph.edges, input.2.1)) :=
    TMPolyTimeMap.prod_mk edges edgeIndex
  have sourceEdge : TMPolyTimeMap X edgeEncodedType
      (fun input : VertexCoverInput × (Nat × Nat) =>
        input.1.graph.edges.getD input.2.1 (0, 0)) := by
    have composed := TMPolyTimeMap.comp
      (Karp21.EncodedListLookup.getD_tm_polytime edgeEncodedType
        (show edgeEncodedType.Carrier from ((0, 0) : Nat × Nat))) lookupInput
    simpa [Function.comp, Karp21.EncodedListLookup.getD, X] using composed
  have endpoint : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput × (Nat × Nat) =>
        if rightEndpoint then
          (input.1.graph.edges.getD input.2.1 (0, 0)).2
        else (input.1.graph.edges.getD input.2.1 (0, 0)).1) := by
    cases rightEndpoint
    · have composed := TMPolyTimeMap.comp
        (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) sourceEdge
      simpa [Function.comp, edgeEncodedType, X] using composed
    · have composed := TMPolyTimeMap.comp
        (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat) sourceEdge
      simpa [Function.comp, edgeEncodedType, X] using composed
  have copyCount : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput × (Nat × Nat) =>
        VertexCoverToMostNeighborsCore.copyCount input.1) := by
    have composed := TMPolyTimeMap.comp copyCount_tmPolyTime sourceInput
    simpa [Function.comp, X] using composed
  have productInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : VertexCoverInput × (Nat × Nat) =>
        (input.2.1, VertexCoverToMostNeighborsCore.copyCount input.1)) :=
    TMPolyTimeMap.prod_mk edgeIndex copyCount
  have product : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput × (Nat × Nat) =>
        input.2.1 * VertexCoverToMostNeighborsCore.copyCount input.1) := by
    have composed := TMPolyTimeMap.comp GenericNatTM.natMul_tm_polytime productInput
    simpa [Function.comp, X] using composed
  have firstAddInput : TMPolyTimeMap X natAddInputEncodedType
      (fun input : VertexCoverInput × (Nat × Nat) =>
        (input.1.graph.vertices,
          input.2.1 * VertexCoverToMostNeighborsCore.copyCount input.1)) := by
    simpa [natAddInputEncodedType] using TMPolyTimeMap.prod_mk vertices product
  have firstAdd : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput × (Nat × Nat) =>
        input.1.graph.vertices +
          input.2.1 * VertexCoverToMostNeighborsCore.copyCount input.1) := by
    have composed := TMPolyTimeMap.comp natAdd_tm_polytime firstAddInput
    simpa [Function.comp] using composed
  have secondAddInput : TMPolyTimeMap X natAddInputEncodedType
      (fun input : VertexCoverInput × (Nat × Nat) =>
        (input.1.graph.vertices +
          input.2.1 * VertexCoverToMostNeighborsCore.copyCount input.1,
          input.2.2)) := by
    simpa [natAddInputEncodedType] using TMPolyTimeMap.prod_mk firstAdd copyIndex
  have constraint : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput × (Nat × Nat) =>
        VertexCoverToMostNeighborsCore.constraintVertex input.1 input.2.1 input.2.2) := by
    have composed := TMPolyTimeMap.comp natAdd_tm_polytime secondAddInput
    simpa [Function.comp, VertexCoverToMostNeighborsCore.constraintVertex] using composed
  simpa [endpointEdgeAt, edgeEncodedType, X] using
    TMPolyTimeMap.prod_mk endpoint constraint

def graphTupleToGraph
    (payload : graphTupleStructuredEncodedType.Carrier) : GraphInput where
  vertices := payload.1
  edges := payload.2.1
  directed := payload.2.2

private theorem graphTupleToGraph_encode
    (payload : graphTupleStructuredEncodedType.Carrier) :
    graphStructuredEncodedType.encode (graphTupleToGraph payload) =
      graphTupleStructuredEncodedType.encode payload := by
  rcases payload with ⟨vertices, edges, directed⟩
  rfl

private noncomputable def graphTupleToGraphTMBackedMap :
    TMBackedCostedMap graphTupleStructuredEncodedType graphStructuredEncodedType
      graphTupleToGraph :=
  TMBackedCostedMap.ofEncodingEquiv
    graphTupleStructuredEncodedType graphStructuredEncodedType graphTupleToGraph
    (Equiv.refl graphTupleStructuredEncodedType.Symbol)
    (by
      intro payload
      change graphStructuredEncodedType.encode (graphTupleToGraph payload) =
        (graphTupleStructuredEncodedType.encode payload).map id
      simp [graphTupleToGraph_encode])

def mostNeighborsTupleToInput
    (payload : Presentation.MostNeighbors.tupleStructuredEncodedType.Carrier) :
    Presentation.MostNeighbors.Input where
  graph := payload.1
  threshold := payload.2

private theorem mostNeighborsTupleToInput_encode
    (payload : Presentation.MostNeighbors.tupleStructuredEncodedType.Carrier) :
    Presentation.MostNeighbors.structuredEncodedType.encode
        (mostNeighborsTupleToInput payload) =
      Presentation.MostNeighbors.tupleStructuredEncodedType.encode payload := by
  rcases payload with ⟨graph, threshold⟩
  rfl

private noncomputable def mostNeighborsTupleToInputTMBackedMap :
    TMBackedCostedMap Presentation.MostNeighbors.tupleStructuredEncodedType
      Presentation.MostNeighbors.structuredEncodedType mostNeighborsTupleToInput :=
  TMBackedCostedMap.ofEncodingEquiv
    Presentation.MostNeighbors.tupleStructuredEncodedType
    Presentation.MostNeighbors.structuredEncodedType mostNeighborsTupleToInput
    (Equiv.refl Presentation.MostNeighbors.tupleStructuredEncodedType.Symbol)
    (by
      intro payload
      change Presentation.MostNeighbors.structuredEncodedType.encode
          (mostNeighborsTupleToInput payload) =
        (Presentation.MostNeighbors.tupleStructuredEncodedType.encode payload).map id
      simp [mostNeighborsTupleToInput_encode])

/-- Direct-TM evidence for the exact Vertex-Cover gadget executable. -/
private theorem fullExecutable_tmPolyTime :
    TMPolyTimeMap vertexCoverEncodedType
      Presentation.MostNeighbors.structuredEncodedType fullExecutable := by
  let X := vertexCoverEncodedType
  have sourceInput : TMPolyTimeMap X vertexCoverEncodedType
      (fun input : VertexCoverInput => input) := by
    simpa [X] using TMPolyTimeMap.id vertexCoverEncodedType
  have graph : TMPolyTimeMap X graphStructuredEncodedType
      (fun input : VertexCoverInput => input.graph) := by
    simpa [X, vertexCoverEncodedType] using
      Problems.Karp21.GraphAtoms.vertexCoverGraphPrimitive_directTM
  have budget : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput => input.k) := by
    simpa [X, vertexCoverEncodedType] using
      Problems.Karp21.GraphAtoms.vertexCoverBudgetPrimitive_directTM
  have vertices : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput => input.graph.vertices) := by
    have composed := TMPolyTimeMap.comp
      Problems.Karp21.GraphAtoms.graphVerticesPrimitive_directTM graph
    simpa [Function.comp, X] using composed
  have graphPayload : TMPolyTimeMap X graphPayloadStructuredEncodedType
      (fun input : VertexCoverInput =>
        ComplexityReduction.Karp21.graphPayloadOfGraph input.graph) := by
    have composed := TMPolyTimeMap.comp
      Problems.Karp21.GraphAtoms.graphPayloadPrimitive_directTM graph
    simpa [Function.comp, X] using composed
  have sourceEdges : TMPolyTimeMap X edgeListEncodedType
      (fun input : VertexCoverInput => input.graph.edges) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst edgeListEncodedType EncodedType.bool) graphPayload
    simpa [Function.comp, ComplexityReduction.Karp21.graphPayloadOfGraph,
      graphPayloadStructuredEncodedType, X] using composed
  have edgeCount : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput => input.graph.edges.length) := by
    have composed := TMPolyTimeMap.comp
      (Karp21.HittingSet.listLengthTMBackedMap edgeEncodedType).tm_polytime sourceEdges
    simpa [Function.comp, edgeListEncodedType, X] using composed
  have copyCount : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput =>
        VertexCoverToMostNeighborsCore.copyCount input) := by
    simpa [X] using copyCount_tmPolyTime
  have coordinateBounds : TMPolyTimeMap X
      RectangularCoordinates.familyContextEncodedType
      (fun input : VertexCoverInput =>
        (input.graph.edges.length,
          VertexCoverToMostNeighborsCore.copyCount input)) := by
    simpa [RectangularCoordinates.familyContextEncodedType,
      RectangularCoordinates.coordinateEncodedType] using
      TMPolyTimeMap.prod_mk edgeCount copyCount
  have coordinateList : TMPolyTimeMap X
      RectangularCoordinates.coordinateListEncodedType coordinates := by
    have composed := TMPolyTimeMap.comp
      RectangularCoordinates.familyExecutable_tmPolyTime coordinateBounds
    simpa [Function.comp, coordinates, X] using composed
  have coordinateContextInput : TMPolyTimeMap X
      (EncodedType.prod vertexCoverEncodedType
        RectangularCoordinates.coordinateListEncodedType)
      (fun input : VertexCoverInput => (input, coordinates input)) :=
    TMPolyTimeMap.prod_mk sourceInput coordinateList
  have attachedCoordinates : TMPolyTimeMap X
      (EncodedType.list endpointContextEncodedType)
      (fun input : VertexCoverInput =>
        Program.contextListMapExecutable
          (C := vertexCoverEncodedType)
          (X := RectangularCoordinates.coordinateEncodedType)
          (input, coordinates input)) := by
    have composed := TMPolyTimeMap.comp
      (Program.contextListMapExecutable_tmPolyTime vertexCoverEncodedType
        RectangularCoordinates.coordinateEncodedType) coordinateContextInput
    simpa [Function.comp, endpointContextEncodedType, X] using composed
  have leftEdges : TMPolyTimeMap X edgeListEncodedType
      (fun input : VertexCoverInput =>
        (coordinates input).map fun coordinate =>
          endpointEdgeAt false (input, coordinate)) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_map (endpointEdgeAt_tmPolyTime false)) attachedCoordinates
    convert composed using 1
    funext input
    change
      (coordinates input).map (fun coordinate => endpointEdgeAt false (input, coordinate)) =
        (Program.contextListMapExecutable
          (C := vertexCoverEncodedType)
          (X := RectangularCoordinates.coordinateEncodedType)
          (input, coordinates input)).map (endpointEdgeAt false)
    rw [Program.contextListMapExecutable_eq_map]
    change
      (coordinates input).map (fun coordinate => endpointEdgeAt false (input, coordinate)) =
        ((coordinates input).map (fun element : Nat × Nat => (input, element))).map
          (endpointEdgeAt false)
    rw [List.map_map]
    simp [Function.comp]
  have rightEdges : TMPolyTimeMap X edgeListEncodedType
      (fun input : VertexCoverInput =>
        (coordinates input).map fun coordinate =>
          endpointEdgeAt true (input, coordinate)) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_map (endpointEdgeAt_tmPolyTime true)) attachedCoordinates
    convert composed using 1
    funext input
    change
      (coordinates input).map (fun coordinate => endpointEdgeAt true (input, coordinate)) =
        (Program.contextListMapExecutable
          (C := vertexCoverEncodedType)
          (X := RectangularCoordinates.coordinateEncodedType)
          (input, coordinates input)).map (endpointEdgeAt true)
    rw [Program.contextListMapExecutable_eq_map]
    change
      (coordinates input).map (fun coordinate => endpointEdgeAt true (input, coordinate)) =
        ((coordinates input).map (fun element : Nat × Nat => (input, element))).map
          (endpointEdgeAt true)
    rw [List.map_map]
    simp [Function.comp]
  have constraintAppendInput : TMPolyTimeMap X
      (EncodedType.prod edgeListEncodedType edgeListEncodedType)
      (fun input : VertexCoverInput =>
        ((coordinates input).map fun coordinate =>
            endpointEdgeAt false (input, coordinate),
          (coordinates input).map fun coordinate =>
            endpointEdgeAt true (input, coordinate))) :=
    TMPolyTimeMap.prod_mk leftEdges rightEdges
  have constraintEdges : TMPolyTimeMap X edgeListEncodedType fullConstraintEdges := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append edgeEncodedType) constraintAppendInput
    simpa [Function.comp, fullConstraintEdges, edgeListEncodedType] using composed
  have constraintCountInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : VertexCoverInput =>
        (input.graph.edges.length,
          VertexCoverToMostNeighborsCore.copyCount input)) :=
    TMPolyTimeMap.prod_mk edgeCount copyCount
  have constraintCount : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput =>
        VertexCoverToMostNeighborsCore.constraintCount input) := by
    have composed := TMPolyTimeMap.comp GenericNatTM.natMul_tm_polytime
      constraintCountInput
    simpa [Function.comp, VertexCoverToMostNeighborsCore.constraintCount] using composed
  have rootInput : TMPolyTimeMap X natAddInputEncodedType
      (fun input : VertexCoverInput =>
        (input.graph.vertices,
          VertexCoverToMostNeighborsCore.constraintCount input)) := by
    simpa [natAddInputEncodedType] using TMPolyTimeMap.prod_mk vertices constraintCount
  have root : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput => VertexCoverToMostNeighborsCore.rootVertex input) := by
    have composed := TMPolyTimeMap.comp natAdd_tm_polytime rootInput
    simpa [Function.comp, VertexCoverToMostNeighborsCore.rootVertex] using composed
  have vertexRange : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun input : VertexCoverInput => List.range input.graph.vertices) := by
    have composed := TMPolyTimeMap.comp natRange_tm_polytime vertices
    simpa [Function.comp] using composed
  have rootContextInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
      (fun input : VertexCoverInput =>
        (VertexCoverToMostNeighborsCore.rootVertex input,
          List.range input.graph.vertices)) :=
    TMPolyTimeMap.prod_mk root vertexRange
  have rootEdgesExecutable : TMPolyTimeMap X edgeListEncodedType
      (fun input : VertexCoverInput =>
        Program.contextListMapExecutable
          (C := EncodedType.nat) (X := EncodedType.nat)
          (VertexCoverToMostNeighborsCore.rootVertex input,
            List.range input.graph.vertices)) := by
    have composed := TMPolyTimeMap.comp
      (Program.contextListMapExecutable_tmPolyTime EncodedType.nat EncodedType.nat)
      rootContextInput
    simpa [Function.comp, edgeListEncodedType, edgeEncodedType] using composed
  have rootEdges : TMPolyTimeMap X edgeListEncodedType
      VertexCoverToMostNeighborsCore.rootEdges := by
    convert rootEdgesExecutable using 1
    funext input
    rw [Program.contextListMapExecutable_eq_map]
    rfl
  have leaf : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput => VertexCoverToMostNeighborsCore.leafVertex input) := by
    have composed := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime root
    simpa [Function.comp, VertexCoverToMostNeighborsCore.leafVertex,
      Nat.succ_eq_add_one] using composed
  have rootLeaf : TMPolyTimeMap X edgeEncodedType
      (fun input : VertexCoverInput =>
        (VertexCoverToMostNeighborsCore.rootVertex input,
          VertexCoverToMostNeighborsCore.leafVertex input)) := by
    simpa [edgeEncodedType] using TMPolyTimeMap.prod_mk root leaf
  have rootLeafSingleton : TMPolyTimeMap X edgeListEncodedType
      (fun input : VertexCoverInput =>
        [(VertexCoverToMostNeighborsCore.rootVertex input,
          VertexCoverToMostNeighborsCore.leafVertex input)]) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton edgeEncodedType) rootLeaf
    simpa [Function.comp, edgeListEncodedType] using composed
  have firstEdgeAppendInput : TMPolyTimeMap X
      (EncodedType.prod edgeListEncodedType edgeListEncodedType)
      (fun input : VertexCoverInput =>
        (fullConstraintEdges input,
          VertexCoverToMostNeighborsCore.rootEdges input)) :=
    TMPolyTimeMap.prod_mk constraintEdges rootEdges
  have firstEdgeAppend : TMPolyTimeMap X edgeListEncodedType
      (fun input : VertexCoverInput =>
        fullConstraintEdges input ++ VertexCoverToMostNeighborsCore.rootEdges input) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append edgeEncodedType) firstEdgeAppendInput
    simpa [Function.comp, edgeListEncodedType] using composed
  have finalEdgeAppendInput : TMPolyTimeMap X
      (EncodedType.prod edgeListEncodedType edgeListEncodedType)
      (fun input : VertexCoverInput =>
        (fullConstraintEdges input ++ VertexCoverToMostNeighborsCore.rootEdges input,
          [(VertexCoverToMostNeighborsCore.rootVertex input,
            VertexCoverToMostNeighborsCore.leafVertex input)])) :=
    TMPolyTimeMap.prod_mk firstEdgeAppend rootLeafSingleton
  have gadgetEdges : TMPolyTimeMap X edgeListEncodedType fullGadgetEdges := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append edgeEncodedType) finalEdgeAppendInput
    simpa [Function.comp, fullGadgetEdges, edgeListEncodedType,
      List.append_assoc] using composed
  have vertexCount : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput => VertexCoverToMostNeighborsCore.vertexCount input) := by
    have composed := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime leaf
    simpa [Function.comp, VertexCoverToMostNeighborsCore.vertexCount,
      Nat.succ_eq_add_one] using composed
  have falseFlag : TMPolyTimeMap X EncodedType.bool
      (fun _input : VertexCoverInput => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have outputGraphPayload : TMPolyTimeMap X graphPayloadStructuredEncodedType
      (fun input : VertexCoverInput => (fullGadgetEdges input, false)) := by
    simpa [graphPayloadStructuredEncodedType] using
      TMPolyTimeMap.prod_mk gadgetEdges falseFlag
  have outputGraphTuple : TMPolyTimeMap X graphTupleStructuredEncodedType
      (fun input : VertexCoverInput =>
        (VertexCoverToMostNeighborsCore.vertexCount input,
          (fullGadgetEdges input, false))) := by
    simpa [graphTupleStructuredEncodedType] using
      TMPolyTimeMap.prod_mk vertexCount outputGraphPayload
  have outputGraph : TMPolyTimeMap X graphStructuredEncodedType fullGraph := by
    have composed := TMPolyTimeMap.comp graphTupleToGraphTMBackedMap.tm_polytime
      outputGraphTuple
    simpa [Function.comp, graphTupleToGraph, fullGraph] using composed
  have budgetSuccessor : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput => input.k + 1) := by
    have composed := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime budget
    simpa [Function.comp, Nat.succ_eq_add_one] using composed
  have thresholdInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : VertexCoverInput =>
        (VertexCoverToMostNeighborsCore.vertexCount input, input.k + 1)) :=
    TMPolyTimeMap.prod_mk vertexCount budgetSuccessor
  have threshold : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput =>
        VertexCoverToMostNeighborsCore.vertexCount input - (input.k + 1)) := by
    have composed := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub thresholdInput
    simpa [Function.comp] using composed
  have outputTuple : TMPolyTimeMap X
      Presentation.MostNeighbors.tupleStructuredEncodedType
      (fun input : VertexCoverInput =>
        (fullGraph input,
          VertexCoverToMostNeighborsCore.vertexCount input - (input.k + 1))) := by
    simpa [Presentation.MostNeighbors.tupleStructuredEncodedType] using
      TMPolyTimeMap.prod_mk outputGraph threshold
  have output := TMPolyTimeMap.comp
    mostNeighborsTupleToInputTMBackedMap.tm_polytime outputTuple
  simpa [Function.comp, mostNeighborsTupleToInput, fullExecutable, X] using output

/-- Direct-TM evidence for the exact composed Clique-to-Most-Neighbors executable. -/
theorem executableDirectTM :
    Agent.Hardness.Authoring.ExecutableDirectTMEvidence source target executable := by
  have mapped := ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverStructured_tm_polytime
  have composed := TMPolyTimeMap.comp fullExecutable_tmPolyTime mapped
  simpa [Function.comp, executable, source, target,
    Problems.Karp21.GraphAtoms.cliqueStructuredProblem,
    Problems.Karp21.GraphAtoms.cliqueStructuredPresentation,
    Presentation.MostNeighbors.presentedProblem,
    Presentation.MostNeighbors.structuredPresentation,
    vertexCoverEncodedType] using composed

/-- Exact atomic primitive for the audited production lower-bound edge. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def primitive :
    Primitive source.representation target.representation :=
  Primitive.ofTMPolyTime executable executableDirectTM

/-- Registered Clique-to-Most-Neighbors edge used by completeness transport. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def certifiedReduction : CertifiedReduction source target where
  program := .atom primitive
  correct := by
    intro input
    change source.accepts input ↔ target.accepts (primitive.run input)
    rw [show primitive.run input = executable input by rfl]
    exact executableCorrect input

/-- Discoverable authoring packet for the public production route. -/
@[complexity_reduction_ir_hardness_program_reduction_template]
def template : Agent.Hardness.Authoring.ProgramIndexedReductionTemplate
    .finalComposition source target executable executableDirectTM executableCorrect :=
  ⟨trivial⟩

end VertexCoverToMostNeighbors
end Domain
end ComplexityReduction

assert_standard_axioms
  ComplexityReduction.Domain.VertexCoverToMostNeighbors.executableDirectTM,
  ComplexityReduction.Domain.VertexCoverToMostNeighbors.executableCorrect,
  ComplexityReduction.Domain.VertexCoverToMostNeighbors.primitive,
  ComplexityReduction.Domain.VertexCoverToMostNeighbors.certifiedReduction
