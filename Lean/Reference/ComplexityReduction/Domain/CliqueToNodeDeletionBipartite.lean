/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.Domain.SetSystemMembershipPairs
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatArithmetic
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.VertexCover
import ComplexityReduction.Legacy.IR.Domains.SetSystem
import ComplexityReduction.Presentation.NodeDeletionBipartite
import ComplexityReduction.Problems.Karp21.GraphAtoms
import ComplexityReduction.Program.ContextListMap
import Mathlib.Tactic

/-!
Public Clique to Node Deletion to Bipartite reduction.

The executable first applies the canonical Clique-to-Vertex-Cover map.  It
then adds one fresh vertex per source edge and closes a triangle on that edge.
Deleting a vertex cover makes the remaining graph bipartite; conversely every
valid deletion set must hit each triangle and projects to a vertex cover.
-/

namespace ComplexityReduction
namespace Domain
namespace CliqueToNodeDeletionBipartite

open Encoding
open Certificate
open Program
open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

abbrev source : PresentedProblem :=
  Problems.Karp21.GraphAtoms.cliqueStructuredProblem

abbrev target : PresentedProblem :=
  Presentation.NodeDeletionBipartite.presentedProblem

/-- Each source edge contributes the ordered two-endpoint set `[u, v]`. -/
def endpointFamily (graph : GraphInput) : List (List Nat) :=
  graph.edges.map fun edge => [edge.1, edge.2]

def endpointSystem (graph : GraphInput) : SetSystemInput where
  universeSize := graph.vertices
  sets := endpointFamily graph

/-- Ordered `(endpoint, edgeIndex)` pairs for all source edges. -/
def endpointPairs (graph : GraphInput) : List (Nat × Nat) :=
  SetSystem.membershipPairs (endpointSystem graph)

def gadgetVertex (graph : GraphInput) (edgeIndex : Nat) : Nat :=
  graph.vertices + edgeIndex

/-- Attach both endpoints of every source edge to its fresh gadget vertex. -/
def gadgetEdges (graph : GraphInput) : List (Nat × Nat) :=
  (endpointPairs graph).map fun pair => (pair.1, gadgetVertex graph pair.2)

/-- Triangle expansion of an undirected graph. -/
def triangleGraph (graph : GraphInput) : GraphInput where
  vertices := graph.vertices + graph.edges.length
  edges := graph.edges ++ gadgetEdges graph
  directed := false

/-- Vertex-Cover instance reinterpreted as a node-deletion instance. -/
def fromVertexCover (input : VertexCoverInput) : Presentation.NodeDeletionBipartite.Input where
  graph := triangleGraph input.graph
  budget := input.k

/-- Exact public executable from Clique. -/
noncomputable def executable (input : source.Instance) : target.Instance :=
  fromVertexCover (ComplexityReduction.Karp21.VertexCover.map input)

theorem endpointPair_bounds {graph : GraphInput} (wellFormed : WellFormed graph)
    {pair : Nat × Nat} (member : pair ∈ endpointPairs graph) :
    pair.1 < graph.vertices ∧ pair.2 < graph.edges.length := by
  constructor
  · rcases SetSystem.mem_membershipPairsFrom_left_mem
      (start := 0) (sets := (endpointSystem graph).sets) member with
      ⟨endpointSet, setMember, endpointMember⟩
    rcases List.mem_map.mp setMember with ⟨edge, edgeMember, rfl⟩
    have edgeBounds := wellFormed edge edgeMember
    simp at endpointMember
    rcases endpointMember with endpointEq | endpointEq
    · rw [endpointEq]
      exact edgeBounds.1
    · rw [endpointEq]
      exact edgeBounds.2
  · have bound := SetSystem.mem_membershipPairsFrom_right_lt
      (start := 0) (sets := (endpointSystem graph).sets) member
    simpa [endpointPairs, endpointSystem, endpointFamily, SetSystem.membershipPairs] using bound

theorem gadgetEdge_of_pair {graph : GraphInput} {endpoint edgeIndex : Nat}
    (member : (endpoint, edgeIndex) ∈ endpointPairs graph) :
    (endpoint, gadgetVertex graph edgeIndex) ∈ gadgetEdges graph :=
  List.mem_map.mpr ⟨(endpoint, edgeIndex), member, rfl⟩

private theorem indexedEndpointPair_of_edge
    {graph : GraphInput} {edge : Nat × Nat} (edgeMember : edge ∈ graph.edges) :
    (edge.1, graph.edges.idxOf edge) ∈ endpointPairs graph ∧
      (edge.2, graph.edges.idxOf edge) ∈ endpointPairs graph := by
  have indexedEdge : graph.edges[graph.edges.idxOf edge]? = some edge :=
    List.getElem?_idxOf edgeMember
  have indexedEndpointSet :
      (endpointSystem graph).sets[graph.edges.idxOf edge]? =
        some [edge.1, edge.2] := by
    simpa [endpointSystem, endpointFamily] using indexedEdge
  constructor
  · apply SetSystem.mem_membershipPairs_iff.mpr
    exact ⟨[edge.1, edge.2], indexedEndpointSet, by simp⟩
  · apply SetSystem.mem_membershipPairs_iff.mpr
    exact ⟨[edge.1, edge.2], indexedEndpointSet, by simp⟩

theorem firstGadgetEdge_of_edge {graph : GraphInput} {edge : Nat × Nat}
    (edgeMember : edge ∈ graph.edges) :
    (edge.1, gadgetVertex graph (graph.edges.idxOf edge)) ∈ gadgetEdges graph :=
  gadgetEdge_of_pair (indexedEndpointPair_of_edge edgeMember).1

theorem secondGadgetEdge_of_edge {graph : GraphInput} {edge : Nat × Nat}
    (edgeMember : edge ∈ graph.edges) :
    (edge.2, gadgetVertex graph (graph.edges.idxOf edge)) ∈ gadgetEdges graph :=
  gadgetEdge_of_pair (indexedEndpointPair_of_edge edgeMember).2

theorem triangleGraph_wellFormed {graph : GraphInput} (wellFormed : WellFormed graph) :
    WellFormed (triangleGraph graph) := by
  intro edge edgeMember
  rcases List.mem_append.mp edgeMember with original | added
  · have bounds := wellFormed edge original
    have leftBound : edge.1 < graph.vertices := bounds.1
    have rightBound : edge.2 < graph.vertices := bounds.2
    change edge.1 < graph.vertices + graph.edges.length ∧
      edge.2 < graph.vertices + graph.edges.length
    omega
  · rcases List.mem_map.mp added with ⟨pair, pairMember, rfl⟩
    have bounds := endpointPair_bounds wellFormed pairMember
    change pair.1 < graph.vertices + graph.edges.length ∧
      graph.vertices + pair.2 < graph.vertices + graph.edges.length
    omega

def triangleColor (originalVertices : Nat) (vertex : Nat) : Bool :=
  if vertex < originalVertices then false else true

theorem cover_to_deletion
    {input : VertexCoverInput} (graphWellFormed : WellFormed input.graph)
    {cover : List Nat}
    (coverLength : cover.length ≤ input.k)
    (coverNodup : cover.Nodup)
    (coverBounds : VerticesWithinBounds input.graph cover)
    (covers : CoversEdges input.graph cover) :
    Presentation.NodeDeletionBipartite.Witness (fromVertexCover input) cover := by
  refine ⟨coverNodup, ?_, coverLength, triangleColor input.graph.vertices, ?_⟩
  · intro vertex member
    have bound := coverBounds vertex member
    simp [fromVertexCover, triangleGraph]
    omega
  · intro edge edgeMember
    rcases List.mem_append.mp edgeMember with original | added
    · rcases covers edge original with leftDeleted | rightDeleted
      · exact Or.inl leftDeleted
      · exact Or.inr (Or.inl rightDeleted)
    · rcases List.mem_map.mp added with ⟨pair, pairMember, rfl⟩
      by_cases endpointDeleted : pair.1 ∈ cover
      · exact Or.inl endpointDeleted
      · right
        right
        have bounds := endpointPair_bounds graphWellFormed pairMember
        simp [triangleColor, gadgetVertex, bounds.1]

def projectDeleted (graph : GraphInput) (vertex : Nat) : Nat :=
  if vertex < graph.vertices then vertex
  else (graph.edges.getD (vertex - graph.vertices) (0, 0)).1

def projectedCover (graph : GraphInput) (deleted : List Nat) : List Nat :=
  (deleted.map (projectDeleted graph)).dedup

theorem projectDeleted_bounds {graph : GraphInput} (wellFormed : WellFormed graph)
    {vertex : Nat} (bound : vertex < (triangleGraph graph).vertices) :
    projectDeleted graph vertex < graph.vertices := by
  by_cases original : vertex < graph.vertices
  · simp [projectDeleted, original]
  · have indexBound : vertex - graph.vertices < graph.edges.length := by
      simp [triangleGraph] at bound
      omega
    have selectedEdgeMember :
        graph.edges.getD (vertex - graph.vertices) (0, 0) ∈ graph.edges := by
      rw [List.getD_eq_getElem (l := graph.edges) (d := (0, 0))
        (n := vertex - graph.vertices) indexBound]
      exact List.getElem_mem indexBound
    have edgeBounds := wellFormed
      (graph.edges.getD (vertex - graph.vertices) (0, 0)) selectedEdgeMember
    rw [projectDeleted, if_neg original]
    exact edgeBounds.1

theorem projectDeleted_original {graph : GraphInput} {vertex : Nat}
    (bound : vertex < graph.vertices) :
    projectDeleted graph vertex = vertex := by
  simp [projectDeleted, bound]

theorem projectDeleted_gadget {graph : GraphInput} {edge : Nat × Nat}
    (edgeMember : edge ∈ graph.edges) :
    projectDeleted graph (gadgetVertex graph (graph.edges.idxOf edge)) = edge.1 := by
  have indexBound : graph.edges.idxOf edge < graph.edges.length :=
    List.idxOf_lt_length_iff.mpr edgeMember
  have notOriginal : ¬ gadgetVertex graph (graph.edges.idxOf edge) < graph.vertices := by
    simp [gadgetVertex]
  rw [projectDeleted, if_neg notOriginal]
  have subtraction :
      gadgetVertex graph (graph.edges.idxOf edge) - graph.vertices = graph.edges.idxOf edge := by
    simp [gadgetVertex]
  rw [subtraction, List.getD_eq_getElem (l := graph.edges) (d := (0, 0)) indexBound,
    List.getElem_idxOf indexBound]

private theorem triangle_hit_by_deleted
    {graph : GraphInput} {deleted : List Nat} {color : Nat → Bool}
    (edgeLegal : ∀ edge ∈ (triangleGraph graph).edges,
      Presentation.NodeDeletionBipartite.SurvivingEdgeProper deleted color edge)
    {edge : Nat × Nat} (edgeMember : edge ∈ graph.edges) :
    edge.1 ∈ deleted ∨ edge.2 ∈ deleted ∨
      gadgetVertex graph (graph.edges.idxOf edge) ∈ deleted := by
  by_cases leftDeleted : edge.1 ∈ deleted
  · exact Or.inl leftDeleted
  by_cases rightDeleted : edge.2 ∈ deleted
  · exact Or.inr (Or.inl rightDeleted)
  let gadget := gadgetVertex graph (graph.edges.idxOf edge)
  by_cases gadgetDeleted : gadget ∈ deleted
  · exact Or.inr (Or.inr gadgetDeleted)
  have originalLegal := edgeLegal edge (List.mem_append_left _ edgeMember)
  have firstLegal := edgeLegal (edge.1, gadget)
    (List.mem_append_right _ (firstGadgetEdge_of_edge edgeMember))
  have secondLegal := edgeLegal (edge.2, gadget)
    (List.mem_append_right _ (secondGadgetEdge_of_edge edgeMember))
  have leftRight : color edge.1 ≠ color edge.2 := by
    rcases originalLegal with contradiction | contradiction | inequality
    · exact False.elim (leftDeleted contradiction)
    · exact False.elim (rightDeleted contradiction)
    · exact inequality
  have leftGadget : color edge.1 ≠ color gadget := by
    rcases firstLegal with contradiction | contradiction | inequality
    · exact False.elim (leftDeleted contradiction)
    · exact False.elim (gadgetDeleted contradiction)
    · exact inequality
  have rightGadget : color edge.2 ≠ color gadget := by
    rcases secondLegal with contradiction | contradiction | inequality
    · exact False.elim (rightDeleted contradiction)
    · exact False.elim (gadgetDeleted contradiction)
    · exact inequality
  cases leftColor : color edge.1 <;>
    cases rightColor : color edge.2 <;>
    cases gadgetColor : color gadget <;>
    simp_all

theorem deletion_to_cover
    {input : VertexCoverInput} (graphWellFormed : WellFormed input.graph)
    {deleted : List Nat}
    (deletedNodup : deleted.Nodup)
    (deletedBounds : VerticesWithinBounds (triangleGraph input.graph) deleted)
    (deletedLength : deleted.length ≤ input.k)
    {color : Nat → Bool}
    (edgeLegal : ∀ edge ∈ (triangleGraph input.graph).edges,
      Presentation.NodeDeletionBipartite.SurvivingEdgeProper deleted color edge) :
    VertexCover input := by
  let cover := projectedCover input.graph deleted
  have coverLength : cover.length ≤ input.k := by
    have dedupLength : cover.length ≤ (deleted.map (projectDeleted input.graph)).length := by
      exact List.Sublist.length_le (List.dedup_sublist _)
    have mappedLength :
        (deleted.map (projectDeleted input.graph)).length ≤ input.k := by
      simpa using deletedLength
    exact dedupLength.trans mappedLength
  have coverBounds : VerticesWithinBounds input.graph cover := by
    intro vertex member
    have mappedMember := List.mem_dedup.mp member
    rcases List.mem_map.mp mappedMember with ⟨deletedVertex, deletedMember, rfl⟩
    exact projectDeleted_bounds graphWellFormed
      (deletedBounds deletedVertex deletedMember)
  have covers : CoversEdges input.graph cover := by
    intro edge edgeMember
    rcases triangle_hit_by_deleted edgeLegal edgeMember with
      leftDeleted | rightDeleted | gadgetDeleted
    · left
      apply List.mem_dedup.mpr
      refine List.mem_map.mpr ⟨edge.1, leftDeleted, ?_⟩
      exact projectDeleted_original (graphWellFormed edge edgeMember).1
    · right
      apply List.mem_dedup.mpr
      refine List.mem_map.mpr ⟨edge.2, rightDeleted, ?_⟩
      exact projectDeleted_original (graphWellFormed edge edgeMember).2
    · left
      apply List.mem_dedup.mpr
      refine List.mem_map.mpr
        ⟨gadgetVertex input.graph (input.graph.edges.idxOf edge), gadgetDeleted, ?_⟩
      exact projectDeleted_gadget edgeMember
  exact ⟨cover, coverLength, List.nodup_dedup _, coverBounds, covers⟩

theorem vertexCover_iff_fromVertexCover
    (input : VertexCoverInput) (graphWellFormed : WellFormed input.graph) :
    VertexCover input ↔ Presentation.NodeDeletionBipartite.IsYes (fromVertexCover input) := by
  constructor
  · rintro ⟨cover, coverLength, coverNodup, coverBounds, covers⟩
    exact ⟨rfl, triangleGraph_wellFormed graphWellFormed, cover,
      cover_to_deletion graphWellFormed coverLength coverNodup coverBounds covers⟩
  · rintro ⟨_undirected, _wellFormed, deleted, deletedNodup, deletedBounds,
      deletedLength, color, edgeLegal⟩
    exact deletion_to_cover graphWellFormed deletedNodup deletedBounds deletedLength edgeLegal

theorem mappedVertexCoverGraph_wellFormed (input : CliqueInput) :
    WellFormed (ComplexityReduction.Karp21.VertexCover.map input).graph := by
  classical
  by_cases budgetBound : input.k ≤ input.graph.vertices
  · simpa [ComplexityReduction.Karp21.VertexCover.map, budgetBound] using
      ComplexityReduction.Karp21.VertexCover.complementGraph_wellFormed input.graph
  · simp [ComplexityReduction.Karp21.VertexCover.map, budgetBound,
      ComplexityReduction.Karp21.VertexCover.noInstance, WellFormed, EdgeWithinBounds]

/-- Mathematical correctness of the public Clique executable. -/
theorem executableCorrect :
    Agent.Hardness.Authoring.ExecutableSemanticProof source target executable := by
  intro input
  change Clique input ↔ Presentation.NodeDeletionBipartite.IsYes (executable input)
  rw [show Clique input ↔ VertexCover (ComplexityReduction.Karp21.VertexCover.map input) by
    simpa [ComplexityReduction.Combinatorics.Graph.cliqueDecisionProblem] using
      ComplexityReduction.Karp21.VertexCover.map_correct input]
  exact vertexCover_iff_fromVertexCover _ (mappedVertexCoverGraph_wellFormed input)

/-! ### Direct-TM realization and registered production edge -/

private theorem cleanMembershipPairsFrom_eq_legacy
    (start : Nat) (sets : List (List Nat)) :
    SetSystemMembershipPairs.membershipPairsFrom start sets =
      SetSystem.membershipPairsFrom start sets := by
  induction sets generalizing start with
  | nil => rfl
  | cons set sets inductionHypothesis =>
      simp [SetSystemMembershipPairs.membershipPairsFrom,
        SetSystem.membershipPairsFrom, inductionHypothesis]

abbrev edgeEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

abbrev edgeListEncodedType : EncodedType :=
  EncodedType.list edgeEncodedType

def edgeToEndpoints (edge : Nat × Nat) : List Nat :=
  [edge.1, edge.2]

private theorem edgeToEndpoints_tmPolyTime :
    TMPolyTimeMap edgeEncodedType (EncodedType.list EncodedType.nat) edgeToEndpoints := by
  let X := edgeEncodedType
  have left : TMPolyTimeMap X EncodedType.nat (fun edge : X.Carrier => edge.1) := by
    simpa [X, edgeEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have right : TMPolyTimeMap X EncodedType.nat (fun edge : X.Carrier => edge.2) := by
    simpa [X, edgeEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have rightSingleton : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun edge : X.Carrier => [edge.2]) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton EncodedType.nat) right
    simpa [Function.comp] using composed
  have consInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat (EncodedType.list EncodedType.nat))
      (fun edge : X.Carrier => (edge.1, [edge.2])) :=
    TMPolyTimeMap.prod_mk left rightSingleton
  have composed := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_cons EncodedType.nat) consInput
  simpa [Function.comp, edgeToEndpoints] using composed

abbrev gadgetContextEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat edgeEncodedType

def gadgetEdgeAtContext (input : Nat × (Nat × Nat)) : Nat × Nat :=
  (input.2.1, input.1 + input.2.2)

private theorem gadgetEdgeAtContext_tmPolyTime :
    TMPolyTimeMap gadgetContextEncodedType edgeEncodedType gadgetEdgeAtContext := by
  let X := gadgetContextEncodedType
  have context : TMPolyTimeMap X EncodedType.nat (fun input : X.Carrier => input.1) := by
    simpa [X, gadgetContextEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat edgeEncodedType
  have pair : TMPolyTimeMap X edgeEncodedType (fun input : X.Carrier => input.2) := by
    simpa [X, gadgetContextEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat edgeEncodedType
  have endpoint : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) pair
    simpa [Function.comp, X, edgeEncodedType] using composed
  have index : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat) pair
    simpa [Function.comp, X, edgeEncodedType] using composed
  have addInput : TMPolyTimeMap X natAddInputEncodedType
      (fun input : X.Carrier => (input.1, input.2.2)) := by
    simpa [natAddInputEncodedType] using TMPolyTimeMap.prod_mk context index
  have gadget : TMPolyTimeMap X EncodedType.nat
      (fun input : Nat × (Nat × Nat) => input.1 + input.2.2) := by
    have composed := TMPolyTimeMap.comp natAdd_tm_polytime addInput
    simpa [Function.comp] using composed
  simpa [gadgetEdgeAtContext, edgeEncodedType] using
    TMPolyTimeMap.prod_mk endpoint gadget

def gadgetEdgesExecutable (graph : GraphInput) : List (Nat × Nat) :=
  (Program.contextListMapExecutable
      (C := EncodedType.nat) (X := edgeEncodedType)
      (graph.vertices, endpointPairs graph)).map gadgetEdgeAtContext

theorem gadgetEdgesExecutable_eq_gadgetEdges (graph : GraphInput) :
    gadgetEdgesExecutable graph = gadgetEdges graph := by
  unfold gadgetEdgesExecutable gadgetEdges
  rw [Program.contextListMapExecutable_eq_map]
  change List.map gadgetEdgeAtContext
      (List.map (fun edge : Nat × Nat => (graph.vertices, edge))
        (endpointPairs graph)) =
    List.map (fun pair => (pair.1, gadgetVertex graph pair.2))
      (endpointPairs graph)
  rw [List.map_map]
  rfl

def graphInputToTuple
    (graph : ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType.Carrier) :
    ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType.Carrier :=
  (graph.vertices, (graph.edges, graph.directed))

private theorem graphInputToTuple_encode (graph : GraphInput) :
    ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType.encode
        (graphInputToTuple graph) =
      ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType.encode graph := by
  cases graph
  rfl

private noncomputable def graphInputToTupleTMBackedMap :
    TMBackedCostedMap
      ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
      ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType
      graphInputToTuple :=
  TMBackedCostedMap.ofEncodingEquiv
    ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
    ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType
    graphInputToTuple
    (Equiv.refl ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType.Symbol)
    (by
      intro graph
      change ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType.encode
          (graphInputToTuple graph) =
        (ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType.encode graph).map id
      simp [graphInputToTuple_encode])

def graphTupleToInput
    (payload : ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType.Carrier) :
    GraphInput where
  vertices := payload.1
  edges := payload.2.1
  directed := payload.2.2

private theorem graphTupleToInput_encode
    (payload : ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType.Carrier) :
    ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType.encode
        (graphTupleToInput payload) =
      ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType.encode payload := by
  rcases payload with ⟨vertices, edges, directed⟩
  rfl

private noncomputable def graphTupleToInputTMBackedMap :
    TMBackedCostedMap
      ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType
      ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
      graphTupleToInput :=
  TMBackedCostedMap.ofEncodingEquiv
    ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType
    ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
    graphTupleToInput
    (Equiv.refl ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType.Symbol)
    (by
      intro payload
      change ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType.encode
          (graphTupleToInput payload) =
        (ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType.encode
          payload).map id
      simp [graphTupleToInput_encode])

def vertexCoverInputToTuple
    (input : ComplexityReduction.Combinatorics.Graph.vertexCoverStructuredEncodedType.Carrier) :
    ComplexityReduction.Combinatorics.Graph.vertexCoverTupleStructuredEncodedType.Carrier :=
  (input.graph, input.k)

private theorem vertexCoverInputToTuple_encode (input : VertexCoverInput) :
    ComplexityReduction.Combinatorics.Graph.vertexCoverTupleStructuredEncodedType.encode
        (vertexCoverInputToTuple input) =
      ComplexityReduction.Combinatorics.Graph.vertexCoverStructuredEncodedType.encode input := by
  cases input
  rfl

private noncomputable def vertexCoverInputToTupleTMBackedMap :
    TMBackedCostedMap
      ComplexityReduction.Combinatorics.Graph.vertexCoverStructuredEncodedType
      ComplexityReduction.Combinatorics.Graph.vertexCoverTupleStructuredEncodedType
      vertexCoverInputToTuple :=
  TMBackedCostedMap.ofEncodingEquiv
    ComplexityReduction.Combinatorics.Graph.vertexCoverStructuredEncodedType
    ComplexityReduction.Combinatorics.Graph.vertexCoverTupleStructuredEncodedType
    vertexCoverInputToTuple
    (Equiv.refl
      ComplexityReduction.Combinatorics.Graph.vertexCoverTupleStructuredEncodedType.Symbol)
    (by
      intro input
      change ComplexityReduction.Combinatorics.Graph.vertexCoverTupleStructuredEncodedType.encode
          (vertexCoverInputToTuple input) =
        (ComplexityReduction.Combinatorics.Graph.vertexCoverStructuredEncodedType.encode
          input).map id
      simp [vertexCoverInputToTuple_encode])

def nodeDeletionTupleToInput
    (payload : Presentation.NodeDeletionBipartite.tupleStructuredEncodedType.Carrier) :
    Presentation.NodeDeletionBipartite.Input where
  graph := payload.1
  budget := payload.2

private theorem nodeDeletionTupleToInput_encode
    (payload : Presentation.NodeDeletionBipartite.tupleStructuredEncodedType.Carrier) :
    Presentation.NodeDeletionBipartite.structuredEncodedType.encode
        (nodeDeletionTupleToInput payload) =
      Presentation.NodeDeletionBipartite.tupleStructuredEncodedType.encode payload := by
  rcases payload with ⟨graph, budget⟩
  rfl

private noncomputable def nodeDeletionTupleToInputTMBackedMap :
    TMBackedCostedMap
      Presentation.NodeDeletionBipartite.tupleStructuredEncodedType
      Presentation.NodeDeletionBipartite.structuredEncodedType
      nodeDeletionTupleToInput :=
  TMBackedCostedMap.ofEncodingEquiv
    Presentation.NodeDeletionBipartite.tupleStructuredEncodedType
    Presentation.NodeDeletionBipartite.structuredEncodedType
    nodeDeletionTupleToInput
    (Equiv.refl Presentation.NodeDeletionBipartite.tupleStructuredEncodedType.Symbol)
    (by
      intro payload
      change Presentation.NodeDeletionBipartite.structuredEncodedType.encode
          (nodeDeletionTupleToInput payload) =
        (Presentation.NodeDeletionBipartite.tupleStructuredEncodedType.encode payload).map id
      simp [nodeDeletionTupleToInput_encode])

private theorem fromVertexCover_tmPolyTime :
    TMPolyTimeMap
      ComplexityReduction.Combinatorics.Graph.vertexCoverStructuredEncodedType
      Presentation.NodeDeletionBipartite.structuredEncodedType
      fromVertexCover := by
  let X := ComplexityReduction.Combinatorics.Graph.vertexCoverStructuredEncodedType
  have inputTuple : TMPolyTimeMap X
      ComplexityReduction.Combinatorics.Graph.vertexCoverTupleStructuredEncodedType
      (fun input : VertexCoverInput => (input.graph, input.k)) := by
    simpa [X, vertexCoverInputToTuple] using vertexCoverInputToTupleTMBackedMap.tm_polytime
  have sourceGraph : TMPolyTimeMap X
      ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
      (fun input : VertexCoverInput => input.graph) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst
        ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType EncodedType.nat)
      inputTuple
    simpa [Function.comp, X,
      ComplexityReduction.Combinatorics.Graph.vertexCoverTupleStructuredEncodedType] using
      composed
  have budget : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput => input.k) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd
        ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType EncodedType.nat)
      inputTuple
    simpa [Function.comp, X,
      ComplexityReduction.Combinatorics.Graph.vertexCoverTupleStructuredEncodedType] using
      composed
  have graphTuple : TMPolyTimeMap X
      ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType
      (fun input : VertexCoverInput =>
        (input.graph.vertices, (input.graph.edges, input.graph.directed))) := by
    have composed := TMPolyTimeMap.comp graphInputToTupleTMBackedMap.tm_polytime sourceGraph
    simpa [Function.comp, graphInputToTuple, X] using composed
  have vertices : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput => input.graph.vertices) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat
        ComplexityReduction.Combinatorics.Graph.graphPayloadStructuredEncodedType)
      graphTuple
    simpa [Function.comp, X,
      ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType] using composed
  have graphPayload : TMPolyTimeMap X
      ComplexityReduction.Combinatorics.Graph.graphPayloadStructuredEncodedType
      (fun input : VertexCoverInput => (input.graph.edges, input.graph.directed)) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat
        ComplexityReduction.Combinatorics.Graph.graphPayloadStructuredEncodedType)
      graphTuple
    simpa [Function.comp, X,
      ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType] using composed
  have originalEdges : TMPolyTimeMap X edgeListEncodedType
      (fun input : VertexCoverInput => input.graph.edges) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst edgeListEncodedType EncodedType.bool) graphPayload
    simpa [Function.comp, X,
      ComplexityReduction.Combinatorics.Graph.graphPayloadStructuredEncodedType,
      edgeListEncodedType, edgeEncodedType] using composed
  have edgeCount : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput => input.graph.edges.length) := by
    have composed := TMPolyTimeMap.comp
      (ComplexityReduction.Karp21.HittingSet.listLengthTMBackedMap edgeEncodedType).tm_polytime
      originalEdges
    simpa [Function.comp, edgeListEncodedType] using composed
  have expandedVertexInput : TMPolyTimeMap X natAddInputEncodedType
      (fun input : VertexCoverInput =>
        (input.graph.vertices, input.graph.edges.length)) := by
    simpa [natAddInputEncodedType] using TMPolyTimeMap.prod_mk vertices edgeCount
  have expandedVertices : TMPolyTimeMap X EncodedType.nat
      (fun input : VertexCoverInput => input.graph.vertices + input.graph.edges.length) := by
    have composed := TMPolyTimeMap.comp natAdd_tm_polytime expandedVertexInput
    simpa [Function.comp] using composed
  have endpointFamilies : TMPolyTimeMap X
      (EncodedType.list (EncodedType.list EncodedType.nat))
      (fun input : VertexCoverInput => endpointFamily input.graph) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_map edgeToEndpoints_tmPolyTime) originalEdges
    simpa [Function.comp, endpointFamily] using composed
  have pairs : TMPolyTimeMap X edgeListEncodedType
      (fun input : VertexCoverInput => endpointPairs input.graph) := by
    have composed := TMPolyTimeMap.comp
      SetSystemMembershipPairs.fromSetFamily_tmPolyTime endpointFamilies
    convert composed using 1
    funext input
    simp [Function.comp, endpointPairs, endpointSystem,
      SetSystemMembershipPairs.fromSetFamily_eq_membershipPairsFrom,
      cleanMembershipPairsFrom_eq_legacy, SetSystem.membershipPairs]
  have gadgetContextInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat edgeListEncodedType)
      (fun input : VertexCoverInput =>
        (input.graph.vertices, endpointPairs input.graph)) :=
    TMPolyTimeMap.prod_mk vertices pairs
  have attachedPairs : TMPolyTimeMap X (EncodedType.list gadgetContextEncodedType)
      (fun input : VertexCoverInput =>
        Program.contextListMapExecutable
          (input.graph.vertices, endpointPairs input.graph)) := by
    have composed := TMPolyTimeMap.comp
      (Program.contextListMapExecutable_tmPolyTime EncodedType.nat edgeEncodedType)
      gadgetContextInput
    simpa [Function.comp, gadgetContextEncodedType] using composed
  have addedExecutable : TMPolyTimeMap X edgeListEncodedType
      (fun input : VertexCoverInput => gadgetEdgesExecutable input.graph) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_map gadgetEdgeAtContext_tmPolyTime) attachedPairs
    simpa [Function.comp, gadgetEdgesExecutable] using composed
  have addedEdges : TMPolyTimeMap X edgeListEncodedType
      (fun input : VertexCoverInput => gadgetEdges input.graph) := by
    convert addedExecutable using 1
    funext input
    exact (gadgetEdgesExecutable_eq_gadgetEdges input.graph).symm
  have appendInput : TMPolyTimeMap X
      (EncodedType.prod edgeListEncodedType edgeListEncodedType)
      (fun input : VertexCoverInput =>
        (input.graph.edges, gadgetEdges input.graph)) :=
    TMPolyTimeMap.prod_mk originalEdges addedEdges
  have expandedEdges : TMPolyTimeMap X edgeListEncodedType
      (fun input : VertexCoverInput => input.graph.edges ++ gadgetEdges input.graph) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append edgeEncodedType) appendInput
    simpa [Function.comp, edgeListEncodedType] using composed
  have falseFlag : TMPolyTimeMap X EncodedType.bool
      (fun _input : VertexCoverInput => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have expandedPayload : TMPolyTimeMap X
      ComplexityReduction.Combinatorics.Graph.graphPayloadStructuredEncodedType
      (fun input : VertexCoverInput =>
        (input.graph.edges ++ gadgetEdges input.graph, false)) := by
    simpa [ComplexityReduction.Combinatorics.Graph.graphPayloadStructuredEncodedType] using
      TMPolyTimeMap.prod_mk expandedEdges falseFlag
  have expandedTuple : TMPolyTimeMap X
      ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType
      (fun input : VertexCoverInput =>
        (input.graph.vertices + input.graph.edges.length,
          (input.graph.edges ++ gadgetEdges input.graph, false))) := by
    simpa [ComplexityReduction.Combinatorics.Graph.graphTupleStructuredEncodedType] using
      TMPolyTimeMap.prod_mk expandedVertices expandedPayload
  have expandedGraph : TMPolyTimeMap X
      ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
      (fun input : VertexCoverInput => triangleGraph input.graph) := by
    have composed := TMPolyTimeMap.comp graphTupleToInputTMBackedMap.tm_polytime expandedTuple
    simpa [Function.comp, graphTupleToInput, triangleGraph] using composed
  have outputTuple : TMPolyTimeMap X
      Presentation.NodeDeletionBipartite.tupleStructuredEncodedType
      (fun input : VertexCoverInput => (triangleGraph input.graph, input.k)) := by
    simpa [Presentation.NodeDeletionBipartite.tupleStructuredEncodedType] using
      TMPolyTimeMap.prod_mk expandedGraph budget
  have output := TMPolyTimeMap.comp nodeDeletionTupleToInputTMBackedMap.tm_polytime outputTuple
  simpa [Function.comp, fromVertexCover, nodeDeletionTupleToInput, X] using output

/-- Direct-TM evidence for the exact composed Clique executable. -/
theorem executableDirectTM :
    Agent.Hardness.Authoring.ExecutableDirectTMEvidence source target executable := by
  have composed := TMPolyTimeMap.comp fromVertexCover_tmPolyTime
    ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverStructured_tm_polytime
  simpa [Function.comp, executable, source, target,
    Problems.Karp21.GraphAtoms.cliqueStructuredProblem,
    Problems.Karp21.GraphAtoms.cliqueStructuredPresentation,
    Presentation.NodeDeletionBipartite.presentedProblem,
    Presentation.NodeDeletionBipartite.structuredPresentation] using composed

/-- Exact atomic primitive admitted only from the dependent direct-TM witness above. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def primitive :
    Primitive source.representation target.representation :=
  Primitive.ofTMPolyTime executable executableDirectTM

/-- Registered public reduction edge used by completeness transport. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def certifiedReduction : CertifiedReduction source target where
  program := .atom primitive
  correct := by
    intro input
    change source.accepts input ↔ target.accepts (primitive.run input)
    rw [show primitive.run input = executable input by rfl]
    exact executableCorrect input

end CliqueToNodeDeletionBipartite
end Domain
end ComplexityReduction

assert_standard_axioms
  ComplexityReduction.Domain.CliqueToNodeDeletionBipartite.executableCorrect,
  ComplexityReduction.Domain.CliqueToNodeDeletionBipartite.executableDirectTM,
  ComplexityReduction.Domain.CliqueToNodeDeletionBipartite.primitive,
  ComplexityReduction.Domain.CliqueToNodeDeletionBipartite.certifiedReduction
