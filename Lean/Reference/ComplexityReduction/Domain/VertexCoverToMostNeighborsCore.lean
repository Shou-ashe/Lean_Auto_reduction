/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Presentation.MostNeighbors
import ComplexityReduction.Problems.Karp21.GraphAtoms
import Mathlib.Tactic

/-!
Mathematical core of the Vertex Cover to Most Neighbors reduction.

For every raw source edge the gadget creates `k + 2` independent constraint
vertices, adjacent only to the in-range endpoints of that source edge.  A
root/leaf pair reserves one slot in every small dominating complement.  Thus
an external neighbourhood of size `|V(H)| - (k + 1)` exists exactly when the
source graph has a vertex cover of size at most `k`, including malformed-edge
cases where neither endpoint is in range.
-/

namespace ComplexityReduction
namespace Domain
namespace VertexCoverToMostNeighborsCore

open Encoding
open ComplexityReduction.Combinatorics.Graph

abbrev source : PresentedProblem :=
  Problems.Karp21.GraphAtoms.vertexCoverStructuredProblem

abbrev target : PresentedProblem :=
  Presentation.MostNeighbors.presentedProblem

def copyCount (input : VertexCoverInput) : Nat :=
  input.k + 2

def constraintCount (input : VertexCoverInput) : Nat :=
  input.graph.edges.length * copyCount input

def constraintVertex (input : VertexCoverInput) (edgeIndex copyIndex : Nat) : Nat :=
  input.graph.vertices + edgeIndex * copyCount input + copyIndex

def rootVertex (input : VertexCoverInput) : Nat :=
  input.graph.vertices + constraintCount input

def leafVertex (input : VertexCoverInput) : Nat :=
  rootVertex input + 1

def vertexCount (input : VertexCoverInput) : Nat :=
  leafVertex input + 1

def endpointEdges (input : VertexCoverInput) (edgeIndex copyIndex : Nat) :
    List (Nat × Nat) :=
  let edge := input.graph.edges.getD edgeIndex (0, 0)
  (if edge.1 < input.graph.vertices then
      [(edge.1, constraintVertex input edgeIndex copyIndex)]
    else []) ++
  (if edge.2 < input.graph.vertices then
      [(edge.2, constraintVertex input edgeIndex copyIndex)]
    else [])

def constraintEdges (input : VertexCoverInput) : List (Nat × Nat) :=
  (List.range input.graph.edges.length).flatMap fun edgeIndex =>
    (List.range (copyCount input)).flatMap fun copyIndex =>
      endpointEdges input edgeIndex copyIndex

def rootEdges (input : VertexCoverInput) : List (Nat × Nat) :=
  (List.range input.graph.vertices).map fun vertex => (rootVertex input, vertex)

def gadgetEdges (input : VertexCoverInput) : List (Nat × Nat) :=
  constraintEdges input ++ rootEdges input ++ [(rootVertex input, leafVertex input)]

def gadgetGraph (input : VertexCoverInput) : GraphInput where
  vertices := vertexCount input
  edges := gadgetEdges input
  directed := false

def executable (input : source.Instance) : target.Instance where
  graph := gadgetGraph input
  threshold := vertexCount input - (input.k + 1)

@[simp] theorem copyCount_pos (input : VertexCoverInput) : 0 < copyCount input := by
  simp [copyCount]

@[simp] theorem root_lt_vertexCount (input : VertexCoverInput) :
    rootVertex input < vertexCount input := by
  simp [vertexCount, leafVertex]

@[simp] theorem leaf_lt_vertexCount (input : VertexCoverInput) :
    leafVertex input < vertexCount input := by
  simp [vertexCount]

theorem original_lt_root (input : VertexCoverInput) {vertex : Nat}
    (bound : vertex < input.graph.vertices) :
    vertex < rootVertex input := by
  simp [rootVertex, constraintCount]
  omega

theorem constraintVertex_bounds (input : VertexCoverInput) {edgeIndex copyIndex : Nat}
    (edgeBound : edgeIndex < input.graph.edges.length)
    (copyBound : copyIndex < copyCount input) :
    input.graph.vertices ≤ constraintVertex input edgeIndex copyIndex ∧
      constraintVertex input edgeIndex copyIndex < rootVertex input := by
  constructor
  · simp only [constraintVertex]
    omega
  · have nextEdge : edgeIndex + 1 ≤ input.graph.edges.length := by omega
    have blockBound :
        (edgeIndex + 1) * copyCount input ≤
          input.graph.edges.length * copyCount input :=
      Nat.mul_le_mul_right (copyCount input) nextEdge
    have withinBlock :
        edgeIndex * copyCount input + copyIndex <
          (edgeIndex + 1) * copyCount input := by
      simp [Nat.add_mul]
      omega
    simp [constraintVertex, rootVertex, constraintCount]
    omega

theorem constraintVertex_lt_vertexCount (input : VertexCoverInput)
    {edgeIndex copyIndex : Nat}
    (edgeBound : edgeIndex < input.graph.edges.length)
    (copyBound : copyIndex < copyCount input) :
    constraintVertex input edgeIndex copyIndex < vertexCount input :=
  (constraintVertex_bounds input edgeBound copyBound).2.trans (root_lt_vertexCount input)

theorem constraintVertex_injective (input : VertexCoverInput)
    {leftEdge leftCopy rightEdge rightCopy : Nat}
    (leftCopyBound : leftCopy < copyCount input)
    (rightCopyBound : rightCopy < copyCount input)
    (equality :
      constraintVertex input leftEdge leftCopy =
        constraintVertex input rightEdge rightCopy) :
    leftEdge = rightEdge ∧ leftCopy = rightCopy := by
  have coreEquality :
      leftEdge * copyCount input + leftCopy =
        rightEdge * copyCount input + rightCopy := by
    unfold constraintVertex at equality
    omega
  have quotientEquality := congrArg (fun value => value / copyCount input) coreEquality
  have leftQuotient :
      (leftEdge * copyCount input + leftCopy) / copyCount input = leftEdge := by
    rw [Nat.add_div (by omega : 0 < copyCount input)]
    simp [Nat.div_eq_of_lt leftCopyBound, Nat.mod_eq_of_lt leftCopyBound,
      Nat.not_le.mpr leftCopyBound]
  have rightQuotient :
      (rightEdge * copyCount input + rightCopy) / copyCount input = rightEdge := by
    rw [Nat.add_div (by omega : 0 < copyCount input)]
    simp [Nat.div_eq_of_lt rightCopyBound, Nat.mod_eq_of_lt rightCopyBound,
      Nat.not_le.mpr rightCopyBound]
  have edgeEquality : leftEdge = rightEdge := by
    simpa [leftQuotient, rightQuotient] using quotientEquality
  subst rightEdge
  exact ⟨rfl, by omega⟩

theorem mem_constraintEdges_iff (input : VertexCoverInput) (edge : Nat × Nat) :
    edge ∈ constraintEdges input ↔
      ∃ edgeIndex copyIndex,
        edgeIndex < input.graph.edges.length ∧
        copyIndex < copyCount input ∧
        let sourceEdge := input.graph.edges.getD edgeIndex (0, 0)
        (sourceEdge.1 < input.graph.vertices ∧
            edge = (sourceEdge.1, constraintVertex input edgeIndex copyIndex)) ∨
          (sourceEdge.2 < input.graph.vertices ∧
            edge = (sourceEdge.2, constraintVertex input edgeIndex copyIndex)) := by
  simp [constraintEdges, endpointEdges]

theorem constraint_edge_mem_left (input : VertexCoverInput) {edgeIndex copyIndex : Nat}
    (edgeBound : edgeIndex < input.graph.edges.length)
    (copyBound : copyIndex < copyCount input)
    (endpointBound : (input.graph.edges.getD edgeIndex (0, 0)).1 < input.graph.vertices) :
    ((input.graph.edges.getD edgeIndex (0, 0)).1,
        constraintVertex input edgeIndex copyIndex) ∈ constraintEdges input := by
  apply (mem_constraintEdges_iff input _).2
  exact ⟨edgeIndex, copyIndex, edgeBound, copyBound, Or.inl ⟨endpointBound, rfl⟩⟩

theorem constraint_edge_mem_right (input : VertexCoverInput) {edgeIndex copyIndex : Nat}
    (edgeBound : edgeIndex < input.graph.edges.length)
    (copyBound : copyIndex < copyCount input)
    (endpointBound : (input.graph.edges.getD edgeIndex (0, 0)).2 < input.graph.vertices) :
    ((input.graph.edges.getD edgeIndex (0, 0)).2,
        constraintVertex input edgeIndex copyIndex) ∈ constraintEdges input := by
  apply (mem_constraintEdges_iff input _).2
  exact ⟨edgeIndex, copyIndex, edgeBound, copyBound, Or.inr ⟨endpointBound, rfl⟩⟩

theorem graph_wellFormed (input : VertexCoverInput) :
    WellFormed (gadgetGraph input) := by
  intro edge member
  change edge.1 < vertexCount input ∧ edge.2 < vertexCount input
  change edge ∈ gadgetEdges input at member
  rw [gadgetEdges] at member
  rcases List.mem_append.mp member with prefixMember | finalMember
  · rcases List.mem_append.mp prefixMember with constraintMember | rootMember
    · rcases (mem_constraintEdges_iff input edge).1 constraintMember with
        ⟨edgeIndex, copyIndex, edgeBound, copyBound, localEdge⟩
      rcases localEdge with ⟨endpointBound, rfl⟩ | ⟨endpointBound, rfl⟩
      · exact ⟨(original_lt_root input endpointBound).trans (root_lt_vertexCount input),
          constraintVertex_lt_vertexCount input edgeBound copyBound⟩
      · exact ⟨(original_lt_root input endpointBound).trans (root_lt_vertexCount input),
          constraintVertex_lt_vertexCount input edgeBound copyBound⟩
    · rcases List.mem_map.mp rootMember with ⟨vertex, vertexMember, rfl⟩
      have vertexBound : vertex < input.graph.vertices := by simpa using vertexMember
      exact ⟨root_lt_vertexCount input,
        (original_lt_root input vertexBound).trans (root_lt_vertexCount input)⟩
  · simp only [List.mem_singleton] at finalMember
    cases finalMember
    exact ⟨root_lt_vertexCount input, leaf_lt_vertexCount input⟩

theorem root_edge_mem (input : VertexCoverInput) {vertex : Nat}
    (bound : vertex < input.graph.vertices) :
    (rootVertex input, vertex) ∈ gadgetEdges input := by
  rw [gadgetEdges]
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨vertex, by simpa using bound, rfl⟩

theorem root_leaf_edge_mem (input : VertexCoverInput) :
    (rootVertex input, leafVertex input) ∈ gadgetEdges input := by
  simp [gadgetEdges]

theorem constraint_edge_mem_gadget_left (input : VertexCoverInput)
    {edgeIndex copyIndex : Nat}
    (edgeBound : edgeIndex < input.graph.edges.length)
    (copyBound : copyIndex < copyCount input)
    (endpointBound : (input.graph.edges.getD edgeIndex (0, 0)).1 < input.graph.vertices) :
    ((input.graph.edges.getD edgeIndex (0, 0)).1,
        constraintVertex input edgeIndex copyIndex) ∈ gadgetEdges input :=
  by
    rw [gadgetEdges]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (constraint_edge_mem_left input edgeBound copyBound endpointBound))))

theorem constraint_edge_mem_gadget_right (input : VertexCoverInput)
    {edgeIndex copyIndex : Nat}
    (edgeBound : edgeIndex < input.graph.edges.length)
    (copyBound : copyIndex < copyCount input)
    (endpointBound : (input.graph.edges.getD edgeIndex (0, 0)).2 < input.graph.vertices) :
    ((input.graph.edges.getD edgeIndex (0, 0)).2,
        constraintVertex input edgeIndex copyIndex) ∈ gadgetEdges input :=
  by
    rw [gadgetEdges]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (constraint_edge_mem_right input edgeBound copyBound endpointBound))))

theorem mem_rootEdges_iff (input : VertexCoverInput) (edge : Nat × Nat) :
    edge ∈ rootEdges input ↔
      ∃ vertex, vertex < input.graph.vertices ∧ edge = (rootVertex input, vertex) := by
  constructor
  · intro member
    unfold rootEdges at member
    rcases List.mem_map.mp member with ⟨vertex, vertexMember, rfl⟩
    exact ⟨vertex, by simpa using vertexMember, rfl⟩
  · rintro ⟨vertex, vertexBound, rfl⟩
    unfold rootEdges
    exact List.mem_map.mpr ⟨vertex, by simpa using vertexBound, rfl⟩

theorem mem_gadgetEdges_iff (input : VertexCoverInput) (edge : Nat × Nat) :
    edge ∈ gadgetEdges input ↔
      edge ∈ constraintEdges input ∨ edge ∈ rootEdges input ∨
        edge = (rootVertex input, leafVertex input) := by
  simp [gadgetEdges, or_assoc]

theorem constraint_edge_endpoint_bounds (input : VertexCoverInput) {edge : Nat × Nat}
    (member : edge ∈ constraintEdges input) :
    edge.1 < input.graph.vertices ∧
      input.graph.vertices ≤ edge.2 ∧ edge.2 < rootVertex input := by
  rcases (mem_constraintEdges_iff input edge).1 member with
    ⟨edgeIndex, copyIndex, edgeBound, copyBound, localEdge⟩
  rcases localEdge with ⟨endpointBound, rfl⟩ | ⟨endpointBound, rfl⟩
  · exact ⟨endpointBound, constraintVertex_bounds input edgeBound copyBound⟩
  · exact ⟨endpointBound, constraintVertex_bounds input edgeBound copyBound⟩

theorem neighbor_of_leaf_eq_root (input : VertexCoverInput) {vertex : Nat}
    (adjacent : HasUndirectedEdge (gadgetGraph input) vertex (leafVertex input)) :
    vertex = rootVertex input := by
  rcases adjacent with forwardEdge | reverseEdge
  · rcases (mem_gadgetEdges_iff input (vertex, leafVertex input)).1 forwardEdge with
      constraintMember | rootMember | finalMember
    · have bounds := constraint_edge_endpoint_bounds input constraintMember
      have leafAbove : rootVertex input < leafVertex input := by simp [leafVertex]
      have leafBelow : leafVertex input < rootVertex input := by
        simpa using bounds.2.2
      omega
    · rcases (mem_rootEdges_iff input _).1 rootMember with
        ⟨original, originalBound, equality⟩
      have secondEquality : leafVertex input = original := by
        simpa using congrArg Prod.snd equality
      have originalBelow := original_lt_root input originalBound
      have leafAbove : rootVertex input < leafVertex input := by simp [leafVertex]
      omega
    · simpa using congrArg Prod.fst finalMember
  · rcases (mem_gadgetEdges_iff input (leafVertex input, vertex)).1 reverseEdge with
      constraintMember | rootMember | finalMember
    · have bounds := constraint_edge_endpoint_bounds input constraintMember
      have leafAbove : rootVertex input < leafVertex input := by simp [leafVertex]
      have leafBelowVertices : leafVertex input < input.graph.vertices := by
        simpa using bounds.1
      have verticesBelowRoot : input.graph.vertices ≤ rootVertex input := by
        simp [rootVertex, constraintCount]
      omega
    · rcases (mem_rootEdges_iff input _).1 rootMember with
        ⟨original, _originalBound, equality⟩
      have firstEquality : leafVertex input = rootVertex input := by
        simpa using congrArg Prod.fst equality
      have leafAbove : rootVertex input < leafVertex input := by simp [leafVertex]
      omega
    · have firstEquality : leafVertex input = rootVertex input := by
        simpa using congrArg Prod.fst finalMember
      have leafAbove : rootVertex input < leafVertex input := by simp [leafVertex]
      omega

theorem neighbor_of_constraint (input : VertexCoverInput) {edgeIndex copyIndex vertex : Nat}
    (edgeBound : edgeIndex < input.graph.edges.length)
    (copyBound : copyIndex < copyCount input)
    (adjacent :
      HasUndirectedEdge (gadgetGraph input) vertex
        (constraintVertex input edgeIndex copyIndex)) :
    (vertex = (input.graph.edges.getD edgeIndex (0, 0)).1 ∧
        (input.graph.edges.getD edgeIndex (0, 0)).1 < input.graph.vertices) ∨
      (vertex = (input.graph.edges.getD edgeIndex (0, 0)).2 ∧
        (input.graph.edges.getD edgeIndex (0, 0)).2 < input.graph.vertices) := by
  have targetBounds := constraintVertex_bounds input edgeBound copyBound
  rcases adjacent with forwardEdge | reverseEdge
  · rcases (mem_gadgetEdges_iff input
      (vertex, constraintVertex input edgeIndex copyIndex)).1 forwardEdge with
      constraintMember | rootMember | finalMember
    · rcases (mem_constraintEdges_iff input _).1 constraintMember with
        ⟨otherEdge, otherCopy, otherEdgeBound, otherCopyBound, localEdge⟩
      rcases localEdge with ⟨endpointBound, equality⟩ | ⟨endpointBound, equality⟩
      · have vertexEquality : vertex =
            (input.graph.edges.getD otherEdge (0, 0)).1 := by
          simpa using congrArg Prod.fst equality
        have constraintEquality :
            constraintVertex input edgeIndex copyIndex =
              constraintVertex input otherEdge otherCopy := by
          simpa using congrArg Prod.snd equality
        rcases constraintVertex_injective input copyBound otherCopyBound
          constraintEquality with ⟨rfl, rfl⟩
        exact Or.inl ⟨vertexEquality, endpointBound⟩
      · have vertexEquality : vertex =
            (input.graph.edges.getD otherEdge (0, 0)).2 := by
          simpa using congrArg Prod.fst equality
        have constraintEquality :
            constraintVertex input edgeIndex copyIndex =
              constraintVertex input otherEdge otherCopy := by
          simpa using congrArg Prod.snd equality
        rcases constraintVertex_injective input copyBound otherCopyBound
          constraintEquality with ⟨rfl, rfl⟩
        exact Or.inr ⟨vertexEquality, endpointBound⟩
    · rcases (mem_rootEdges_iff input _).1 rootMember with
        ⟨original, originalBound, equality⟩
      have secondEquality :
          constraintVertex input edgeIndex copyIndex = original := by
        simpa using congrArg Prod.snd equality
      omega
    · have secondEquality :
          constraintVertex input edgeIndex copyIndex = leafVertex input := by
        simpa using congrArg Prod.snd finalMember
      have leafAbove : rootVertex input < leafVertex input := by simp [leafVertex]
      omega
  · rcases (mem_gadgetEdges_iff input
      (constraintVertex input edgeIndex copyIndex, vertex)).1 reverseEdge with
      constraintMember | rootMember | finalMember
    · have bounds := constraint_edge_endpoint_bounds input constraintMember
      omega
    · rcases (mem_rootEdges_iff input _).1 rootMember with
        ⟨original, _originalBound, equality⟩
      have firstEquality :
          constraintVertex input edgeIndex copyIndex = rootVertex input := by
        simpa using congrArg Prod.fst equality
      omega
    · have firstEquality :
          constraintVertex input edgeIndex copyIndex = rootVertex input := by
        simpa using congrArg Prod.fst finalMember
      omega

def selectedVertices (input : VertexCoverInput) (cover : List Nat) : Finset Nat :=
  cover.toFinset ∪ {rootVertex input}

def assignmentForCover (input : VertexCoverInput) (cover : List Nat) : List Nat :=
  (List.range (vertexCount input)).map fun vertex =>
    if vertex ∈ selectedVertices input cover then
      Presentation.MostNeighbors.selectedMarker
    else Presentation.MostNeighbors.outsideMarker

@[simp] theorem assignmentForCover_length (input : VertexCoverInput) (cover : List Nat) :
    (assignmentForCover input cover).length = vertexCount input := by
  simp [assignmentForCover]

theorem assignmentForCover_value (input : VertexCoverInput) (cover : List Nat)
    {vertex : Nat} (bound : vertex < vertexCount input) :
    Presentation.MostNeighbors.assignmentValue (assignmentForCover input cover) vertex =
      if vertex ∈ selectedVertices input cover then
        Presentation.MostNeighbors.selectedMarker
      else Presentation.MostNeighbors.outsideMarker := by
  rw [Presentation.MostNeighbors.assignmentValue,
    List.getD_eq_getElem (l := assignmentForCover input cover) (d := 0)
      (n := vertex) (by simp [assignmentForCover, bound])]
  simp [assignmentForCover, bound]

theorem selectedVertices_subset_range (input : VertexCoverInput) (cover : List Nat)
    (bounds : VerticesWithinBounds input.graph cover) :
    selectedVertices input cover ⊆ Finset.range (vertexCount input) := by
  intro vertex member
  rcases Finset.mem_union.mp member with coverMember | rootMember
  · have listMember : vertex ∈ cover := List.mem_toFinset.mp coverMember
    have vertexBound := bounds vertex listMember
    exact Finset.mem_range.mpr
      ((original_lt_root input vertexBound).trans (root_lt_vertexCount input))
  · have vertexEq : vertex = rootVertex input := by simpa using rootMember
    subst vertex
    exact Finset.mem_range.mpr (root_lt_vertexCount input)

theorem outsideVertices_assignmentForCover (input : VertexCoverInput) (cover : List Nat) :
    Presentation.MostNeighbors.outsideVertices (executable input)
        (assignmentForCover input cover) =
      Finset.range (vertexCount input) \ selectedVertices input cover := by
  ext vertex
  by_cases bound : vertex < vertexCount input
  · change
      (vertex ∈ (Finset.range (vertexCount input)).filter fun candidate =>
          Presentation.MostNeighbors.assignmentValue
              (assignmentForCover input cover) candidate =
            Presentation.MostNeighbors.outsideMarker) ↔
        vertex ∈ Finset.range (vertexCount input) \ selectedVertices input cover
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_filter, Finset.mem_range]
    simp only [bound, true_and]
    rw [assignmentForCover_value input cover bound]
    by_cases selected : vertex ∈ selectedVertices input cover <;>
      simp [selected, Presentation.MostNeighbors.outsideMarker,
        Presentation.MostNeighbors.selectedMarker]
  · simp [Presentation.MostNeighbors.outsideVertices, executable, gadgetGraph,
      Finset.mem_sdiff, bound]

theorem assignmentForCover_values_legal (input : VertexCoverInput) (cover : List Nat) :
    ∀ value ∈ assignmentForCover input cover, value < 3 := by
  intro value member
  rcases List.mem_map.mp member with ⟨vertex, _vertexMember, rfl⟩
  split <;> simp [Presentation.MostNeighbors.selectedMarker,
    Presentation.MostNeighbors.outsideMarker]

theorem edge_getD_mem (edges : List (Nat × Nat)) {index : Nat}
    (bound : index < edges.length) : edges.getD index (0, 0) ∈ edges := by
  rw [List.getD_eq_getElem (l := edges) (d := (0, 0)) (n := index) bound]
  exact List.getElem_mem bound

theorem nonselected_supported (input : VertexCoverInput) (cover : List Nat)
    (coverBounds : VerticesWithinBounds input.graph cover)
    (covers : CoversEdges input.graph cover)
    {vertex : Nat} (vertexBound : vertex < vertexCount input)
    (notSelected : vertex ∉ selectedVertices input cover) :
    Presentation.MostNeighbors.OutsideSupported
      (executable input) (assignmentForCover input cover) vertex := by
  have rootSelected : rootVertex input ∈ selectedVertices input cover := by
    simp [selectedVertices]
  have rootValue :
      Presentation.MostNeighbors.assignmentValue (assignmentForCover input cover)
          (rootVertex input) = Presentation.MostNeighbors.selectedMarker := by
    rw [assignmentForCover_value input cover (root_lt_vertexCount input)]
    simp [rootSelected]
  by_cases original : vertex < input.graph.vertices
  · refine ⟨rootVertex input, root_lt_vertexCount input, rootValue, ?_⟩
    exact Or.inl (root_edge_mem input original)
  by_cases leaf : vertex = leafVertex input
  · subst vertex
    refine ⟨rootVertex input, root_lt_vertexCount input, rootValue, ?_⟩
    exact Or.inl (root_leaf_edge_mem input)
  have notRoot : vertex ≠ rootVertex input := by
    intro equality
    subst vertex
    exact notSelected rootSelected
  have belowRoot : vertex < rootVertex input := by
    have vertexBound' := vertexBound
    change vertex < leafVertex input + 1 at vertexBound'
    have leafEq : leafVertex input = rootVertex input + 1 := rfl
    rw [leafEq] at vertexBound' leaf
    omega
  have aboveOriginal : input.graph.vertices ≤ vertex := Nat.le_of_not_gt original
  let offset := vertex - input.graph.vertices
  let edgeIndex := offset / copyCount input
  let copyIndex := offset % copyCount input
  have offsetBound : offset < input.graph.edges.length * copyCount input := by
    simp [rootVertex, constraintCount] at belowRoot
    omega
  have edgeBound : edgeIndex < input.graph.edges.length := by
    exact (Nat.div_lt_iff_lt_mul (copyCount_pos input)).2 (by
      simpa [edgeIndex, offset, Nat.mul_comm] using offsetBound)
  have copyBound : copyIndex < copyCount input := by
    exact Nat.mod_lt _ (copyCount_pos input)
  have offsetDecomposition :
      edgeIndex * copyCount input + copyIndex = offset := by
    simpa [edgeIndex, copyIndex, Nat.mul_comm] using
      (Nat.div_add_mod offset (copyCount input))
  have vertexEq : vertex = constraintVertex input edgeIndex copyIndex := by
    simp [constraintVertex, offset]
    omega
  let sourceEdge := input.graph.edges.getD edgeIndex (0, 0)
  have sourceEdgeMember : sourceEdge ∈ input.graph.edges := by
    exact edge_getD_mem input.graph.edges edgeBound
  rcases covers sourceEdge sourceEdgeMember with leftCovered | rightCovered
  · have endpointBound := coverBounds sourceEdge.1 leftCovered
    have endpointSelected : sourceEdge.1 ∈ selectedVertices input cover := by
      exact Finset.mem_union_left _ (List.mem_toFinset.mpr leftCovered)
    have endpointValue :
        Presentation.MostNeighbors.assignmentValue (assignmentForCover input cover)
            sourceEdge.1 = Presentation.MostNeighbors.selectedMarker := by
      rw [assignmentForCover_value input cover
        ((original_lt_root input endpointBound).trans (root_lt_vertexCount input))]
      simp [endpointSelected]
    refine ⟨sourceEdge.1,
      (by simpa [executable, gadgetGraph] using
        (original_lt_root input endpointBound).trans (root_lt_vertexCount input)),
      endpointValue, ?_⟩
    rw [vertexEq]
    exact Or.inl (constraint_edge_mem_gadget_left input edgeBound copyBound endpointBound)
  · have endpointBound := coverBounds sourceEdge.2 rightCovered
    have endpointSelected : sourceEdge.2 ∈ selectedVertices input cover := by
      exact Finset.mem_union_left _ (List.mem_toFinset.mpr rightCovered)
    have endpointValue :
        Presentation.MostNeighbors.assignmentValue (assignmentForCover input cover)
            sourceEdge.2 = Presentation.MostNeighbors.selectedMarker := by
      rw [assignmentForCover_value input cover
        ((original_lt_root input endpointBound).trans (root_lt_vertexCount input))]
      simp [endpointSelected]
    refine ⟨sourceEdge.2,
      (by simpa [executable, gadgetGraph] using
        (original_lt_root input endpointBound).trans (root_lt_vertexCount input)),
      endpointValue, ?_⟩
    rw [vertexEq]
    exact Or.inl (constraint_edge_mem_gadget_right input edgeBound copyBound endpointBound)

theorem forward (input : VertexCoverInput) :
    VertexCover input → Presentation.MostNeighbors.IsYes (executable input) := by
  rintro ⟨cover, coverLength, coverNodup, coverBounds, covers⟩
  refine ⟨rfl, graph_wellFormed input, assignmentForCover input cover, ?_⟩
  refine ⟨assignmentForCover_length input cover,
    assignmentForCover_values_legal input cover, ?_, ?_⟩
  · rw [outsideVertices_assignmentForCover input cover]
    have subset := selectedVertices_subset_range input cover coverBounds
    rw [Finset.card_sdiff_of_subset subset, Finset.card_range]
    have selectedCard : (selectedVertices input cover).card ≤ cover.length + 1 := by
      calc
        (selectedVertices input cover).card ≤ cover.toFinset.card + ({rootVertex input} : Finset Nat).card :=
          Finset.card_union_le _ _
        _ = cover.length + 1 := by
          rw [List.toFinset_card_of_nodup coverNodup, Finset.card_singleton]
    change vertexCount input - (input.k + 1) ≤
      vertexCount input - (selectedVertices input cover).card
    omega
  · intro vertex vertexBound outsideValue
    have executableBound : vertex < vertexCount input := by
      simpa [executable, gadgetGraph] using vertexBound
    have notSelected : vertex ∉ selectedVertices input cover := by
      intro selected
      rw [assignmentForCover_value input cover executableBound] at outsideValue
      simp [selected, Presentation.MostNeighbors.selectedMarker,
        Presentation.MostNeighbors.outsideMarker] at outsideValue
    exact nonselected_supported input cover coverBounds covers executableBound notSelected

def outsideSet (input : VertexCoverInput) (assignment : List Nat) : Finset Nat :=
  Presentation.MostNeighbors.outsideVertices (executable input) assignment

def complementSet (input : VertexCoverInput) (assignment : List Nat) : Finset Nat :=
  Finset.range (vertexCount input) \ outsideSet input assignment

def extractedCoverSet (input : VertexCoverInput) (assignment : List Nat) : Finset Nat :=
  (complementSet input assignment).filter fun vertex => vertex < input.graph.vertices

noncomputable def extractedCover (input : VertexCoverInput) (assignment : List Nat) : List Nat :=
  (extractedCoverSet input assignment).toList

theorem mem_outsideSet_iff (input : VertexCoverInput) (assignment : List Nat)
    {vertex : Nat} :
    vertex ∈ outsideSet input assignment ↔
      vertex < vertexCount input ∧
        Presentation.MostNeighbors.assignmentValue assignment vertex =
          Presentation.MostNeighbors.outsideMarker := by
  simp [outsideSet, Presentation.MostNeighbors.outsideVertices, executable, gadgetGraph]

theorem mem_complementSet_iff (input : VertexCoverInput) (assignment : List Nat)
    {vertex : Nat} :
    vertex ∈ complementSet input assignment ↔
      vertex < vertexCount input ∧ vertex ∉ outsideSet input assignment := by
  simp [complementSet]

theorem outsideSet_subset_range (input : VertexCoverInput) (assignment : List Nat) :
    outsideSet input assignment ⊆ Finset.range (vertexCount input) := by
  intro vertex member
  exact Finset.mem_range.mpr ((mem_outsideSet_iff input assignment).1 member).1

theorem selected_mem_complementSet (input : VertexCoverInput) (assignment : List Nat)
    {vertex : Nat} (vertexBound : vertex < vertexCount input)
    (selectedValue :
      Presentation.MostNeighbors.assignmentValue assignment vertex =
        Presentation.MostNeighbors.selectedMarker) :
    vertex ∈ complementSet input assignment := by
  apply (mem_complementSet_iff input assignment).2
  refine ⟨vertexBound, ?_⟩
  intro outsideMember
  have outsideValue := ((mem_outsideSet_iff input assignment).1 outsideMember).2
  rw [selectedValue] at outsideValue
  simp [Presentation.MostNeighbors.selectedMarker,
    Presentation.MostNeighbors.outsideMarker] at outsideValue

theorem complementSet_card_le (input : VertexCoverInput) (assignment : List Nat)
    (edgeExists : input.graph.edges ≠ [])
    (witness : Presentation.MostNeighbors.Witness (executable input) assignment) :
    (complementSet input assignment).card ≤ input.k + 1 := by
  have edgeCountPositive : 0 < input.graph.edges.length :=
    List.length_pos_iff.mpr edgeExists
  have oneLeEdgeCount : 1 ≤ input.graph.edges.length := by omega
  have oneBlockLe : copyCount input ≤ constraintCount input := by
    unfold constraintCount
    simpa using Nat.mul_le_mul_right (copyCount input) oneLeEdgeCount
  have oneBlockLe' : input.k + 2 ≤ constraintCount input := by
    simpa [copyCount] using oneBlockLe
  have budgetWithin : input.k + 1 ≤ vertexCount input := by
    unfold vertexCount leafVertex rootVertex
    omega
  have outsideSubset := outsideSet_subset_range input assignment
  have outsideCardLe :
      (outsideSet input assignment).card ≤ vertexCount input := by
    calc
      (outsideSet input assignment).card ≤
          (Finset.range (vertexCount input)).card := Finset.card_le_card outsideSubset
      _ = vertexCount input := Finset.card_range _
  have thresholdBound :
      vertexCount input - (input.k + 1) ≤
        (outsideSet input assignment).card := by
    simpa [executable, outsideSet] using witness.2.2.1
  have complementCard :
      (complementSet input assignment).card =
        vertexCount input - (outsideSet input assignment).card := by
    unfold complementSet
    rw [Finset.card_sdiff_of_subset outsideSubset, Finset.card_range]
  rw [complementCard]
  omega

theorem root_or_leaf_mem_complementSet (input : VertexCoverInput) (assignment : List Nat)
    (witness : Presentation.MostNeighbors.Witness (executable input) assignment) :
    rootVertex input ∈ complementSet input assignment ∨
      leafVertex input ∈ complementSet input assignment := by
  by_cases leafOutside : leafVertex input ∈ outsideSet input assignment
  · have leafData := (mem_outsideSet_iff input assignment).1 leafOutside
    have supported := witness.2.2.2 (leafVertex input)
      (by simpa [executable, gadgetGraph] using leafData.1) leafData.2
    rcases supported with
      ⟨selected, selectedBound, selectedValue, adjacent⟩
    have adjacent' :
        HasUndirectedEdge (gadgetGraph input) selected (leafVertex input) := by
      simpa [executable] using adjacent
    have selectedEq := neighbor_of_leaf_eq_root input adjacent'
    subst selected
    left
    apply selected_mem_complementSet input assignment (root_lt_vertexCount input)
    simpa using selectedValue
  · right
    exact (mem_complementSet_iff input assignment).2
      ⟨leaf_lt_vertexCount input, leafOutside⟩

theorem extractedCoverSet_card_le (input : VertexCoverInput) (assignment : List Nat)
    (complementBound : (complementSet input assignment).card ≤ input.k + 1)
    (specialMember :
      rootVertex input ∈ complementSet input assignment ∨
        leafVertex input ∈ complementSet input assignment) :
    (extractedCoverSet input assignment).card ≤ input.k := by
  have nonOriginalPositive :
      0 < ((complementSet input assignment).filter fun vertex =>
        ¬ vertex < input.graph.vertices).card := by
    apply Finset.card_pos.mpr
    rcases specialMember with rootMember | leafMember
    · refine ⟨rootVertex input, Finset.mem_filter.mpr ⟨rootMember, ?_⟩⟩
      simp [rootVertex, constraintCount]
    · refine ⟨leafVertex input, Finset.mem_filter.mpr ⟨leafMember, ?_⟩⟩
      simp only [leafVertex, rootVertex, constraintCount]
      omega
  have splitCount :
      (extractedCoverSet input assignment).card +
          ((complementSet input assignment).filter fun vertex =>
            ¬ vertex < input.graph.vertices).card =
        (complementSet input assignment).card := by
    simpa [extractedCoverSet] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := complementSet input assignment)
        (fun vertex => vertex < input.graph.vertices))
  omega

def constraintBlock (input : VertexCoverInput) (edgeIndex : Nat) : Finset Nat :=
  (Finset.range (copyCount input)).image fun copyIndex =>
    constraintVertex input edgeIndex copyIndex

theorem constraintBlock_card (input : VertexCoverInput) (edgeIndex : Nat) :
    (constraintBlock input edgeIndex).card = copyCount input := by
  unfold constraintBlock
  calc
    ((Finset.range (copyCount input)).image fun copyIndex =>
        constraintVertex input edgeIndex copyIndex).card =
        (Finset.range (copyCount input)).card := by
      apply (Finset.card_image_iff).2
      intro left leftMember right rightMember equality
      exact (constraintVertex_injective input
        (Finset.mem_range.mp leftMember) (Finset.mem_range.mp rightMember) equality).2
    _ = copyCount input := Finset.card_range _

theorem constraintBlock_subset_complementSet (input : VertexCoverInput)
    (assignment : List Nat) {edgeIndex : Nat}
    (edgeBound : edgeIndex < input.graph.edges.length)
    (leftMissing :
      (input.graph.edges.getD edgeIndex (0, 0)).1 ∉
        extractedCoverSet input assignment)
    (rightMissing :
      (input.graph.edges.getD edgeIndex (0, 0)).2 ∉
        extractedCoverSet input assignment)
    (witness : Presentation.MostNeighbors.Witness (executable input) assignment) :
    constraintBlock input edgeIndex ⊆ complementSet input assignment := by
  intro vertex member
  rcases Finset.mem_image.mp member with ⟨copyIndex, copyMember, rfl⟩
  have copyBound := Finset.mem_range.mp copyMember
  apply (mem_complementSet_iff input assignment).2
  refine ⟨constraintVertex_lt_vertexCount input edgeBound copyBound, ?_⟩
  intro outsideMember
  have outsideData := (mem_outsideSet_iff input assignment).1 outsideMember
  have supported := witness.2.2.2
    (constraintVertex input edgeIndex copyIndex)
    (by simpa [executable, gadgetGraph] using outsideData.1) outsideData.2
  rcases supported with
    ⟨selected, selectedBound, selectedValue, adjacent⟩
  have selectedBound' : selected < vertexCount input := by
    simpa [executable, gadgetGraph] using selectedBound
  have selectedMember :=
    selected_mem_complementSet input assignment selectedBound' selectedValue
  have adjacent' :
      HasUndirectedEdge (gadgetGraph input) selected
        (constraintVertex input edgeIndex copyIndex) := by
    simpa [executable] using adjacent
  rcases neighbor_of_constraint input edgeBound copyBound adjacent' with
    ⟨selectedEq, endpointBound⟩ | ⟨selectedEq, endpointBound⟩
  · apply leftMissing
    subst selected
    exact Finset.mem_filter.mpr ⟨selectedMember, endpointBound⟩
  · apply rightMissing
    subst selected
    exact Finset.mem_filter.mpr ⟨selectedMember, endpointBound⟩

theorem extractedCover_bounds (input : VertexCoverInput) (assignment : List Nat) :
    VerticesWithinBounds input.graph (extractedCover input assignment) := by
  intro vertex member
  have setMember : vertex ∈ extractedCoverSet input assignment := by
    simpa [extractedCover] using member
  exact (Finset.mem_filter.mp setMember).2

theorem extractedCover_covers (input : VertexCoverInput) (assignment : List Nat)
    (witness : Presentation.MostNeighbors.Witness (executable input) assignment)
    (complementBound : (complementSet input assignment).card ≤ input.k + 1) :
    CoversEdges input.graph (extractedCover input assignment) := by
  intro edge edgeMember
  by_contra uncovered
  have leftMissingList : edge.1 ∉ extractedCover input assignment := by
    intro member
    exact uncovered (Or.inl member)
  have rightMissingList : edge.2 ∉ extractedCover input assignment := by
    intro member
    exact uncovered (Or.inr member)
  have leftMissingSet : edge.1 ∉ extractedCoverSet input assignment := by
    intro member
    exact leftMissingList (by simpa [extractedCover] using member)
  have rightMissingSet : edge.2 ∉ extractedCoverSet input assignment := by
    intro member
    exact rightMissingList (by simpa [extractedCover] using member)
  let edgeIndex := input.graph.edges.idxOf edge
  have edgeBound : edgeIndex < input.graph.edges.length := by
    exact (List.idxOf_lt_length_iff).2 edgeMember
  have edgeAtIndex : input.graph.edges.getD edgeIndex (0, 0) = edge := by
    rw [List.getD_eq_getElem (l := input.graph.edges) (d := (0, 0))
      (n := edgeIndex) edgeBound]
    exact List.getElem_idxOf edgeBound
  have leftMissing :
      (input.graph.edges.getD edgeIndex (0, 0)).1 ∉
        extractedCoverSet input assignment := by
    rw [edgeAtIndex]
    exact leftMissingSet
  have rightMissing :
      (input.graph.edges.getD edgeIndex (0, 0)).2 ∉
        extractedCoverSet input assignment := by
    rw [edgeAtIndex]
    exact rightMissingSet
  have blockSubset := constraintBlock_subset_complementSet input assignment edgeBound
    leftMissing rightMissing witness
  have blockCardLe := Finset.card_le_card blockSubset
  rw [constraintBlock_card] at blockCardLe
  simp [copyCount] at blockCardLe
  omega

theorem reverse (input : VertexCoverInput) :
    Presentation.MostNeighbors.IsYes (executable input) → VertexCover input := by
  rintro ⟨_undirected, _wellFormed, assignment, witness⟩
  by_cases noEdges : input.graph.edges = []
  · refine ⟨[], by simp, by simp, by simp [VerticesWithinBounds], ?_⟩
    simp [CoversEdges, noEdges]
  · have complementBound := complementSet_card_le input assignment noEdges witness
    have specialMember := root_or_leaf_mem_complementSet input assignment witness
    have coverCardBound := extractedCoverSet_card_le input assignment
      complementBound specialMember
    refine ⟨extractedCover input assignment, ?_, ?_,
      extractedCover_bounds input assignment,
      extractedCover_covers input assignment witness complementBound⟩
    · simpa [extractedCover] using coverCardBound
    · exact (extractedCoverSet input assignment).nodup_toList

theorem executableCorrect (input : VertexCoverInput) :
    source.accepts input ↔ target.accepts (executable input) := by
  change VertexCover input ↔ Presentation.MostNeighbors.IsYes (executable input)
  exact ⟨forward input, reverse input⟩

end VertexCoverToMostNeighborsCore
end Domain
end ComplexityReduction
