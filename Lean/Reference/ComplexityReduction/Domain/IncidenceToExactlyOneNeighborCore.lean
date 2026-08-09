/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Tactic
import ComplexityReduction.Domain.Core.IncidenceIRValidation
import ComplexityReduction.Legacy.IR.Domains.Graph.Combinatorics.ExactlyOneNeighbor

/-!
Canonical hub-level construction for Exact Cover to Exactly-One-Neighbor.

This module owns the executable graph assembly used by the shared incidence
gadget. Its input is only `Domain.IncidenceIR`; it deliberately imports no
`SetSystemInput`, `ExactCoverInput`, public route, registry, legacy assembly,
or program/certificate API.
-/

namespace ComplexityReduction
namespace Domain
namespace IncidenceToExactlyOneNeighbor

private abbrev ExactlyOneNeighborInput :=
  _root_.ComplexityReduction.ExactlyOneNeighborInput

private abbrev ExactlyOneNeighborYes :=
  _root_.ComplexityReduction.ExactlyOneNeighborYes

/-- The generic incidence-hub validation guard, retained here as a compatibility alias. -/
abbrev wellFormedBool := IncidenceIRValidation.wellFormedBool

/-- The executable guard recognizes exactly the hub's bounds predicate. -/
theorem wellFormedBool_eq_true_iff (input : IncidenceIR) :
    wellFormedBool input = true ↔ input.WellFormed := by
  exact IncidenceIRValidation.wellFormedBool_eq_true_iff input

/-- The graph vertex for a retained right-side incidence identity. -/
def rightVertex (input : IncidenceIR) (index : Nat) : Nat :=
  input.leftSize + index

/-- Forward element-to-right-vertex incidence edges. -/
def forwardEdges (input : IncidenceIR) : List (Nat × Nat) :=
  input.membershipPairs.map fun pair => (pair.1, rightVertex input pair.2)

/-- The undirected incidence graph stores each edge in both orientations. -/
def incidenceGraphEdges (input : IncidenceIR) : List (Nat × Nat) :=
  forwardEdges input ++ (forwardEdges input).map fun edge => (edge.2, edge.1)

/-- The graph assembled from the canonical incidence hub. -/
def incidenceGraph (input : IncidenceIR) : ComplexityReduction.Combinatorics.Graph.GraphInput where
  vertices := input.leftSize + input.rightSize
  edges := incidenceGraphEdges input
  directed := false

/-- The target before its executable source-validity guard is applied. -/
def coreTarget (input : IncidenceIR) : ExactlyOneNeighborInput where
  graph := incidenceGraph input
  R := List.range input.leftSize

/-- A fixed non-yes target for invalid raw incidence tables. -/
def noTarget : ExactlyOneNeighborInput where
  graph := { vertices := 1, edges := [], directed := false }
  R := [0]

/-- Total shared-gadget executable, guarded only by canonical hub well-formedness. -/
def run (input : IncidenceIR) : ExactlyOneNeighborInput :=
  if wellFormedBool input then coreTarget input else noTarget

/-- On a well-formed hub input, the executable is precisely the core construction. -/
theorem run_eq_coreTarget {input : IncidenceIR} (wellFormed : input.WellFormed) :
    run input = coreTarget input := by
  simp [run, (wellFormedBool_eq_true_iff input).mpr wellFormed]

/-- A forward graph edge is exactly one retained incidence pair. -/
theorem mem_forwardEdges_iff {input : IncidenceIR} {left right : Nat} :
    (left, rightVertex input right) ∈ forwardEdges input ↔
      (left, right) ∈ input.membershipPairs := by
  constructor
  · intro member
    unfold forwardEdges at member
    rcases List.mem_map.mp member with ⟨pair, pairMember, pairEquality⟩
    cases pair with
    | mk source target =>
        simp [rightVertex] at pairEquality
        rcases pairEquality with ⟨rfl, rfl⟩
        exact pairMember
  · intro member
    unfold forwardEdges
    exact List.mem_map.mpr ⟨(left, right), member, rfl⟩

/-- A right-side graph vertex cannot occur as the left endpoint of a forward edge. -/
theorem rightVertex_not_left_mem_forwardEdges
    {input : IncidenceIR} (wellFormed : input.WellFormed) (right left : Nat) :
    (rightVertex input right, left) ∉ forwardEdges input := by
  intro member
  unfold forwardEdges at member
  rcases List.mem_map.mp member with ⟨pair, pairMember, pairEquality⟩
  cases pair with
  | mk source target =>
      simp [rightVertex] at pairEquality
      rcases pairEquality with ⟨sourceEquality, _⟩
      have sourceBound := (wellFormed (source, target) pairMember).1
      omega

/-- Membership in the doubled graph edge table is membership in one orientation. -/
theorem mem_incidenceGraphEdges_iff {input : IncidenceIR} {edge : Nat × Nat} :
    edge ∈ incidenceGraphEdges input ↔
      edge ∈ forwardEdges input ∨ (edge.2, edge.1) ∈ forwardEdges input := by
  constructor
  · intro member
    unfold incidenceGraphEdges at member
    rcases List.mem_append.mp member with member | member
    · exact Or.inl member
    · rcases List.mem_map.mp member with ⟨original, originalMember, swapped⟩
      cases edge with
      | mk first second =>
          cases original with
          | mk originalFirst originalSecond =>
              simp at swapped
              rcases swapped with ⟨rfl, rfl⟩
              exact Or.inr originalMember
  · intro member
    unfold incidenceGraphEdges
    rcases member with member | member
    · exact List.mem_append_left _ member
    · exact List.mem_append_right _
        (List.mem_map.mpr ⟨(edge.2, edge.1), member, by
          rcases edge with ⟨first, second⟩
          rfl⟩)

/-- At a bounded left vertex, graph adjacency exactly recovers a bounded right incidence. -/
theorem hasUndirectedEdge_core_iff
    {input : IncidenceIR} (wellFormed : input.WellFormed)
    {left vertex : Nat} (leftBound : left < input.leftSize) :
    ComplexityReduction.Combinatorics.Graph.HasUndirectedEdge (incidenceGraph input) vertex left ↔
      ∃ right, right < input.rightSize ∧ vertex = rightVertex input right ∧
        (left, right) ∈ input.membershipPairs := by
  constructor
  · intro edge
    unfold ComplexityReduction.Combinatorics.Graph.HasUndirectedEdge incidenceGraph at edge
    rcases edge with edge | edge
    · rcases mem_incidenceGraphEdges_iff.mp edge with forward | reverse
      · exfalso
        unfold forwardEdges at forward
        rcases List.mem_map.mp forward with ⟨pair, _pairMember, pairEquality⟩
        cases pair with
        | mk source right =>
            simp [rightVertex] at pairEquality
            rcases pairEquality with ⟨_, rightEquality⟩
            omega
      · unfold forwardEdges at reverse
        rcases List.mem_map.mp reverse with ⟨pair, pairMember, pairEquality⟩
        cases pair with
        | mk source right =>
            simp [rightVertex] at pairEquality
            rcases pairEquality with ⟨rfl, rfl⟩
            exact ⟨right, (wellFormed (source, right) pairMember).2, rfl, pairMember⟩
    · rcases mem_incidenceGraphEdges_iff.mp edge with forward | reverse
      · unfold forwardEdges at forward
        rcases List.mem_map.mp forward with ⟨pair, pairMember, pairEquality⟩
        cases pair with
        | mk source right =>
            simp [rightVertex] at pairEquality
            rcases pairEquality with ⟨rfl, rfl⟩
            exact ⟨right, (wellFormed (source, right) pairMember).2, rfl, pairMember⟩
      · exfalso
        unfold forwardEdges at reverse
        rcases List.mem_map.mp reverse with ⟨pair, _pairMember, pairEquality⟩
        cases pair with
        | mk source right =>
            simp [rightVertex] at pairEquality
            rcases pairEquality with ⟨_, rightEquality⟩
            omega
  · rintro ⟨right, _rightBound, rfl, member⟩
    unfold ComplexityReduction.Combinatorics.Graph.HasUndirectedEdge incidenceGraph
    right
    exact mem_incidenceGraphEdges_iff.mpr (Or.inl (mem_forwardEdges_iff.mpr member))

/-- Natural-index spelling of canonical exact cover, used by the graph witness transformation. -/
def ExistsExactCoverByIndex (input : IncidenceIR) : Prop :=
  input.WellFormed ∧
    ∃ selected : List Nat,
      selected.Nodup ∧
        (∀ right ∈ selected, right < input.rightSize) ∧
          ∀ left, left < input.leftSize →
            ∃! right, right ∈ selected ∧ (left, right) ∈ input.membershipPairs

/-- Map the hub's bounded right identities to the natural index view. -/
def selectedRightIndices {input : IncidenceIR} (selected : List input.RightVertex) : List Nat :=
  selected.map Fin.val

@[simp] theorem selectedRightIndices_mem_iff {input : IncidenceIR}
    {selected : List input.RightVertex} {right : Nat} :
    right ∈ selectedRightIndices selected ↔ ∃ bounded : input.RightVertex,
      bounded ∈ selected ∧ bounded.val = right := by
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨bounded, boundedMember, equality⟩
    exact ⟨bounded, boundedMember, equality⟩
  · rintro ⟨bounded, boundedMember, rfl⟩
    exact List.mem_map.mpr ⟨bounded, boundedMember, rfl⟩

/-- The natural image of a nodup bounded selection is nodup. -/
theorem selectedRightIndices_nodup {input : IncidenceIR}
    {selected : List input.RightVertex} (selectedNodup : selected.Nodup) :
    (selectedRightIndices selected).Nodup :=
  selectedNodup.map Fin.val_injective

/-- The canonical `Fin` exact-cover predicate is equivalent to its natural-index view. -/
theorem existsExactCover_iff_byIndex (input : IncidenceIR) :
    input.ExistsExactCover ↔ ExistsExactCoverByIndex input := by
  constructor
  · rintro ⟨wellFormed, selected, selectedNodup, covers⟩
    refine ⟨wellFormed, selectedRightIndices selected, selectedRightIndices_nodup selectedNodup, ?_, ?_⟩
    · intro right rightMember
      rcases selectedRightIndices_mem_iff.mp rightMember with ⟨bounded, _boundedMember, equality⟩
      rw [← equality]
      exact bounded.isLt
    · intro left leftBound
      let boundedLeft : input.LeftVertex := ⟨left, leftBound⟩
      rcases covers boundedLeft with ⟨boundedRight, ⟨boundedMember, boundedEdge⟩, unique⟩
      refine ⟨boundedRight.val, ?_, ?_⟩
      · exact ⟨selectedRightIndices_mem_iff.mpr ⟨boundedRight, boundedMember, rfl⟩,
          boundedEdge⟩
      · intro other otherWitness
        rcases otherWitness with ⟨otherSelected, otherEdge⟩
        have otherBound : other < input.rightSize := by
          rcases selectedRightIndices_mem_iff.mp otherSelected with ⟨bounded, _member, equality⟩
          rw [← equality]
          exact bounded.isLt
        let otherRight : input.RightVertex := ⟨other, otherBound⟩
        have otherRightSelected : otherRight ∈ selected := by
          rcases selectedRightIndices_mem_iff.mp otherSelected with ⟨bounded, boundedMember, equality⟩
          have sameRight : otherRight = bounded := by
            apply Fin.ext
            simpa [otherRight] using equality.symm
          simpa [sameRight] using boundedMember
        have otherRightEdge : input.Membership boundedLeft otherRight := by
          simpa [IncidenceIR.Membership, boundedLeft, otherRight] using otherEdge
        have equality := unique otherRight ⟨otherRightSelected, otherRightEdge⟩
        exact congrArg Fin.val equality
  · rintro ⟨wellFormed, selected, selectedNodup, selectedBounds, covers⟩
    let boundedSelected : List input.RightVertex :=
      selected.attach.map fun entry : { right // right ∈ selected } =>
        ⟨entry.val, selectedBounds entry.val entry.property⟩
    refine ⟨wellFormed, boundedSelected, ?_, ?_⟩
    · apply selectedNodup.attach.map
      intro first second equality
      apply Subtype.ext
      exact congrArg Fin.val equality
    · intro boundedLeft
      rcases covers boundedLeft.val boundedLeft.isLt with
        ⟨right, ⟨rightSelected, rightEdge⟩, unique⟩
      let boundedRight : input.RightVertex := ⟨right, selectedBounds right rightSelected⟩
      refine ⟨boundedRight, ?_, ?_⟩
      · constructor
        · unfold boundedSelected
          apply List.mem_map.mpr
          exact ⟨⟨right, rightSelected⟩, by simp, rfl⟩
        · simpa [IncidenceIR.Membership, boundedRight] using rightEdge
      · intro other otherWitness
        rcases otherWitness with ⟨otherSelected, otherEdge⟩
        have otherSelectedNat : other.val ∈ selected := by
          unfold boundedSelected at otherSelected
          rcases List.mem_map.mp otherSelected with ⟨entry, _entryMember, equality⟩
          have valueEquality : entry.val = other.val := congrArg Fin.val equality
          rw [← valueEquality]
          exact entry.property
        have otherEdgeNat : (boundedLeft.val, other.val) ∈ input.membershipPairs := by
          simpa [IncidenceIR.Membership] using otherEdge
        have equality := unique other.val ⟨otherSelectedNat, otherEdgeNat⟩
        apply Fin.ext
        simpa [boundedRight] using equality

/-- Graph witness vertices obtained from a selected list of canonical right indices. -/
def selectedIndexVertices (input : IncidenceIR) (selected : List Nat) : List Nat :=
  selected.map (rightVertex input)

theorem selectedIndexVertices_nodup {input : IncidenceIR} {selected : List Nat}
    (selectedNodup : selected.Nodup) :
    (selectedIndexVertices input selected).Nodup := by
  unfold selectedIndexVertices
  exact List.Pairwise.map (rightVertex input)
    (fun first second distinct equality => distinct (Nat.add_left_cancel equality)) selectedNodup

theorem selectedIndexVertices_mem_iff {input : IncidenceIR} {selected : List Nat} {vertex : Nat} :
    vertex ∈ selectedIndexVertices input selected ↔
      ∃ right ∈ selected, vertex = rightVertex input right := by
  unfold selectedIndexVertices
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨right, rightMember, rfl⟩
    exact ⟨right, rightMember, rfl⟩
  · rintro ⟨right, rightMember, rfl⟩
    exact List.mem_map.mpr ⟨right, rightMember, rfl⟩

/-- A canonical incidence exact-cover witness produces an EON witness for the core target. -/
theorem existsExactCoverByIndex_to_coreTarget {input : IncidenceIR}
    (cover : ExistsExactCoverByIndex input) :
    ExactlyOneNeighborYes (coreTarget input) := by
  rcases cover with ⟨wellFormed, selected, selectedNodup, selectedBounds, covers⟩
  refine ⟨selectedIndexVertices input selected, ?_⟩
  refine ⟨selectedIndexVertices_nodup selectedNodup, ?_, ?_, ?_⟩
  · intro vertex vertexMember
    rcases selectedIndexVertices_mem_iff.mp vertexMember with ⟨right, rightMember, rfl⟩
    exact Nat.add_lt_add_left (selectedBounds right rightMember) input.leftSize
  · intro left leftMember
    simp [coreTarget, incidenceGraph] at leftMember ⊢
    exact Nat.lt_add_right input.rightSize leftMember
  · intro left leftMember
    have leftBound : left < input.leftSize := by
      simpa [coreTarget] using leftMember
    rcases covers left leftBound with ⟨right, ⟨rightMember, pairMember⟩, unique⟩
    refine ⟨rightVertex input right, ?_, ?_, ?_⟩
    · exact selectedIndexVertices_mem_iff.mpr ⟨right, rightMember, rfl⟩
    · exact (hasUndirectedEdge_core_iff wellFormed leftBound).mpr
        ⟨right, selectedBounds right rightMember, rfl, pairMember⟩
    · intro other otherMember otherEdge
      rcases selectedIndexVertices_mem_iff.mp otherMember with ⟨otherRight, otherRightMember, rfl⟩
      rcases (hasUndirectedEdge_core_iff wellFormed leftBound).mp otherEdge with
        ⟨edgeRight, _edgeRightBound, edgeVertex, edgeMember⟩
      have rightEquality : otherRight = edgeRight := Nat.add_left_cancel edgeVertex
      subst edgeRight
      have indexEquality := unique otherRight ⟨otherRightMember, edgeMember⟩
      subst otherRight
      rfl

/-- Recover selected right indices from an EON witness list. -/
def witnessSelectedIndices (input : IncidenceIR) (witness : List Nat) : List Nat :=
  (List.range input.rightSize).filter fun right =>
    decide (rightVertex input right ∈ witness)

theorem mem_witnessSelectedIndices_iff {input : IncidenceIR} {witness : List Nat} {right : Nat} :
    right ∈ witnessSelectedIndices input witness ↔
      right < input.rightSize ∧ rightVertex input right ∈ witness := by
  unfold witnessSelectedIndices
  rw [List.mem_filter]
  simp [List.mem_range, decide_eq_true_eq]

theorem witnessSelectedIndices_nodup (input : IncidenceIR) (witness : List Nat) :
    (witnessSelectedIndices input witness).Nodup := by
  unfold witnessSelectedIndices
  exact List.Sublist.nodup List.filter_sublist List.nodup_range

/-- An EON witness for the core target recovers a canonical incidence exact-cover witness. -/
theorem coreTarget_to_existsExactCoverByIndex {input : IncidenceIR}
    (wellFormed : input.WellFormed)
    (targetYes : ExactlyOneNeighborYes (coreTarget input)) :
    ExistsExactCoverByIndex input := by
  rcases targetYes with ⟨witness, witnessProof⟩
  rcases witnessProof with ⟨_witnessNodup, _witnessBounds, _requiredBounds, covers⟩
  refine ⟨wellFormed, witnessSelectedIndices input witness,
    witnessSelectedIndices_nodup input witness, ?_, ?_⟩
  · intro right rightMember
    exact (mem_witnessSelectedIndices_iff.mp rightMember).1
  · intro left leftBound
    have requiredMember : left ∈ (coreTarget input).R := by
      simp [coreTarget, leftBound]
    rcases covers left requiredMember with ⟨vertex, vertexMember, edge, unique⟩
    rcases (hasUndirectedEdge_core_iff wellFormed leftBound).mp edge with
      ⟨right, rightBound, vertexEquality, pairMember⟩
    refine ⟨right, ⟨?_, pairMember⟩, ?_⟩
    · exact mem_witnessSelectedIndices_iff.mpr
        ⟨rightBound, by simpa [vertexEquality] using vertexMember⟩
    · intro other otherWitness
      rcases otherWitness with ⟨otherMember, otherPairMember⟩
      have otherBound := (mem_witnessSelectedIndices_iff.mp otherMember).1
      have otherWitnessMember := (mem_witnessSelectedIndices_iff.mp otherMember).2
      have otherEdge :
          ComplexityReduction.Combinatorics.Graph.HasUndirectedEdge (incidenceGraph input)
            (rightVertex input other) left :=
        (hasUndirectedEdge_core_iff wellFormed leftBound).mpr
          ⟨other, otherBound, rfl, otherPairMember⟩
      have vertexEquality' := unique (rightVertex input other) otherWitnessMember otherEdge
      have additionEquality : rightVertex input other = rightVertex input right := by
        simpa [vertexEquality] using vertexEquality'
      exact Nat.add_left_cancel additionEquality

/-- On a well-formed hub input, the core graph realizes exactly canonical incidence exact cover. -/
theorem existsExactCoverByIndex_iff_coreTarget {input : IncidenceIR}
    (wellFormed : input.WellFormed) :
    ExistsExactCoverByIndex input ↔ ExactlyOneNeighborYes (coreTarget input) := by
  constructor
  · exact existsExactCoverByIndex_to_coreTarget
  · exact coreTarget_to_existsExactCoverByIndex wellFormed

/-- The invalid-incidence fallback target is not an EON yes-instance. -/
theorem noTarget_not_yes : ¬ ExactlyOneNeighborYes noTarget := by
  rintro ⟨witness, witnessProof⟩
  rcases witnessProof with ⟨_witnessNodup, _witnessBounds, _requiredBounds, covers⟩
  rcases covers 0 (by simp [noTarget]) with ⟨vertex, _vertexMember, edge, _unique⟩
  simp [noTarget, ComplexityReduction.Combinatorics.Graph.HasUndirectedEdge] at edge

/-- The total guarded construction preserves exactly the canonical hub predicate. -/
theorem existsExactCover_iff_run (input : IncidenceIR) :
    input.ExistsExactCover ↔ ExactlyOneNeighborYes (run input) := by
  constructor
  · intro cover
    rw [run_eq_coreTarget cover.1]
    exact (existsExactCoverByIndex_iff_coreTarget cover.1).mp
      ((existsExactCover_iff_byIndex input).mp cover)
  · intro targetYes
    by_cases wellFormed : input.WellFormed
    · rw [run_eq_coreTarget wellFormed] at targetYes
      exact (existsExactCover_iff_byIndex input).mpr
        ((existsExactCoverByIndex_iff_coreTarget wellFormed).mpr targetYes)
    · have guardFalse : wellFormedBool input = false := by
        cases guard : wellFormedBool input with
        | false => rfl
        | true => exact (wellFormed ((wellFormedBool_eq_true_iff input).mp guard)).elim
      have impossible : ExactlyOneNeighborYes noTarget := by
        simpa [run, guardFalse] using targetYes
      exact (noTarget_not_yes impossible).elim

end IncidenceToExactlyOneNeighbor
end Domain
end ComplexityReduction
