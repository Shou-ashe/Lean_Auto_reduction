/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.GraphColoringToIncidenceCore
import Mathlib.Tactic

/-!
Semantic lemmas for the wrapper-independent Graph-Coloring-to-Incidence
construction.

This is a family-local combinatorics leaf.  It has no Program, Certificate,
route, registry, Legacy, `ChromaticNumberInput`, or `ExactCoverInput`
dependency; the later trusted component will use its final hub-level iff.
-/

namespace ComplexityReduction
namespace Domain
namespace GraphColoringToIncidence

open ComplexityReduction.Combinatorics.Graph

theorem mem_edgeColorPairs_iff (input : GraphColoringIR) (pair : Nat × Nat) :
    pair ∈ edgeColorPairs input ↔
      pair.1 < input.graph.edges.length ∧ pair.2 < input.colors := by
  cases pair with
  | mk edgeIndex color => simp [edgeColorPairs]

theorem edgeColorPairs_nodup (input : GraphColoringIR) :
    (edgeColorPairs input).Nodup := by
  simpa [edgeColorPairs] using
    (List.nodup_range (n := input.graph.edges.length)).product
      (List.nodup_range (n := input.colors))

theorem edgeColorPairs_length (input : GraphColoringIR) :
    (edgeColorPairs input).length = input.graph.edges.length * input.colors := by
  simp [edgeColorPairs, List.length_product]

theorem edgeAt_eq_getElem {input : GraphColoringIR} {edgeIndex : Nat}
    (edgeBound : edgeIndex < input.graph.edges.length) :
    edgeAt input edgeIndex = input.graph.edges[edgeIndex] :=
  List.getD_eq_getElem (l := input.graph.edges) (d := (0, 0)) edgeBound

theorem edgeIncidentBool_eq_true_iff (input : GraphColoringIR) (edgeIndex vertex : Nat) :
    edgeIncidentBool input edgeIndex vertex = true ↔ EdgeIncident input edgeIndex vertex := by
  simp [edgeIncidentBool]

theorem edgeSelfLoopBool_eq_true_iff (edge : Nat × Nat) :
    decide (edge.1 = edge.2) = true ↔ edge.1 = edge.2 := by
  simp

theorem graphHasSelfLoopBool_eq_true_iff (input : GraphColoringIR) :
    graphHasSelfLoopBool input = true ↔ GraphHasSelfLoop input := by
  unfold graphHasSelfLoopBool GraphHasSelfLoop
  induction input.graph.edges with
  | nil => simp
  | cons edge edges inductionHypothesis =>
      simp [inductionHypothesis]

theorem properColoring_not_graphHasSelfLoop {input : GraphColoringIR}
    {colorOf : Nat → Nat} (proper : ProperColoring input.graph input.colors colorOf) :
    ¬ GraphHasSelfLoop input := by
  rintro ⟨edge, edgeMember, loop⟩
  exact (proper.2 edge edgeMember) (by simp [loop])

theorem mem_incidentEdgeIndices_iff (input : GraphColoringIR) (vertex edgeIndex : Nat) :
    edgeIndex ∈ incidentEdgeIndices input vertex ↔
      edgeIndex < input.graph.edges.length ∧ EdgeIncident input edgeIndex vertex := by
  simp [incidentEdgeIndices, edgeIncidentBool_eq_true_iff]

theorem vertexCode_lt_universe {input : GraphColoringIR} {vertex : Nat}
    (vertexBound : vertex < input.graph.vertices) :
    vertexCode input vertex < universeSize input := by
  simp [vertexCode, universeSize]
  omega

theorem edgeColorCode_lt_universe {input : GraphColoringIR} {edgeIndex color : Nat}
    (edgeBound : edgeIndex < input.graph.edges.length) (colorBound : color < input.colors) :
    edgeColorCode input edgeIndex color < universeSize input := by
  have pairMember : (edgeIndex, color) ∈ edgeColorPairs input :=
    (mem_edgeColorPairs_iff input (edgeIndex, color)).2 ⟨edgeBound, colorBound⟩
  have indexBound : (edgeColorPairs input).idxOf (edgeIndex, color) <
      (edgeColorPairs input).length :=
    List.idxOf_lt_length_iff.mpr pairMember
  simp [edgeColorCode, universeSize]
  omega

theorem vertexCode_ne_edgeColorCode {input : GraphColoringIR} {vertex edgeIndex color : Nat}
    (vertexBound : vertex < input.graph.vertices) :
    vertexCode input vertex ≠ edgeColorCode input edgeIndex color := by
  intro equality
  simp [vertexCode, edgeColorCode] at equality
  omega

theorem edgeColorCode_inj {input : GraphColoringIR} {firstEdge firstColor secondEdge secondColor : Nat}
    (firstEdgeBound : firstEdge < input.graph.edges.length)
    (firstColorBound : firstColor < input.colors)
    (equality : edgeColorCode input firstEdge firstColor =
      edgeColorCode input secondEdge secondColor) :
    firstEdge = secondEdge ∧ firstColor = secondColor := by
  have firstMember : (firstEdge, firstColor) ∈ edgeColorPairs input :=
    (mem_edgeColorPairs_iff input (firstEdge, firstColor)).2 ⟨firstEdgeBound, firstColorBound⟩
  have indexEquality : (edgeColorPairs input).idxOf (firstEdge, firstColor) =
      (edgeColorPairs input).idxOf (secondEdge, secondColor) := by
    simp [edgeColorCode] at equality
    omega
  have pairEquality : (firstEdge, firstColor) = (secondEdge, secondColor) :=
    (List.idxOf_inj firstMember).1 indexEquality
  exact Prod.ext_iff.mp pairEquality

theorem mem_choiceBlock_iff (input : GraphColoringIR) (vertex color marker : Nat) :
    marker ∈ choiceBlock input vertex color ↔
      marker = vertexCode input vertex ∨
        ∃ edgeIndex, edgeIndex < input.graph.edges.length ∧
          EdgeIncident input edgeIndex vertex ∧ marker = edgeColorCode input edgeIndex color := by
  constructor
  · intro member
    simp [choiceBlock] at member
    rcases member with vertexMember | edgeMember
    · exact Or.inl vertexMember
    · rcases edgeMember with ⟨edgeIndex, edgeMember, markerEquality⟩
      rcases (mem_incidentEdgeIndices_iff input vertex edgeIndex).1 edgeMember with
        ⟨edgeBound, incident⟩
      exact Or.inr ⟨edgeIndex, edgeBound, incident, markerEquality.symm⟩
  · intro member
    rcases member with vertexMember | edgeMember
    · simp [choiceBlock, vertexMember]
    · rcases edgeMember with ⟨edgeIndex, edgeBound, incident, markerEquality⟩
      simp [choiceBlock, markerEquality]
      exact Or.inr ⟨edgeIndex,
        (mem_incidentEdgeIndices_iff input vertex edgeIndex).2 ⟨edgeBound, incident⟩, rfl⟩

theorem vertexCode_mem_choiceBlock (input : GraphColoringIR) (vertex color : Nat) :
    vertexCode input vertex ∈ choiceBlock input vertex color := by
  simp [choiceBlock]

theorem edgeColorCode_mem_choiceBlock {input : GraphColoringIR}
    {edgeIndex vertex color : Nat} (edgeBound : edgeIndex < input.graph.edges.length)
    (incident : EdgeIncident input edgeIndex vertex) :
    edgeColorCode input edgeIndex color ∈ choiceBlock input vertex color :=
  (mem_choiceBlock_iff input vertex color (edgeColorCode input edgeIndex color)).2
    (Or.inr ⟨edgeIndex, edgeBound, incident, rfl⟩)

theorem mem_fillerBlock_iff (input : GraphColoringIR) (edgeIndex color marker : Nat) :
    marker ∈ fillerBlock input edgeIndex color ↔ marker = edgeColorCode input edgeIndex color := by
  simp [fillerBlock]

theorem mem_choiceBlocks_iff (input : GraphColoringIR) (block : List Nat) :
    block ∈ choiceBlocks input ↔
      ∃ vertex, vertex < input.graph.vertices ∧
        ∃ color, color < input.colors ∧ block = choiceBlock input vertex color := by
  constructor
  · intro member
    rcases List.mem_flatMap.mp member with ⟨vertex, vertexMember, blockMember⟩
    rcases List.mem_map.mp blockMember with ⟨color, colorMember, rfl⟩
    exact ⟨vertex, by simpa using vertexMember, color, by simpa using colorMember, rfl⟩
  · rintro ⟨vertex, vertexBound, color, colorBound, rfl⟩
    exact List.mem_flatMap.mpr
      ⟨vertex, by simpa using vertexBound,
        List.mem_map.mpr ⟨color, by simpa using colorBound, rfl⟩⟩

theorem mem_fillerBlocks_iff (input : GraphColoringIR) (block : List Nat) :
    block ∈ fillerBlocks input ↔
      ∃ edgeIndex, edgeIndex < input.graph.edges.length ∧
        ∃ color, color < input.colors ∧ block = fillerBlock input edgeIndex color := by
  constructor
  · intro member
    rcases List.mem_flatMap.mp member with ⟨edgeIndex, edgeMember, blockMember⟩
    rcases List.mem_map.mp blockMember with ⟨color, colorMember, rfl⟩
    exact ⟨edgeIndex, by simpa using edgeMember, color, by simpa using colorMember, rfl⟩
  · rintro ⟨edgeIndex, edgeBound, color, colorBound, rfl⟩
    exact List.mem_flatMap.mpr
      ⟨edgeIndex, by simpa using edgeBound,
        List.mem_map.mpr ⟨color, by simpa using colorBound, rfl⟩⟩

/-- Every stored membership pair keeps its right index inside the emitted block suffix. -/
theorem mem_membershipPairsFrom_right_lt (start : Nat) (blocks : List (List Nat))
    (pair : Nat × Nat) (member : pair ∈ membershipPairsFrom start blocks) :
    pair.2 < start + blocks.length := by
  induction blocks generalizing start pair with
  | nil => simp [membershipPairsFrom] at member
  | cons block blocks inductionHypothesis =>
      rw [membershipPairsFrom, List.mem_append] at member
      rcases member with fromBlock | fromTail
      · rcases List.mem_map.mp fromBlock with ⟨marker, _markerMember, equality⟩
        subst pair
        simp
      · have tailBound := inductionHypothesis (start := start + 1) (pair := pair) fromTail
        simp only [List.length_cons]
        omega

/-- Every stored membership pair records an element from one of the emitted blocks. -/
theorem mem_membershipPairsFrom_left_mem (start : Nat) (blocks : List (List Nat))
    (pair : Nat × Nat) (member : pair ∈ membershipPairsFrom start blocks) :
    ∃ block ∈ blocks, pair.1 ∈ block := by
  induction blocks generalizing start pair with
  | nil => simp [membershipPairsFrom] at member
  | cons block blocks inductionHypothesis =>
      rw [membershipPairsFrom, List.mem_append] at member
      rcases member with fromBlock | fromTail
      · rcases List.mem_map.mp fromBlock with ⟨marker, markerMember, equality⟩
        subst pair
        exact ⟨block, by simp, markerMember⟩
      · rcases inductionHypothesis (start := start + 1) (pair := pair) fromTail with
          ⟨other, otherMember, pairMember⟩
        exact ⟨other, by simp [otherMember], pairMember⟩

/-- Every emitted pair keeps the lower right-index offset of its block suffix. -/
theorem mem_membershipPairsFrom_right_ge (start : Nat) (blocks : List (List Nat))
    (pair : Nat × Nat) (member : pair ∈ membershipPairsFrom start blocks) :
    start ≤ pair.2 := by
  induction blocks generalizing start pair with
  | nil => simp [membershipPairsFrom] at member
  | cons block blocks inductionHypothesis =>
      rw [membershipPairsFrom, List.mem_append] at member
      rcases member with fromBlock | fromTail
      · rcases List.mem_map.mp fromBlock with ⟨marker, _markerMember, equality⟩
        subst pair
        exact Nat.le_refl _
      · exact (Nat.le_succ start).trans
          (inductionHypothesis (start := start + 1) (pair := pair) fromTail)

/--
At an explicit offset, the ordered pair encoder is exactly membership in the
block stored at that offset.  This is the representation bridge used by the
future indexed exact-cover semantic proof; it preserves right-vertex identity
instead of quotienting extensionally equal blocks.
-/
theorem mem_membershipPairsFrom_offset_iff (start : Nat) (blocks : List (List Nat))
    (marker offset : Nat) :
    (marker, start + offset) ∈ membershipPairsFrom start blocks ↔
      offset < blocks.length ∧ marker ∈ blocks.getD offset [] := by
  induction blocks generalizing start offset with
  | nil => simp [membershipPairsFrom]
  | cons block blocks inductionHypothesis =>
      cases offset with
      | zero =>
          constructor
          · intro member
            rw [membershipPairsFrom, List.mem_append] at member
            rcases member with fromBlock | fromTail
            · rcases List.mem_map.mp fromBlock with ⟨other, otherMember, equality⟩
              have markerEquality : other = marker := by
                exact congrArg Prod.fst equality
              simpa [markerEquality] using otherMember
            · have rightEquality : start + 1 ≤ start := by
                exact mem_membershipPairsFrom_right_ge (start + 1) blocks
                  (marker, start) fromTail
              omega
          · rintro ⟨_offsetBound, markerMember⟩
            rw [membershipPairsFrom, List.mem_append]
            exact Or.inl (List.mem_map.mpr ⟨marker, markerMember, by simp⟩)
      | succ offset =>
          constructor
          · intro member
            rw [membershipPairsFrom, List.mem_append] at member
            rcases member with fromBlock | fromTail
            · rcases List.mem_map.mp fromBlock with ⟨other, _otherMember, equality⟩
              have rightEquality : start = start + (offset + 1) := by
                exact congrArg Prod.snd equality
              omega
            · have tailMember : (marker, (start + 1) + offset) ∈
                  membershipPairsFrom (start + 1) blocks := by
                have coordinate : start + (offset + 1) = (start + 1) + offset := by omega
                rw [coordinate] at fromTail
                exact fromTail
              rcases (inductionHypothesis (start := start + 1) (offset := offset)).1 tailMember with
                ⟨offsetBound, markerMember⟩
              exact ⟨by simpa using offsetBound, by simpa using markerMember⟩
          · rintro ⟨offsetBound, markerMember⟩
            rw [membershipPairsFrom, List.mem_append]
            apply Or.inr
            have tailMember : (marker, (start + 1) + offset) ∈
                membershipPairsFrom (start + 1) blocks :=
              (inductionHypothesis (start := start + 1) (offset := offset)).2
                ⟨by simpa using offsetBound, by simpa using markerMember⟩
            have coordinate : start + (offset + 1) = (start + 1) + offset := by omega
            rw [coordinate]
            exact tailMember

/-- The zero-based emitted pair list is membership in the correspondingly indexed block. -/
theorem mem_membershipPairs_iff (blocks : List (List Nat)) (marker right : Nat) :
    (marker, right) ∈ membershipPairsFrom 0 blocks ↔
      right < blocks.length ∧ marker ∈ blocks.getD right [] := by
  simpa using mem_membershipPairsFrom_offset_iff 0 blocks marker right

/--
Index-preserving exact-cover semantics for one ordered block family.

Unlike a selected list of block *values*, the witness retains natural block
indices.  This is essential when two independently selectable right vertices
carry extensionally equal blocks, and matches the canonical `IncidenceIR`
semantics exactly.
-/
def IndexedBlockExactCover (universeSize : Nat) (blocks : List (List Nat)) : Prop :=
  (∀ block ∈ blocks, ∀ marker ∈ block, marker < universeSize) ∧
    ∃ selected : List Nat,
      selected.Nodup ∧
        (∀ right ∈ selected, right < blocks.length) ∧
          ∀ marker, marker < universeSize →
            ∃! right, right ∈ selected ∧ marker ∈ blocks.getD right []

/-- The canonical incidence encoding of an ordered block family. -/
def incidenceOfBlocks (universeSize : Nat) (blocks : List (List Nat)) : IncidenceIR :=
  IncidenceIR.mk universeSize blocks.length (membershipPairsFrom 0 blocks)

@[simp] theorem incidenceOfBlocks_leftSize (universeSize : Nat) (blocks : List (List Nat)) :
    (incidenceOfBlocks universeSize blocks).leftSize = universeSize :=
  rfl

@[simp] theorem incidenceOfBlocks_rightSize (universeSize : Nat) (blocks : List (List Nat)) :
    (incidenceOfBlocks universeSize blocks).rightSize = blocks.length :=
  rfl

@[simp] theorem incidenceOfBlocks_membershipPairs (universeSize : Nat) (blocks : List (List Nat)) :
    (incidenceOfBlocks universeSize blocks).membershipPairs = membershipPairsFrom 0 blocks :=
  rfl

private theorem getD_mem {α : Type} (fallback : α) (values : List α)
    {index : Nat} (indexBound : index < values.length) :
    values.getD index fallback ∈ values := by
  rw [List.getD_eq_getElem (l := values) (d := fallback) indexBound]
  exact List.getElem_mem indexBound

private theorem getD_eq_of_getElem {α : Type} (fallback : α) (values : List α)
    {index : Nat} (indexBound : index < values.length) {value : α}
    (valueEquality : values[index] = value) :
    values.getD index fallback = value := by
  rw [List.getD_eq_getElem (l := values) (d := fallback) indexBound, valueEquality]

private theorem boundedSelection_nodup {blocks : List (List Nat)} {selected : List Nat}
    (selectedNodup : selected.Nodup)
    (selectedBound : ∀ right ∈ selected, right < blocks.length) :
    (selected.attach.map fun entry : { right // right ∈ selected } =>
      (⟨entry.val, selectedBound entry.val entry.property⟩ : Fin blocks.length)).Nodup := by
  apply selectedNodup.attach.map
  intro first second equality
  apply Subtype.ext
  exact congrArg Fin.val equality

/-- Ordered indexed block cover is definitionally equivalent to canonical incidence exact cover. -/
theorem indexedBlockExactCover_iff_incidence (universeSize : Nat) (blocks : List (List Nat)) :
    IndexedBlockExactCover universeSize blocks ↔
      IncidenceIR.ExistsExactCover (incidenceOfBlocks universeSize blocks) := by
  constructor
  · rintro ⟨blockBounds, selected, selectedNodup, selectedBound, covers⟩
    let boundedSelected : List (IncidenceIR.RightVertex (incidenceOfBlocks universeSize blocks)) :=
      selected.attach.map fun entry : { right // right ∈ selected } =>
        ⟨entry.val, selectedBound entry.val entry.property⟩
    refine ⟨?_, boundedSelected, boundedSelection_nodup selectedNodup selectedBound, ?_⟩
    · intro pair pairMember
      rcases (mem_membershipPairs_iff blocks pair.1 pair.2).1 pairMember with
        ⟨rightBound, markerMember⟩
      exact ⟨blockBounds (blocks.getD pair.2 []) (getD_mem [] blocks rightBound)
          pair.1 markerMember, rightBound⟩
    · intro left
      rcases covers left.val left.isLt with ⟨right, ⟨rightSelected, markerMember⟩, unique⟩
      let boundedRight : IncidenceIR.RightVertex (incidenceOfBlocks universeSize blocks) :=
        ⟨right, selectedBound right rightSelected⟩
      refine ⟨boundedRight, ?_, ?_⟩
      · constructor
        · unfold boundedSelected
          apply List.mem_map.mpr
          exact ⟨⟨right, rightSelected⟩, by simp, rfl⟩
        · exact (mem_membershipPairs_iff blocks left.val right).2
            ⟨selectedBound right rightSelected, markerMember⟩
      · intro other otherWitness
        rcases otherWitness with ⟨otherSelected, otherMembership⟩
        have otherSelectedNat : other.val ∈ selected := by
          unfold boundedSelected at otherSelected
          rcases List.mem_map.mp otherSelected with ⟨entry, _entryMember, equality⟩
          have valueEquality : entry.val = other.val := congrArg Fin.val equality
          rw [← valueEquality]
          exact entry.property
        have otherMarkerMember : left.val ∈ blocks.getD other.val [] :=
          (mem_membershipPairs_iff blocks left.val other.val).1 otherMembership |>.2
        have valueEquality : other.val = right :=
          unique other.val ⟨otherSelectedNat, otherMarkerMember⟩
        apply Fin.ext
        simpa [boundedRight] using valueEquality
  · rintro ⟨wellFormed, selected, selectedNodup, covers⟩
    let naturalSelected : List Nat := selected.map Fin.val
    refine ⟨?_, naturalSelected, selectedNodup.map Fin.val_injective, ?_, ?_⟩
    · intro block blockMember marker markerMember
      rcases List.mem_iff_getElem.mp blockMember with ⟨right, rightBound, blockEquality⟩
      have pairMember : (marker, right) ∈ membershipPairsFrom 0 blocks :=
        (mem_membershipPairs_iff blocks marker right).2
          ⟨rightBound, by
            rw [getD_eq_of_getElem [] blocks rightBound blockEquality]
            exact markerMember⟩
      exact (wellFormed (marker, right) pairMember).1
    · intro right rightSelected
      rcases List.mem_map.mp rightSelected with ⟨bounded, _boundedMember, equality⟩
      rw [← equality]
      exact bounded.isLt
    · intro marker markerBound
      let boundedMarker : IncidenceIR.LeftVertex (incidenceOfBlocks universeSize blocks) :=
        ⟨marker, markerBound⟩
      rcases covers boundedMarker with ⟨boundedRight, ⟨boundedSelected, boundedMember⟩, unique⟩
      refine ⟨boundedRight.val, ?_, ?_⟩
      · constructor
        · unfold naturalSelected
          exact List.mem_map.mpr ⟨boundedRight, boundedSelected, rfl⟩
        · exact (mem_membershipPairs_iff blocks marker boundedRight.val).1 boundedMember |>.2
      · intro other otherWitness
        rcases otherWitness with ⟨otherSelected, otherMarkerMember⟩
        unfold naturalSelected at otherSelected
        rcases List.mem_map.mp otherSelected with ⟨otherRight, otherRightSelected, equality⟩
        have otherMembership : IncidenceIR.Membership
            (incidenceOfBlocks universeSize blocks) boundedMarker otherRight := by
          exact (mem_membershipPairs_iff blocks marker otherRight.val).2
            ⟨otherRight.isLt, by
              rw [equality]
              exact otherMarkerMember⟩
        have sameRight : otherRight = boundedRight :=
          unique otherRight ⟨otherRightSelected, otherMembership⟩
        exact equality.symm.trans (congrArg Fin.val sameRight)

/-- The exact indexed-block target predicate of the canonical graph-colouring construction. -/
def BlockExactCover (input : GraphColoringIR) : Prop :=
  IndexedBlockExactCover (universeSize input) (blockFamily input)

/-- The non-self-loop construction is definitionally the generic indexed-block incidence encoding. -/
theorem constructed_eq_incidenceOfBlocks (input : GraphColoringIR) :
    IncidenceIR.mk (universeSize input) (blockFamily input).length (membershipPairs input) =
      incidenceOfBlocks (universeSize input) (blockFamily input) :=
  rfl

/-- The canonical graph construction reaches incidence exact cover precisely at its indexed block predicate. -/
theorem constructed_blockExactCover_iff_incidence (input : GraphColoringIR) :
    BlockExactCover input ↔
      IncidenceIR.ExistsExactCover
        (IncidenceIR.mk (universeSize input) (blockFamily input).length (membershipPairs input)) := by
  exact indexedBlockExactCover_iff_incidence (universeSize input) (blockFamily input)

/-- The false self-loop guard branch has the generic indexed-block exact-cover semantics. -/
theorem run_of_noSelfLoop_blockExactCover_iff_incidence (input : GraphColoringIR)
    (noSelfLoop : graphHasSelfLoopBool input = false) :
    BlockExactCover input ↔ IncidenceIR.ExistsExactCover (run input) := by
  rw [run_of_graphHasSelfLoopBool_false input noSelfLoop]
  exact constructed_blockExactCover_iff_incidence input

/-- One selected choice block per source vertex under a proposed colouring. -/
def selectedChoiceBlocks (input : GraphColoringIR) (colorOf : Nat → Nat) : List (List Nat) :=
  (List.range input.graph.vertices).map fun vertex => choiceBlock input vertex (colorOf vertex)

/-- Filler blocks for one edge, excluding colours used by its two endpoints. -/
def selectedFillerBlocksForEdge
    (input : GraphColoringIR) (colorOf : Nat → Nat) (edgeIndex : Nat) : List (List Nat) :=
  ((List.range input.colors).filter fun color =>
    decide (color ≠ colorOf (edgeAt input edgeIndex).1 ∧
      color ≠ colorOf (edgeAt input edgeIndex).2)).map
    fun color => fillerBlock input edgeIndex color

/-- All selected filler blocks under a proposed colouring. -/
def selectedFillerBlocks (input : GraphColoringIR) (colorOf : Nat → Nat) : List (List Nat) :=
  (List.range input.graph.edges.length).flatMap
    (selectedFillerBlocksForEdge input colorOf)

/-- The raw selected block family induced by a proposed colouring. -/
def selectedBlocksRaw (input : GraphColoringIR) (colorOf : Nat → Nat) : List (List Nat) :=
  selectedChoiceBlocks input colorOf ++ selectedFillerBlocks input colorOf

/-- Deduplicated selected blocks, suitable for value-level exact-cover semantics. -/
def selectedBlocks (input : GraphColoringIR) (colorOf : Nat → Nat) : List (List Nat) :=
  (selectedBlocksRaw input colorOf).dedup

/--
Value-level exact-cover semantics for a block family.

This is only a semantic proof aid.  Trusted V2 routing continues to use
`IndexedBlockExactCover`/`IncidenceIR`, whose right vertices preserve identity
even when block values coincide.
-/
def ValueBlockExactCover (universeSize : Nat) (blocks : List (List Nat)) : Prop :=
  (∀ block ∈ blocks, ∀ marker ∈ block, marker < universeSize) ∧
    ∃ selected : List (List Nat),
      (∀ block ∈ selected, block ∈ blocks) ∧
        selected.Nodup ∧
          (∀ first ∈ selected, ∀ second ∈ selected, first ≠ second →
            ∀ marker, marker ∈ first → marker ∈ second → False) ∧
            ∀ marker, marker < universeSize → ∃ block ∈ selected, marker ∈ block

theorem mem_selectedChoiceBlocks_iff
    (input : GraphColoringIR) (colorOf : Nat → Nat) (block : List Nat) :
    block ∈ selectedChoiceBlocks input colorOf ↔
      ∃ vertex, vertex < input.graph.vertices ∧ block = choiceBlock input vertex (colorOf vertex) := by
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨vertex, vertexMember, rfl⟩
    exact ⟨vertex, by simpa using vertexMember, rfl⟩
  · rintro ⟨vertex, vertexBound, rfl⟩
    exact List.mem_map.mpr ⟨vertex, by simpa using vertexBound, rfl⟩

theorem mem_selectedFillerBlocksForEdge_iff
    (input : GraphColoringIR) (colorOf : Nat → Nat) (edgeIndex : Nat) (block : List Nat) :
    block ∈ selectedFillerBlocksForEdge input colorOf edgeIndex ↔
      ∃ color, color < input.colors ∧
        color ≠ colorOf (edgeAt input edgeIndex).1 ∧
        color ≠ colorOf (edgeAt input edgeIndex).2 ∧
          block = fillerBlock input edgeIndex color := by
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨color, colorMember, rfl⟩
    rcases List.mem_filter.mp colorMember with ⟨colorRange, colorPredicate⟩
    have colorPredicateProp :
        color ≠ colorOf (edgeAt input edgeIndex).1 ∧
          color ≠ colorOf (edgeAt input edgeIndex).2 :=
      of_decide_eq_true colorPredicate
    exact ⟨color, by simpa using colorRange, colorPredicateProp.1, colorPredicateProp.2, rfl⟩
  · rintro ⟨color, colorBound, leftDifferent, rightDifferent, rfl⟩
    apply List.mem_map.mpr
    refine ⟨color, List.mem_filter.mpr ⟨by simpa using colorBound, ?_⟩, rfl⟩
    simp [leftDifferent, rightDifferent]

theorem mem_selectedFillerBlocks_iff
    (input : GraphColoringIR) (colorOf : Nat → Nat) (block : List Nat) :
    block ∈ selectedFillerBlocks input colorOf ↔
      ∃ edgeIndex, edgeIndex < input.graph.edges.length ∧
        ∃ color, color < input.colors ∧
          color ≠ colorOf (edgeAt input edgeIndex).1 ∧
          color ≠ colorOf (edgeAt input edgeIndex).2 ∧
            block = fillerBlock input edgeIndex color := by
  constructor
  · intro member
    rcases List.mem_flatMap.mp member with ⟨edgeIndex, edgeMember, blockMember⟩
    rcases (mem_selectedFillerBlocksForEdge_iff input colorOf edgeIndex block).1 blockMember with
      ⟨color, colorBound, leftDifferent, rightDifferent, rfl⟩
    exact ⟨edgeIndex, by simpa using edgeMember, color, colorBound,
      leftDifferent, rightDifferent, rfl⟩
  · rintro ⟨edgeIndex, edgeBound, color, colorBound, leftDifferent, rightDifferent, rfl⟩
    exact List.mem_flatMap.mpr
      ⟨edgeIndex, by simpa using edgeBound,
        (mem_selectedFillerBlocksForEdge_iff input colorOf edgeIndex
          (fillerBlock input edgeIndex color)).2
          ⟨color, colorBound, leftDifferent, rightDifferent, rfl⟩⟩

theorem mem_selectedBlocksRaw_iff
    (input : GraphColoringIR) (colorOf : Nat → Nat) (block : List Nat) :
    block ∈ selectedBlocksRaw input colorOf ↔
      (∃ vertex, vertex < input.graph.vertices ∧ block = choiceBlock input vertex (colorOf vertex)) ∨
        ∃ edgeIndex, edgeIndex < input.graph.edges.length ∧
          ∃ color, color < input.colors ∧
            color ≠ colorOf (edgeAt input edgeIndex).1 ∧
            color ≠ colorOf (edgeAt input edgeIndex).2 ∧
              block = fillerBlock input edgeIndex color := by
  constructor
  · intro member
    rcases List.mem_append.mp member with choiceMember | fillerMember
    · exact Or.inl ((mem_selectedChoiceBlocks_iff input colorOf block).1 choiceMember)
    · exact Or.inr ((mem_selectedFillerBlocks_iff input colorOf block).1 fillerMember)
  · intro member
    rcases member with choiceMember | fillerMember
    · exact List.mem_append.mpr (Or.inl ((mem_selectedChoiceBlocks_iff input colorOf block).2 choiceMember))
    · exact List.mem_append.mpr (Or.inr ((mem_selectedFillerBlocks_iff input colorOf block).2 fillerMember))

theorem mem_selectedBlocks_iff
    (input : GraphColoringIR) (colorOf : Nat → Nat) (block : List Nat) :
    block ∈ selectedBlocks input colorOf ↔ block ∈ selectedBlocksRaw input colorOf := by
  simp [selectedBlocks]

/-- A proper colouring only selects blocks from the constructed family. -/
theorem selectedBlocks_family_of_proper {input : GraphColoringIR}
    {colorOf : Nat → Nat} (proper : ProperColoring input.graph input.colors colorOf) :
    ∀ block ∈ selectedBlocks input colorOf, block ∈ blockFamily input := by
  intro block selectedMember
  rcases (mem_selectedBlocksRaw_iff input colorOf block).1
      ((mem_selectedBlocks_iff input colorOf block).1 selectedMember) with
    selectedChoice | selectedFiller
  · rcases selectedChoice with ⟨vertex, vertexBound, rfl⟩
    apply List.mem_append.mpr
    apply Or.inl
    exact (mem_choiceBlocks_iff input (choiceBlock input vertex (colorOf vertex))).2
      ⟨vertex, vertexBound, colorOf vertex, proper.1 vertex vertexBound, rfl⟩
  · rcases selectedFiller with
      ⟨edgeIndex, edgeBound, color, colorBound, _leftDifferent, _rightDifferent, rfl⟩
    apply List.mem_append.mpr
    apply Or.inr
    exact (mem_fillerBlocks_iff input (fillerBlock input edgeIndex color)).2
      ⟨edgeIndex, edgeBound, color, colorBound, rfl⟩

/-- Deduplication makes the selected value-level witness nodup. -/
theorem selectedBlocks_nodup (input : GraphColoringIR) (colorOf : Nat → Nat) :
    (selectedBlocks input colorOf).Nodup :=
  List.nodup_dedup _

/-- Every marker occurring in a constructed block lies inside the constructed universe. -/
theorem marker_lt_universe_of_mem_blockFamily {input : GraphColoringIR}
    {block : List Nat} (blockMember : block ∈ blockFamily input)
    {marker : Nat} (markerMember : marker ∈ block) :
    marker < universeSize input := by
  rw [blockFamily, List.mem_append] at blockMember
  rcases blockMember with choiceMember | fillerMember
  · rcases (mem_choiceBlocks_iff input block).1 choiceMember with
      ⟨vertex, vertexBound, color, colorBound, blockEquality⟩
    subst block
    rcases (mem_choiceBlock_iff input vertex color marker).1 markerMember with
      vertexMarker | edgeMarker
    · rw [vertexMarker]
      exact vertexCode_lt_universe vertexBound
    · rcases edgeMarker with ⟨edgeIndex, edgeBound, _incident, markerEquality⟩
      rw [markerEquality]
      exact edgeColorCode_lt_universe edgeBound colorBound
  · rcases (mem_fillerBlocks_iff input block).1 fillerMember with
      ⟨edgeIndex, edgeBound, color, colorBound, blockEquality⟩
    subst block
    rw [(mem_fillerBlock_iff input edgeIndex color marker).1 markerMember]
    exact edgeColorCode_lt_universe edgeBound colorBound

/-- Every marker in a selected proper-colouring block is inside the marker universe. -/
theorem selectedBlocks_marker_lt_universe_of_proper {input : GraphColoringIR}
    {colorOf : Nat → Nat} (proper : ProperColoring input.graph input.colors colorOf)
    {block : List Nat} (selectedMember : block ∈ selectedBlocks input colorOf)
    {marker : Nat} (markerMember : marker ∈ block) :
    marker < universeSize input :=
  marker_lt_universe_of_mem_blockFamily
    (selectedBlocks_family_of_proper proper block selectedMember) markerMember

theorem edgeAt_mem_edges {input : GraphColoringIR} {edgeIndex : Nat}
    (edgeBound : edgeIndex < input.graph.edges.length) :
    edgeAt input edgeIndex ∈ input.graph.edges := by
  rw [edgeAt_eq_getElem edgeBound]
  exact List.getElem_mem edgeBound

theorem selectedChoiceChoice_eq_of_inter {input : GraphColoringIR}
    {colorOf : Nat → Nat} (proper : ProperColoring input.graph input.colors colorOf)
    {firstVertex secondVertex marker : Nat}
    (firstVertexBound : firstVertex < input.graph.vertices)
    (secondVertexBound : secondVertex < input.graph.vertices)
    (firstMember : marker ∈ choiceBlock input firstVertex (colorOf firstVertex))
    (secondMember : marker ∈ choiceBlock input secondVertex (colorOf secondVertex)) :
    choiceBlock input firstVertex (colorOf firstVertex) =
      choiceBlock input secondVertex (colorOf secondVertex) := by
  rcases (mem_choiceBlock_iff input firstVertex (colorOf firstVertex) marker).1 firstMember with
    firstVertexMarker | firstEdgeMarker
  · rcases (mem_choiceBlock_iff input secondVertex (colorOf secondVertex) marker).1 secondMember with
      secondVertexMarker | secondEdgeMarker
    · have verticesEqual : firstVertex = secondVertex := by
        simpa [vertexCode] using firstVertexMarker.symm.trans secondVertexMarker
      subst secondVertex
      rfl
    · rcases secondEdgeMarker with ⟨edgeIndex, _edgeBound, _incident, markerEquality⟩
      have codeEquality : vertexCode input firstVertex =
          edgeColorCode input edgeIndex (colorOf secondVertex) := by
        rw [← firstVertexMarker, markerEquality]
      exact (vertexCode_ne_edgeColorCode firstVertexBound codeEquality).elim
  · rcases firstEdgeMarker with ⟨firstEdge, firstEdgeBound, firstIncident, firstMarkerEquality⟩
    rcases (mem_choiceBlock_iff input secondVertex (colorOf secondVertex) marker).1 secondMember with
      secondVertexMarker | secondEdgeMarker
    · have codeEquality : vertexCode input secondVertex =
          edgeColorCode input firstEdge (colorOf firstVertex) := by
        rw [← secondVertexMarker, firstMarkerEquality]
      exact (vertexCode_ne_edgeColorCode secondVertexBound codeEquality).elim
    · rcases secondEdgeMarker with
        ⟨secondEdge, _secondEdgeBound, secondIncident, secondMarkerEquality⟩
      have codeEquality : edgeColorCode input firstEdge (colorOf firstVertex) =
          edgeColorCode input secondEdge (colorOf secondVertex) := by
        rw [← firstMarkerEquality, secondMarkerEquality]
      rcases edgeColorCode_inj firstEdgeBound (proper.1 firstVertex firstVertexBound)
          codeEquality with ⟨edgeEquality, colorEquality⟩
      subst secondEdge
      by_cases verticesEqual : firstVertex = secondVertex
      · subst secondVertex
        rfl
      · have edgeMember : edgeAt input firstEdge ∈ input.graph.edges :=
          edgeAt_mem_edges firstEdgeBound
        have properDifferent := proper.2 (edgeAt input firstEdge) edgeMember
        rcases firstIncident with firstLeft | firstRight <;>
          rcases secondIncident with secondLeft | secondRight
        · exact (verticesEqual (by simpa [firstLeft] using secondLeft)).elim
        · have sameColor : colorOf (edgeAt input firstEdge).1 =
            colorOf (edgeAt input firstEdge).2 := by
            simpa [firstLeft, secondRight] using colorEquality
          exact (properDifferent sameColor).elim
        · have sameColor : colorOf (edgeAt input firstEdge).1 =
            colorOf (edgeAt input firstEdge).2 := by
            simpa [secondLeft, firstRight] using colorEquality.symm
          exact (properDifferent sameColor).elim
        · exact (verticesEqual (by simpa [firstRight] using secondRight)).elim

theorem selectedChoiceFiller_disjoint {input : GraphColoringIR}
    {colorOf : Nat → Nat} (proper : ProperColoring input.graph input.colors colorOf)
    {vertex edgeIndex color marker : Nat}
    (vertexBound : vertex < input.graph.vertices)
    (leftDifferent : color ≠ colorOf (edgeAt input edgeIndex).1)
    (rightDifferent : color ≠ colorOf (edgeAt input edgeIndex).2)
    (choiceMember : marker ∈ choiceBlock input vertex (colorOf vertex))
    (fillerMember : marker ∈ fillerBlock input edgeIndex color) : False := by
  have fillerCode := (mem_fillerBlock_iff input edgeIndex color marker).1 fillerMember
  rcases (mem_choiceBlock_iff input vertex (colorOf vertex) marker).1 choiceMember with
    vertexMarker | edgeMarker
  · have codeEquality : vertexCode input vertex = edgeColorCode input edgeIndex color := by
      rw [← vertexMarker, fillerCode]
    exact vertexCode_ne_edgeColorCode vertexBound codeEquality
  · rcases edgeMarker with ⟨otherEdge, otherEdgeBound, incident, choiceCode⟩
    have codeEquality : edgeColorCode input otherEdge (colorOf vertex) =
        edgeColorCode input edgeIndex color := by
      rw [← choiceCode, fillerCode]
    rcases edgeColorCode_inj otherEdgeBound (proper.1 vertex vertexBound) codeEquality with
      ⟨edgeEquality, colorEquality⟩
    subst otherEdge
    rcases incident with leftIncident | rightIncident
    · have contradiction : color = colorOf (edgeAt input edgeIndex).1 := by
        rw [leftIncident]
        exact colorEquality.symm
      exact leftDifferent contradiction
    · have contradiction : color = colorOf (edgeAt input edgeIndex).2 := by
        rw [rightIncident]
        exact colorEquality.symm
      exact rightDifferent contradiction

theorem selectedBlocks_unique_of_inter {input : GraphColoringIR}
    {colorOf : Nat → Nat} (proper : ProperColoring input.graph input.colors colorOf)
    {firstBlock secondBlock : List Nat} {marker : Nat}
    (firstSelected : firstBlock ∈ selectedBlocks input colorOf)
    (secondSelected : secondBlock ∈ selectedBlocks input colorOf)
    (firstMember : marker ∈ firstBlock) (secondMember : marker ∈ secondBlock) :
    firstBlock = secondBlock := by
  have firstRaw := (mem_selectedBlocks_iff input colorOf firstBlock).1 firstSelected
  have secondRaw := (mem_selectedBlocks_iff input colorOf secondBlock).1 secondSelected
  rcases (mem_selectedBlocksRaw_iff input colorOf firstBlock).1 firstRaw with
    firstChoice | firstFiller
  · rcases firstChoice with ⟨firstVertex, firstVertexBound, rfl⟩
    rcases (mem_selectedBlocksRaw_iff input colorOf secondBlock).1 secondRaw with
      secondChoice | secondFiller
    · rcases secondChoice with ⟨secondVertex, secondVertexBound, rfl⟩
      exact selectedChoiceChoice_eq_of_inter proper firstVertexBound secondVertexBound
        firstMember secondMember
    · rcases secondFiller with
        ⟨edgeIndex, _edgeBound, color, _colorBound, leftDifferent, rightDifferent, rfl⟩
      exact (selectedChoiceFiller_disjoint proper firstVertexBound
        leftDifferent rightDifferent firstMember secondMember).elim
  · rcases firstFiller with
      ⟨edgeIndex, edgeBound, color, colorBound, leftDifferent, rightDifferent, rfl⟩
    rcases (mem_selectedBlocksRaw_iff input colorOf secondBlock).1 secondRaw with
      secondChoice | secondFiller
    · rcases secondChoice with ⟨vertex, vertexBound, rfl⟩
      exact (selectedChoiceFiller_disjoint proper vertexBound
        leftDifferent rightDifferent secondMember firstMember).elim
    · rcases secondFiller with
        ⟨otherEdge, _otherEdgeBound, otherColor, _otherColorBound,
          _otherLeftDifferent, _otherRightDifferent, rfl⟩
      have firstCode := (mem_fillerBlock_iff input edgeIndex color marker).1 firstMember
      have secondCode := (mem_fillerBlock_iff input otherEdge otherColor marker).1 secondMember
      have codeEquality : edgeColorCode input edgeIndex color =
          edgeColorCode input otherEdge otherColor := by
        rw [← firstCode, secondCode]
      rcases edgeColorCode_inj edgeBound colorBound codeEquality with ⟨rfl, rfl⟩
      rfl

theorem selectedBlocks_pairwiseDisjoint {input : GraphColoringIR}
    {colorOf : Nat → Nat} (proper : ProperColoring input.graph input.colors colorOf) :
    ∀ first ∈ selectedBlocks input colorOf, ∀ second ∈ selectedBlocks input colorOf,
      first ≠ second → ∀ marker, marker ∈ first → marker ∈ second → False := by
  intro first firstSelected second secondSelected different marker firstMember secondMember
  exact different (selectedBlocks_unique_of_inter proper firstSelected secondSelected firstMember secondMember)

/--
Extend a colouring off the declared vertex range without accidentally choosing
one of the finite construction colours.  This keeps the hub construction
sound even though the legacy graph record permits out-of-range edge endpoints.
-/
def normalizedColor (input : GraphColoringIR) (colorOf : Nat → Nat) (vertex : Nat) : Nat :=
  if vertex < input.graph.vertices then colorOf vertex else input.colors + vertex

theorem normalizedColor_eq_of_lt (input : GraphColoringIR) (colorOf : Nat → Nat)
    {vertex : Nat} (vertexBound : vertex < input.graph.vertices) :
    normalizedColor input colorOf vertex = colorOf vertex := by
  simp [normalizedColor, vertexBound]

theorem normalizedColor_eq_of_not_lt (input : GraphColoringIR) (colorOf : Nat → Nat)
    {vertex : Nat} (vertexBound : ¬ vertex < input.graph.vertices) :
    normalizedColor input colorOf vertex = input.colors + vertex := by
  simp [normalizedColor, vertexBound]

theorem normalizedColor_proper {input : GraphColoringIR} {colorOf : Nat → Nat}
    (noSelfLoop : ¬ GraphHasSelfLoop input)
    (proper : ProperColoring input.graph input.colors colorOf) :
    ProperColoring input.graph input.colors (normalizedColor input colorOf) := by
  constructor
  · intro vertex vertexBound
    simpa [normalizedColor, vertexBound] using proper.1 vertex vertexBound
  · intro edge edgeMember sameColor
    by_cases leftBound : edge.1 < input.graph.vertices
    · by_cases rightBound : edge.2 < input.graph.vertices
      · have sameOriginal : colorOf edge.1 = colorOf edge.2 := by
          simpa [normalizedColor, leftBound, rightBound] using sameColor
        exact proper.2 edge edgeMember sameOriginal
      · have leftColor := proper.1 edge.1 leftBound
        have sameOut : colorOf edge.1 = input.colors + edge.2 := by
          simpa [normalizedColor, leftBound, rightBound] using sameColor
        omega
    · by_cases rightBound : edge.2 < input.graph.vertices
      · have rightColor := proper.1 edge.2 rightBound
        have sameOut : input.colors + edge.1 = colorOf edge.2 := by
          simpa [normalizedColor, leftBound, rightBound] using sameColor
        omega
      · have sameOut : input.colors + edge.1 = input.colors + edge.2 := by
          simpa [normalizedColor, leftBound, rightBound] using sameColor
        have selfLoop : edge.1 = edge.2 := by omega
        exact noSelfLoop ⟨edge, edgeMember, selfLoop⟩

/-- The normalized selected blocks cover every marker in the canonical universe. -/
theorem selectedBlocks_coversUniverse (input : GraphColoringIR) (colorOf : Nat → Nat) :
    ∀ marker, marker < universeSize input →
      ∃ block ∈ selectedBlocks input (normalizedColor input colorOf), marker ∈ block := by
  intro marker markerBound
  by_cases vertexMarker : marker < input.graph.vertices
  · refine ⟨choiceBlock input marker (normalizedColor input colorOf marker), ?_, ?_⟩
    · exact (mem_selectedBlocks_iff input (normalizedColor input colorOf)
        (choiceBlock input marker (normalizedColor input colorOf marker))).2
        ((mem_selectedBlocksRaw_iff input (normalizedColor input colorOf)
          (choiceBlock input marker (normalizedColor input colorOf marker))).2
          (Or.inl ⟨marker, vertexMarker, rfl⟩))
    · exact vertexCode_mem_choiceBlock input marker (normalizedColor input colorOf marker)
  · have afterVertices : input.graph.vertices ≤ marker := Nat.le_of_not_gt vertexMarker
    let offset := marker - input.graph.vertices
    have offsetBound : offset < (edgeColorPairs input).length := by
      simp [universeSize] at markerBound
      omega
    let pair : Nat × Nat := (edgeColorPairs input)[offset]
    have pairMember : pair ∈ edgeColorPairs input := List.getElem_mem offsetBound
    rcases pairEquality : pair with ⟨edgeIndex, color⟩
    have pairBounds : edgeIndex < input.graph.edges.length ∧ color < input.colors := by
      simpa [pair, pairEquality] using (mem_edgeColorPairs_iff input pair).1 pairMember
    rcases pairBounds with ⟨edgeBound, colorBound⟩
    have indexOf : (edgeColorPairs input).idxOf (edgeIndex, color) = offset := by
      simpa [pair, pairEquality] using (edgeColorPairs_nodup input).idxOf_getElem offset offsetBound
    have markerCode : marker = edgeColorCode input edgeIndex color := by
      have markerAdd : marker = input.graph.vertices + offset := by omega
      rw [markerAdd, edgeColorCode, indexOf]
    by_cases leftColor : color = normalizedColor input colorOf (edgeAt input edgeIndex).1
    · refine ⟨choiceBlock input (edgeAt input edgeIndex).1
          (normalizedColor input colorOf (edgeAt input edgeIndex).1), ?_, ?_⟩
      · have leftBound : (edgeAt input edgeIndex).1 < input.graph.vertices := by
          by_contra leftBound
          have normalized := normalizedColor_eq_of_not_lt input colorOf leftBound
          omega
        exact (mem_selectedBlocks_iff input (normalizedColor input colorOf)
          (choiceBlock input (edgeAt input edgeIndex).1
            (normalizedColor input colorOf (edgeAt input edgeIndex).1))).2
          ((mem_selectedBlocksRaw_iff input (normalizedColor input colorOf)
            (choiceBlock input (edgeAt input edgeIndex).1
              (normalizedColor input colorOf (edgeAt input edgeIndex).1))).2
            (Or.inl ⟨(edgeAt input edgeIndex).1, leftBound, rfl⟩))
      · rw [markerCode, leftColor]
        exact edgeColorCode_mem_choiceBlock edgeBound (Or.inl rfl)
    · by_cases rightColor : color = normalizedColor input colorOf (edgeAt input edgeIndex).2
      · refine ⟨choiceBlock input (edgeAt input edgeIndex).2
            (normalizedColor input colorOf (edgeAt input edgeIndex).2), ?_, ?_⟩
        · have rightBound : (edgeAt input edgeIndex).2 < input.graph.vertices := by
            by_contra rightBound
            have normalized := normalizedColor_eq_of_not_lt input colorOf rightBound
            omega
          exact (mem_selectedBlocks_iff input (normalizedColor input colorOf)
            (choiceBlock input (edgeAt input edgeIndex).2
              (normalizedColor input colorOf (edgeAt input edgeIndex).2))).2
            ((mem_selectedBlocksRaw_iff input (normalizedColor input colorOf)
              (choiceBlock input (edgeAt input edgeIndex).2
                (normalizedColor input colorOf (edgeAt input edgeIndex).2))).2
              (Or.inl ⟨(edgeAt input edgeIndex).2, rightBound, rfl⟩))
        · rw [markerCode, rightColor]
          exact edgeColorCode_mem_choiceBlock edgeBound (Or.inr rfl)
      · refine ⟨fillerBlock input edgeIndex color, ?_, ?_⟩
        · exact (mem_selectedBlocks_iff input (normalizedColor input colorOf)
            (fillerBlock input edgeIndex color)).2
            ((mem_selectedBlocksRaw_iff input (normalizedColor input colorOf)
              (fillerBlock input edgeIndex color)).2
              (Or.inr ⟨edgeIndex, edgeBound, color, colorBound,
                leftColor, rightColor, rfl⟩))
        · rw [markerCode]
          simp [fillerBlock]

/-- A proper source colouring gives a value-level exact-cover witness. -/
theorem properColoring_to_valueBlockExactCover {input : GraphColoringIR}
    {colorOf : Nat → Nat} (proper : ProperColoring input.graph input.colors colorOf) :
    ValueBlockExactCover (universeSize input) (blockFamily input) := by
  let normalized := normalizedColor input colorOf
  have noSelfLoop : ¬ GraphHasSelfLoop input := properColoring_not_graphHasSelfLoop proper
  have normalizedProper : ProperColoring input.graph input.colors normalized := by
    simpa [normalized] using normalizedColor_proper noSelfLoop proper
  refine ⟨?_, selectedBlocks input normalized, ?_, selectedBlocks_nodup input normalized, ?_, ?_⟩
  · intro block blockMember marker markerMember
    exact marker_lt_universe_of_mem_blockFamily blockMember markerMember
  · exact selectedBlocks_family_of_proper normalizedProper
  · exact selectedBlocks_pairwiseDisjoint normalizedProper
  · simpa [normalized] using selectedBlocks_coversUniverse input colorOf

/--
Promote a value-level cover to the index-preserving cover required by
`IncidenceIR`.  `attach` keeps the proof that each selected value is present
in the ordered family, so duplicate family values are never quotient-ed away.
-/
theorem valueBlockExactCover_to_indexed {universeSize : Nat} {blocks : List (List Nat)} :
    ValueBlockExactCover universeSize blocks → IndexedBlockExactCover universeSize blocks := by
  rintro ⟨blockBounds, selected, selectedInFamily, selectedNodup, disjoint, covers⟩
  let selectedIndices : List Nat :=
    selected.attach.map fun entry : { block // block ∈ selected } => blocks.idxOf entry.val
  refine ⟨blockBounds, selectedIndices, ?_, ?_, ?_⟩
  · apply selectedNodup.attach.map
    intro first second sameIndex
    apply Subtype.ext
    exact (List.idxOf_inj (selectedInFamily first.val first.property)).1 sameIndex
  · intro right selectedRight
    unfold selectedIndices at selectedRight
    rcases List.mem_map.mp selectedRight with ⟨entry, _entryMember, rightEquality⟩
    rw [← rightEquality]
    exact List.idxOf_lt_length_iff.mpr (selectedInFamily entry.val entry.property)
  · intro marker markerBound
    rcases covers marker markerBound with ⟨block, blockSelected, markerMember⟩
    let right := blocks.idxOf block
    refine ⟨right, ?_, ?_⟩
    · constructor
      · unfold selectedIndices
        apply List.mem_map.mpr
        exact ⟨⟨block, blockSelected⟩, by simp, rfl⟩
      · have rightBound : right < blocks.length := by
          exact List.idxOf_lt_length_iff.mpr (selectedInFamily block blockSelected)
        exact (getD_eq_of_getElem [] blocks rightBound (List.idxOf_get rightBound)).symm ▸ markerMember
    · intro other otherWitness
      rcases otherWitness with ⟨otherSelected, otherMarkerMember⟩
      unfold selectedIndices at otherSelected
      rcases List.mem_map.mp otherSelected with ⟨entry, _entryMember, otherEquality⟩
      have entryInFamily := selectedInFamily entry.val entry.property
      have entryBound : blocks.idxOf entry.val < blocks.length :=
        List.idxOf_lt_length_iff.mpr entryInFamily
      have entryBlock : blocks.getD (blocks.idxOf entry.val) [] = entry.val :=
        getD_eq_of_getElem [] blocks entryBound (List.idxOf_get entryBound)
      have markerInEntry : marker ∈ entry.val := by
        rw [← otherEquality] at otherMarkerMember
        rw [← entryBlock]
        exact otherMarkerMember
      have sameBlock : entry.val = block := by
        rcases disjoint entry.val entry.property block blockSelected with disjointEntry
        by_contra different
        exact disjointEntry different marker markerInEntry markerMember
      calc
        other = blocks.idxOf entry.val := otherEquality.symm
        _ = blocks.idxOf block := by rw [sameBlock]
        _ = right := rfl

/--
Forget right-vertex indices only as a local semantic aid.  The returned
value-level witness is deduplicated; the canonical target remains the indexed
predicate above.
-/
theorem indexedBlockExactCover_to_value {universeSize : Nat} {blocks : List (List Nat)} :
    IndexedBlockExactCover universeSize blocks → ValueBlockExactCover universeSize blocks := by
  rintro ⟨blockBounds, selected, selectedNodup, selectedBound, covers⟩
  let selectedBlocks := (selected.map fun right => blocks.getD right []).dedup
  refine ⟨blockBounds, selectedBlocks, ?_, List.nodup_dedup _, ?_, ?_⟩
  · intro block blockSelected
    have rawSelected : block ∈ selected.map (fun right => blocks.getD right []) := by
      simpa [selectedBlocks] using blockSelected
    rcases List.mem_map.mp rawSelected with ⟨right, rightSelected, blockEquality⟩
    rw [← blockEquality]
    exact getD_mem [] blocks (selectedBound right rightSelected)
  · intro first firstSelected second secondSelected different marker firstMember secondMember
    have firstRaw : first ∈ selected.map (fun right => blocks.getD right []) := by
      simpa [selectedBlocks] using firstSelected
    have secondRaw : second ∈ selected.map (fun right => blocks.getD right []) := by
      simpa [selectedBlocks] using secondSelected
    rcases List.mem_map.mp firstRaw with ⟨firstRight, firstRightSelected, firstEquality⟩
    rcases List.mem_map.mp secondRaw with ⟨secondRight, secondRightSelected, secondEquality⟩
    have firstInFamily : first ∈ blocks := by
      rw [← firstEquality]
      exact getD_mem [] blocks (selectedBound firstRight firstRightSelected)
    have markerBound : marker < universeSize :=
      blockBounds first firstInFamily marker firstMember
    rcases covers marker markerBound with ⟨right, ⟨rightSelected, rightMember⟩, unique⟩
    have firstMemberAtRight : marker ∈ blocks.getD firstRight [] := by
      rw [firstEquality]
      exact firstMember
    have secondMemberAtRight : marker ∈ blocks.getD secondRight [] := by
      rw [secondEquality]
      exact secondMember
    have firstRightEquality : firstRight = right :=
      unique firstRight ⟨firstRightSelected, firstMemberAtRight⟩
    have secondRightEquality : secondRight = right :=
      unique secondRight ⟨secondRightSelected, secondMemberAtRight⟩
    apply different
    calc
      first = blocks.getD firstRight [] := firstEquality.symm
      _ = blocks.getD secondRight [] := by rw [firstRightEquality, secondRightEquality]
      _ = second := secondEquality
  · intro marker markerBound
    rcases covers marker markerBound with ⟨right, ⟨rightSelected, rightMember⟩, _unique⟩
    refine ⟨blocks.getD right [], ?_, rightMember⟩
    simp only [selectedBlocks, List.mem_dedup, List.mem_map]
    exact ⟨right, rightSelected, rfl⟩

/-- Recover the chosen colour block for a vertex from a value-level cover. -/
theorem exists_selectedChoiceBlock_of_covers {input : GraphColoringIR}
    {selected : List (List Nat)}
    (selectedInFamily : ∀ block ∈ selected, block ∈ blockFamily input)
    (covers : ∀ marker, marker < universeSize input → ∃ block ∈ selected, marker ∈ block)
    {vertex : Nat} (vertexBound : vertex < input.graph.vertices) :
    ∃ color, color < input.colors ∧ choiceBlock input vertex color ∈ selected := by
  rcases covers (vertexCode input vertex) (vertexCode_lt_universe vertexBound) with
    ⟨block, blockSelected, vertexMember⟩
  rcases List.mem_append.mp (selectedInFamily block blockSelected) with choiceMember | fillerMember
  · rcases (mem_choiceBlocks_iff input block).1 choiceMember with
      ⟨otherVertex, _otherVertexBound, color, colorBound, rfl⟩
    rcases (mem_choiceBlock_iff input otherVertex color (vertexCode input vertex)).1 vertexMember with
      vertexCodeEquality | edgeCodeEquality
    · have verticesEqual : vertex = otherVertex := by
        simpa [vertexCode] using vertexCodeEquality
      subst otherVertex
      exact ⟨color, colorBound, blockSelected⟩
    · rcases edgeCodeEquality with ⟨edgeIndex, _edgeBound, _incident, codeEquality⟩
      exact (vertexCode_ne_edgeColorCode vertexBound codeEquality).elim
  · rcases (mem_fillerBlocks_iff input block).1 fillerMember with
      ⟨edgeIndex, _edgeBound, color, _colorBound, rfl⟩
    have codeEquality := (mem_fillerBlock_iff input edgeIndex color (vertexCode input vertex)).1
      vertexMember
    exact (vertexCode_ne_edgeColorCode vertexBound codeEquality).elim

/-- Extract a proper hub-level colouring from an indexed exact-cover witness. -/
theorem blockExactCover_to_isColorable {input : GraphColoringIR}
    (noSelfLoop : ¬ GraphHasSelfLoop input) (exactCover : BlockExactCover input) :
    GraphColoringIR.IsColorable input := by
  classical
  rcases indexedBlockExactCover_to_value exactCover with
    ⟨_blockBounds, selected, selectedInFamily, _selectedNodup, disjoint, covers⟩
  have existsColor :
      ∀ vertex, vertex < input.graph.vertices →
        ∃ color, color < input.colors ∧ choiceBlock input vertex color ∈ selected := by
    intro vertex vertexBound
    exact exists_selectedChoiceBlock_of_covers selectedInFamily covers vertexBound
  let colorOf : Nat → Nat := fun vertex =>
    if vertexBound : vertex < input.graph.vertices then
      Classical.choose (existsColor vertex vertexBound)
    else input.colors + vertex
  refine ⟨colorOf, ?_, ?_⟩
  · intro vertex vertexBound
    have colorSpec := Classical.choose_spec (existsColor vertex vertexBound)
    simpa [colorOf, vertexBound] using colorSpec.1
  · intro edge edgeMember sameColor
    by_cases leftBound : edge.1 < input.graph.vertices
    · by_cases rightBound : edge.2 < input.graph.vertices
      · let edgeIndex := input.graph.edges.idxOf edge
        have edgeIndexBound : edgeIndex < input.graph.edges.length :=
          List.idxOf_lt_length_iff.mpr edgeMember
        have edgeAtEquality : edgeAt input edgeIndex = edge := by
          rw [edgeAt_eq_getElem edgeIndexBound]
          exact List.idxOf_get (l := input.graph.edges) (a := edge) edgeIndexBound
        have leftSpec := Classical.choose_spec (existsColor edge.1 leftBound)
        have rightSpec := Classical.choose_spec (existsColor edge.2 rightBound)
        have leftColor : colorOf edge.1 = Classical.choose (existsColor edge.1 leftBound) := by
          simp [colorOf, leftBound]
        have rightColor : colorOf edge.2 = Classical.choose (existsColor edge.2 rightBound) := by
          simp [colorOf, rightBound]
        have leftSelected : choiceBlock input edge.1 (colorOf edge.1) ∈ selected := by
          simpa [leftColor] using leftSpec.2
        have rightSelected : choiceBlock input edge.2 (colorOf edge.2) ∈ selected := by
          simpa [rightColor] using rightSpec.2
        have blocksDifferent : choiceBlock input edge.1 (colorOf edge.1) ≠
            choiceBlock input edge.2 (colorOf edge.2) := by
          intro blockEquality
          have verticesEqual : edge.1 = edge.2 := by
            simpa [choiceBlock, vertexCode] using congrArg List.head! blockEquality
          exact noSelfLoop ⟨edge, edgeMember, verticesEqual⟩
        have leftMarker : edgeColorCode input edgeIndex (colorOf edge.1) ∈
            choiceBlock input edge.1 (colorOf edge.1) := by
          exact edgeColorCode_mem_choiceBlock edgeIndexBound (by
            unfold EdgeIncident
            rw [edgeAtEquality]
            exact Or.inl rfl)
        have rightMarker : edgeColorCode input edgeIndex (colorOf edge.1) ∈
            choiceBlock input edge.2 (colorOf edge.2) := by
          rw [sameColor]
          exact edgeColorCode_mem_choiceBlock edgeIndexBound (by
            unfold EdgeIncident
            rw [edgeAtEquality]
            exact Or.inr rfl)
        exact disjoint (choiceBlock input edge.1 (colorOf edge.1)) leftSelected
          (choiceBlock input edge.2 (colorOf edge.2)) rightSelected blocksDifferent
          (edgeColorCode input edgeIndex (colorOf edge.1)) leftMarker rightMarker
      · have leftSpec := Classical.choose_spec (existsColor edge.1 leftBound) |>.1
        have leftColor : colorOf edge.1 = Classical.choose (existsColor edge.1 leftBound) := by
          simp [colorOf, leftBound]
        have rightColor : colorOf edge.2 = input.colors + edge.2 := by
          simp [colorOf, rightBound]
        omega
    · by_cases rightBound : edge.2 < input.graph.vertices
      · have rightSpec := Classical.choose_spec (existsColor edge.2 rightBound) |>.1
        have leftColor : colorOf edge.1 = input.colors + edge.1 := by
          simp [colorOf, leftBound]
        have rightColor : colorOf edge.2 = Classical.choose (existsColor edge.2 rightBound) := by
          simp [colorOf, rightBound]
        omega
      · have leftColor : colorOf edge.1 = input.colors + edge.1 := by
          simp [colorOf, leftBound]
        have rightColor : colorOf edge.2 = input.colors + edge.2 := by
          simp [colorOf, rightBound]
        have selfLoop : edge.1 = edge.2 := by omega
        exact noSelfLoop ⟨edge, edgeMember, selfLoop⟩

/-- The graph hub and ordered-block semantics agree whenever the loop guard is false. -/
theorem isColorable_iff_blockExactCover {input : GraphColoringIR}
    (noSelfLoop : ¬ GraphHasSelfLoop input) :
    GraphColoringIR.IsColorable input ↔ BlockExactCover input := by
  constructor
  · rintro ⟨colorOf, proper⟩
    exact valueBlockExactCover_to_indexed (properColoring_to_valueBlockExactCover proper)
  · exact blockExactCover_to_isColorable noSelfLoop

/--
The canonical hub-level semantic iff for the reusable Graph-to-Incidence
construction.  The self-loop branch is explicitly fail-closed, while the
ordinary branch preserves the ordered right-vertex identity of every block.
-/
theorem isColorable_iff_run_exactCover (input : GraphColoringIR) :
    GraphColoringIR.IsColorable input ↔ IncidenceIR.ExistsExactCover (run input) := by
  cases loop : graphHasSelfLoopBool input with
  | false =>
      have noSelfLoop : ¬ GraphHasSelfLoop input := by
        intro selfLoop
        have detected := (graphHasSelfLoopBool_eq_true_iff input).2 selfLoop
        simp [loop] at detected
      calc
        GraphColoringIR.IsColorable input ↔ BlockExactCover input :=
          isColorable_iff_blockExactCover noSelfLoop
        _ ↔ IncidenceIR.ExistsExactCover (run input) :=
          run_of_noSelfLoop_blockExactCover_iff_incidence input loop
  | true =>
      have selfLoop : GraphHasSelfLoop input :=
        (graphHasSelfLoopBool_eq_true_iff input).1 loop
      constructor
      · rintro ⟨colorOf, proper⟩
        exact (properColoring_not_graphHasSelfLoop proper selfLoop).elim
      · intro exactCover
        have noExactCover : ¬ IncidenceIR.ExistsExactCover (run input) := by
          rw [run_of_graphHasSelfLoopBool_true input loop]
          exact noTarget_not_exactCover
        exact (noExactCover exactCover).elim

/-- A proper colouring directly yields the index-preserving hub predicate. -/
theorem properColoring_to_blockExactCover {input : GraphColoringIR}
    {colorOf : Nat → Nat} (proper : ProperColoring input.graph input.colors colorOf) :
    BlockExactCover input :=
  valueBlockExactCover_to_indexed (properColoring_to_valueBlockExactCover proper)

/-- The non-self-loop branch always emits a well-formed canonical incidence table. -/
theorem constructed_wellFormed (input : GraphColoringIR) :
    (IncidenceIR.mk (universeSize input) (blockFamily input).length (membershipPairs input)).WellFormed := by
  intro pair pairMember
  constructor
  · rcases mem_membershipPairsFrom_left_mem 0 (blockFamily input) pair pairMember with
      ⟨block, blockMember, markerMember⟩
    exact marker_lt_universe_of_mem_blockFamily blockMember markerMember
  · simpa [membershipPairs] using
      mem_membershipPairsFrom_right_lt 0 (blockFamily input) pair pairMember

/-- Both branches of the pure construction are well formed at the incidence hub. -/
theorem run_wellFormed (input : GraphColoringIR) : (run input).WellFormed := by
  cases loop : graphHasSelfLoopBool input with
  | false =>
      rw [run_of_graphHasSelfLoopBool_false input loop]
      exact constructed_wellFormed input
  | true =>
      rw [run_of_graphHasSelfLoopBool_true input loop]
      intro pair pairMember
      simp [noTarget, IncidenceIR.mk, IncidenceIR.membershipPairs] at pairMember

end GraphColoringToIncidence
end Domain
end ComplexityReduction
