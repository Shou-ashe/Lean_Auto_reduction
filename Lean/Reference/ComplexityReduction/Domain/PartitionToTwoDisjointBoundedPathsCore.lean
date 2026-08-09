/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Presentation.PartitionBinary
import ComplexityReduction.Presentation.TwoDisjointBoundedPaths
import Mathlib.Tactic

/-!
Semantic core of a binary-Partition to Two Disjoint Bounded Paths reduction.

For `n` source weights the output has `n + 1` directed stages.  Every stage
contains two parallel edges.  The first copy costs `2 * w + 1`, the second
costs `1`, and the extra final stage has weight zero.  Two edge-disjoint
source-to-target paths must therefore choose complementary copies at every
stage.  Requiring both costs to be at most `(n + 1) + sum weights` is exactly
the Partition equality.
-/

namespace ComplexityReduction
namespace Domain
namespace PartitionToTwoDisjointBoundedPathsCore

open Encoding
open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

abbrev source : PresentedProblem :=
  Presentation.PartitionBinary.structuredProblem

abbrev target : PresentedProblem :=
  Presentation.TwoDisjointBoundedPaths.presentedProblem

/-- One extra zero-weight stage makes the public terminals distinct even on `[]`. -/
def stageCount (input : PartitionInput) : Nat :=
  input.weights.length + 1

/-- The common directed edge carried by both parallel copies at one stage. -/
def stageEdge (stage : Nat) : Nat × Nat :=
  (stage, stage + 1)

/-- One ordered copy of all stage edges. -/
def stageEdges (input : PartitionInput) : List (Nat × Nat) :=
  (List.range (stageCount input)).map stageEdge

/-- First-copy edges followed by their parallel second-copy counterparts. -/
def ladderEdges (input : PartitionInput) : List (Nat × Nat) :=
  stageEdges input ++ stageEdges input

/-- The zero-weight terminal stage. -/
def augmentedWeights (input : PartitionInput) : List Nat :=
  input.weights ++ [0]

/-- The cost of selecting the first copy of every stage. -/
def heavyCosts (input : PartitionInput) : List Nat :=
  (augmentedWeights input).map fun weight => weight + weight + 1

/-- Every second-copy edge has unit cost. -/
def lightCosts (input : PartitionInput) : List Nat :=
  (List.range (stageCount input)).map fun _ => 1

/-- Costs aligned with `ladderEdges`. -/
def ladderCosts (input : PartitionInput) : List Nat :=
  heavyCosts input ++ lightCosts input

/-- The complete directed two-copy ladder. -/
def ladderGraph (input : PartitionInput) : GraphInput where
  vertices := stageCount input + 1
  edges := ladderEdges input
  directed := true

/-- Exact target instance. -/
def executable (input : PartitionInput) : target.Instance where
  graph := ladderGraph input
  costs := ladderCosts input
  source := 0
  target := stageCount input
  bound := stageCount input + input.weights.sum

@[simp] theorem stageCount_pos (input : PartitionInput) :
    0 < stageCount input := by
  simp [stageCount]

@[simp] theorem stageEdges_length (input : PartitionInput) :
    (stageEdges input).length = stageCount input := by
  simp [stageEdges]

@[simp] theorem ladderEdges_length (input : PartitionInput) :
    (ladderEdges input).length = 2 * stageCount input := by
  simp [ladderEdges, Nat.mul_comm, Nat.two_mul]

@[simp] theorem augmentedWeights_length (input : PartitionInput) :
    (augmentedWeights input).length = stageCount input := by
  simp [augmentedWeights, stageCount]

@[simp] theorem heavyCosts_length (input : PartitionInput) :
    (heavyCosts input).length = stageCount input := by
  simp [heavyCosts]

@[simp] theorem lightCosts_length (input : PartitionInput) :
    (lightCosts input).length = stageCount input := by
  simp [lightCosts]

@[simp] theorem ladderCosts_length (input : PartitionInput) :
    (ladderCosts input).length = 2 * stageCount input := by
  simp [ladderCosts, Nat.mul_comm, Nat.two_mul]

theorem ladderGraph_wellFormed (input : PartitionInput) :
    WellFormed (ladderGraph input) := by
  intro edge member
  simp only [ladderGraph, ladderEdges, List.mem_append] at member
  rcases member with member | member
  · rcases List.mem_map.mp member with ⟨stage, stageMember, rfl⟩
    have bound := List.mem_range.mp stageMember
    change stage < stageCount input + 1 ∧ stage + 1 < stageCount input + 1
    omega
  · rcases List.mem_map.mp member with ⟨stage, stageMember, rfl⟩
    have bound := List.mem_range.mp stageMember
    change stage < stageCount input + 1 ∧ stage + 1 < stageCount input + 1
    omega

theorem ladderCosts_positive (input : PartitionInput) :
    ∀ cost ∈ ladderCosts input, 0 < cost := by
  intro cost member
  simp only [ladderCosts, List.mem_append] at member
  rcases member with member | member
  · rcases List.mem_map.mp member with ⟨weight, _weightMember, rfl⟩
    omega
  · rcases List.mem_map.mp member with ⟨stage, _stageMember, rfl⟩
    simp

theorem executable_fixedProperties (input : PartitionInput) :
    (executable input).graph.directed = true ∧
      WellFormed (executable input).graph ∧
      (executable input).source < (executable input).graph.vertices ∧
      (executable input).target < (executable input).graph.vertices ∧
      (executable input).source ≠ (executable input).target ∧
      (executable input).costs.length = (executable input).graph.edges.length ∧
      (∀ cost ∈ (executable input).costs, 0 < cost) := by
  refine ⟨rfl, ladderGraph_wellFormed input, ?_, ?_, ?_, ?_, ladderCosts_positive input⟩
  · simp [executable, ladderGraph]
  · simp [executable, ladderGraph]
  · simp [executable, stageCount]
  · simp [executable, ladderGraph]

theorem stageEdges_getD (input : PartitionInput) {stage : Nat}
    (stageBound : stage < stageCount input) :
    (stageEdges input).getD stage (0, 0) = stageEdge stage := by
  rw [List.getD_eq_getElem (l := stageEdges input) (d := (0, 0))
    (n := stage) (by simpa using stageBound)]
  simp [stageEdges, stageEdge]

theorem ladderEdgeAt_first (input : PartitionInput) {stage : Nat}
    (stageBound : stage < stageCount input) :
    Presentation.TwoDisjointBoundedPaths.edgeAt (ladderGraph input) stage =
      stageEdge stage := by
  unfold Presentation.TwoDisjointBoundedPaths.edgeAt ladderGraph ladderEdges
  rw [List.getD_append (l := stageEdges input) (l' := stageEdges input)
    (d := (0, 0)) (n := stage) (by simpa using stageBound)]
  exact stageEdges_getD input stageBound

theorem ladderEdgeAt_second (input : PartitionInput) {stage : Nat}
    (stageBound : stage < stageCount input) :
    Presentation.TwoDisjointBoundedPaths.edgeAt (ladderGraph input)
        (stageCount input + stage) = stageEdge stage := by
  unfold Presentation.TwoDisjointBoundedPaths.edgeAt ladderGraph ladderEdges
  rw [List.getD_append_right (l := stageEdges input) (l' := stageEdges input)
    (d := (0, 0)) (n := stageCount input + stage) (by simp)]
  simp only [stageEdges_length, Nat.add_sub_cancel_left]
  exact stageEdges_getD input stageBound

/-- Every in-range ladder edge has a unique stage and one of two copy indices. -/
theorem ladderEdgeAt_shape (input : PartitionInput) {index : Nat}
    (indexBound : index < (ladderGraph input).edges.length) :
    ∃ stage,
      stage < stageCount input ∧
        Presentation.TwoDisjointBoundedPaths.edgeAt (ladderGraph input) index =
          stageEdge stage ∧
        (index = stage ∨ index = stageCount input + stage) := by
  have fullBound : index < 2 * stageCount input := by
    simpa [ladderGraph] using indexBound
  by_cases firstCopy : index < stageCount input
  · exact ⟨index, firstCopy, ladderEdgeAt_first input firstCopy, Or.inl rfl⟩
  · let stage := index - stageCount input
    have stageBound : stage < stageCount input := by
      dsimp [stage]
      omega
    have indexEquality : index = stageCount input + stage := by
      dsimp [stage]
      omega
    have edgeEquality :
        Presentation.TwoDisjointBoundedPaths.edgeAt (ladderGraph input) index =
          stageEdge stage := by
      rw [indexEquality]
      exact ladderEdgeAt_second input stageBound
    exact ⟨stage, stageBound, edgeEquality, Or.inr indexEquality⟩

/-- Every later edge in a ladder chain starts no earlier than the chain source. -/
theorem edgeChain_member_source_ge (input : PartitionInput) :
    ∀ {current path targetVertex index},
      Presentation.TwoDisjointBoundedPaths.EdgeChain
          (ladderGraph input) current path targetVertex →
        index ∈ path →
        current ≤
          (Presentation.TwoDisjointBoundedPaths.edgeAt
            (ladderGraph input) index).1 := by
  intro current path
  induction path generalizing current with
  | nil =>
      intro targetVertex index _chain member
      simp at member
  | cons head rest inductionHypothesis =>
      intro targetVertex index chain member
      rcases chain with ⟨headBound, headSource, tailChain⟩
      rcases (ladderEdgeAt_shape input headBound) with
        ⟨stage, _stageBound, headEdge, _headIndex⟩
      have stageCurrent : stage = current := by
        simpa [headEdge, stageEdge] using headSource
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simpa [headEdge, stageEdge, stageCurrent]
      · have tailLower := inductionHypothesis tailChain member
        have nextCurrent :
            (Presentation.TwoDisjointBoundedPaths.edgeAt
              (ladderGraph input) head).2 = current + 1 := by
          simp [headEdge, stageEdge, stageCurrent]
        rw [nextCurrent] at tailLower
        omega

/-- Edge simplicity is automatic for any directed chain in the staged ladder. -/
theorem edgeChain_nodup (input : PartitionInput) :
    ∀ {current path targetVertex},
      Presentation.TwoDisjointBoundedPaths.EdgeChain
          (ladderGraph input) current path targetVertex →
        path.Nodup := by
  intro current path
  induction path generalizing current with
  | nil =>
      intro targetVertex _chain
      exact List.nodup_nil
  | cons head rest inductionHypothesis =>
      intro targetVertex chain
      rcases chain with ⟨headBound, headSource, tailChain⟩
      rcases (ladderEdgeAt_shape input headBound) with
        ⟨stage, _stageBound, headEdge, _headIndex⟩
      have stageCurrent : stage = current := by
        simpa [headEdge, stageEdge] using headSource
      have nextCurrent :
          (Presentation.TwoDisjointBoundedPaths.edgeAt
            (ladderGraph input) head).2 = current + 1 := by
        simp [headEdge, stageEdge, stageCurrent]
      constructor
      · rintro other otherMember rfl
        have lower := edgeChain_member_source_ge input tailChain otherMember
        rw [nextCurrent] at lower
        simp [headEdge, stageEdge, stageCurrent] at lower
      · exact inductionHypothesis tailChain

/-- A valid chain exposes exactly one of the two copy indices at each stage. -/
theorem edgeChain_shape (input : PartitionInput) :
    ∀ {current path},
      Presentation.TwoDisjointBoundedPaths.EdgeChain
          (ladderGraph input) current path (stageCount input) →
        current ≤ stageCount input →
        path.length = stageCount input - current ∧
          ∀ offset, offset < path.length →
            path.getD offset 0 = current + offset ∨
              path.getD offset 0 = stageCount input + (current + offset) := by
  intro current path
  induction path generalizing current with
  | nil =>
      intro chain currentBound
      have equality : current = stageCount input := by
        simpa [Presentation.TwoDisjointBoundedPaths.EdgeChain] using chain
      subst current
      simp
  | cons head rest inductionHypothesis =>
      intro chain currentBound
      rcases chain with ⟨headBound, headSource, tailChain⟩
      rcases (ladderEdgeAt_shape input headBound) with
        ⟨stage, stageBound, headEdge, headIndex⟩
      have stageCurrent : stage = current := by
        simpa [headEdge, stageEdge] using headSource
      have currentStrict : current < stageCount input := by
        simpa [stageCurrent] using stageBound
      have nextCurrent :
          (Presentation.TwoDisjointBoundedPaths.edgeAt
            (ladderGraph input) head).2 = current + 1 := by
        simp [headEdge, stageEdge, stageCurrent]
      rw [nextCurrent] at tailChain
      have tailShape := inductionHypothesis tailChain (by omega)
      constructor
      · simp only [List.length_cons, tailShape.1]
        omega
      · intro offset offsetBound
        cases offset with
        | zero =>
            simp only [List.getD_cons_zero, Nat.add_zero]
            rcases headIndex with first | second
            · exact Or.inl (by simpa [stageCurrent] using first)
            · exact Or.inr (by simpa [stageCurrent] using second)
        | succ offset =>
            simp only [List.getD_cons_succ]
            have localBound : offset < rest.length := by simp at offsetBound; omega
            rcases tailShape.2 offset localBound with first | second
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)

/-! ### Aligned binary costs and the Boolean selection decoded from a path -/

theorem augmentedWeights_getD (input : PartitionInput) {stage : Nat}
    (stageBound : stage < stageCount input) :
    (augmentedWeights input).getD stage 0 = input.weights.getD stage 0 := by
  by_cases originalBound : stage < input.weights.length
  · unfold augmentedWeights
    rw [List.getD_append (l := input.weights) (l' := [0]) (d := 0)
      (n := stage) originalBound]
  · have stageEquality : stage = input.weights.length := by
      unfold stageCount at stageBound
      omega
    subst stage
    simp [augmentedWeights]

theorem heavyCosts_getD (input : PartitionInput) {stage : Nat}
    (stageBound : stage < stageCount input) :
    (heavyCosts input).getD stage 0 =
      input.weights.getD stage 0 + input.weights.getD stage 0 + 1 := by
  rw [List.getD_eq_getElem (l := heavyCosts input) (d := 0) (n := stage)
    (by simpa using stageBound)]
  simp only [heavyCosts, List.getElem_map]
  rw [← List.getD_eq_getElem (l := augmentedWeights input) (d := 0) (n := stage)
    (by simpa using stageBound)]
  rw [augmentedWeights_getD input stageBound]

theorem lightCosts_getD (input : PartitionInput) {stage : Nat}
    (stageBound : stage < stageCount input) :
    (lightCosts input).getD stage 0 = 1 := by
  rw [List.getD_eq_getElem (l := lightCosts input) (d := 0) (n := stage)
    (by simpa using stageBound)]
  simp [lightCosts]

theorem ladderCosts_getD_first (input : PartitionInput) {stage : Nat}
    (stageBound : stage < stageCount input) :
    (ladderCosts input).getD stage 0 =
      input.weights.getD stage 0 + input.weights.getD stage 0 + 1 := by
  unfold ladderCosts
  rw [List.getD_append (l := heavyCosts input) (l' := lightCosts input)
    (d := 0) (n := stage) (by simpa using stageBound)]
  exact heavyCosts_getD input stageBound

theorem ladderCosts_getD_second (input : PartitionInput) {stage : Nat}
    (stageBound : stage < stageCount input) :
    (ladderCosts input).getD (stageCount input + stage) 0 = 1 := by
  unfold ladderCosts
  rw [List.getD_append_right (l := heavyCosts input) (l' := lightCosts input)
    (d := 0) (n := stageCount input + stage) (by simp)]
  simp only [heavyCosts_length, Nat.add_sub_cancel_left]
  exact lightCosts_getD input stageBound

private theorem range_map_getD (values : List Nat) :
    (List.range values.length).map (fun index => values.getD index 0) = values := by
  apply List.ext_get
  · simp
  · intro index leftBound rightBound
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem (l := values) (d := 0) (n := index) rightBound

/-- The first `n` stages decode to the source Partition selection. -/
def pathSelection (input : PartitionInput) (path : List Nat) : List Bool :=
  (List.range input.weights.length).map fun stage =>
    decide (path.getD stage 0 = stage)

@[simp] theorem pathSelection_length (input : PartitionInput) (path : List Nat) :
    (pathSelection input path).length = input.weights.length := by
  simp [pathSelection]

theorem pathSelection_getD (input : PartitionInput) (path : List Nat) {stage : Nat}
    (stageBound : stage < input.weights.length) :
    (pathSelection input path).getD stage false =
      decide (path.getD stage 0 = stage) := by
  rw [List.getD_eq_getElem (l := pathSelection input path) (d := false) (n := stage)
    (by simpa using stageBound)]
  simp [pathSelection, stageBound]

theorem selectedPartitionWeight_eq_indexed
    (weights : List Nat) (bits : List Bool)
    (lengthEquality : bits.length = weights.length) :
    selectedPartitionWeight { weights := weights } bits =
      ((List.range weights.length).map fun index =>
        if bits.getD index false then weights.getD index 0 else 0).sum := by
  induction weights generalizing bits with
  | nil =>
      cases bits with
      | nil => simp [selectedPartitionWeight]
      | cons bit bits => simp at lengthEquality
  | cons weight weights inductionHypothesis =>
      cases bits with
      | nil => simp at lengthEquality
      | cons bit bits =>
          have tailLength : bits.length = weights.length := by simpa using lengthEquality
          change
            (if bit then weight else 0) +
                selectedPartitionWeight { weights := weights } bits = _
          rw [inductionHypothesis bits tailLength]
          simp only [List.length_cons]
          rw [List.range_succ_eq_map]
          simp only [List.map_cons, List.sum_cons, List.map_map, List.getD_cons_zero]
          congr 1

theorem unselectedPartitionWeight_eq_indexed
    (weights : List Nat) (bits : List Bool)
    (lengthEquality : bits.length = weights.length) :
    unselectedPartitionWeight { weights := weights } bits =
      ((List.range weights.length).map fun index =>
        if bits.getD index false then 0 else weights.getD index 0).sum := by
  induction weights generalizing bits with
  | nil =>
      cases bits with
      | nil => simp [unselectedPartitionWeight]
      | cons bit bits => simp at lengthEquality
  | cons weight weights inductionHypothesis =>
      cases bits with
      | nil => simp at lengthEquality
      | cons bit bits =>
          have tailLength : bits.length = weights.length := by simpa using lengthEquality
          change
            (if bit then 0 else weight) +
                unselectedPartitionWeight { weights := weights } bits = _
          rw [inductionHypothesis bits tailLength]
          simp only [List.length_cons]
          rw [List.range_succ_eq_map]
          simp only [List.map_cons, List.sum_cons, List.map_map, List.getD_cons_zero]
          congr 1

theorem selected_add_unselected_eq_sum
    (weights : List Nat) (bits : List Bool)
    (lengthEquality : bits.length = weights.length) :
    selectedPartitionWeight { weights := weights } bits +
        unselectedPartitionWeight { weights := weights } bits = weights.sum := by
  induction weights generalizing bits with
  | nil =>
      cases bits with
      | nil => simp [selectedPartitionWeight, unselectedPartitionWeight]
      | cons bit bits => simp at lengthEquality
  | cons weight weights inductionHypothesis =>
      cases bits with
      | nil => simp at lengthEquality
      | cons bit bits =>
          have tailLength : bits.length = weights.length := by simpa using lengthEquality
          have tailEquality := inductionHypothesis bits tailLength
          cases bit <;>
            simp [selectedPartitionWeight, unselectedPartitionWeight] at tailEquality ⊢ <;>
            omega

theorem selectedWeight_pathSelection (input : PartitionInput) (path : List Nat) :
    selectedPartitionWeight input (pathSelection input path) =
      ((List.range input.weights.length).map fun stage =>
        if path.getD stage 0 = stage then input.weights.getD stage 0 else 0).sum := by
  rw [selectedPartitionWeight_eq_indexed input.weights (pathSelection input path)
    (pathSelection_length input path)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro stage stageMember
  have stageBound := List.mem_range.mp stageMember
  rw [pathSelection_getD input path stageBound]
  by_cases selected : path.getD stage 0 = stage <;> simp [selected]

theorem unselectedWeight_pathSelection (input : PartitionInput) (path : List Nat) :
    unselectedPartitionWeight input (pathSelection input path) =
      ((List.range input.weights.length).map fun stage =>
        if path.getD stage 0 = stage then 0 else input.weights.getD stage 0).sum := by
  rw [unselectedPartitionWeight_eq_indexed input.weights (pathSelection input path)
    (pathSelection_length input path)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro stage stageMember
  have stageBound := List.mem_range.mp stageMember
  rw [pathSelection_getD input path stageBound]
  by_cases selected : path.getD stage 0 = stage <;> simp [selected]

theorem ladderCost_of_stageChoice (input : PartitionInput) {pathIndex stage : Nat}
    (stageBound : stage < stageCount input)
    (choice : pathIndex = stage ∨ pathIndex = stageCount input + stage) :
    (ladderCosts input).getD pathIndex 0 =
      1 + 2 * (if pathIndex = stage then input.weights.getD stage 0 else 0) := by
  rcases choice with rfl | second
  · rw [ladderCosts_getD_first input stageBound]
    simp
    omega
  · rw [second, ladderCosts_getD_second input stageBound]
    have different : stageCount input + stage ≠ stage := by
      have positive := stageCount_pos input
      omega
    rw [if_neg different]

theorem pathCost_eq_indexed (input : PartitionInput) (path : List Nat)
    (lengthEquality : path.length = stageCount input) :
    Presentation.TwoDisjointBoundedPaths.pathCost (ladderCosts input) path =
      ((List.range (stageCount input)).map fun stage =>
        (ladderCosts input).getD (path.getD stage 0) 0).sum := by
  have equality := congrArg
    (fun values : List Nat =>
      (values.map fun index => (ladderCosts input).getD index 0).sum)
    (range_map_getD path).symm
  simpa [Presentation.TwoDisjointBoundedPaths.pathCost, List.map_map,
    Function.comp, lengthEquality] using equality

theorem pathCost_eq_stageCount_add_two_mul_selected
    (input : PartitionInput) (path : List Nat)
    (chain : Presentation.TwoDisjointBoundedPaths.EdgeChain
      (ladderGraph input) 0 path (stageCount input)) :
    Presentation.TwoDisjointBoundedPaths.pathCost (ladderCosts input) path =
      stageCount input +
        2 * selectedPartitionWeight input (pathSelection input path) := by
  have shape := edgeChain_shape input chain (Nat.zero_le _)
  rw [pathCost_eq_indexed input path shape.1]
  have localEquality :
      ((List.range (stageCount input)).map fun stage =>
        (ladderCosts input).getD (path.getD stage 0) 0) =
      ((List.range (stageCount input)).map fun stage =>
        1 + 2 *
          (if path.getD stage 0 = stage then input.weights.getD stage 0 else 0)) := by
    apply List.map_congr_left
    intro stage stageMember
    have stageBound := List.mem_range.mp stageMember
    have choice := shape.2 stage (by simpa [shape.1])
    exact ladderCost_of_stageChoice input stageBound (by simpa using choice)
  rw [localEquality]
  have sumIdentity : ∀ stages : List Nat,
      (stages.map fun stage =>
        1 + 2 *
          (if path.getD stage 0 = stage then input.weights.getD stage 0 else 0)).sum =
        stages.length +
          2 * (stages.map fun stage =>
            if path.getD stage 0 = stage then input.weights.getD stage 0 else 0).sum := by
    intro stages
    induction stages with
    | nil => simp
    | cons stage stages inductionHypothesis =>
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        rw [inductionHypothesis]
        omega
  rw [sumIdentity, List.length_range]
  have finalWeight : input.weights.getD input.weights.length 0 = 0 := by
    exact List.getD_eq_default _ _ (Nat.le_refl _)
  have chosenStages :
      ((List.range (stageCount input)).map fun stage =>
        if path.getD stage 0 = stage then input.weights.getD stage 0 else 0).sum =
      selectedPartitionWeight input (pathSelection input path) := by
    rw [selectedWeight_pathSelection]
    simp [stageCount, List.range_succ, finalWeight]
  rw [chosenStages]

end PartitionToTwoDisjointBoundedPathsCore
end Domain
end ComplexityReduction
