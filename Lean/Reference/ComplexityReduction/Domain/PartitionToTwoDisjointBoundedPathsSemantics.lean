/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Domain.PartitionToTwoDisjointBoundedPathsCore

/-!
Witness construction and reverse decoding for the two-copy Partition ladder.
-/

namespace ComplexityReduction
namespace Domain
namespace PartitionToTwoDisjointBoundedPathsCore

open ComplexityReduction.Combinatorics

/-- First path: choose the first copy on `true`, the second copy on `false`. -/
def leftPathFrom (copies offset : Nat) : List Bool → List Nat
  | [] => [offset]
  | bit :: bits =>
      (if bit then offset else copies + offset) ::
        leftPathFrom copies (offset + 1) bits

/-- Second path chooses the complementary copy at every source-weight stage. -/
def rightPathFrom (copies offset : Nat) : List Bool → List Nat
  | [] => [copies + offset]
  | bit :: bits =>
      (if bit then copies + offset else offset) ::
        rightPathFrom copies (offset + 1) bits

def leftPath (input : PartitionInput) (bits : List Bool) : List Nat :=
  leftPathFrom (stageCount input) 0 bits

def rightPath (input : PartitionInput) (bits : List Bool) : List Nat :=
  rightPathFrom (stageCount input) 0 bits

@[simp] theorem leftPathFrom_length (copies offset : Nat) (bits : List Bool) :
    (leftPathFrom copies offset bits).length = bits.length + 1 := by
  induction bits generalizing offset with
  | nil => simp [leftPathFrom]
  | cons bit bits inductionHypothesis =>
      simp [leftPathFrom, inductionHypothesis]

@[simp] theorem rightPathFrom_length (copies offset : Nat) (bits : List Bool) :
    (rightPathFrom copies offset bits).length = bits.length + 1 := by
  induction bits generalizing offset with
  | nil => simp [rightPathFrom]
  | cons bit bits inductionHypothesis =>
      simp [rightPathFrom, inductionHypothesis]

theorem leftPathFrom_getD (copies offset : Nat) (bits : List Bool) {index : Nat}
    (indexBound : index < bits.length) :
    (leftPathFrom copies offset bits).getD index 0 =
      if bits.getD index false then offset + index else copies + (offset + index) := by
  induction bits generalizing offset index with
  | nil => simp at indexBound
  | cons bit bits inductionHypothesis =>
      cases index with
      | zero => simp [leftPathFrom]
      | succ index =>
          have tailBound : index < bits.length := by simpa using indexBound
          simp only [leftPathFrom, List.getD_cons_succ, List.getD_cons_succ]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            inductionHypothesis (offset + 1) tailBound

theorem rightPathFrom_getD (copies offset : Nat) (bits : List Bool) {index : Nat}
    (indexBound : index < bits.length) :
    (rightPathFrom copies offset bits).getD index 0 =
      if bits.getD index false then copies + (offset + index) else offset + index := by
  induction bits generalizing offset index with
  | nil => simp at indexBound
  | cons bit bits inductionHypothesis =>
      cases index with
      | zero => simp [rightPathFrom]
      | succ index =>
          have tailBound : index < bits.length := by simpa using indexBound
          simp only [rightPathFrom, List.getD_cons_succ, List.getD_cons_succ]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            inductionHypothesis (offset + 1) tailBound

theorem leftPathFrom_getD_final (copies offset : Nat) (bits : List Bool) :
    (leftPathFrom copies offset bits).getD bits.length 0 = offset + bits.length := by
  induction bits generalizing offset with
  | nil => simp [leftPathFrom]
  | cons bit bits inductionHypothesis =>
      simp only [leftPathFrom, List.length_cons, List.getD_cons_succ]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (offset + 1)

theorem rightPathFrom_getD_final (copies offset : Nat) (bits : List Bool) :
    (rightPathFrom copies offset bits).getD bits.length 0 =
      copies + (offset + bits.length) := by
  induction bits generalizing offset with
  | nil => simp [rightPathFrom]
  | cons bit bits inductionHypothesis =>
      simp only [rightPathFrom, List.length_cons, List.getD_cons_succ]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (offset + 1)

theorem leftPathFrom_chain (input : PartitionInput) (bits : List Bool) (offset : Nat)
    (stageEquality : offset + bits.length = input.weights.length) :
    Presentation.TwoDisjointBoundedPaths.EdgeChain (ladderGraph input) offset
      (leftPathFrom (stageCount input) offset bits) (stageCount input) := by
  induction bits generalizing offset with
  | nil =>
      have offsetBound : offset < stageCount input := by
        simp [stageCount] at stageEquality ⊢
        omega
      simp only [leftPathFrom, Presentation.TwoDisjointBoundedPaths.EdgeChain]
      rw [ladderEdgeAt_first input offsetBound]
      simp [ladderGraph, stageEdge, stageCount] at stageEquality ⊢
      omega
  | cons bit bits inductionHypothesis =>
      have offsetBound : offset < stageCount input := by
        simp [stageCount] at stageEquality ⊢
        omega
      have tailEquality : offset + 1 + bits.length = input.weights.length := by
        simp at stageEquality
        omega
      have tailChain := inductionHypothesis (offset + 1) tailEquality
      cases bit
      · simp only [leftPathFrom, Bool.false_eq_true, ↓reduceIte,
          Presentation.TwoDisjointBoundedPaths.EdgeChain]
        rw [ladderEdgeAt_second input offsetBound]
        refine ⟨?_, by simp [stageEdge], ?_⟩
        · simp [ladderGraph]
          omega
        · simpa [stageEdge] using tailChain
      · simp only [leftPathFrom, ↓reduceIte,
          Presentation.TwoDisjointBoundedPaths.EdgeChain]
        rw [ladderEdgeAt_first input offsetBound]
        refine ⟨?_, by simp [stageEdge], ?_⟩
        · simp [ladderGraph]
          omega
        · simpa [stageEdge] using tailChain

theorem rightPathFrom_chain (input : PartitionInput) (bits : List Bool) (offset : Nat)
    (stageEquality : offset + bits.length = input.weights.length) :
    Presentation.TwoDisjointBoundedPaths.EdgeChain (ladderGraph input) offset
      (rightPathFrom (stageCount input) offset bits) (stageCount input) := by
  induction bits generalizing offset with
  | nil =>
      have offsetBound : offset < stageCount input := by
        simp [stageCount] at stageEquality ⊢
        omega
      simp only [rightPathFrom, Presentation.TwoDisjointBoundedPaths.EdgeChain]
      rw [ladderEdgeAt_second input offsetBound]
      refine ⟨?_, by simp [stageEdge], ?_⟩
      · simp [ladderGraph]
        omega
      · simp [stageEdge, stageCount] at stageEquality ⊢
        omega
  | cons bit bits inductionHypothesis =>
      have offsetBound : offset < stageCount input := by
        simp [stageCount] at stageEquality ⊢
        omega
      have tailEquality : offset + 1 + bits.length = input.weights.length := by
        simp at stageEquality
        omega
      have tailChain := inductionHypothesis (offset + 1) tailEquality
      cases bit
      · simp only [rightPathFrom, Bool.false_eq_true, ↓reduceIte,
          Presentation.TwoDisjointBoundedPaths.EdgeChain]
        rw [ladderEdgeAt_first input offsetBound]
        refine ⟨?_, by simp [stageEdge], ?_⟩
        · simp [ladderGraph]
          omega
        · simpa [stageEdge] using tailChain
      · simp only [rightPathFrom, ↓reduceIte,
          Presentation.TwoDisjointBoundedPaths.EdgeChain]
        rw [ladderEdgeAt_second input offsetBound]
        refine ⟨?_, by simp [stageEdge], ?_⟩
        · simp [ladderGraph]
          omega
        · simpa [stageEdge] using tailChain

theorem copyIndex_stage_eq {copies firstStage secondStage firstIndex secondIndex : Nat}
    (copiesPositive : 0 < copies)
    (firstBound : firstStage < copies) (secondBound : secondStage < copies)
    (firstChoice : firstIndex = firstStage ∨ firstIndex = copies + firstStage)
    (secondChoice : secondIndex = secondStage ∨ secondIndex = copies + secondStage)
    (indexEquality : firstIndex = secondIndex) :
    firstStage = secondStage := by
  rcases firstChoice with rfl | rfl <;>
    rcases secondChoice with rfl | rfl <;> omega

theorem leftPathFrom_getD_choice (copies offset : Nat) (bits : List Bool) {index : Nat}
    (indexBound : index < (leftPathFrom copies offset bits).length) :
    (leftPathFrom copies offset bits).getD index 0 = offset + index ∨
      (leftPathFrom copies offset bits).getD index 0 = copies + (offset + index) := by
  by_cases beforeFinal : index < bits.length
  · rw [leftPathFrom_getD copies offset bits beforeFinal]
    cases bitValue : bits.getD index false <;> simp [bitValue]
  · have finalIndex : index = bits.length := by
      rw [leftPathFrom_length] at indexBound
      omega
    subst index
    exact Or.inl (leftPathFrom_getD_final copies offset bits)

theorem rightPathFrom_getD_choice (copies offset : Nat) (bits : List Bool) {index : Nat}
    (indexBound : index < (rightPathFrom copies offset bits).length) :
    (rightPathFrom copies offset bits).getD index 0 = offset + index ∨
      (rightPathFrom copies offset bits).getD index 0 = copies + (offset + index) := by
  by_cases beforeFinal : index < bits.length
  · rw [rightPathFrom_getD copies offset bits beforeFinal]
    cases bitValue : bits.getD index false <;> simp [bitValue]
  · have finalIndex : index = bits.length := by
      rw [rightPathFrom_length] at indexBound
      omega
    subst index
    exact Or.inr (rightPathFrom_getD_final copies offset bits)

theorem left_right_getD_ne (copies offset : Nat) (bits : List Bool) {index : Nat}
    (copiesPositive : 0 < copies)
    (indexBound : index < (leftPathFrom copies offset bits).length) :
    (leftPathFrom copies offset bits).getD index 0 ≠
      (rightPathFrom copies offset bits).getD index 0 := by
  by_cases beforeFinal : index < bits.length
  · rw [leftPathFrom_getD copies offset bits beforeFinal,
      rightPathFrom_getD copies offset bits beforeFinal]
    cases bitValue : bits.getD index false <;> simp [bitValue]
    all_goals omega
  · have finalIndex : index = bits.length := by
      rw [leftPathFrom_length] at indexBound
      omega
    subst index
    rw [leftPathFrom_getD_final, rightPathFrom_getD_final]
    omega

theorem constructedPaths_disjoint (copies offset : Nat) (bits : List Bool)
    (copiesPositive : 0 < copies)
    (stageBound : offset + bits.length < copies) :
    Presentation.TwoDisjointBoundedPaths.EdgeDisjoint
      (leftPathFrom copies offset bits) (rightPathFrom copies offset bits) := by
  intro value leftMember rightMember
  rcases List.mem_iff_getElem.mp leftMember with ⟨leftIndex, leftBound, leftValue⟩
  rcases List.mem_iff_getElem.mp rightMember with ⟨rightIndex, rightBound, rightValue⟩
  have leftGetD :
      (leftPathFrom copies offset bits).getD leftIndex 0 = value := by
    rw [List.getD_eq_getElem (l := leftPathFrom copies offset bits) (d := 0)
      (n := leftIndex) leftBound]
    exact leftValue
  have rightGetD :
      (rightPathFrom copies offset bits).getD rightIndex 0 = value := by
    rw [List.getD_eq_getElem (l := rightPathFrom copies offset bits) (d := 0)
      (n := rightIndex) rightBound]
    exact rightValue
  have leftStageBound : offset + leftIndex < copies := by
    rw [leftPathFrom_length] at leftBound
    omega
  have rightStageBound : offset + rightIndex < copies := by
    rw [rightPathFrom_length] at rightBound
    omega
  have stageEquality := copyIndex_stage_eq copiesPositive leftStageBound rightStageBound
    (leftPathFrom_getD_choice copies offset bits leftBound)
    (rightPathFrom_getD_choice copies offset bits rightBound)
    (leftGetD.trans rightGetD.symm)
  have indexEquality : leftIndex = rightIndex := by omega
  subst rightIndex
  exact (left_right_getD_ne copies offset bits copiesPositive leftBound)
    (leftGetD.trans rightGetD.symm)

theorem pathSelection_leftPath (input : PartitionInput) (bits : List Bool)
    (lengthEquality : bits.length = input.weights.length) :
    pathSelection input (leftPath input bits) = bits := by
  apply List.ext_getElem
  · simp [lengthEquality]
  · intro index leftBound rightBound
    have indexBound : index < bits.length := rightBound
    rw [← List.getD_eq_getElem (l := pathSelection input (leftPath input bits))
      (d := false) (n := index) leftBound]
    rw [← List.getD_eq_getElem (l := bits) (d := false) (n := index) rightBound]
    have sourceBound : index < input.weights.length := by omega
    rw [pathSelection_getD input (leftPath input bits) sourceBound]
    change decide
      ((leftPathFrom (stageCount input) 0 bits).getD index 0 = index) =
        bits.getD index false
    rw [leftPathFrom_getD (stageCount input) 0 bits indexBound]
    cases bitValue : bits.getD index false <;> simp [bitValue]
    have positive := stageCount_pos input
    all_goals omega

theorem pathSelection_rightPath (input : PartitionInput) (bits : List Bool)
    (lengthEquality : bits.length = input.weights.length) :
    pathSelection input (rightPath input bits) = bits.map Bool.not := by
  apply List.ext_getElem
  · simp [lengthEquality]
  · intro index leftBound rightBound
    have indexBound : index < bits.length := by simpa using rightBound
    rw [← List.getD_eq_getElem (l := pathSelection input (rightPath input bits))
      (d := false) (n := index) leftBound]
    have sourceBound : index < input.weights.length := by omega
    rw [pathSelection_getD input (rightPath input bits) sourceBound]
    change decide
      ((rightPathFrom (stageCount input) 0 bits).getD index 0 = index) = _
    rw [rightPathFrom_getD (stageCount input) 0 bits indexBound]
    simp only [List.getElem_map]
    rw [← List.getD_eq_getElem (l := bits) (d := false) (n := index) indexBound]
    cases bitValue : bits.getD index false <;> simp [bitValue]
    have positive := stageCount_pos input
    all_goals omega

theorem selectedPartitionWeight_map_not_eq_unselected
    (weights : List Nat) (bits : List Bool)
    (lengthEquality : bits.length = weights.length) :
    selectedPartitionWeight { weights := weights } (bits.map Bool.not) =
      unselectedPartitionWeight { weights := weights } bits := by
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
          change
            (if Bool.not bit then weight else 0) +
                selectedPartitionWeight { weights := weights } (bits.map Bool.not) =
              (if bit then 0 else weight) +
                unselectedPartitionWeight { weights := weights } bits
          rw [inductionHypothesis bits tailLength]
          cases bit <;> simp

theorem path_getD_ne_of_disjoint
    {left right : List Nat} (disjoint :
      Presentation.TwoDisjointBoundedPaths.EdgeDisjoint left right)
    {leftIndex rightIndex : Nat}
    (leftBound : leftIndex < left.length) (rightBound : rightIndex < right.length) :
    left.getD leftIndex 0 ≠ right.getD rightIndex 0 := by
  intro equality
  have leftMember : left.getD leftIndex 0 ∈ left := by
    rw [List.getD_eq_getElem (l := left) (d := 0) (n := leftIndex) leftBound]
    exact List.getElem_mem leftBound
  have rightMember : right.getD rightIndex 0 ∈ right := by
    rw [List.getD_eq_getElem (l := right) (d := 0) (n := rightIndex) rightBound]
    exact List.getElem_mem rightBound
  apply disjoint _ leftMember
  rw [equality]
  exact rightMember

theorem pathSelections_complement (input : PartitionInput) (left right : List Nat)
    (leftChain : Presentation.TwoDisjointBoundedPaths.EdgeChain
      (ladderGraph input) 0 left (stageCount input))
    (rightChain : Presentation.TwoDisjointBoundedPaths.EdgeChain
      (ladderGraph input) 0 right (stageCount input))
    (disjoint : Presentation.TwoDisjointBoundedPaths.EdgeDisjoint left right) :
    pathSelection input right = (pathSelection input left).map Bool.not := by
  have leftShape := edgeChain_shape input leftChain (Nat.zero_le _)
  have rightShape := edgeChain_shape input rightChain (Nat.zero_le _)
  apply List.ext_getElem
  · simp
  · intro stage leftBound rightBound
    have stageBound : stage < input.weights.length := by simpa using leftBound
    have ladderStageBound : stage < stageCount input := by
      simp [stageCount]
      omega
    rw [← List.getD_eq_getElem (l := pathSelection input right) (d := false)
      (n := stage) leftBound]
    rw [pathSelection_getD input right stageBound]
    simp only [List.getElem_map]
    rw [← List.getD_eq_getElem (l := pathSelection input left) (d := false)
      (n := stage) (by simpa using stageBound)]
    rw [pathSelection_getD input left stageBound]
    have leftChoice :
        left.getD stage 0 = stage ∨
          left.getD stage 0 = stageCount input + stage := by
      simpa using leftShape.2 stage (by simpa [leftShape.1])
    have rightChoice :
        right.getD stage 0 = stage ∨
          right.getD stage 0 = stageCount input + stage := by
      simpa using rightShape.2 stage (by simpa [rightShape.1])
    have different := path_getD_ne_of_disjoint disjoint
      (leftIndex := stage) (rightIndex := stage)
      (by simpa [leftShape.1] using ladderStageBound)
      (by simpa [rightShape.1] using ladderStageBound)
    rcases leftChoice with leftFirst | leftSecond <;>
      rcases rightChoice with rightFirst | rightSecond
    · exact False.elim (different (leftFirst.trans rightFirst.symm))
    · have rightNot : right.getD stage 0 ≠ stage := by
        rw [rightSecond]
        have positive := stageCount_pos input
        omega
      change decide (right.getD stage 0 = stage) =
        Bool.not (decide (left.getD stage 0 = stage))
      calc
        decide (right.getD stage 0 = stage) = false :=
          (Bool.decide_false_iff _).2 rightNot
        _ = Bool.not true := rfl
        _ = Bool.not (decide (left.getD stage 0 = stage)) := by
          rw [show decide (left.getD stage 0 = stage) = true from
            (Bool.decide_iff _).2 leftFirst]
    · have leftNot : left.getD stage 0 ≠ stage := by
        rw [leftSecond]
        have positive := stageCount_pos input
        omega
      change decide (right.getD stage 0 = stage) =
        Bool.not (decide (left.getD stage 0 = stage))
      calc
        decide (right.getD stage 0 = stage) = true :=
          (Bool.decide_iff _).2 rightFirst
        _ = Bool.not false := rfl
        _ = Bool.not (decide (left.getD stage 0 = stage)) := by
          rw [show decide (left.getD stage 0 = stage) = false from
            (Bool.decide_false_iff _).2 leftNot]
    · exact False.elim (different (leftSecond.trans rightSecond.symm))

/-- The two-copy ladder is yes exactly when the binary Partition source is yes. -/
theorem executableCorrect (input : PartitionInput) :
    Partition input ↔ Presentation.TwoDisjointBoundedPaths.IsYes (executable input) := by
  constructor
  · rintro ⟨bits, lengthEquality, balanced⟩
    rcases executable_fixedProperties input with
      ⟨directed, wellFormed, sourceBound, targetBound, terminalsDistinct,
        costLength, positiveCosts⟩
    let left := leftPath input bits
    let right := rightPath input bits
    have leftChain : Presentation.TwoDisjointBoundedPaths.EdgeChain
        (ladderGraph input) 0 left (stageCount input) := by
      simpa [left, leftPath] using
        leftPathFrom_chain input bits 0 (by simpa using lengthEquality)
    have rightChain : Presentation.TwoDisjointBoundedPaths.EdgeChain
        (ladderGraph input) 0 right (stageCount input) := by
      simpa [right, rightPath] using
        rightPathFrom_chain input bits 0 (by simpa using lengthEquality)
    have total := selected_add_unselected_eq_sum input.weights bits lengthEquality
    change selectedPartitionWeight input bits + unselectedPartitionWeight input bits =
      input.weights.sum at total
    change selectedPartitionWeight input bits = unselectedPartitionWeight input bits at balanced
    have twiceSelected :
        2 * selectedPartitionWeight input bits = input.weights.sum := by
      omega
    have twiceUnselected :
        2 * unselectedPartitionWeight input bits = input.weights.sum := by
      omega
    have leftSelection : pathSelection input left = bits := by
      simpa [left] using pathSelection_leftPath input bits lengthEquality
    have rightSelection : pathSelection input right = bits.map Bool.not := by
      simpa [right] using pathSelection_rightPath input bits lengthEquality
    refine ⟨directed, wellFormed, sourceBound, targetBound, terminalsDistinct,
      costLength, positiveCosts, left, right, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨edgeChain_nodup input leftChain, leftChain⟩
    · exact ⟨edgeChain_nodup input rightChain, rightChain⟩
    · rw [show (executable input).costs = ladderCosts input by rfl,
        show (executable input).bound = stageCount input + input.weights.sum by rfl,
        pathCost_eq_stageCount_add_two_mul_selected input left leftChain,
        leftSelection, twiceSelected]
    · rw [show (executable input).costs = ladderCosts input by rfl,
        show (executable input).bound = stageCount input + input.weights.sum by rfl,
        pathCost_eq_stageCount_add_two_mul_selected input right rightChain,
        rightSelection,
        selectedPartitionWeight_map_not_eq_unselected input.weights bits lengthEquality,
        twiceUnselected]
    · simpa [left, right, leftPath, rightPath, stageCount] using
        constructedPaths_disjoint (stageCount input) 0 bits (stageCount_pos input) (by
          simp [stageCount, lengthEquality])
  · rintro ⟨_directed, _wellFormed, _sourceBound, _targetBound, _terminalsDistinct,
      _costLength, _positiveCosts, left, right, leftPathProof, rightPathProof,
      leftCost, rightCost, disjoint⟩
    let bits := pathSelection input left
    have complement := pathSelections_complement input left right
      leftPathProof.2 rightPathProof.2 disjoint
    have total := selected_add_unselected_eq_sum input.weights bits
      (pathSelection_length input left)
    have leftFormula := pathCost_eq_stageCount_add_two_mul_selected
      input left leftPathProof.2
    have rightFormula := pathCost_eq_stageCount_add_two_mul_selected
      input right rightPathProof.2
    have leftBound :
        stageCount input + 2 * selectedPartitionWeight input bits ≤
          stageCount input + input.weights.sum := by
      change
        Presentation.TwoDisjointBoundedPaths.pathCost (ladderCosts input) left ≤
          stageCount input + input.weights.sum at leftCost
      rw [leftFormula] at leftCost
      simpa [bits] using leftCost
    have rightBound :
        stageCount input + 2 * unselectedPartitionWeight input bits ≤
          stageCount input + input.weights.sum := by
      change
        Presentation.TwoDisjointBoundedPaths.pathCost (ladderCosts input) right ≤
          stageCount input + input.weights.sum at rightCost
      rw [rightFormula, complement,
        selectedPartitionWeight_map_not_eq_unselected input.weights
          (pathSelection input left) (pathSelection_length input left)] at rightCost
      simpa [bits, executable] using rightCost
    change selectedPartitionWeight input bits + unselectedPartitionWeight input bits =
      input.weights.sum at total
    refine ⟨bits, pathSelection_length input left, ?_⟩
    omega

end PartitionToTwoDisjointBoundedPathsCore
end Domain
end ComplexityReduction
