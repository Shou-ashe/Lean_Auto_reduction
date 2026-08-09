/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-!
P15c arithmetic target: Knapsack to Partition.
-/

namespace ComplexityReduction
namespace Karp21
namespace Partition

open ComplexityReduction.Combinatorics

/-- All Boolean lists of a fixed length. -/
def boolLists : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      (boolLists n).map (fun xs => false :: xs) ++
        (boolLists n).map (fun xs => true :: xs)

theorem mem_boolLists_length {n : Nat} {xs : List Bool}
    (h : xs ∈ boolLists n) :
    xs.length = n := by
  induction n generalizing xs with
  | zero =>
      simpa [boolLists] using h
  | succ n ih =>
      simp [boolLists] at h
      rcases h with ⟨tail, hTail, rfl⟩ | ⟨tail, hTail, rfl⟩
      · simp [ih hTail]
      · simp [ih hTail]

theorem mem_boolLists_of_length {n : Nat} {xs : List Bool}
    (h : xs.length = n) :
    xs ∈ boolLists n := by
  induction n generalizing xs with
  | zero =>
      have hnil : xs = [] := by
        cases xs with
        | nil => rfl
        | cons b bs => simp at h
      simp [boolLists, hnil]
  | succ n ih =>
      cases xs with
      | nil =>
          simp at h
      | cons b tail =>
          have hTail : tail.length = n := by simpa using h
          cases b <;> simp [boolLists, ih hTail]

/-- Knapsack witnesses enumerated as finite Boolean lists. -/
def satisfyingSelections (I : KnapsackInput) : List (List Bool) := by
  classical
  exact (boolLists I.items.length).filter fun selected =>
    decide
      (selectedWeight I selected ≤ I.capacity ∧
        I.targetValue ≤ selectedValue I selected)

theorem mem_satisfyingSelections_iff (I : KnapsackInput) (selected : List Bool) :
    selected ∈ satisfyingSelections I ↔
      selected ∈ boolLists I.items.length ∧
        selectedWeight I selected ≤ I.capacity ∧
          I.targetValue ≤ selectedValue I selected := by
  classical
  simp [satisfyingSelections]

theorem knapsack_iff_satisfyingSelections_pos (I : KnapsackInput) :
    Knapsack I ↔ 0 < (satisfyingSelections I).length := by
  constructor
  · rintro ⟨selected, hLen, hWeight, hValue⟩
    have hMem : selected ∈ satisfyingSelections I :=
      (mem_satisfyingSelections_iff I selected).2
        ⟨mem_boolLists_of_length hLen, hWeight, hValue⟩
    exact List.length_pos_of_mem hMem
  · intro hPos
    cases hList : satisfyingSelections I with
    | nil =>
        simp [hList] at hPos
    | cons selected rest =>
        have hMem : selected ∈ satisfyingSelections I := by
          simp [hList]
        rcases (mem_satisfyingSelections_iff I selected).1 hMem with
          ⟨hBool, hWeight, hValue⟩
        exact ⟨selected, mem_boolLists_length hBool, hWeight, hValue⟩

/-- A small guard equal to `1` at `m = 0` and `0` for positive `m`. -/
def zeroGuard (m : Nat) : Nat :=
  1 / (m + 1)

/-- Partition family that is satisfiable exactly when `m > 0`. -/
def nonemptyPartitionInput (m : Nat) : PartitionInput :=
  { weights := [m, 1, m + 1 + zeroGuard m] }

theorem nonemptyPartitionInput_zero_not :
    ¬ Partition (nonemptyPartitionInput 0) := by
  rintro ⟨selected, hLen, hEq⟩
  cases selected with
  | nil =>
      simp [nonemptyPartitionInput] at hLen
  | cons b₁ rest =>
      cases rest with
      | nil =>
          simp [nonemptyPartitionInput] at hLen
      | cons b₂ rest₂ =>
          cases rest₂ with
          | nil =>
              cases b₁ <;> cases b₂ <;>
                simp [nonemptyPartitionInput, selectedPartitionWeight,
                  unselectedPartitionWeight, zeroGuard] at hEq
          | cons b₃ rest₃ =>
              have hRest : rest₃ = [] := by
                simpa [nonemptyPartitionInput] using hLen
              subst rest₃
              cases b₁ <;> cases b₂ <;> cases b₃ <;>
                simp [nonemptyPartitionInput, selectedPartitionWeight,
                  unselectedPartitionWeight, zeroGuard] at hEq

theorem nonemptyPartitionInput_succ (k : Nat) :
    Partition (nonemptyPartitionInput (k + 1)) := by
  have hGuard : zeroGuard (k + 1) = 0 := by
    unfold zeroGuard
    exact Nat.div_eq_of_lt (by omega)
  refine ⟨[true, true, false], ?_, ?_⟩
  · simp [nonemptyPartitionInput]
  · simp [nonemptyPartitionInput, selectedPartitionWeight, unselectedPartitionWeight, hGuard]

theorem nonemptyPartitionInput_correct (m : Nat) :
    Partition (nonemptyPartitionInput m) ↔ 0 < m := by
  constructor
  · intro h
    cases m with
    | zero =>
        exact (nonemptyPartitionInput_zero_not h).elim
    | succ m =>
        omega
  · intro h
    cases m with
    | zero =>
        omega
    | succ m =>
        exact nonemptyPartitionInput_succ m

/-- P15c syntax map from Knapsack to Partition. -/
def map (I : KnapsackInput) : PartitionInput :=
  nonemptyPartitionInput (satisfyingSelections I).length

theorem map_correct (I : KnapsackInput) :
    knapsackKarpDecisionProblem.isYes I ↔ Partition (map I) := by
  change Combinatorics.Knapsack I ↔ Partition (map I)
  rw [knapsack_iff_satisfyingSelections_pos]
  exact (nonemptyPartitionInput_correct (satisfyingSelections I).length).symm

/-! ### Textbook-style balancing route via an exact subset-sum view -/

/-- Sum of selected weights, written recursively for local balancing proofs. -/
def chosenSum : List Nat → List Bool → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | w :: ws, b :: bs => (if b then w else 0) + chosenSum ws bs

/-- Sum of unselected weights, written recursively for local balancing proofs. -/
def rejectedSum : List Nat → List Bool → Nat
  | [], _ => 0
  | _ :: _, [] => 0
  | w :: ws, b :: bs => (if b then 0 else w) + rejectedSum ws bs

theorem chosenSum_eq_selectedPartitionWeight (weights : List Nat) (selected : List Bool) :
    chosenSum weights selected =
      selectedPartitionWeight { weights := weights } selected := by
  induction weights generalizing selected with
  | nil =>
      cases selected <;> simp [chosenSum, selectedPartitionWeight]
  | cons w ws ih =>
      cases selected <;> simp [chosenSum, selectedPartitionWeight, ih]

theorem rejectedSum_eq_unselectedPartitionWeight (weights : List Nat) (selected : List Bool) :
    rejectedSum weights selected =
      unselectedPartitionWeight { weights := weights } selected := by
  induction weights generalizing selected with
  | nil =>
      cases selected <;> simp [rejectedSum, unselectedPartitionWeight]
  | cons w ws ih =>
      cases selected <;> simp [rejectedSum, unselectedPartitionWeight, ih]

theorem chosenSum_append {xs ys : List Nat} {bits rest : List Bool}
    (hLen : bits.length = xs.length) :
    chosenSum (xs ++ ys) (bits ++ rest) =
      chosenSum xs bits + chosenSum ys rest := by
  induction xs generalizing bits with
  | nil =>
      cases bits <;> simp [chosenSum] at hLen ⊢
  | cons x xs ih =>
      cases bits with
      | nil =>
          simp at hLen
      | cons b bits =>
          simp at hLen
          cases b <;> simp [chosenSum, ih hLen, Nat.add_assoc]

theorem rejectedSum_append {xs ys : List Nat} {bits rest : List Bool}
    (hLen : bits.length = xs.length) :
    rejectedSum (xs ++ ys) (bits ++ rest) =
      rejectedSum xs bits + rejectedSum ys rest := by
  induction xs generalizing bits with
  | nil =>
      cases bits <;> simp [rejectedSum] at hLen ⊢
  | cons x xs ih =>
      cases bits with
      | nil =>
          simp at hLen
      | cons b bits =>
          simp at hLen
          cases b <;> simp [rejectedSum, ih hLen, Nat.add_assoc]

theorem chosen_add_rejected_eq_sum {weights : List Nat} {selected : List Bool}
    (hLen : selected.length = weights.length) :
    chosenSum weights selected + rejectedSum weights selected = weights.sum := by
  induction weights generalizing selected with
  | nil =>
      cases selected <;> simp [chosenSum, rejectedSum] at hLen ⊢
  | cons w ws ih =>
      cases selected with
      | nil =>
          simp at hLen
      | cons b bs =>
          simp at hLen
          have hTail := ih hLen
          cases b <;>
            simp [chosenSum, rejectedSum, hTail, Nat.add_assoc, Nat.add_left_comm]

theorem chosenSum_le_sum (weights : List Nat) (selected : List Bool) :
    chosenSum weights selected ≤ weights.sum := by
  induction weights generalizing selected with
  | nil =>
      simp [chosenSum]
  | cons w ws ih =>
      cases selected with
      | nil =>
          simp [chosenSum]
      | cons b bs =>
          cases b
          ·
            exact (by
              simpa [chosenSum] using (ih bs).trans (Nat.le_add_left ws.sum w))
          · simpa [chosenSum] using Nat.add_le_add_left (ih bs) w

/-- Number of true bits in a selected-list segment. -/
def trueCount : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + trueCount bs

theorem trueCount_le_length (bits : List Bool) :
    trueCount bits ≤ bits.length := by
  induction bits with
  | nil =>
      simp [trueCount]
  | cons b bs ih =>
      cases b
      · exact (by simpa [trueCount] using ih.trans (Nat.le_succ bs.length))
      · exact (by simpa [trueCount, Nat.add_comm] using Nat.succ_le_succ ih)

/-- Select the first `k` positions of a unary slack block of length `n`. -/
def prefixSelector (n k : Nat) : List Bool :=
  List.replicate k true ++ List.replicate (n - k) false

theorem length_prefixSelector {n k : Nat} (h : k ≤ n) :
    (prefixSelector n k).length = n := by
  unfold prefixSelector
  simp [h]

theorem trueCount_replicate_true (n : Nat) :
    trueCount (List.replicate n true) = n := by
  induction n with
  | zero =>
      simp [trueCount]
  | succ n ih =>
      simp [List.replicate, trueCount, ih]
      omega

theorem trueCount_replicate_false (n : Nat) :
    trueCount (List.replicate n false) = 0 := by
  induction n with
  | zero =>
      simp [trueCount]
  | succ n ih =>
      simp [List.replicate, trueCount, ih]

theorem trueCount_append (xs ys : List Bool) :
    trueCount (xs ++ ys) = trueCount xs + trueCount ys := by
  induction xs with
  | nil =>
      simp [trueCount]
  | cons b xs ih =>
      cases b <;> simp [trueCount, ih, Nat.add_assoc]

theorem trueCount_prefixSelector {n k : Nat} (_h : k ≤ n) :
    trueCount (prefixSelector n k) = k := by
  unfold prefixSelector
  rw [trueCount_append, trueCount_replicate_true, trueCount_replicate_false]
  simp

theorem chosenSum_replicate_of_length (a n : Nat) {bits : List Bool}
    (hLen : bits.length = n) :
    chosenSum (List.replicate n a) bits = a * trueCount bits := by
  induction n generalizing bits with
  | zero =>
      have hnil : bits = [] := by
        cases bits with
        | nil => rfl
        | cons b bs => simp at hLen
      simp [hnil, chosenSum, trueCount]
  | succ n ih =>
      cases bits with
      | nil =>
          simp at hLen
      | cons b bs =>
          simp at hLen
          cases b <;>
            simp [List.replicate, chosenSum, trueCount, ih hLen, Nat.mul_add]

/-- Weight total of the item list. -/
def itemWeightTotal (items : List (Nat × Nat)) : Nat :=
  (items.map Prod.fst).sum

/-- Value total of the item list. -/
def itemValueTotal (items : List (Nat × Nat)) : Nat :=
  (items.map Prod.snd).sum

/-- Auxiliary input sharing the item list, for reusing the generic selected sum definitions. -/
def itemOnlyKnapsackInput (items : List (Nat × Nat)) : KnapsackInput :=
  { items := items, capacity := 0, targetValue := 0 }

theorem selectedWeight_itemOnly (I : KnapsackInput) (bits : List Bool) :
    selectedWeight (itemOnlyKnapsackInput I.items) bits = selectedWeight I bits := by
  simp [selectedWeight, itemOnlyKnapsackInput]

theorem selectedValue_itemOnly (I : KnapsackInput) (bits : List Bool) :
    selectedValue (itemOnlyKnapsackInput I.items) bits = selectedValue I bits := by
  simp [selectedValue, itemOnlyKnapsackInput]

theorem selectedWeight_le_itemWeightTotal (items : List (Nat × Nat)) (bits : List Bool) :
    selectedWeight (itemOnlyKnapsackInput items) bits ≤ itemWeightTotal items := by
  induction items generalizing bits with
  | nil =>
      simp [selectedWeight, itemOnlyKnapsackInput, itemWeightTotal]
  | cons item items ih =>
      cases item with
      | mk w v =>
          cases bits with
          | nil =>
              simp [selectedWeight, itemOnlyKnapsackInput, itemWeightTotal]
          | cons b bits =>
              cases b
              ·
                exact (by
                  simpa [selectedWeight, itemOnlyKnapsackInput, itemWeightTotal] using
                    (ih bits).trans (Nat.le_add_left (itemWeightTotal items) w))
              ·
                simpa [selectedWeight, itemOnlyKnapsackInput, itemWeightTotal] using
                  Nat.add_le_add_left (ih bits) w

theorem selectedValue_le_itemValueTotal (items : List (Nat × Nat)) (bits : List Bool) :
    selectedValue (itemOnlyKnapsackInput items) bits ≤ itemValueTotal items := by
  induction items generalizing bits with
  | nil =>
      simp [selectedValue, itemOnlyKnapsackInput, itemValueTotal]
  | cons item items ih =>
      cases item with
      | mk w v =>
          cases bits with
          | nil =>
              simp [selectedValue, itemOnlyKnapsackInput, itemValueTotal]
          | cons b bits =>
              cases b
              ·
                exact (by
                  simpa [selectedValue, itemOnlyKnapsackInput, itemValueTotal] using
                    (ih bits).trans (Nat.le_add_left (itemValueTotal items) v))
              ·
                simpa [selectedValue, itemOnlyKnapsackInput, itemValueTotal] using
                  Nat.add_le_add_left (ih bits) v

theorem selectedValue_le_itemValueTotal_input (I : KnapsackInput) (bits : List Bool) :
    selectedValue I bits ≤ itemValueTotal I.items := by
  simpa [selectedValue_itemOnly] using selectedValue_le_itemValueTotal I.items bits

/-- Encode one Knapsack item into two no-carry coordinates. -/
def encodedItem (base : Nat) (item : Nat × Nat) : Nat :=
  base * item.1 + item.2

/-- Encoded original items for the exact-sum view. -/
def encodedItems (base : Nat) (items : List (Nat × Nat)) : List Nat :=
  items.map (encodedItem base)

theorem chosenSum_encodedItems (base : Nat) (items : List (Nat × Nat))
    (bits : List Bool) :
    chosenSum (encodedItems base items) bits =
      base * selectedWeight (itemOnlyKnapsackInput items) bits +
        selectedValue (itemOnlyKnapsackInput items) bits := by
  induction items generalizing bits with
  | nil =>
      cases bits <;> simp [encodedItems, chosenSum, selectedWeight, selectedValue,
        itemOnlyKnapsackInput]
  | cons item items ih =>
      cases bits with
      | nil =>
          cases item
          simp [encodedItems, chosenSum, selectedWeight, selectedValue, itemOnlyKnapsackInput]
      | cons b bits =>
          cases item with
          | mk w v =>
          cases b
          ·
            simpa [encodedItems, encodedItem, chosenSum, selectedWeight, selectedValue,
              itemOnlyKnapsackInput] using ih bits
          ·
            have hTail := ih bits
            simpa [encodedItems, encodedItem, chosenSum, selectedWeight, selectedValue,
              itemOnlyKnapsackInput, Nat.mul_add, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hTail

/-- A local exact subset-sum predicate used only to structure the Partition proof. -/
def SubsetSum (weights : List Nat) (target : Nat) : Prop :=
  ∃ selected : List Bool, selected.length = weights.length ∧ chosenSum weights selected = target

/-- Low-coordinate target used to enforce the Knapsack value lower bound. -/
def valueTargetLevel (I : KnapsackInput) : Nat :=
  max (itemValueTotal I.items) I.targetValue

/-- Base for the two-coordinate no-carry exact-sum encoding. -/
def partitionTextbookBase (I : KnapsackInput) : Nat :=
  2 * valueTargetLevel I + 1

/-- Value slack budget: selected value plus slack must reach `valueTargetLevel`. -/
def valueSlackBudget (I : KnapsackInput) : Nat :=
  valueTargetLevel I - I.targetValue

/-- Exact-sum weights for the Knapsack instance before the final Partition wrapper. -/
def knapsackSubsetWeights (I : KnapsackInput) : List Nat :=
  encodedItems (partitionTextbookBase I) I.items ++
    List.replicate I.capacity (partitionTextbookBase I) ++
      List.replicate (valueSlackBudget I) 1

/-- Exact-sum target: capacity in the high coordinate and target level in the low coordinate. -/
def knapsackSubsetTarget (I : KnapsackInput) : Nat :=
  partitionTextbookBase I * I.capacity + valueTargetLevel I

/-- Final Partition weights obtained from an exact subset-sum instance. -/
def subsetToPartitionWeights (weights : List Nat) (target : Nat) : List Nat :=
  weights ++ [weights.sum, 2 * target]

/-- P15n syntax-only Partition map. -/
def textbookMap (I : KnapsackInput) : PartitionInput :=
  { weights := subsetToPartitionWeights (knapsackSubsetWeights I) (knapsackSubsetTarget I) }

def subsetItemBits (I : KnapsackInput) (bits : List Bool) : List Bool :=
  bits.take I.items.length

def subsetWeightSlackBits (I : KnapsackInput) (bits : List Bool) : List Bool :=
  (bits.drop I.items.length).take I.capacity

def subsetValueSlackBits (I : KnapsackInput) (bits : List Bool) : List Bool :=
  (bits.drop I.items.length).drop I.capacity

/-- Boolean complement of a selected-list segment. -/
def complementBits (bits : List Bool) : List Bool :=
  bits.map not

theorem length_complementBits (bits : List Bool) :
    (complementBits bits).length = bits.length := by
  simp [complementBits]

theorem chosenSum_complementBits (weights : List Nat) (bits : List Bool) :
    chosenSum weights (complementBits bits) = rejectedSum weights bits := by
  induction weights generalizing bits with
  | nil =>
      cases bits <;> simp [chosenSum, rejectedSum]
  | cons w ws ih =>
      cases bits with
      | nil =>
          simp [chosenSum, rejectedSum, complementBits]
      | cons b bs =>
          cases b <;> simpa [chosenSum, rejectedSum, complementBits] using ih bs

theorem chosenSum_allFalse (weights : List Nat) :
    chosenSum weights (List.replicate weights.length false) = 0 := by
  induction weights with
  | nil =>
      simp [chosenSum]
  | cons w ws ih =>
      simp [List.replicate, chosenSum, ih]

theorem subsetToPartition_correct (weights : List Nat) (target : Nat) :
    SubsetSum weights target ↔
      Partition { weights := subsetToPartitionWeights weights target } := by
  constructor
  · rintro ⟨selected, hLen, hSum⟩
    refine ⟨selected ++ [true, false], by simp [subsetToPartitionWeights, hLen], ?_⟩
    rw [← chosenSum_eq_selectedPartitionWeight, ← rejectedSum_eq_unselectedPartitionWeight]
    have hTotal := chosen_add_rejected_eq_sum hLen
    simp [subsetToPartitionWeights, chosenSum_append hLen, rejectedSum_append hLen,
      chosenSum, rejectedSum, hSum]
    omega
  · rintro ⟨selected, hLen, hEq⟩
    let core := selected.take weights.length
    let rest := selected.drop weights.length
    have hCoreLen : core.length = weights.length := by
      have hTake : weights.length ≤ selected.length := by
        simp [subsetToPartitionWeights] at hLen
        omega
      simp [core, hTake]
    have hRestLen : rest.length = 2 := by
      simp [rest, subsetToPartitionWeights] at hLen ⊢
      omega
    have hSplit : selected = core ++ rest := by
      simp [core, rest]
    rw [hSplit] at hEq
    rw [← chosenSum_eq_selectedPartitionWeight, ← rejectedSum_eq_unselectedPartitionWeight] at hEq
    have hTotal := chosen_add_rejected_eq_sum hCoreLen
    cases hRestCase : rest with
    | nil =>
        simp [hRestCase] at hRestLen
    | cons b₁ restTail =>
        cases hTailCase : restTail with
        | nil =>
            simp [hRestCase, hTailCase] at hRestLen
        | cons b₂ restExtra =>
            have hRestExtra : restExtra = [] := by
              have hRestExtraLen : restExtra.length = 0 := by
                simpa [hRestCase, hTailCase] using hRestLen
              exact List.eq_nil_of_length_eq_zero hRestExtraLen
            subst restExtra
            cases b₁ <;> cases b₂
            · refine ⟨complementBits core, by simp [length_complementBits, hCoreLen], ?_⟩
              have hEq' :
                  chosenSum weights core =
                    rejectedSum weights core + (weights.sum + 2 * target) := by
                simpa [subsetToPartitionWeights, chosenSum_append hCoreLen,
                  rejectedSum_append hCoreLen, hRestCase, hTailCase, chosenSum,
                  rejectedSum] using hEq
              rw [chosenSum_complementBits]
              omega
            · refine ⟨complementBits core, by simp [length_complementBits, hCoreLen], ?_⟩
              have hEq' :
                  chosenSum weights core + 2 * target =
                    rejectedSum weights core + weights.sum := by
                simpa [subsetToPartitionWeights, chosenSum_append hCoreLen,
                  rejectedSum_append hCoreLen, hRestCase, hTailCase, chosenSum,
                  rejectedSum] using hEq
              rw [chosenSum_complementBits]
              omega
            · refine ⟨core, hCoreLen, ?_⟩
              have hEq' :
                  chosenSum weights core + weights.sum =
                    rejectedSum weights core + 2 * target := by
                simpa [subsetToPartitionWeights, chosenSum_append hCoreLen,
                rejectedSum_append hCoreLen, hRestCase, hTailCase, chosenSum,
                  rejectedSum] using hEq
              omega
            · refine ⟨core, hCoreLen, ?_⟩
              have hEq' :
                  chosenSum weights core + (weights.sum + 2 * target) =
                    rejectedSum weights core := by
                simpa [subsetToPartitionWeights, chosenSum_append hCoreLen,
                  rejectedSum_append hCoreLen, hRestCase, hTailCase, chosenSum,
                  rejectedSum] using hEq
              omega

theorem partitionTextbookBase_pos (I : KnapsackInput) :
    0 < partitionTextbookBase I := by
  unfold partitionTextbookBase
  omega

theorem itemValueTotal_le_valueTargetLevel (I : KnapsackInput) :
    itemValueTotal I.items ≤ valueTargetLevel I := by
  exact Nat.le_max_left _ _

theorem targetValue_le_valueTargetLevel (I : KnapsackInput) :
    I.targetValue ≤ valueTargetLevel I := by
  exact Nat.le_max_right _ _

theorem noCarry_pair_eq {base high targetHigh low targetLow : Nat}
    (hBase : 0 < base) (hLow : low < base) (hTargetLow : targetLow < base)
    (hEq : base * high + low = base * targetHigh + targetLow) :
    low = targetLow ∧ high = targetHigh := by
  have hLowEq : low = targetLow := by
    have hmod := congrArg (fun n => n % base) hEq
    change (base * high + low) % base =
      (base * targetHigh + targetLow) % base at hmod
    rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add] at hmod
    simpa [Nat.mod_eq_of_lt hLow, Nat.mod_eq_of_lt hTargetLow] using hmod
  have hHighEq : high = targetHigh := by
    rw [hLowEq] at hEq
    exact Nat.eq_of_mul_eq_mul_left hBase (Nat.add_right_cancel hEq)
  exact ⟨hLowEq, hHighEq⟩

theorem chosenSum_knapsackSubsetWeights_eq (I : KnapsackInput) {bits : List Bool}
    (hLen : bits.length = (knapsackSubsetWeights I).length) :
    chosenSum (knapsackSubsetWeights I) bits =
      partitionTextbookBase I *
          (selectedWeight I (subsetItemBits I bits) +
            trueCount (subsetWeightSlackBits I bits)) +
        (selectedValue I (subsetItemBits I bits) +
          trueCount (subsetValueSlackBits I bits)) := by
  let itemBits := subsetItemBits I bits
  let rest := bits.drop I.items.length
  let weightBits := subsetWeightSlackBits I bits
  let valueBits := subsetValueSlackBits I bits
  have hBitsLen :
      bits.length = I.items.length + I.capacity + valueSlackBudget I := by
    simpa [knapsackSubsetWeights, encodedItems, Nat.add_assoc] using hLen
  change
    chosenSum (knapsackSubsetWeights I) bits =
      partitionTextbookBase I *
          (selectedWeight I itemBits + trueCount weightBits) +
        (selectedValue I itemBits + trueCount valueBits)
  have hItemLen : itemBits.length = I.items.length := by
    have hTake : I.items.length ≤ bits.length := by
      omega
    simp [itemBits, subsetItemBits, hTake]
  have hRestLen : rest.length = I.capacity + valueSlackBudget I := by
    simp [rest, knapsackSubsetWeights, encodedItems] at hLen ⊢
    omega
  have hDropLen :
      (bits.drop I.items.length).length = I.capacity + valueSlackBudget I := by
    simpa [rest] using hRestLen
  have hWeightLen : weightBits.length = I.capacity := by
    simp [weightBits, subsetWeightSlackBits, hDropLen]
  have hValueLen : valueBits.length = valueSlackBudget I := by
    simp [valueBits, subsetValueSlackBits]
    omega
  have hRestSplit : rest = weightBits ++ valueBits := by
    simp [weightBits, valueBits, subsetWeightSlackBits, subsetValueSlackBits, rest]
  have hSplit : bits = itemBits ++ (weightBits ++ valueBits) := by
    calc
      bits = itemBits ++ rest := by
        simp [itemBits, rest, subsetItemBits]
      _ = itemBits ++ (weightBits ++ valueBits) := by rw [hRestSplit]
  rw [hSplit]
  simp [knapsackSubsetWeights, itemBits, weightBits, valueBits]
  have hItemLenEncoded :
      itemBits.length = (encodedItems (partitionTextbookBase I) I.items).length := by
    simpa [encodedItems] using hItemLen
  rw [chosenSum_append hItemLenEncoded]
  have hWeightLenRep :
      weightBits.length = (List.replicate I.capacity (partitionTextbookBase I)).length := by
    simpa using hWeightLen
  rw [chosenSum_append hWeightLenRep]
  rw [chosenSum_encodedItems]
  rw [chosenSum_replicate_of_length (partitionTextbookBase I) I.capacity hWeightLen]
  rw [chosenSum_replicate_of_length 1 (valueSlackBudget I) hValueLen]
  have hItemBitsDef : subsetItemBits I bits = itemBits := rfl
  have hWeightBitsDef : subsetWeightSlackBits I bits = weightBits := rfl
  have hValueBitsDef : subsetValueSlackBits I bits = valueBits := rfl
  simp [hItemBitsDef, hWeightBitsDef, hValueBitsDef, selectedWeight, selectedValue,
    itemOnlyKnapsackInput, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem knapsack_subsetSum_correct (I : KnapsackInput) :
    Combinatorics.Knapsack I ↔
      SubsetSum (knapsackSubsetWeights I) (knapsackSubsetTarget I) := by
  constructor
  · rintro ⟨selected, hSelectedLen, hWeight, hValue⟩
    let weightSlack := I.capacity - selectedWeight I selected
    let valueSlack := valueTargetLevel I - selectedValue I selected
    have hWeightSlackLe : weightSlack ≤ I.capacity := by
      omega
    have hSelectedValueLeLevel : selectedValue I selected ≤ valueTargetLevel I := by
      exact (selectedValue_le_itemValueTotal_input I selected).trans
        (itemValueTotal_le_valueTargetLevel I)
    have hValueSlackLe : valueSlack ≤ valueSlackBudget I := by
      simp [valueSlack, valueSlackBudget]
      omega
    let bits :=
      selected ++ prefixSelector I.capacity weightSlack ++
        prefixSelector (valueSlackBudget I) valueSlack
    refine ⟨bits, ?_, ?_⟩
    · simp [bits, knapsackSubsetWeights, encodedItems, hSelectedLen,
        length_prefixSelector hWeightSlackLe, length_prefixSelector hValueSlackLe]
    · unfold bits
      rw [knapsackSubsetWeights]
      rw [List.append_assoc (encodedItems (partitionTextbookBase I) I.items)
        (List.replicate I.capacity (partitionTextbookBase I))
        (List.replicate (valueSlackBudget I) 1)]
      rw [List.append_assoc selected (prefixSelector I.capacity weightSlack)
        (prefixSelector (valueSlackBudget I) valueSlack)]
      have hSelectedLenEncoded :
          selected.length = (encodedItems (partitionTextbookBase I) I.items).length := by
        simpa [encodedItems] using hSelectedLen
      rw [chosenSum_append hSelectedLenEncoded]
      have hWeightPrefixLen :
          (prefixSelector I.capacity weightSlack).length =
            (List.replicate I.capacity (partitionTextbookBase I)).length := by
        simp [length_prefixSelector hWeightSlackLe]
      rw [chosenSum_append hWeightPrefixLen]
      rw [chosenSum_encodedItems]
      rw [chosenSum_replicate_of_length (partitionTextbookBase I) I.capacity
        (length_prefixSelector hWeightSlackLe)]
      rw [chosenSum_replicate_of_length 1 (valueSlackBudget I)
        (length_prefixSelector hValueSlackLe)]
      rw [trueCount_prefixSelector hWeightSlackLe, trueCount_prefixSelector hValueSlackLe]
      simp [knapsackSubsetTarget, selectedWeight_itemOnly, selectedValue_itemOnly,
        weightSlack, valueSlack, Nat.add_assoc, Nat.add_comm]
      have hWeightEq :
          selectedWeight I selected + (I.capacity - selectedWeight I selected) =
            I.capacity :=
        Nat.add_sub_of_le hWeight
      have hValueEq :
          selectedValue I selected + (valueTargetLevel I - selectedValue I selected) =
            valueTargetLevel I :=
        Nat.add_sub_of_le hSelectedValueLeLevel
      nlinarith [hWeightEq, hValueEq]
  · rintro ⟨bits, hLen, hSum⟩
    let itemBits := subsetItemBits I bits
    let weightBits := subsetWeightSlackBits I bits
    let valueBits := subsetValueSlackBits I bits
    have hBitsLen :
        bits.length = I.items.length + I.capacity + valueSlackBudget I := by
      simpa [knapsackSubsetWeights, encodedItems, Nat.add_assoc] using hLen
    have hItemLen : itemBits.length = I.items.length := by
      have hTake : I.items.length ≤ bits.length := by
        omega
      simp [itemBits, subsetItemBits, hTake]
    have hDropLen :
        (bits.drop I.items.length).length = I.capacity + valueSlackBudget I := by
      simp [hBitsLen]
      omega
    have hValueLen : valueBits.length = valueSlackBudget I := by
      simp [valueBits, subsetValueSlackBits]
      omega
    have hEqRaw := (chosenSum_knapsackSubsetWeights_eq I hLen).symm.trans hSum
    have hEq :
        partitionTextbookBase I *
            (selectedWeight I itemBits + trueCount weightBits) +
          (selectedValue I itemBits + trueCount valueBits) =
            partitionTextbookBase I * I.capacity + valueTargetLevel I := by
      simpa [itemBits, weightBits, valueBits, knapsackSubsetTarget] using hEqRaw
    have hValueLeLevel : selectedValue I itemBits ≤ valueTargetLevel I := by
      exact (selectedValue_le_itemValueTotal_input I itemBits).trans
        (itemValueTotal_le_valueTargetLevel I)
    have hVsLeBudget : trueCount valueBits ≤ valueSlackBudget I := by
      have hTrue := trueCount_le_length valueBits
      omega
    have hLowBound :
        selectedValue I itemBits + trueCount valueBits < partitionTextbookBase I := by
      unfold partitionTextbookBase
      have hBudgetLeLevel : valueSlackBudget I ≤ valueTargetLevel I := by
        unfold valueSlackBudget
        omega
      omega
    have hTargetLowBound : valueTargetLevel I < partitionTextbookBase I := by
      unfold partitionTextbookBase
      omega
    rcases noCarry_pair_eq (partitionTextbookBase_pos I) hLowBound hTargetLowBound hEq with
      ⟨hLowEq, hHighEq⟩
    have hWeightBound : selectedWeight I itemBits ≤ I.capacity := by
      omega
    have hValueBound : I.targetValue ≤ selectedValue I itemBits := by
      have hTargetLeLevel := targetValue_le_valueTargetLevel I
      unfold valueSlackBudget at hVsLeBudget
      omega
    exact ⟨itemBits, hItemLen, hWeightBound, hValueBound⟩

theorem textbookMap_correct (I : KnapsackInput) :
    knapsackKarpDecisionProblem.isYes I ↔ Partition (textbookMap I) := by
  change Combinatorics.Knapsack I ↔ Partition (textbookMap I)
  rw [knapsack_subsetSum_correct I]
  simpa [textbookMap] using
    subsetToPartition_correct (knapsackSubsetWeights I) (knapsackSubsetTarget I)

/-! ### Compact binary-numeric balancing route -/

theorem binaryNat_inputSize_eq_size (n : Nat) :
    EncodedType.binaryNat.inputSize n = Nat.size n := by
  apply le_antisymm
  · exact Knapsack.binaryNat_inputSize_le_of_lt_two_pow (Nat.lt_size_self n)
  · exact Nat.size_le.2 (Knapsack.binaryNat_lt_two_pow_inputSize n)

theorem chosenSum_map_two_mul (weights : List Nat) (selections : List Bool) :
    chosenSum (weights.map fun weight => 2 * weight) selections =
      2 * chosenSum weights selections := by
  induction weights generalizing selections with
  | nil =>
      simp [chosenSum]
  | cons weight weights ih =>
      cases selections with
      | nil =>
          simp [chosenSum]
      | cons selected selections =>
          cases selected <;> simp [chosenSum, ih selections, Nat.mul_add]

theorem chosenSum_compactBinaryPowers_digits (digits : List Nat)
    (hDigits : ∀ digit ∈ digits, digit < 2) :
    chosenSum (Knapsack.compactBinaryPowers digits.length)
        (digits.map fun digit => decide (digit = 1)) =
      Nat.ofDigits 2 digits := by
  induction digits with
  | nil =>
      simp [chosenSum, Knapsack.compactBinaryPowers]
  | cons digit digits ih =>
      have hDigit : digit = 0 ∨ digit = 1 := by
        have hlt : digit < 2 := hDigits digit (by simp)
        omega
      have hTail : ∀ tailDigit ∈ digits, tailDigit < 2 := by
        intro tailDigit htail
        exact hDigits tailDigit (by simp [htail])
      rcases hDigit with rfl | rfl
      · simp [chosenSum, Knapsack.compactBinaryPowers, chosenSum_map_two_mul, ih hTail,
          Nat.ofDigits_cons]
      · simp [chosenSum, Knapsack.compactBinaryPowers, chosenSum_map_two_mul, ih hTail,
          Nat.ofDigits_cons]

theorem chosenSum_compactBinaryPowers_digitsAppend {length slack : Nat}
    (hSlack : slack < 2 ^ length) :
    chosenSum (Knapsack.compactBinaryPowers length)
        ((Nat.digitsAppend 2 length slack).map fun digit => decide (digit = 1)) =
      slack := by
  let digits := Nat.digitsAppend 2 length slack
  have hLength : digits.length = length := by
    simpa [digits] using Nat.length_digitsAppend (by decide : 1 < 2) length hSlack
  have hDigitsLt : ∀ digit ∈ digits, digit < 2 := by
    intro digit hdigit
    exact Nat.lt_of_mem_digitsAppend (by decide : 1 < 2) length digit hdigit
  have hSelected := chosenSum_compactBinaryPowers_digits digits hDigitsLt
  have hValue : Nat.ofDigits 2 digits = slack := by
    change Nat.ofDigits 2 (Nat.digitsAppend 2 length slack) = slack
    rw [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
  simpa [digits, hLength, hValue] using hSelected

theorem list_sum_map_two_mul (weights : List Nat) :
    (weights.map fun weight => 2 * weight).sum = 2 * weights.sum := by
  induction weights with
  | nil =>
      simp
  | cons weight weights ih =>
      simp [ih, Nat.mul_add]

theorem compactBinaryPowers_sum (length : Nat) :
    (Knapsack.compactBinaryPowers length).sum = 2 ^ length - 1 := by
  induction length with
  | zero =>
      simp [Knapsack.compactBinaryPowers]
  | succ length ih =>
      rw [Knapsack.compactBinaryPowers]
      simp only [List.sum_cons, list_sum_map_two_mul, ih]
      rw [Nat.pow_succ']
      have hpos : 1 ≤ 2 ^ length := by
        exact Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))
      omega

/--
Number of ordinary binary powers used before the final adjusted slack weight.
For a budget `n`, the first `2^m - 1` slack values are covered by powers
`1, 2, ..., 2^(m-1)`, and a final adjusted item fills the remaining budget.
-/
def boundedSlackPrefixLength (budget : Nat) : Nat :=
  Nat.size (budget + 1) - 1

def boundedSlackPrefixSum (budget : Nat) : Nat :=
  2 ^ boundedSlackPrefixLength budget - 1

def boundedSlackRemainder (budget : Nat) : Nat :=
  budget - boundedSlackPrefixSum budget

/--
Compact slack weights with total sum exactly `budget` while still representing
every value `≤ budget`.
-/
def boundedSlackPowers (budget : Nat) : List Nat :=
  let pref := Knapsack.compactBinaryPowers (boundedSlackPrefixLength budget)
  let remainder := boundedSlackRemainder budget
  if remainder = 0 then pref else pref ++ [remainder]

theorem boundedSlackPrefixLength_add_one (budget : Nat) :
    boundedSlackPrefixLength budget + 1 = Nat.size (budget + 1) := by
  unfold boundedSlackPrefixLength
  have hpos : 0 < Nat.size (budget + 1) := by
    exact Nat.size_pos.mpr (by omega)
  exact Nat.sub_add_cancel hpos

theorem boundedSlackPrefixPow_le_succ (budget : Nat) :
    2 ^ boundedSlackPrefixLength budget ≤ budget + 1 := by
  have hlt : boundedSlackPrefixLength budget < Nat.size (budget + 1) := by
    rw [← boundedSlackPrefixLength_add_one budget]
    exact Nat.lt_succ_self _
  exact Nat.lt_size.mp hlt

theorem budget_succ_lt_next_prefixPow (budget : Nat) :
    budget + 1 < 2 ^ (boundedSlackPrefixLength budget + 1) := by
  simpa [boundedSlackPrefixLength_add_one budget] using Nat.lt_size_self (budget + 1)

end Partition
end Karp21
end ComplexityReduction
