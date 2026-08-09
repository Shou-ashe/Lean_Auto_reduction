/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core

namespace ComplexityReduction
namespace Combinatorics

/-- Basic knapsack schema with weights, values, capacity, and target value. -/
structure KnapsackInput where
  items : List (Nat × Nat)
  capacity : Nat
  targetValue : Nat
  deriving Repr

def knapsackEncodedType : EncodedType :=
  EncodedType.raw KnapsackInput

/-- Structured finite-alphabet encoding for one knapsack item `(weight, value)`. -/
def knapsackItemStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

/-- Structured finite-alphabet encoding for the item list. -/
def knapsackItemListStructuredEncodedType : EncodedType :=
  EncodedType.list knapsackItemStructuredEncodedType

/-- Structured finite-alphabet encoding for `(capacity, targetValue)`. -/
def knapsackBoundsStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat EncodedType.nat

/-- Tuple-shaped finite-alphabet encoding for Knapsack fields. -/
def knapsackTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod knapsackItemListStructuredEncodedType knapsackBoundsStructuredEncodedType

/-- Concrete finite-alphabet Knapsack encoding. -/
def knapsackStructuredEncodedType : EncodedType where
  Carrier := KnapsackInput
  Symbol := knapsackTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => knapsackTupleStructuredEncodedType.encode
    (I.items, (I.capacity, I.targetValue))

/-- Binary-numeric finite-alphabet encoding for one knapsack item `(weight, value)`. -/
def knapsackItemBinaryStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat

/-- Binary-numeric finite-alphabet encoding for the item list. -/
def knapsackItemListBinaryStructuredEncodedType : EncodedType :=
  EncodedType.list knapsackItemBinaryStructuredEncodedType

/-- Binary-numeric finite-alphabet encoding for `(capacity, targetValue)`. -/
def knapsackBoundsBinaryStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat

/-- Tuple-shaped binary-numeric finite-alphabet encoding for Knapsack fields. -/
def knapsackTupleBinaryStructuredEncodedType : EncodedType :=
  EncodedType.prod knapsackItemListBinaryStructuredEncodedType
    knapsackBoundsBinaryStructuredEncodedType

/-- Concrete binary-numeric finite-alphabet Knapsack encoding. -/
def knapsackBinaryStructuredEncodedType : EncodedType where
  Carrier := KnapsackInput
  Symbol := knapsackTupleBinaryStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => knapsackTupleBinaryStructuredEncodedType.encode
    (I.items, (I.capacity, I.targetValue))

theorem knapsackItemStructuredEncodedType_encode_injective :
    Function.Injective knapsackItemStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    EncodedType.nat_encode_injective
    EncodedType.nat_encode_injective

theorem knapsackItemListStructuredEncodedType_encode_injective :
    Function.Injective knapsackItemListStructuredEncodedType.encode :=
  EncodedType.list_encode_injective knapsackItemStructuredEncodedType_encode_injective

theorem knapsackBoundsStructuredEncodedType_encode_injective :
    Function.Injective knapsackBoundsStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    EncodedType.nat_encode_injective
    EncodedType.nat_encode_injective

theorem knapsackTupleStructuredEncodedType_encode_injective :
    Function.Injective knapsackTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    knapsackItemListStructuredEncodedType_encode_injective
    knapsackBoundsStructuredEncodedType_encode_injective

theorem knapsackStructuredEncodedType_encode_injective :
    Function.Injective knapsackStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.items, (I.capacity, I.targetValue)) =
      (J.items, (J.capacity, J.targetValue)) :=
    knapsackTupleStructuredEncodedType_encode_injective (by
      simpa [knapsackStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl, rfl⟩
  rfl

theorem knapsackItemBinaryStructuredEncodedType_encode_injective :
    Function.Injective knapsackItemBinaryStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    EncodedType.binaryNat_encode_injective
    EncodedType.binaryNat_encode_injective

theorem knapsackItemListBinaryStructuredEncodedType_encode_injective :
    Function.Injective knapsackItemListBinaryStructuredEncodedType.encode :=
  EncodedType.list_encode_injective knapsackItemBinaryStructuredEncodedType_encode_injective

theorem knapsackBoundsBinaryStructuredEncodedType_encode_injective :
    Function.Injective knapsackBoundsBinaryStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    EncodedType.binaryNat_encode_injective
    EncodedType.binaryNat_encode_injective

theorem knapsackTupleBinaryStructuredEncodedType_encode_injective :
    Function.Injective knapsackTupleBinaryStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    knapsackItemListBinaryStructuredEncodedType_encode_injective
    knapsackBoundsBinaryStructuredEncodedType_encode_injective

theorem knapsackBinaryStructuredEncodedType_encode_injective :
    Function.Injective knapsackBinaryStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.items, (I.capacity, I.targetValue)) =
      (J.items, (J.capacity, J.targetValue)) :=
    knapsackTupleBinaryStructuredEncodedType_encode_injective (by
      simpa [knapsackBinaryStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl, rfl⟩
  rfl

def knapsackDecisionProblem (P : KnapsackInput → Prop) : EncodedDecisionProblem where
  Instance := knapsackEncodedType
  isYes := P

/-- Weight of the selected knapsack items. -/
def selectedWeight (I : KnapsackInput) (selected : List Bool) : Nat :=
  (I.items.zip selected).map (fun p => if p.2 then p.1.1 else 0) |>.sum

/-- Value of the selected knapsack items. -/
def selectedValue (I : KnapsackInput) (selected : List Bool) : Nat :=
  (I.items.zip selected).map (fun p => if p.2 then p.1.2 else 0) |>.sum

/-- Semantic predicate for Karp's knapsack target. -/
def Knapsack (I : KnapsackInput) : Prop :=
  ∃ selected : List Bool,
    selected.length = I.items.length ∧
      selectedWeight I selected ≤ I.capacity ∧
      I.targetValue ≤ selectedValue I selected

def knapsackKarpDecisionProblem : EncodedDecisionProblem :=
  knapsackDecisionProblem Knapsack

/-- Knapsack over the structured finite-alphabet encoding. -/
def knapsackStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := knapsackStructuredEncodedType
  isYes := Knapsack

/-- Knapsack over the binary-numeric finite-alphabet encoding. -/
def knapsackBinaryStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := knapsackBinaryStructuredEncodedType
  isYes := Knapsack

/-- Karp-style partition instance. -/
structure PartitionInput where
  weights : List Nat
  deriving Repr

def partitionEncodedType : EncodedType :=
  EncodedType.raw PartitionInput

/-- Structured finite-alphabet encoding for Partition weights. -/
def partitionWeightsStructuredEncodedType : EncodedType :=
  EncodedType.list EncodedType.nat

/-- Concrete finite-alphabet Partition encoding. -/
def partitionStructuredEncodedType : EncodedType where
  Carrier := PartitionInput
  Symbol := partitionWeightsStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => partitionWeightsStructuredEncodedType.encode I.weights

/-- Binary-numeric finite-alphabet encoding for Partition weights. -/
def partitionWeightsBinaryStructuredEncodedType : EncodedType :=
  EncodedType.list EncodedType.binaryNat

/-- Concrete binary-numeric finite-alphabet Partition encoding. -/
def partitionBinaryStructuredEncodedType : EncodedType where
  Carrier := PartitionInput
  Symbol := partitionWeightsBinaryStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => partitionWeightsBinaryStructuredEncodedType.encode I.weights

theorem partitionWeightsStructuredEncodedType_encode_injective :
    Function.Injective partitionWeightsStructuredEncodedType.encode :=
  EncodedType.list_encode_injective EncodedType.nat_encode_injective

theorem partitionStructuredEncodedType_encode_injective :
    Function.Injective partitionStructuredEncodedType.encode := by
  intro I J henc
  have hweights : I.weights = J.weights :=
    partitionWeightsStructuredEncodedType_encode_injective (by
      simpa [partitionStructuredEncodedType] using henc)
  cases I
  cases J
  simp at hweights
  rcases hweights with rfl
  rfl

theorem partitionWeightsBinaryStructuredEncodedType_encode_injective :
    Function.Injective partitionWeightsBinaryStructuredEncodedType.encode :=
  EncodedType.list_encode_injective EncodedType.binaryNat_encode_injective

theorem partitionBinaryStructuredEncodedType_encode_injective :
    Function.Injective partitionBinaryStructuredEncodedType.encode := by
  intro I J henc
  have hweights : I.weights = J.weights :=
    partitionWeightsBinaryStructuredEncodedType_encode_injective (by
      simpa [partitionBinaryStructuredEncodedType] using henc)
  cases I
  cases J
  simp at hweights
  rcases hweights with rfl
  rfl

def selectedPartitionWeight (I : PartitionInput) (selected : List Bool) : Nat :=
  (I.weights.zip selected).map (fun p => if p.2 then p.1 else 0) |>.sum

def unselectedPartitionWeight (I : PartitionInput) (selected : List Bool) : Nat :=
  (I.weights.zip selected).map (fun p => if p.2 then 0 else p.1) |>.sum

/-- Semantic predicate for Karp's partition target. -/
def Partition (I : PartitionInput) : Prop :=
  ∃ selected : List Bool,
    selected.length = I.weights.length ∧
      selectedPartitionWeight I selected = unselectedPartitionWeight I selected

def partitionDecisionProblem : EncodedDecisionProblem where
  Instance := partitionEncodedType
  isYes := Partition

/-- Partition over the structured finite-alphabet encoding. -/
def partitionStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := partitionStructuredEncodedType
  isYes := Partition

/-- Partition over the binary-numeric finite-alphabet encoding. -/
def partitionBinaryStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := partitionBinaryStructuredEncodedType
  isYes := Partition

end Combinatorics
end ComplexityReduction
