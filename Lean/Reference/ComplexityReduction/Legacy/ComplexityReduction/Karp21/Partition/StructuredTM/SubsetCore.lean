import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.Arithmetic

namespace ComplexityReduction
namespace Karp21
namespace Partition

open ComplexityReduction.Combinatorics

/-!
Direct TM components for the Knapsack-to-exact-subset-sum core arithmetic in
the structured Partition route.
-/

abbrev KnapsackTupleCarrier := List (Nat × Nat) × (Nat × Nat)

def knapsackAsTuple (I : KnapsackInput) : KnapsackTupleCarrier :=
  (I.items, (I.capacity, I.targetValue))

def knapsackTupleToInput (p : KnapsackTupleCarrier) : KnapsackInput :=
  { items := p.1, capacity := p.2.1, targetValue := p.2.2 }

@[simp] theorem knapsackTupleToInput_asTuple (I : KnapsackInput) :
    knapsackTupleToInput (knapsackAsTuple I) = I := by
  cases I
  rfl

theorem knapsackAsTuple_tm_polytime :
    TMPolyTimeMap
      knapsackStructuredEncodedType
      knapsackTupleStructuredEncodedType
      knapsackAsTuple :=
  TMPolyTimeMap.of_encodingEquiv
    knapsackStructuredEncodedType
    knapsackTupleStructuredEncodedType
    knapsackAsTuple
    (Equiv.refl knapsackTupleStructuredEncodedType.Symbol)
    (by
      intro I
      change
        knapsackTupleStructuredEncodedType.encode (knapsackAsTuple I) =
          (knapsackStructuredEncodedType.encode I).map id
      simp [knapsackAsTuple, knapsackStructuredEncodedType]
      rfl)

theorem itemWeightTotal_tm_polytime :
    TMPolyTimeMap
      knapsackItemListStructuredEncodedType
      EncodedType.nat
      itemWeightTotal := by
  have hItemWeight :
      TMPolyTimeMap
        knapsackItemStructuredEncodedType
        EncodedType.nat
        (fun item : Nat × Nat => item.1) := by
    simpa [knapsackItemStructuredEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hWeights :
      TMPolyTimeMap
        knapsackItemListStructuredEncodedType
        partitionWeightsStructuredEncodedType
        (fun items : List (Nat × Nat) => items.map Prod.fst) := by
    simpa [knapsackItemListStructuredEncodedType, partitionWeightsStructuredEncodedType]
      using TMPolyTimeMap.list_map hItemWeight
  have hSum := TMPolyTimeMap.comp natListSum_tm_polytime hWeights
  convert hSum using 1
  funext items
  simp [Function.comp, itemWeightTotal, natListSum_eq_sum]
  rfl

theorem itemValueTotal_tm_polytime :
    TMPolyTimeMap
      knapsackItemListStructuredEncodedType
      EncodedType.nat
      itemValueTotal := by
  have hItemValue :
      TMPolyTimeMap
        knapsackItemStructuredEncodedType
        EncodedType.nat
        (fun item : Nat × Nat => item.2) := by
    simpa [knapsackItemStructuredEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hValues :
      TMPolyTimeMap
        knapsackItemListStructuredEncodedType
        partitionWeightsStructuredEncodedType
        (fun items : List (Nat × Nat) => items.map Prod.snd) := by
    simpa [knapsackItemListStructuredEncodedType, partitionWeightsStructuredEncodedType]
      using TMPolyTimeMap.list_map hItemValue
  have hSum := TMPolyTimeMap.comp natListSum_tm_polytime hValues
  convert hSum using 1
  funext items
  simp [Function.comp, itemValueTotal, natListSum_eq_sum]
  rfl

abbrev NatPairCarrier := Nat × Nat

def natMaxViaSub (p : NatPairCarrier) : Nat :=
  p.1 + (p.2 - p.1)

def natMaxStructured (p : NatPairCarrier) : Nat :=
  max p.1 p.2

theorem natMaxViaSub_eq_max (p : NatPairCarrier) :
    natMaxViaSub p = natMaxStructured p := by
  rcases p with ⟨a, b⟩
  simp [natMaxViaSub, natMaxStructured]
  omega

theorem natMax_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.nat
      natMaxStructured := by
  have hLeft :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        EncodedType.nat
        (fun p : Nat × Nat => p.1) :=
    TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hRight :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        EncodedType.nat
        (fun p : Nat × Nat => p.2) :=
    TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hSubInput :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat => (p.2, p.1)) :=
    TMPolyTimeMap.prod_mk hRight hLeft
  have hSub :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        EncodedType.nat
        (fun p : Nat × Nat => p.2 - p.1) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hSubInput
    simpa [Function.comp] using hComp
  have hAddInput :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : Nat × Nat => (p.1, p.2 - p.1)) :=
    TMPolyTimeMap.prod_mk hLeft hSub
  have hAdd :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        EncodedType.nat
        natMaxViaSub := by
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hAddInput
    simpa [Function.comp, natMaxViaSub] using hComp
  convert hAdd using 1
  funext p
  exact (natMaxViaSub_eq_max p).symm

def knapsackTupleValueTargetLevel (p : KnapsackTupleCarrier) : Nat :=
  natMaxStructured (itemValueTotal p.1, p.2.2)

@[simp] theorem knapsackTupleValueTargetLevel_eq
    (p : KnapsackTupleCarrier) :
    knapsackTupleValueTargetLevel p =
      valueTargetLevel (knapsackTupleToInput p) := by
  simp [knapsackTupleValueTargetLevel, valueTargetLevel, natMaxStructured,
    knapsackTupleToInput]

theorem knapsackTupleValueTargetLevel_tm_polytime :
    TMPolyTimeMap
      knapsackTupleStructuredEncodedType
      EncodedType.nat
      knapsackTupleValueTargetLevel := by
  have hItems :
      TMPolyTimeMap
        knapsackTupleStructuredEncodedType
        knapsackItemListStructuredEncodedType
        (fun p : KnapsackTupleCarrier => p.1) := by
    simpa [knapsackTupleStructuredEncodedType] using
      TMPolyTimeMap.fst knapsackItemListStructuredEncodedType knapsackBoundsStructuredEncodedType
  have hValueTotal :
      TMPolyTimeMap
        knapsackTupleStructuredEncodedType
        EncodedType.nat
        (fun p : KnapsackTupleCarrier => itemValueTotal p.1) := by
    have hComp := TMPolyTimeMap.comp itemValueTotal_tm_polytime hItems
    simpa [Function.comp] using hComp
  have hBounds :
      TMPolyTimeMap
        knapsackTupleStructuredEncodedType
        knapsackBoundsStructuredEncodedType
        (fun p : KnapsackTupleCarrier => p.2) := by
    simpa [knapsackTupleStructuredEncodedType] using
      TMPolyTimeMap.snd knapsackItemListStructuredEncodedType knapsackBoundsStructuredEncodedType
  have hTarget :
      TMPolyTimeMap
        knapsackTupleStructuredEncodedType
        EncodedType.nat
        (fun p : KnapsackTupleCarrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hBounds
    simpa [Function.comp, knapsackBoundsStructuredEncodedType] using hComp
  have hPair :
      TMPolyTimeMap
        knapsackTupleStructuredEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : KnapsackTupleCarrier => (itemValueTotal p.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hValueTotal hTarget
  have hComp := TMPolyTimeMap.comp natMax_tm_polytime hPair
  simpa [Function.comp, knapsackTupleValueTargetLevel] using hComp

def knapsackTuplePartitionTextbookBase
    (p : KnapsackTupleCarrier) : Nat :=
  2 * knapsackTupleValueTargetLevel p + 1

@[simp] theorem knapsackTuplePartitionTextbookBase_eq
    (p : KnapsackTupleCarrier) :
    knapsackTuplePartitionTextbookBase p =
      partitionTextbookBase (knapsackTupleToInput p) := by
  simp [knapsackTuplePartitionTextbookBase, partitionTextbookBase,
    knapsackTupleValueTargetLevel_eq]

theorem knapsackTuplePartitionTextbookBase_tm_polytime :
    TMPolyTimeMap
      knapsackTupleStructuredEncodedType
      EncodedType.nat
      knapsackTuplePartitionTextbookBase := by
  have hDouble :
      TMPolyTimeMap knapsackTupleStructuredEncodedType EncodedType.nat
        (fun p => natDouble (knapsackTupleValueTargetLevel p)) := by
    have hComp := TMPolyTimeMap.comp natDouble_tm_polytime
      knapsackTupleValueTargetLevel_tm_polytime
    simpa [Function.comp] using hComp
  have hSucc := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hDouble
  convert hSucc using 1
  funext p
  simp [Function.comp, knapsackTuplePartitionTextbookBase, natDouble]
  omega

def knapsackTupleValueSlackBudget
    (p : KnapsackTupleCarrier) : Nat :=
  knapsackTupleValueTargetLevel p - p.2.2

@[simp] theorem knapsackTupleValueSlackBudget_eq
    (p : KnapsackTupleCarrier) :
    knapsackTupleValueSlackBudget p =
      valueSlackBudget (knapsackTupleToInput p) := by
  simp [knapsackTupleValueSlackBudget, valueSlackBudget, knapsackTupleValueTargetLevel_eq,
    knapsackTupleToInput]

theorem knapsackTupleValueSlackBudget_tm_polytime :
    TMPolyTimeMap
      knapsackTupleStructuredEncodedType
      EncodedType.nat
      knapsackTupleValueSlackBudget := by
  have hLevel := knapsackTupleValueTargetLevel_tm_polytime
  have hBounds :
      TMPolyTimeMap
        knapsackTupleStructuredEncodedType
        knapsackBoundsStructuredEncodedType
        (fun p : KnapsackTupleCarrier => p.2) := by
    simpa [knapsackTupleStructuredEncodedType] using
      TMPolyTimeMap.snd knapsackItemListStructuredEncodedType knapsackBoundsStructuredEncodedType
  have hTarget :
      TMPolyTimeMap
        knapsackTupleStructuredEncodedType
        EncodedType.nat
        (fun p : KnapsackTupleCarrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hBounds
    simpa [Function.comp, knapsackBoundsStructuredEncodedType] using hComp
  have hPair :
      TMPolyTimeMap
        knapsackTupleStructuredEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : KnapsackTupleCarrier =>
          (knapsackTupleValueTargetLevel p, p.2.2)) :=
    TMPolyTimeMap.prod_mk hLevel hTarget
  have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_sub hPair
  simpa [Function.comp, knapsackTupleValueSlackBudget] using hComp

def knapsackTupleSubsetTarget
    (p : KnapsackTupleCarrier) : Nat :=
  knapsackTuplePartitionTextbookBase p * p.2.1 +
    knapsackTupleValueTargetLevel p

@[simp] theorem knapsackTupleSubsetTarget_eq
    (p : KnapsackTupleCarrier) :
    knapsackTupleSubsetTarget p =
      knapsackSubsetTarget (knapsackTupleToInput p) := by
  simp [knapsackTupleSubsetTarget, knapsackSubsetTarget,
    knapsackTuplePartitionTextbookBase_eq, knapsackTupleValueTargetLevel_eq,
    knapsackTupleToInput]

theorem knapsackTupleSubsetTarget_tm_polytime :
    TMPolyTimeMap
      knapsackTupleStructuredEncodedType
      EncodedType.nat
      knapsackTupleSubsetTarget := by
  have hBase := knapsackTuplePartitionTextbookBase_tm_polytime
  have hLevel := knapsackTupleValueTargetLevel_tm_polytime
  have hBounds :
      TMPolyTimeMap
        knapsackTupleStructuredEncodedType
        knapsackBoundsStructuredEncodedType
        (fun p : KnapsackTupleCarrier => p.2) := by
    simpa [knapsackTupleStructuredEncodedType] using
      TMPolyTimeMap.snd knapsackItemListStructuredEncodedType knapsackBoundsStructuredEncodedType
  have hCapacity :
      TMPolyTimeMap
        knapsackTupleStructuredEncodedType
        EncodedType.nat
        (fun p : KnapsackTupleCarrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hBounds
    simpa [Function.comp, knapsackBoundsStructuredEncodedType] using hComp
  have hMulInput :
      TMPolyTimeMap
        knapsackTupleStructuredEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : KnapsackTupleCarrier =>
          (knapsackTuplePartitionTextbookBase p, p.2.1)) :=
    TMPolyTimeMap.prod_mk hBase hCapacity
  have hMul :
      TMPolyTimeMap
        knapsackTupleStructuredEncodedType
        EncodedType.nat
        (fun p : KnapsackTupleCarrier =>
          knapsackTuplePartitionTextbookBase p * p.2.1) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_mul hMulInput
    simpa [Function.comp] using hComp
  have hAddInput :
      TMPolyTimeMap
        knapsackTupleStructuredEncodedType
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : KnapsackTupleCarrier =>
          (knapsackTuplePartitionTextbookBase p * p.2.1,
            knapsackTupleValueTargetLevel p)) :=
    TMPolyTimeMap.prod_mk hMul hLevel
  have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hAddInput
  simpa [Function.comp, knapsackTupleSubsetTarget] using hComp

theorem valueTargetLevel_tm_polytime :
    TMPolyTimeMap
      knapsackStructuredEncodedType
      EncodedType.nat
      valueTargetLevel := by
  have hComp := TMPolyTimeMap.comp
    knapsackTupleValueTargetLevel_tm_polytime knapsackAsTuple_tm_polytime
  simpa [Function.comp, knapsackAsTuple, valueTargetLevel,
    knapsackTupleValueTargetLevel, natMaxStructured] using hComp

theorem partitionTextbookBase_tm_polytime :
    TMPolyTimeMap
      knapsackStructuredEncodedType
      EncodedType.nat
      partitionTextbookBase := by
  have hComp := TMPolyTimeMap.comp
    knapsackTuplePartitionTextbookBase_tm_polytime knapsackAsTuple_tm_polytime
  simpa [Function.comp, knapsackAsTuple, partitionTextbookBase,
    knapsackTuplePartitionTextbookBase, knapsackTupleValueTargetLevel,
    natMaxStructured] using hComp

theorem valueSlackBudget_tm_polytime :
    TMPolyTimeMap
      knapsackStructuredEncodedType
      EncodedType.nat
      valueSlackBudget := by
  have hComp := TMPolyTimeMap.comp
    knapsackTupleValueSlackBudget_tm_polytime knapsackAsTuple_tm_polytime
  simpa [Function.comp, knapsackAsTuple, valueSlackBudget,
    knapsackTupleValueSlackBudget, knapsackTupleValueTargetLevel, natMaxStructured]
    using hComp

theorem knapsackSubsetTarget_tm_polytime :
    TMPolyTimeMap
      knapsackStructuredEncodedType
      EncodedType.nat
      knapsackSubsetTarget := by
  have hComp := TMPolyTimeMap.comp
    knapsackTupleSubsetTarget_tm_polytime knapsackAsTuple_tm_polytime
  simpa [Function.comp, knapsackAsTuple, knapsackSubsetTarget,
    knapsackTupleSubsetTarget, knapsackTuplePartitionTextbookBase,
    knapsackTupleValueTargetLevel, natMaxStructured] using hComp

end Partition
end Karp21
end ComplexityReduction
