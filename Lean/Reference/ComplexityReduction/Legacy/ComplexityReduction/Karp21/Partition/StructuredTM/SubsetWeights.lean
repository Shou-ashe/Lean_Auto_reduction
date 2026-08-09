import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.KnapsackWeights
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.SubsetCore

namespace ComplexityReduction
namespace Karp21
namespace Partition

open ComplexityReduction.Combinatorics

/-!
Direct TM assembly for the exact-subset-sum weights in the structured
Knapsack-to-Partition textbook route.
-/

def baseReplicateItemsFromUnits (units : List Unit) : List (Nat × Nat) :=
  List.replicate units.length ((1 : Nat), (0 : Nat))

def baseReplicateFromUnits (p : Nat × List Unit) : List Nat :=
  encodedItems p.1 (baseReplicateItemsFromUnits p.2)

def baseReplicateFromNat (p : Nat × Nat) : List Nat :=
  baseReplicateFromUnits (p.1, List.replicate p.2 ())

def onesReplicateFromUnits (units : List Unit) : List Nat :=
  List.replicate units.length (1 : Nat)

theorem baseReplicateItemsFromUnits_length (units : List Unit) :
    (baseReplicateItemsFromUnits units).length = units.length := by
  simp [baseReplicateItemsFromUnits]

theorem baseReplicateFromUnits_eq (base : Nat) (units : List Unit) :
    baseReplicateFromUnits (base, units) = List.replicate units.length base := by
  simp [baseReplicateFromUnits, baseReplicateItemsFromUnits, encodedItems, encodedItem]

theorem baseReplicateFromNat_eq (p : Nat × Nat) :
    baseReplicateFromNat p = List.replicate p.2 p.1 := by
  rcases p with ⟨base, n⟩
  simpa [baseReplicateFromNat] using
    baseReplicateFromUnits_eq base (List.replicate n ())

theorem onesReplicateFromUnits_eq (units : List Unit) :
    onesReplicateFromUnits units = List.replicate units.length (1 : Nat) := by
  rfl

theorem baseReplicateItemsFromUnits_tm_polytime :
    TMPolyTimeMap
      rawUnitListEncodedType
      knapsackItemListStructuredEncodedType
      baseReplicateItemsFromUnits := by
  simpa [rawUnitListEncodedType, knapsackItemListStructuredEncodedType,
    baseReplicateItemsFromUnits] using
    TMPolyTimeMap.list_const (EncodedType.raw Unit) knapsackItemStructuredEncodedType
      ((1 : Nat), (0 : Nat))

theorem baseReplicateFromUnits_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat rawUnitListEncodedType)
      partitionWeightsStructuredEncodedType
      baseReplicateFromUnits := by
  let X := EncodedType.prod EncodedType.nat rawUnitListEncodedType
  have hBase :
      TMPolyTimeMap X EncodedType.nat (fun p : Nat × List Unit => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat rawUnitListEncodedType
  have hUnits :
      TMPolyTimeMap X rawUnitListEncodedType (fun p : Nat × List Unit => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.nat rawUnitListEncodedType
  have hItems :
      TMPolyTimeMap X knapsackItemListStructuredEncodedType
        (fun p : Nat × List Unit => baseReplicateItemsFromUnits p.2) := by
    have hComp := TMPolyTimeMap.comp baseReplicateItemsFromUnits_tm_polytime hUnits
    simpa [Function.comp, X] using hComp
  have hPair :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat knapsackItemListStructuredEncodedType)
        (fun p : Nat × List Unit => (p.1, baseReplicateItemsFromUnits p.2)) :=
    TMPolyTimeMap.prod_mk hBase hItems
  have hComp := TMPolyTimeMap.comp encodedItems_pair_tm_polytime hPair
  simpa [Function.comp, baseReplicateFromUnits, X] using hComp

theorem baseReplicateFromNat_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      partitionWeightsStructuredEncodedType
      baseReplicateFromNat := by
  let X := EncodedType.prod EncodedType.nat EncodedType.nat
  have hBase :
      TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.1) :=
    TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
  have hCount :
      TMPolyTimeMap X EncodedType.nat (fun p : Nat × Nat => p.2) :=
    TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
  have hUnits :
      TMPolyTimeMap X rawUnitListEncodedType
        (fun p : Nat × Nat => List.replicate p.2 ()) := by
    have hComp := TMPolyTimeMap.comp natToRawUnitListTMBackedMap.tm_polytime hCount
    simpa [Function.comp, X] using hComp
  have hPair :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat rawUnitListEncodedType)
        (fun p : Nat × Nat => (p.1, List.replicate p.2 ())) :=
    TMPolyTimeMap.prod_mk hBase hUnits
  have hComp := TMPolyTimeMap.comp baseReplicateFromUnits_tm_polytime hPair
  simpa [Function.comp, baseReplicateFromNat, X] using hComp

theorem baseReplicate_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      partitionWeightsStructuredEncodedType
      (fun p : Nat × Nat => List.replicate p.2 p.1) := by
  convert baseReplicateFromNat_tm_polytime using 1
  funext p
  exact (baseReplicateFromNat_eq p).symm

theorem onesReplicateFromUnits_tm_polytime :
    TMPolyTimeMap
      rawUnitListEncodedType
      partitionWeightsStructuredEncodedType
      onesReplicateFromUnits := by
  simpa [rawUnitListEncodedType, partitionWeightsStructuredEncodedType,
    onesReplicateFromUnits] using
    TMPolyTimeMap.list_const (EncodedType.raw Unit) EncodedType.nat (1 : Nat)

theorem onesReplicate_tm_polytime :
    TMPolyTimeMap
      EncodedType.nat
      partitionWeightsStructuredEncodedType
      (fun n : Nat => List.replicate n (1 : Nat)) := by
  have hComp :=
    TMPolyTimeMap.comp onesReplicateFromUnits_tm_polytime
      natToRawUnitListTMBackedMap.tm_polytime
  convert hComp using 1
  funext n
  rw [Function.comp]
  simpa using (onesReplicateFromUnits_eq (List.replicate n ())).symm

theorem knapsackItems_tm_polytime :
    TMPolyTimeMap
      knapsackStructuredEncodedType
      knapsackItemListStructuredEncodedType
      (fun I : KnapsackInput => I.items) := by
  have hFst :
      TMPolyTimeMap
        knapsackTupleStructuredEncodedType
        knapsackItemListStructuredEncodedType
        (fun p : KnapsackTupleCarrier => p.1) := by
    simpa [knapsackTupleStructuredEncodedType] using
      TMPolyTimeMap.fst knapsackItemListStructuredEncodedType knapsackBoundsStructuredEncodedType
  have hComp := TMPolyTimeMap.comp hFst knapsackAsTuple_tm_polytime
  simpa [Function.comp, knapsackAsTuple] using hComp

theorem knapsackCapacity_tm_polytime :
    TMPolyTimeMap
      knapsackStructuredEncodedType
      EncodedType.nat
      (fun I : KnapsackInput => I.capacity) := by
  have hBounds :
      TMPolyTimeMap
        knapsackTupleStructuredEncodedType
        knapsackBoundsStructuredEncodedType
        (fun p : KnapsackTupleCarrier => p.2) := by
    simpa [knapsackTupleStructuredEncodedType] using
      TMPolyTimeMap.snd knapsackItemListStructuredEncodedType knapsackBoundsStructuredEncodedType
  have hCapacityTuple :
      TMPolyTimeMap
        knapsackTupleStructuredEncodedType
        EncodedType.nat
        (fun p : KnapsackTupleCarrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hBounds
    simpa [Function.comp, knapsackBoundsStructuredEncodedType] using hComp
  have hComp := TMPolyTimeMap.comp hCapacityTuple knapsackAsTuple_tm_polytime
  simpa [Function.comp, knapsackAsTuple] using hComp

theorem knapsackSubsetWeights_tm_polytime :
    TMPolyTimeMap
      knapsackStructuredEncodedType
      partitionWeightsStructuredEncodedType
      knapsackSubsetWeights := by
  let X := knapsackStructuredEncodedType
  have hBase := partitionTextbookBase_tm_polytime
  have hItems := knapsackItems_tm_polytime
  have hEncodedItemsInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat knapsackItemListStructuredEncodedType)
        (fun I : KnapsackInput => (partitionTextbookBase I, I.items)) :=
    TMPolyTimeMap.prod_mk hBase hItems
  have hEncodedItems :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType
        (fun I : KnapsackInput => encodedItems (partitionTextbookBase I) I.items) := by
    have hComp := TMPolyTimeMap.comp encodedItems_pair_tm_polytime hEncodedItemsInput
    simpa [Function.comp, X] using hComp
  have hCapacity := knapsackCapacity_tm_polytime
  have hBaseRepInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun I : KnapsackInput => (partitionTextbookBase I, I.capacity)) :=
    TMPolyTimeMap.prod_mk hBase hCapacity
  have hBaseRep :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType
        (fun I : KnapsackInput =>
          List.replicate I.capacity (partitionTextbookBase I)) := by
    have hComp := TMPolyTimeMap.comp baseReplicate_tm_polytime hBaseRepInput
    simpa [Function.comp, X] using hComp
  have hFirstAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod partitionWeightsStructuredEncodedType
          partitionWeightsStructuredEncodedType)
        (fun I : KnapsackInput =>
          (encodedItems (partitionTextbookBase I) I.items,
            List.replicate I.capacity (partitionTextbookBase I))) :=
    TMPolyTimeMap.prod_mk hEncodedItems hBaseRep
  have hFirstAppend :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType
        (fun I : KnapsackInput =>
          encodedItems (partitionTextbookBase I) I.items ++
            List.replicate I.capacity (partitionTextbookBase I)) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append EncodedType.nat) hFirstAppendInput
    simpa [Function.comp, partitionWeightsStructuredEncodedType, X] using hComp
  have hSlack := valueSlackBudget_tm_polytime
  have hOnes :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType
        (fun I : KnapsackInput => List.replicate (valueSlackBudget I) (1 : Nat)) := by
    have hComp := TMPolyTimeMap.comp onesReplicate_tm_polytime hSlack
    simpa [Function.comp, X] using hComp
  have hAllInput :
      TMPolyTimeMap X
        (EncodedType.prod partitionWeightsStructuredEncodedType
          partitionWeightsStructuredEncodedType)
        (fun I : KnapsackInput =>
          (encodedItems (partitionTextbookBase I) I.items ++
            List.replicate I.capacity (partitionTextbookBase I),
            List.replicate (valueSlackBudget I) (1 : Nat))) :=
    TMPolyTimeMap.prod_mk hFirstAppend hOnes
  have hAll := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append EncodedType.nat) hAllInput
  simpa [Function.comp, knapsackSubsetWeights, partitionWeightsStructuredEncodedType, X]
    using hAll

def knapsackSubsetPairTM (I : KnapsackInput) : List Nat × Nat :=
  (knapsackSubsetWeights I, knapsackSubsetTarget I)

theorem knapsackSubsetPairTM_tm_polytime :
    TMPolyTimeMap
      knapsackStructuredEncodedType
      exactSubsetPartitionPairStructuredEncodedType
      knapsackSubsetPairTM :=
  TMPolyTimeMap.prod_mk knapsackSubsetWeights_tm_polytime knapsackSubsetTarget_tm_polytime

def knapsackToPartitionStructuredTM (I : KnapsackInput) : PartitionInput :=
  subsetToPartitionInputTM (knapsackSubsetPairTM I)

theorem knapsackToPartitionStructuredTM_eq_textbook (I : KnapsackInput) :
    knapsackToPartitionStructuredTM I = textbookMap I := by
  simp [knapsackToPartitionStructuredTM, knapsackSubsetPairTM, textbookMap,
    subsetToPartitionInputTM_eq_textbook]

theorem knapsackToPartitionStructured_tm_polytime :
    TMPolyTimeMap
      knapsackStructuredEncodedType
      partitionStructuredEncodedType
      textbookMap := by
  have hComp := TMPolyTimeMap.comp subsetToPartitionInputTM_tm_polytime
    knapsackSubsetPairTM_tm_polytime
  convert hComp using 1
  funext I
  exact (knapsackToPartitionStructuredTM_eq_textbook I).symm

end Partition
end Karp21
end ComplexityReduction
