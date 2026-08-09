import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.Part1
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ChromaticNumber.StructuredRoute

namespace ComplexityReduction
namespace Karp21
namespace Partition

open ComplexityReduction.Combinatorics

/-!
Direct TM components for the final exact-subset-sum to Partition balancing
wrapper.  This is the small arithmetic/list layer used by `textbookMap` after
the Knapsack instance has been converted to exact subset-sum weights and target.
-/

def exactSubsetPartitionPairStructuredEncodedType : EncodedType :=
  EncodedType.prod partitionWeightsStructuredEncodedType EncodedType.nat

def natListSum (xs : List Nat) : Nat :=
  xs.foldl (fun acc x => acc + x) 0

theorem natListSum_foldl_eq (xs : List Nat) (acc : Nat) :
    xs.foldl (fun acc x => acc + x) acc = acc + xs.sum := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih (acc + x)]
      simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem natListSum_eq_sum (xs : List Nat) :
    natListSum xs = xs.sum := by
  simp [natListSum, natListSum_foldl_eq]

theorem natListSum_step_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.nat
      (fun p : Nat × Nat => p.1 + p.2) :=
  natAdd_tm_polytime

theorem natListSum_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list EncodedType.nat)
      EncodedType.nat
      natListSum := by
  rcases natListSum_step_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      EncodedType.nat EncodedType.nat
      (fun p : Nat × Nat => p.1 + p.2) (0 : Nat)
      hStep (Polynomial.C 1) Polynomial.X ?_ ?_
  · intro xs
    simp [EncodedType.inputSize_nat]
  · intro source acc x hx
    simp [EncodedType.inputSize_nat, Polynomial.eval_X] at hx ⊢
    omega

def exactSubsetPartitionTail (p : List Nat × Nat) :
    List Nat :=
  [natListSum p.1, natDouble p.2]

theorem exactSubsetPartitionTail_tm_polytime :
    TMPolyTimeMap
      exactSubsetPartitionPairStructuredEncodedType
      partitionWeightsStructuredEncodedType
      exactSubsetPartitionTail := by
  let X := exactSubsetPartitionPairStructuredEncodedType
  have hWeights :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType (fun p : List Nat × Nat => p.1) := by
    simpa [X, exactSubsetPartitionPairStructuredEncodedType,
      partitionWeightsStructuredEncodedType] using
      TMPolyTimeMap.fst partitionWeightsStructuredEncodedType EncodedType.nat
  have hTarget :
      TMPolyTimeMap X EncodedType.nat (fun p : List Nat × Nat => p.2) := by
    simpa [X, exactSubsetPartitionPairStructuredEncodedType] using
      TMPolyTimeMap.snd partitionWeightsStructuredEncodedType EncodedType.nat
  have hSum :
      TMPolyTimeMap X EncodedType.nat (fun p : List Nat × Nat => natListSum p.1) := by
    have hComp := TMPolyTimeMap.comp natListSum_tm_polytime hWeights
    simpa [Function.comp, X] using hComp
  have hDouble :
      TMPolyTimeMap X EncodedType.nat (fun p : List Nat × Nat => natDouble p.2) := by
    have hComp := TMPolyTimeMap.comp natDouble_tm_polytime hTarget
    simpa [Function.comp, X] using hComp
  have hDoubleSingleton :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType
        (fun p : List Nat × Nat => [natDouble p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton EncodedType.nat) hDouble
    simpa [Function.comp, partitionWeightsStructuredEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat partitionWeightsStructuredEncodedType)
        (fun p : List Nat × Nat => (natListSum p.1, [natDouble p.2])) :=
    TMPolyTimeMap.prod_mk hSum hDoubleSingleton
  have hCons :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType
        (fun p : List Nat × Nat => natListSum p.1 :: [natDouble p.2]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_cons EncodedType.nat) hConsInput
    simpa [Function.comp, partitionWeightsStructuredEncodedType, X] using hComp
  simpa [exactSubsetPartitionTail] using hCons

def subsetToPartitionWeightsTM (p : List Nat × Nat) :
    List Nat :=
  p.1 ++ exactSubsetPartitionTail p

theorem subsetToPartitionWeightsTM_eq_textbook
    (p : List Nat × Nat) :
    subsetToPartitionWeightsTM p = subsetToPartitionWeights p.1 p.2 := by
  rcases p with ⟨weights, target⟩
  simp [subsetToPartitionWeightsTM, exactSubsetPartitionTail, subsetToPartitionWeights,
    natListSum_eq_sum, natDouble]
  omega

theorem subsetToPartitionWeightsTM_tm_polytime :
    TMPolyTimeMap
      exactSubsetPartitionPairStructuredEncodedType
      partitionWeightsStructuredEncodedType
      subsetToPartitionWeightsTM := by
  let X := exactSubsetPartitionPairStructuredEncodedType
  have hWeights :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType (fun p : List Nat × Nat => p.1) := by
    simpa [X, exactSubsetPartitionPairStructuredEncodedType,
      partitionWeightsStructuredEncodedType] using
      TMPolyTimeMap.fst partitionWeightsStructuredEncodedType EncodedType.nat
  have hTail := exactSubsetPartitionTail_tm_polytime
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod partitionWeightsStructuredEncodedType
          partitionWeightsStructuredEncodedType)
        (fun p : List Nat × Nat => (p.1, exactSubsetPartitionTail p)) :=
    TMPolyTimeMap.prod_mk hWeights hTail
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append EncodedType.nat) hAppendInput
  simpa [Function.comp, subsetToPartitionWeightsTM, partitionWeightsStructuredEncodedType, X]
    using hAppend

def partitionInputFromWeights (weights : List Nat) : PartitionInput :=
  { weights := weights }

theorem partitionInputFromWeights_encode (weights : List Nat) :
    partitionStructuredEncodedType.encode (partitionInputFromWeights weights) =
      partitionWeightsStructuredEncodedType.encode weights := by
  rfl

noncomputable def partitionInputFromWeightsTMBackedMap :
    TMBackedCostedMap
      partitionWeightsStructuredEncodedType
      partitionStructuredEncodedType
      partitionInputFromWeights :=
  TMBackedCostedMap.ofEncodingEquiv
    partitionWeightsStructuredEncodedType partitionStructuredEncodedType
    partitionInputFromWeights
    (Equiv.refl partitionWeightsStructuredEncodedType.Symbol)
    (by
      intro weights
      change
        partitionStructuredEncodedType.encode (partitionInputFromWeights weights) =
          (partitionWeightsStructuredEncodedType.encode weights).map id
      simp [partitionInputFromWeights_encode])

def subsetToPartitionInputTM (p : List Nat × Nat) :
    PartitionInput :=
  partitionInputFromWeights (subsetToPartitionWeightsTM p)

theorem subsetToPartitionInputTM_eq_textbook
    (p : List Nat × Nat) :
    subsetToPartitionInputTM p =
      { weights := subsetToPartitionWeights p.1 p.2 } := by
  rcases p with ⟨weights, target⟩
  simp [subsetToPartitionInputTM, partitionInputFromWeights,
    subsetToPartitionWeightsTM_eq_textbook]

theorem subsetToPartitionInputTM_tm_polytime :
    TMPolyTimeMap
      exactSubsetPartitionPairStructuredEncodedType
      partitionStructuredEncodedType
      subsetToPartitionInputTM := by
  have hComp :=
    TMPolyTimeMap.comp partitionInputFromWeightsTMBackedMap.tm_polytime
      subsetToPartitionWeightsTM_tm_polytime
  simpa [Function.comp, subsetToPartitionInputTM] using hComp

end Partition
end Karp21
end ComplexityReduction
