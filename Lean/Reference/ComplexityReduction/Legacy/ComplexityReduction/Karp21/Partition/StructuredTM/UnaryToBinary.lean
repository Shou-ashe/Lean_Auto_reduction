import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.UnaryToBinary
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.Part3

namespace ComplexityReduction
namespace Karp21
namespace Partition

open ComplexityReduction.Combinatorics

/-!
Direct unary-to-binary encoding bridge for faithful structured Partition.

The semantic map is the identity on `PartitionInput`; only the finite-alphabet
encoding changes from unary `EncodedType.nat` weights to `EncodedType.binaryNat`
weights.
-/

def partitionWeightsForUnaryToBinary (I : PartitionInput) : List Nat :=
  I.weights

theorem partitionWeightsForUnaryToBinary_encode (I : PartitionInput) :
    partitionWeightsStructuredEncodedType.encode (partitionWeightsForUnaryToBinary I) =
      partitionStructuredEncodedType.encode I := by
  rfl

noncomputable def partitionWeightsForUnaryToBinaryTMBackedMap :
    TMBackedCostedMap
      partitionStructuredEncodedType
      partitionWeightsStructuredEncodedType
      partitionWeightsForUnaryToBinary :=
  TMBackedCostedMap.ofEncodingEquiv
    partitionStructuredEncodedType
    partitionWeightsStructuredEncodedType
    partitionWeightsForUnaryToBinary
    (Equiv.refl partitionWeightsStructuredEncodedType.Symbol)
    (by
      intro I
      change
        partitionWeightsStructuredEncodedType.encode (partitionWeightsForUnaryToBinary I) =
          (partitionStructuredEncodedType.encode I).map id
      simp [partitionWeightsForUnaryToBinary_encode])

def partitionInputFromBinaryWeights (weights : List Nat) : PartitionInput :=
  { weights := weights }

theorem partitionInputFromBinaryWeights_encode (weights : List Nat) :
    partitionBinaryStructuredEncodedType.encode (partitionInputFromBinaryWeights weights) =
      partitionWeightsBinaryStructuredEncodedType.encode weights := by
  rfl

noncomputable def partitionInputFromBinaryWeightsTMBackedMap :
    TMBackedCostedMap
      partitionWeightsBinaryStructuredEncodedType
      partitionBinaryStructuredEncodedType
      partitionInputFromBinaryWeights :=
  TMBackedCostedMap.ofEncodingEquiv
    partitionWeightsBinaryStructuredEncodedType
    partitionBinaryStructuredEncodedType
    partitionInputFromBinaryWeights
    (Equiv.refl partitionWeightsBinaryStructuredEncodedType.Symbol)
    (by
      intro weights
      change
        partitionBinaryStructuredEncodedType.encode
            (partitionInputFromBinaryWeights weights) =
          (partitionWeightsBinaryStructuredEncodedType.encode weights).map id
      simp [partitionInputFromBinaryWeights_encode])

theorem partitionWeightsStructuredToBinary_tm_polytime :
    TMPolyTimeMap
      partitionWeightsStructuredEncodedType
      partitionWeightsBinaryStructuredEncodedType
      id := by
  have hMap := TMPolyTimeMap.list_map Knapsack.unaryNatToBinaryNat_tm_polytime
  convert hMap using 1
  funext weights
  exact (List.map_id weights).symm

theorem partitionStructuredToBinary_tm_polytime :
    TMPolyTimeMap
      partitionStructuredEncodedType
      partitionBinaryStructuredEncodedType
      id := by
  have hWeightsFrom := partitionWeightsForUnaryToBinaryTMBackedMap.tm_polytime
  have hWeights :
      TMPolyTimeMap
        partitionStructuredEncodedType
        partitionWeightsBinaryStructuredEncodedType
        partitionWeightsForUnaryToBinary := by
    have hComp :=
      TMPolyTimeMap.comp partitionWeightsStructuredToBinary_tm_polytime hWeightsFrom
    simpa [Function.comp] using hComp
  have hOut :=
    TMPolyTimeMap.comp partitionInputFromBinaryWeightsTMBackedMap.tm_polytime hWeights
  simpa [Function.comp, partitionWeightsForUnaryToBinary, partitionInputFromBinaryWeights]
    using hOut

noncomputable def partitionStructuredToBinaryStructuredTMKarpReduction :
    TMKarpReduction
      partitionStructuredDecisionProblem
      partitionBinaryStructuredDecisionProblem where
  f := id
  polytime := partitionStructuredToBinary_tm_polytime
  correct := by
    intro I
    rfl

end Partition
end Karp21
end ComplexityReduction
