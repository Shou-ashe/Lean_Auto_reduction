import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.Part2
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.StructuredTM.PairInstructions
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.ExactWrapper

namespace ComplexityReduction
namespace Karp21
namespace MaxCut

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Direct TM-backed structured assembly for the faithful Partition-to-MaxCut
complete-graph route.
-/

def partitionWeightsOfInput (I : PartitionInput) : List Nat :=
  I.weights

theorem partitionWeightsOfInput_encode (I : PartitionInput) :
    partitionWeightsStructuredEncodedType.encode (partitionWeightsOfInput I) =
      partitionStructuredEncodedType.encode I := by
  rfl

noncomputable def partitionWeightsOfInputTMBackedMap :
    TMBackedCostedMap
      partitionStructuredEncodedType
      partitionWeightsStructuredEncodedType
      partitionWeightsOfInput :=
  TMBackedCostedMap.ofEncodingEquiv
    partitionStructuredEncodedType partitionWeightsStructuredEncodedType
    partitionWeightsOfInput
    (Equiv.refl partitionWeightsStructuredEncodedType.Symbol)
    (by
      intro I
      change
        partitionWeightsStructuredEncodedType.encode (partitionWeightsOfInput I) =
          (partitionStructuredEncodedType.encode I).map id
      simp [partitionWeightsOfInput_encode])

def maxCutGraphTupleToGraph (p : graphTupleStructuredEncodedType.Carrier) :
    GraphInput where
  vertices := p.1
  edges := p.2.1
  directed := p.2.2

theorem maxCutGraphTupleToGraph_encode (p : graphTupleStructuredEncodedType.Carrier) :
    graphStructuredEncodedType.encode (maxCutGraphTupleToGraph p) =
      graphTupleStructuredEncodedType.encode p := by
  rcases p with ⟨vertices, edges, directed⟩
  rfl

noncomputable def maxCutGraphTupleToGraphTMBackedMap :
    TMBackedCostedMap
      graphTupleStructuredEncodedType
      graphStructuredEncodedType
      maxCutGraphTupleToGraph :=
  TMBackedCostedMap.ofEncodingEquiv
    graphTupleStructuredEncodedType graphStructuredEncodedType maxCutGraphTupleToGraph
    (Equiv.refl graphTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change graphStructuredEncodedType.encode (maxCutGraphTupleToGraph p) =
        (graphTupleStructuredEncodedType.encode p).map id
      simp [maxCutGraphTupleToGraph_encode])

def maxCutTupleToMaxCutInput (p : maxCutTupleStructuredEncodedType.Carrier) :
    MaxCutInput where
  graph := p.1
  threshold := p.2

theorem maxCutTupleToMaxCutInput_encode (p : maxCutTupleStructuredEncodedType.Carrier) :
    maxCutStructuredEncodedType.encode (maxCutTupleToMaxCutInput p) =
      maxCutTupleStructuredEncodedType.encode p := by
  rcases p with ⟨graph, threshold⟩
  rfl

noncomputable def maxCutTupleToMaxCutInputTMBackedMap :
    TMBackedCostedMap
      maxCutTupleStructuredEncodedType
      maxCutStructuredEncodedType
      maxCutTupleToMaxCutInput :=
  TMBackedCostedMap.ofEncodingEquiv
    maxCutTupleStructuredEncodedType maxCutStructuredEncodedType maxCutTupleToMaxCutInput
    (Equiv.refl maxCutTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change maxCutStructuredEncodedType.encode (maxCutTupleToMaxCutInput p) =
        (maxCutTupleStructuredEncodedType.encode p).map id
      simp [maxCutTupleToMaxCutInput_encode])

def partitionToMaxCutStructuredTMGraph (I : PartitionInput) : GraphInput where
  vertices := I.weights.length
  edges :=
    maxCutEdgesFromBlockInstructions
      (maxCutEdgeBlockInstructionsFromWeights I.weights)
  directed := false

def partitionToMaxCutStructuredTMMap (I : PartitionInput) : MaxCutInput where
  graph := partitionToMaxCutStructuredTMGraph I
  threshold := Partition.natListSum I.weights * Partition.natListSum I.weights

theorem partitionToMaxCutStructuredTMMap_eq_textbookMap (I : PartitionInput) :
    partitionToMaxCutStructuredTMMap I = textbookMap I := by
  cases I with
  | mk weights =>
      simp [partitionToMaxCutStructuredTMMap, partitionToMaxCutStructuredTMGraph,
        textbookMap, maxCutTextbookEdgesFromWeights_eq_textbookEdges,
        Partition.natListSum_eq_sum]

theorem partitionToMaxCutStructuredTMMap_inputSize_le_partition_poly
    (I : PartitionInput) :
    maxCutStructuredEncodedType.inputSize (partitionToMaxCutStructuredTMMap I) ≤
      1000 * (partitionStructuredEncodedType.inputSize I) ^ 4 + 1000 := by
  rw [partitionToMaxCutStructuredTMMap_eq_textbookMap]
  exact maxCutStructured_inputSize_textbookMap_le_partition_poly I

theorem partitionToMaxCutStructuredTMMap_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : PartitionInput => partitionStructuredEncodedType.inputSize I)
      (fun J : MaxCutInput => maxCutStructuredEncodedType.inputSize J)
      partitionToMaxCutStructuredTMMap := by
  refine PolynomialSizeBound.intro_with 4 1000 1000 ?_
  intro I
  exact partitionToMaxCutStructuredTMMap_inputSize_le_partition_poly I

theorem partitionToMaxCutStructuredTMGraph_tm_polytime :
    TMPolyTimeMap
      partitionStructuredEncodedType
      graphStructuredEncodedType
      partitionToMaxCutStructuredTMGraph := by
  let X := partitionStructuredEncodedType
  have hWeights :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType
        (fun I : X.Carrier => I.weights) := by
    simpa [X, partitionWeightsOfInput] using
      partitionWeightsOfInputTMBackedMap.tm_polytime
  have hVertices :
      TMPolyTimeMap X EncodedType.nat
        (fun I : X.Carrier => I.weights.length) := by
    have hComp :=
      TMPolyTimeMap.comp (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime
        hWeights
    simpa [Function.comp, partitionWeightsStructuredEncodedType, X] using hComp
  have hEdges :
      TMPolyTimeMap X edgeListStructuredEncodedType
        (fun I : X.Carrier =>
          maxCutEdgesFromBlockInstructions
            (maxCutEdgeBlockInstructionsFromWeights I.weights)) := by
    have hComp := TMPolyTimeMap.comp maxCutTextbookEdgesFromWeights_tm_polytime hWeights
    simpa [Function.comp, X] using hComp
  have hDirected :
      TMPolyTimeMap X EncodedType.bool
        (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hPayload :
      TMPolyTimeMap X graphPayloadStructuredEncodedType
        (fun I : X.Carrier =>
          (maxCutEdgesFromBlockInstructions
            (maxCutEdgeBlockInstructionsFromWeights I.weights), false)) :=
    TMPolyTimeMap.prod_mk hEdges hDirected
  have hTuple :
      TMPolyTimeMap X graphTupleStructuredEncodedType
        (fun I : X.Carrier =>
          (I.weights.length,
            (maxCutEdgesFromBlockInstructions
              (maxCutEdgeBlockInstructionsFromWeights I.weights), false))) :=
    TMPolyTimeMap.prod_mk hVertices hPayload
  have hGraph :=
    TMPolyTimeMap.comp maxCutGraphTupleToGraphTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, maxCutGraphTupleToGraph, partitionToMaxCutStructuredTMGraph, X]
    using hGraph

theorem partitionToMaxCutStructured_tm_polytime :
    TMPolyTimeMap
      partitionStructuredEncodedType
      maxCutStructuredEncodedType
      partitionToMaxCutStructuredTMMap := by
  let X := partitionStructuredEncodedType
  have hWeights :
      TMPolyTimeMap X partitionWeightsStructuredEncodedType
        (fun I : X.Carrier => I.weights) := by
    simpa [X, partitionWeightsOfInput] using
      partitionWeightsOfInputTMBackedMap.tm_polytime
  have hGraph :
      TMPolyTimeMap X graphStructuredEncodedType
        partitionToMaxCutStructuredTMGraph := by
    simpa [X] using partitionToMaxCutStructuredTMGraph_tm_polytime
  have hSum :
      TMPolyTimeMap X EncodedType.nat
        (fun I : X.Carrier => Partition.natListSum I.weights) := by
    have hComp := TMPolyTimeMap.comp Partition.natListSum_tm_polytime hWeights
    simpa [Function.comp, X] using hComp
  have hThresholdInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun I : X.Carrier =>
          (Partition.natListSum I.weights, Partition.natListSum I.weights)) :=
    TMPolyTimeMap.prod_mk hSum hSum
  have hThreshold :
      TMPolyTimeMap X EncodedType.nat
        (fun I : X.Carrier =>
          Partition.natListSum I.weights * Partition.natListSum I.weights) := by
    have hComp := TMPolyTimeMap.comp TMPolyTimeMap.nat_mul hThresholdInput
    simpa [Function.comp, X] using hComp
  have hTuple :
      TMPolyTimeMap X maxCutTupleStructuredEncodedType
        (fun I : X.Carrier =>
          (partitionToMaxCutStructuredTMGraph I,
            Partition.natListSum I.weights * Partition.natListSum I.weights)) :=
    TMPolyTimeMap.prod_mk hGraph hThreshold
  have hMaxCut :=
    TMPolyTimeMap.comp maxCutTupleToMaxCutInputTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, maxCutTupleToMaxCutInput, partitionToMaxCutStructuredTMMap, X]
    using hMaxCut

noncomputable def partitionToMaxCutStructuredTMBackedMap :
    TMBackedCostedMap
      partitionStructuredEncodedType
      maxCutStructuredEncodedType
      partitionToMaxCutStructuredTMMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      partitionToMaxCutStructuredTMMap_polynomialSizeBound
  tm_polytime := partitionToMaxCutStructured_tm_polytime

theorem partitionToMaxCutStructuredTMMap_correct (I : PartitionInput) :
    partitionStructuredDecisionProblem.isYes I ↔
      maxCutStructuredDecisionProblem.isYes (partitionToMaxCutStructuredTMMap I) := by
  rw [partitionToMaxCutStructuredTMMap_eq_textbookMap]
  simpa [partitionStructuredDecisionProblem, maxCutStructuredDecisionProblem]
    using textbookMap_correct I

noncomputable def partitionToMaxCutStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      partitionStructuredDecisionProblem
      maxCutStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    partitionToMaxCutStructuredTMBackedMap
    (by
      intro I
      exact partitionToMaxCutStructuredTMMap_correct I)

/--
Public P16c structured finite-alphabet Partition-to-MaxCut reduction, projected
from the direct TM-backed witness.
-/
noncomputable def partitionToMaxCutStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      partitionStructuredDecisionProblem
      maxCutStructuredDecisionProblem :=
  partitionToMaxCutStructuredTMBackedKarpReduction.toCostedKarpReduction

/-- Direct TM-facing structured Partition-to-MaxCut reduction. -/
noncomputable def partitionToMaxCutStructuredTMKarpReduction :
    TMKarpReduction
      partitionStructuredDecisionProblem
      maxCutStructuredDecisionProblem :=
  partitionToMaxCutStructuredTMBackedKarpReduction.toTMKarpReduction

end MaxCut
end Karp21
end ComplexityReduction
