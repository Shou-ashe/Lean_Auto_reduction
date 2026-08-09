/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.AxiomGate
import ComplexityReduction.Domain.PartitionToTwoDisjointBoundedPathsSemantics
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.GraphStructuredTM.Range
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.ListNat
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.UnaryToBinary
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipPartitionBinary
import ComplexityReduction.Problems.Karp21.GraphAtoms
import Mathlib.Tactic

/-!
Production binary-Partition to Two Disjoint Bounded Paths reduction packet.
-/

namespace ComplexityReduction
namespace Domain
namespace PartitionToTwoDisjointBoundedPaths

open Encoding
open Certificate
open Program
open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph
open PartitionToTwoDisjointBoundedPathsCore

abbrev source : PresentedProblem :=
  Presentation.PartitionBinary.structuredProblem

abbrev target : PresentedProblem :=
  Presentation.TwoDisjointBoundedPaths.presentedProblem

def executable (input : source.Instance) : target.Instance :=
  PartitionToTwoDisjointBoundedPathsCore.executable input

theorem executableCorrect :
    Agent.Hardness.Authoring.ExecutableSemanticProof source target executable := by
  intro input
  change Partition input ↔
    Presentation.TwoDisjointBoundedPaths.IsYes
      (PartitionToTwoDisjointBoundedPathsCore.executable input)
  exact PartitionToTwoDisjointBoundedPathsCore.executableCorrect input

abbrev sourceEncodedType : EncodedType :=
  partitionBinaryStructuredEncodedType

abbrev binaryNatListEncodedType : EncodedType :=
  EncodedType.list EncodedType.binaryNat

abbrev unaryNatListEncodedType : EncodedType :=
  EncodedType.list EncodedType.nat

abbrev edgeEncodedType : EncodedType :=
  edgeStructuredEncodedType

abbrev edgeListEncodedType : EncodedType :=
  edgeListStructuredEncodedType

theorem stageEdge_tmPolyTime :
    TMPolyTimeMap EncodedType.nat edgeEncodedType
      PartitionToTwoDisjointBoundedPathsCore.stageEdge := by
  have identity : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have successor : TMPolyTimeMap EncodedType.nat EncodedType.nat
      (fun stage : Nat => stage + 1) := by
    simpa [Nat.succ_eq_add_one] using natSuccTMBackedMap.tm_polytime
  simpa [PartitionToTwoDisjointBoundedPathsCore.stageEdge, edgeEncodedType] using
    TMPolyTimeMap.prod_mk identity successor

def heavyCost (weight : Nat) : Nat :=
  weight + weight + 1

theorem heavyCost_tmPolyTime :
    TMPolyTimeMap EncodedType.binaryNat EncodedType.binaryNat heavyCost := by
  have pair : TMPolyTimeMap EncodedType.binaryNat
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      (fun weight : Nat => (weight, weight)) :=
    TMPolyTimeMap.prod_mk (TMPolyTimeMap.id EncodedType.binaryNat)
      (TMPolyTimeMap.id EncodedType.binaryNat)
  have doubled : TMPolyTimeMap EncodedType.binaryNat EncodedType.binaryNat
      (fun weight : Nat => weight + weight) := by
    have composed := TMPolyTimeMap.comp Karp21.Knapsack.binaryNatAdd_tm_polytime pair
    simpa [Function.comp] using composed
  have composed := TMPolyTimeMap.comp Karp21.Knapsack.binaryNatSucc_tm_polytime doubled
  simpa [Function.comp, heavyCost, Nat.succ_eq_add_one] using composed

def unitBinary (_stage : Nat) : Nat := 1

theorem unitBinary_tmPolyTime :
    TMPolyTimeMap EncodedType.nat EncodedType.binaryNat unitBinary :=
  TMPolyTimeMap.const EncodedType.nat EncodedType.binaryNat (1 : Nat)

def graphTupleToGraph (payload : graphTupleStructuredEncodedType.Carrier) : GraphInput where
  vertices := payload.1
  edges := payload.2.1
  directed := payload.2.2

private theorem graphTupleToGraph_encode
    (payload : graphTupleStructuredEncodedType.Carrier) :
    graphStructuredEncodedType.encode (graphTupleToGraph payload) =
      graphTupleStructuredEncodedType.encode payload := by
  rcases payload with ⟨vertices, edges, directed⟩
  rfl

private noncomputable def graphTupleToGraphTMBackedMap :
    TMBackedCostedMap graphTupleStructuredEncodedType graphStructuredEncodedType
      graphTupleToGraph :=
  TMBackedCostedMap.ofEncodingEquiv
    graphTupleStructuredEncodedType graphStructuredEncodedType graphTupleToGraph
    (Equiv.refl graphTupleStructuredEncodedType.Symbol)
    (by
      intro payload
      change graphStructuredEncodedType.encode (graphTupleToGraph payload) =
        (graphTupleStructuredEncodedType.encode payload).map id
      simp [graphTupleToGraph_encode])

def tupleToInput
    (payload : Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType.Carrier) :
    Presentation.TwoDisjointBoundedPaths.Input where
  graph := payload.1
  costs := payload.2.1
  source := payload.2.2.1
  target := payload.2.2.2.1
  bound := payload.2.2.2.2

private theorem tupleToInput_encode
    (payload : Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType.Carrier) :
    Presentation.TwoDisjointBoundedPaths.structuredEncodedType.encode
        (tupleToInput payload) =
      Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType.encode payload := by
  rcases payload with ⟨graph, costs, source, target, bound⟩
  rfl

private noncomputable def tupleToInputTMBackedMap :
    TMBackedCostedMap
      Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType
      Presentation.TwoDisjointBoundedPaths.structuredEncodedType tupleToInput :=
  TMBackedCostedMap.ofEncodingEquiv
    Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType
    Presentation.TwoDisjointBoundedPaths.structuredEncodedType tupleToInput
    (Equiv.refl Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType.Symbol)
    (by
      intro payload
      change Presentation.TwoDisjointBoundedPaths.structuredEncodedType.encode
          (tupleToInput payload) =
        (Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType.encode payload).map id
      simp [tupleToInput_encode])

private theorem executable_tmPolyTime :
    TMPolyTimeMap sourceEncodedType
      Presentation.TwoDisjointBoundedPaths.structuredEncodedType executable := by
  let X := sourceEncodedType
  have weights : TMPolyTimeMap X binaryNatListEncodedType
      (fun input : PartitionInput => input.weights) := by
    simpa [X, sourceEncodedType, binaryNatListEncodedType] using
      Karp21.Partition.partitionBinaryWeightsForMembershipTMBackedMap.tm_polytime
  have weightCount : TMPolyTimeMap X EncodedType.nat
      (fun input : PartitionInput => input.weights.length) := by
    have composed := TMPolyTimeMap.comp
      (Karp21.HittingSet.listLengthTMBackedMap EncodedType.binaryNat).tm_polytime weights
    simpa [Function.comp, binaryNatListEncodedType, X] using composed
  have stages : TMPolyTimeMap X EncodedType.nat
      (fun input : PartitionInput => stageCount input) := by
    have composed := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime weightCount
    simpa [Function.comp, stageCount, Nat.succ_eq_add_one, X] using composed
  have stageRange : TMPolyTimeMap X unaryNatListEncodedType
      (fun input : PartitionInput => List.range (stageCount input)) := by
    have composed := TMPolyTimeMap.comp natRange_tm_polytime stages
    simpa [Function.comp, unaryNatListEncodedType, X] using composed
  have oneEdgeCopy : TMPolyTimeMap X edgeListEncodedType
      (fun input : PartitionInput => stageEdges input) := by
    have mapped := TMPolyTimeMap.comp (TMPolyTimeMap.list_map stageEdge_tmPolyTime) stageRange
    simpa [Function.comp, stageEdges, edgeListEncodedType, unaryNatListEncodedType, X]
      using mapped
  have edgeCopies : TMPolyTimeMap X
      (EncodedType.prod edgeListEncodedType edgeListEncodedType)
      (fun input : PartitionInput => (stageEdges input, stageEdges input)) :=
    TMPolyTimeMap.prod_mk oneEdgeCopy oneEdgeCopy
  have edges : TMPolyTimeMap X edgeListEncodedType
      (fun input : PartitionInput => ladderEdges input) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append edgeEncodedType) edgeCopies
    simpa [Function.comp, ladderEdges, edgeListEncodedType, X] using composed
  have zeroBinary : TMPolyTimeMap X EncodedType.binaryNat
      (fun _ : PartitionInput => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have zeroSingleton : TMPolyTimeMap X binaryNatListEncodedType
      (fun _ : PartitionInput => [(0 : Nat)]) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton EncodedType.binaryNat) zeroBinary
    simpa [Function.comp, binaryNatListEncodedType, X] using composed
  have augmentedInput : TMPolyTimeMap X
      (EncodedType.prod binaryNatListEncodedType binaryNatListEncodedType)
      (fun input : PartitionInput => (input.weights, [(0 : Nat)])) :=
    TMPolyTimeMap.prod_mk weights zeroSingleton
  have augmented : TMPolyTimeMap X binaryNatListEncodedType
      (fun input : PartitionInput => augmentedWeights input) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append EncodedType.binaryNat) augmentedInput
    simpa [Function.comp, augmentedWeights, binaryNatListEncodedType, X] using composed
  have heavy : TMPolyTimeMap X binaryNatListEncodedType
      (fun input : PartitionInput => heavyCosts input) := by
    have composed := TMPolyTimeMap.comp (TMPolyTimeMap.list_map heavyCost_tmPolyTime) augmented
    simpa [Function.comp, heavyCosts, heavyCost, binaryNatListEncodedType, X]
      using composed
  have light : TMPolyTimeMap X binaryNatListEncodedType
      (fun input : PartitionInput => lightCosts input) := by
    have composed := TMPolyTimeMap.comp (TMPolyTimeMap.list_map unitBinary_tmPolyTime) stageRange
    change TMPolyTimeMap X binaryNatListEncodedType
      (fun input : PartitionInput =>
        (List.range (stageCount input)).map unitBinary)
    simpa only [Function.comp] using composed
  have costsInput : TMPolyTimeMap X
      (EncodedType.prod binaryNatListEncodedType binaryNatListEncodedType)
      (fun input : PartitionInput => (heavyCosts input, lightCosts input)) :=
    TMPolyTimeMap.prod_mk heavy light
  have costs : TMPolyTimeMap X binaryNatListEncodedType
      (fun input : PartitionInput => ladderCosts input) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_append EncodedType.binaryNat) costsInput
    simpa [Function.comp, ladderCosts, binaryNatListEncodedType, X] using composed
  have vertexCount : TMPolyTimeMap X EncodedType.nat
      (fun input : PartitionInput => stageCount input + 1) := by
    have composed := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime stages
    simpa [Function.comp, Nat.succ_eq_add_one, X] using composed
  have trueFlag : TMPolyTimeMap X EncodedType.bool
      (fun _ : PartitionInput => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have graphPayload : TMPolyTimeMap X graphPayloadStructuredEncodedType
      (fun input : PartitionInput => (ladderEdges input, true)) := by
    simpa [graphPayloadStructuredEncodedType] using TMPolyTimeMap.prod_mk edges trueFlag
  have graphTuple : TMPolyTimeMap X graphTupleStructuredEncodedType
      (fun input : PartitionInput => (stageCount input + 1, (ladderEdges input, true))) := by
    simpa [graphTupleStructuredEncodedType] using TMPolyTimeMap.prod_mk vertexCount graphPayload
  have graph : TMPolyTimeMap X graphStructuredEncodedType
      (fun input : PartitionInput => ladderGraph input) := by
    have composed := TMPolyTimeMap.comp graphTupleToGraphTMBackedMap.tm_polytime graphTuple
    simpa [Function.comp, graphTupleToGraph, ladderGraph, X] using composed
  have weightSum : TMPolyTimeMap X EncodedType.binaryNat
      (fun input : PartitionInput => input.weights.sum) := by
    have composed := TMPolyTimeMap.comp
      Karp21.Knapsack.binaryNatListSum_tm_polytime_sum weights
    simpa [Function.comp, X] using composed
  have stagesBinary : TMPolyTimeMap X EncodedType.binaryNat
      (fun input : PartitionInput => stageCount input) := by
    have composed := TMPolyTimeMap.comp
      Karp21.Knapsack.unaryNatToBinaryNat_tm_polytime stages
    simpa [Function.comp, X] using composed
  have boundInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      (fun input : PartitionInput => (stageCount input, input.weights.sum)) :=
    TMPolyTimeMap.prod_mk stagesBinary weightSum
  have bound : TMPolyTimeMap X EncodedType.binaryNat
      (fun input : PartitionInput => stageCount input + input.weights.sum) := by
    have composed := TMPolyTimeMap.comp Karp21.Knapsack.binaryNatAdd_tm_polytime boundInput
    simpa [Function.comp, X] using composed
  have sourceZero : TMPolyTimeMap X EncodedType.nat
      (fun _ : PartitionInput => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have targetBound : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.binaryNat)
      (fun input : PartitionInput => (stageCount input,
        stageCount input + input.weights.sum)) :=
    TMPolyTimeMap.prod_mk stages bound
  have sourceTail : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.binaryNat))
      (fun input : PartitionInput =>
        ((0 : Nat), (stageCount input, stageCount input + input.weights.sum))) :=
    TMPolyTimeMap.prod_mk sourceZero targetBound
  have costTail : TMPolyTimeMap X
      (EncodedType.prod binaryNatListEncodedType
        (EncodedType.prod EncodedType.nat
          (EncodedType.prod EncodedType.nat EncodedType.binaryNat)))
      (fun input : PartitionInput =>
        (ladderCosts input,
          ((0 : Nat), (stageCount input, stageCount input + input.weights.sum)))) :=
    TMPolyTimeMap.prod_mk costs sourceTail
  have outputTuple : TMPolyTimeMap X
      Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType
      (fun input : PartitionInput =>
        (ladderGraph input,
          (ladderCosts input,
            ((0 : Nat), (stageCount input, stageCount input + input.weights.sum))))) := by
    simpa [Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType,
      binaryNatListEncodedType] using TMPolyTimeMap.prod_mk graph costTail
  have output := TMPolyTimeMap.comp tupleToInputTMBackedMap.tm_polytime outputTuple
  simpa [Function.comp, tupleToInput, executable,
    PartitionToTwoDisjointBoundedPathsCore.executable, X] using output

theorem executableDirectTM :
    Agent.Hardness.Authoring.ExecutableDirectTMEvidence source target executable := by
  simpa [source, target, sourceEncodedType,
    Presentation.PartitionBinary.structuredProblem,
    Presentation.PartitionBinary.structuredPresentation,
    Presentation.TwoDisjointBoundedPaths.presentedProblem,
    Presentation.TwoDisjointBoundedPaths.structuredPresentation] using executable_tmPolyTime

/-- Exact atomic primitive for the audited production lower-bound edge. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def primitive :
    Primitive source.representation target.representation :=
  Primitive.ofTMPolyTime executable executableDirectTM

/-- Registered Partition-to-two-paths edge used by completeness transport. -/
@[complexity_reduction_ir_typed_edge, complexity_reduction_ir_component_shared_gadget]
noncomputable def certifiedReduction : CertifiedReduction source target where
  program := .atom primitive
  correct := by
    intro input
    change source.accepts input ↔ target.accepts (primitive.run input)
    rw [show primitive.run input = executable input by rfl]
    exact executableCorrect input

@[complexity_reduction_ir_hardness_program_reduction_template]
def template : Agent.Hardness.Authoring.ProgramIndexedReductionTemplate
    .finalComposition source target executable executableDirectTM executableCorrect :=
  ⟨trivial⟩

end PartitionToTwoDisjointBoundedPaths
end Domain
end ComplexityReduction

assert_standard_axioms
  ComplexityReduction.Domain.PartitionToTwoDisjointBoundedPaths.stageEdge_tmPolyTime,
  ComplexityReduction.Domain.PartitionToTwoDisjointBoundedPaths.heavyCost_tmPolyTime,
  ComplexityReduction.Domain.PartitionToTwoDisjointBoundedPaths.executableDirectTM,
  ComplexityReduction.Domain.PartitionToTwoDisjointBoundedPaths.primitive,
  ComplexityReduction.Domain.PartitionToTwoDisjointBoundedPaths.certifiedReduction,
  ComplexityReduction.Domain.PartitionToTwoDisjointBoundedPaths.template
