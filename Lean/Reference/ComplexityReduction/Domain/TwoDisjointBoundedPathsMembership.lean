/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.Agent.Hardness.FiniteWitnessNative
import ComplexityReduction.Domain.NodeDeletionBipartiteMembership
import ComplexityReduction.Presentation.TwoDisjointBoundedPaths
import ComplexityReduction.Problems.Karp21.HittingSetStandardTM
import ComplexityReduction.Program.ContextListAll
import ComplexityReduction.Program.PairOfPaths
import ComplexityReduction.Program.PairOfPathsCertificate
import Mathlib.Tactic

/-!
Native unary-nat-list NP membership for Two Disjoint Bounded Paths.

The flat certificate contains two fixed-width edge-index path blocks.  The
checker validates the complete public input contract and then checks two
simple directed paths, their individual binary costs, and edge disjointness.
-/

namespace ComplexityReduction
namespace Domain
namespace TwoDisjointBoundedPathsMembership

open Encoding
open Certificate
open Program
open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.Karp21
open ComplexityReduction.Agent.Hardness.FiniteWitness
open ComplexityReduction.Agent.Hardness.FiniteWitnessNative

abbrev problem : PresentedProblem :=
  Presentation.TwoDisjointBoundedPaths.presentedProblem

abbrev certificateEncodedType : EncodedType := setStructuredEncodedType

abbrev natListEncodedType : EncodedType := natListPresentation.encodedType

abbrev binaryNatListEncodedType : EncodedType :=
  Program.PairOfPaths.binaryNatListEncodedType

abbrev edgeEncodedType : EncodedType := edgeStructuredEncodedType

abbrev edgeListEncodedType : EncodedType := edgeListStructuredEncodedType

/-! ### Positive aligned costs -/

/-- One binary cost is strictly positive.  The Boolean context is inert. -/
def costPositiveBool (input : Bool × Nat) : Bool :=
  Knapsack.binaryNatLeBool (1, input.2)

theorem costPositiveBool_eq_true_iff (context : Bool) (cost : Nat) :
    costPositiveBool (context, cost) = true ↔ 0 < cost := by
  rw [costPositiveBool, Knapsack.binaryNatLeBool_eq_true_iff]
  omega

theorem costPositiveBool_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.bool EncodedType.binaryNat)
      EncodedType.bool costPositiveBool := by
  let X := EncodedType.prod EncodedType.bool EncodedType.binaryNat
  have one : TMPolyTimeMap X EncodedType.binaryNat
      (fun _input : Bool × Nat => (1 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (1 : Nat)
  have cost : TMPolyTimeMap X EncodedType.binaryNat
      (fun input : Bool × Nat => input.2) := by
    simpa [X] using
      TMPolyTimeMap.snd EncodedType.bool EncodedType.binaryNat
  have compareInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      (fun input : Bool × Nat => ((1 : Nat), input.2)) :=
    TMPolyTimeMap.prod_mk one cost
  have composed := TMPolyTimeMap.comp
    Knapsack.binaryNatLeBool_tm_polytime compareInput
  simpa [Function.comp, costPositiveBool, X] using composed

/-- Every aligned binary edge cost is positive. -/
def allCostsPositiveBool (costs : List Nat) : Bool :=
  ContextListAll.executable
    (C := EncodedType.bool) (X := EncodedType.binaryNat)
    costPositiveBool (true, costs)

theorem allCostsPositiveBool_eq_true_iff (costs : List Nat) :
    allCostsPositiveBool costs = true ↔ ∀ cost ∈ costs, 0 < cost := by
  rw [allCostsPositiveBool,
    ContextListAll.executable_eq_true_iff
      (C := EncodedType.bool) (X := EncodedType.binaryNat)
      costPositiveBool true costs]
  constructor
  · intro checked cost member
    exact (costPositiveBool_eq_true_iff true cost).1 (checked cost member)
  · intro positive cost member
    exact (costPositiveBool_eq_true_iff true cost).2 (positive cost member)

theorem allCostsPositiveBool_tmPolyTime :
    TMPolyTimeMap binaryNatListEncodedType EncodedType.bool
      allCostsPositiveBool := by
  let X := binaryNatListEncodedType
  have truth : TMPolyTimeMap X EncodedType.bool
      (fun _costs : List Nat => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have costs : TMPolyTimeMap X binaryNatListEncodedType id :=
    TMPolyTimeMap.id X
  have input : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool binaryNatListEncodedType)
      (fun costs : List Nat => (true, costs)) :=
    TMPolyTimeMap.prod_mk truth costs
  have all := ContextListAll.executable_tmPolyTime
    (C := EncodedType.bool) (X := EncodedType.binaryNat)
    costPositiveBool costPositiveBool_tmPolyTime
  have composed := TMPolyTimeMap.comp all input
  simpa [Function.comp, allCostsPositiveBool, binaryNatListEncodedType, X] using composed

/-! ### Flat path-pair certificate and public semantic bridges -/

/-- Decode the two fixed-width path blocks using the public edge count. -/
def certificatePair
    (input : Presentation.TwoDisjointBoundedPaths.Input)
    (certificate : List Nat) : List Nat × List Nat :=
  PairOfPathsCertificate.parsePathPair
    (input.graph.edges.length, certificate)

theorem edgeIndexChain_iff_public
    (graph : GraphInput) (source target : Nat) (path : List Nat) :
    PairOfPaths.EdgeIndexChain graph.edges source path target ↔
      Presentation.TwoDisjointBoundedPaths.EdgeChain
        graph source path target := by
  induction path generalizing source with
  | nil => rfl
  | cons index rest inductionHypothesis =>
      simp only [PairOfPaths.EdgeIndexChain,
        Presentation.TwoDisjointBoundedPaths.EdgeChain,
        Presentation.TwoDisjointBoundedPaths.edgeAt]
      rw [inductionHypothesis]

theorem edgeIndexPathBool_eq_true_iff_public
    (graph : GraphInput) (source target : Nat) (path : List Nat) :
    PairOfPaths.edgeIndexPathBool
        (graph.edges, source, target, path) = true ↔
      Presentation.TwoDisjointBoundedPaths.EdgeIndexPath
        graph source target path := by
  rw [PairOfPaths.edgeIndexPathBool_eq_true_iff]
  unfold Presentation.TwoDisjointBoundedPaths.EdgeIndexPath
  rw [edgeIndexChain_iff_public]

theorem boundedCostBool_eq_true_iff_public
    (costs : List Nat) (bound : Nat) (path : List Nat) :
    PairOfPaths.boundedCostBool (costs, bound, path) = true ↔
      Presentation.TwoDisjointBoundedPaths.pathCost costs path ≤ bound := by
  rw [PairOfPaths.boundedCostBool_eq_true_iff,
    PairOfPaths.pathCost_eq_map_sum]
  rfl

theorem pathsDisjointBool_eq_true_iff_public (left right : List Nat) :
    PairOfPaths.pathsDisjointBool (left, right) = true ↔
      Presentation.TwoDisjointBoundedPaths.EdgeDisjoint left right := by
  exact PairOfPaths.pathsDisjointBool_eq_true_iff left right

theorem pathsDisjointPairBool_eq_true_iff_public
    (pair : List Nat × List Nat) :
    PairOfPaths.pathsDisjointBool pair = true ↔
      Presentation.TwoDisjointBoundedPaths.EdgeDisjoint pair.1 pair.2 := by
  rcases pair with ⟨left, right⟩
  exact pathsDisjointBool_eq_true_iff_public left right

theorem terminalsDifferentBool_eq_true_iff (source target : Nat) :
    Bool.not (PairOfPaths.natEqBool (source, target)) = true ↔
      source ≠ target := by
  simp [PairOfPaths.natEqBool]

theorem natEqBool_eq_false_iff (source target : Nat) :
    PairOfPaths.natEqBool (source, target) = false ↔ source ≠ target := by
  simp [PairOfPaths.natEqBool]

/-! ### Exact verifier semantics -/

/-- Exact flat-certificate verifier Boolean. -/
def finiteVerify
    (input : Presentation.TwoDisjointBoundedPaths.Input)
    (certificate : List Nat) : Bool :=
  let pair := certificatePair input certificate
  graphBoolAndPair
    (input.graph.directed,
      graphBoolAndPair
        (NodeDeletionBipartiteMembership.edgesWithinBoundsBool
          ((input.graph.vertices, input.graph.vertices), input.graph.edges),
          graphBoolAndPair
            (natLtBool (input.source, input.graph.vertices),
              graphBoolAndPair
                (natLtBool (input.target, input.graph.vertices),
                  graphBoolAndPair
                    (Bool.not (PairOfPaths.natEqBool (input.source, input.target)),
                      graphBoolAndPair
                        (PairOfPaths.natEqBool
                          (input.costs.length, input.graph.edges.length),
                          graphBoolAndPair
                            (allCostsPositiveBool input.costs,
                              graphBoolAndPair
                                (PairOfPaths.edgeIndexPathBool
                                  (input.graph.edges, input.source,
                                    input.target, pair.1),
                                  graphBoolAndPair
                                    (PairOfPaths.edgeIndexPathBool
                                      (input.graph.edges, input.source,
                                        input.target, pair.2),
                                      graphBoolAndPair
                                        (PairOfPaths.boundedCostBool
                                          (input.costs, input.bound, pair.1),
                                          graphBoolAndPair
                                            (PairOfPaths.boundedCostBool
                                              (input.costs, input.bound, pair.2),
                                              PairOfPaths.pathsDisjointBool pair)))))))))))

theorem finiteVerify_eq_true_iff
    (input : Presentation.TwoDisjointBoundedPaths.Input)
    (certificate : List Nat) :
    finiteVerify input certificate = true ↔
      input.graph.directed = true ∧
        WellFormed input.graph ∧
        input.source < input.graph.vertices ∧
        input.target < input.graph.vertices ∧
        input.source ≠ input.target ∧
        input.costs.length = input.graph.edges.length ∧
        (∀ cost ∈ input.costs, 0 < cost) ∧
        Presentation.TwoDisjointBoundedPaths.EdgeIndexPath
          input.graph input.source input.target
          (certificatePair input certificate).1 ∧
        Presentation.TwoDisjointBoundedPaths.EdgeIndexPath
          input.graph input.source input.target
          (certificatePair input certificate).2 ∧
        Presentation.TwoDisjointBoundedPaths.pathCost input.costs
            (certificatePair input certificate).1 ≤ input.bound ∧
        Presentation.TwoDisjointBoundedPaths.pathCost input.costs
            (certificatePair input certificate).2 ≤ input.bound ∧
        Presentation.TwoDisjointBoundedPaths.EdgeDisjoint
          (certificatePair input certificate).1
          (certificatePair input certificate).2 := by
  simp [finiteVerify, graphBoolAndPair_eq_true_iff,
    NodeDeletionBipartiteMembership.edgesWithinBoundsBool_eq_true_iff,
    natLtBool_eq_true_iff, PairOfPaths.natEqBool_eq_true_iff,
    natEqBool_eq_false_iff,
    allCostsPositiveBool_eq_true_iff,
    edgeIndexPathBool_eq_true_iff_public,
    boundedCostBool_eq_true_iff_public,
    pathsDisjointPairBool_eq_true_iff_public,
    WellFormed, EdgeWithinBounds]

/-- Soundness against the exact public finite semantics. -/
theorem finiteVerify_sound
    (input : Presentation.TwoDisjointBoundedPaths.Input)
    (certificate : List Nat)
    (accepted : finiteVerify input certificate = true) :
    Presentation.TwoDisjointBoundedPaths.IsYes input := by
  rcases (finiteVerify_eq_true_iff input certificate).1 accepted with
    ⟨directed, wellFormed, sourceBound, targetBound, terminalsDifferent,
      costLength, positiveCosts, leftPath, rightPath, leftCost, rightCost,
      disjoint⟩
  exact ⟨directed, wellFormed, sourceBound, targetBound, terminalsDifferent,
    costLength, positiveCosts,
    (certificatePair input certificate).1,
    (certificatePair input certificate).2,
    leftPath, rightPath, leftCost, rightCost, disjoint⟩

private theorem edgeChain_indices_bound
    (graph : GraphInput) (source target : Nat) (path : List Nat)
    (chain : Presentation.TwoDisjointBoundedPaths.EdgeChain
      graph source path target) :
    ∀ index ∈ path, index < graph.edges.length := by
  induction path generalizing source with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rcases chain with ⟨headBound, _sourceMatch, tailChain⟩
      intro index member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact headBound
      · exact inductionHypothesis
          (source := (Presentation.TwoDisjointBoundedPaths.edgeAt graph head).2)
          tailChain index member

theorem path_length_le_edgeCount
    (graph : GraphInput) (source target : Nat) (path : List Nat)
    (pathProof : Presentation.TwoDisjointBoundedPaths.EdgeIndexPath
      graph source target path) :
    path.length ≤ graph.edges.length := by
  classical
  rcases pathProof with ⟨nodup, chain⟩
  have bounds := edgeChain_indices_bound graph source target path chain
  have subset : path.toFinset ⊆ Finset.range graph.edges.length := by
    intro index member
    have listMember : index ∈ path := by simpa using member
    simpa using bounds index listMember
  have cardBound := Finset.card_le_card subset
  simpa [List.toFinset_card_of_nodup nodup] using cardBound

/-- Completeness using the canonical fixed-width pair certificate. -/
theorem finiteVerify_complete
    (input : Presentation.TwoDisjointBoundedPaths.Input)
    (yes : Presentation.TwoDisjointBoundedPaths.IsYes input) :
    ∃ certificate : List Nat, finiteVerify input certificate = true := by
  rcases yes with
    ⟨directed, wellFormed, sourceBound, targetBound, terminalsDifferent,
      costLength, positiveCosts, left, right, leftPath, rightPath,
      leftCost, rightCost, disjoint⟩
  have leftLength := path_length_le_edgeCount
    input.graph input.source input.target left leftPath
  have rightLength := path_length_le_edgeCount
    input.graph input.source input.target right rightPath
  let certificate := PairOfPathsCertificate.certificate
    input.graph.edges.length left right
  have pairEquality : certificatePair input certificate = (left, right) := by
    simpa [certificatePair, certificate] using
      PairOfPathsCertificate.parsePathPair_certificate
        input.graph.edges.length left right leftLength rightLength
  refine ⟨certificate, (finiteVerify_eq_true_iff input certificate).2 ?_⟩
  rw [pairEquality]
  exact ⟨directed, wellFormed, sourceBound, targetBound, terminalsDifferent,
    costLength, positiveCosts, leftPath, rightPath, leftCost, rightCost, disjoint⟩

/-! ### Polynomial canonical-certificate bound -/

theorem pathBlock_values_lt
    (edgeCount : Nat) (path : List Nat)
    (lengthBound : path.length ≤ edgeCount)
    (indexBounds : ∀ index ∈ path, index < edgeCount) :
    ∀ value ∈ PairOfPathsCertificate.pathBlock edgeCount path,
      value < edgeCount + 1 := by
  intro value member
  change value ∈
    path.length ::
      (path ++ List.replicate (edgeCount - path.length) 0) at member
  rcases List.mem_cons.mp member with equality | tailMember
  · subst value
    omega
  rcases List.mem_append.mp tailMember with pathMember | paddingMember
  · exact (indexBounds value pathMember).trans_le (Nat.le_succ edgeCount)
  · have equality : value = 0 := by
      simpa using (List.mem_replicate.mp paddingMember).2
    subst value
    omega

theorem certificate_values_lt
    (edgeCount : Nat) (left right : List Nat)
    (leftLength : left.length ≤ edgeCount)
    (rightLength : right.length ≤ edgeCount)
    (leftBounds : ∀ index ∈ left, index < edgeCount)
    (rightBounds : ∀ index ∈ right, index < edgeCount) :
    ∀ value ∈ PairOfPathsCertificate.certificate edgeCount left right,
      value < edgeCount + 1 := by
  intro value member
  rcases List.mem_append.mp member with leftMember | rightMember
  · exact pathBlock_values_lt edgeCount left leftLength leftBounds value leftMember
  · exact pathBlock_values_lt edgeCount right rightLength rightBounds value rightMember

theorem structured_inputSize_eq
    (input : Presentation.TwoDisjointBoundedPaths.Input) :
    Presentation.TwoDisjointBoundedPaths.structuredEncodedType.inputSize input =
      graphStructuredEncodedType.inputSize input.graph +
        (EncodedType.list EncodedType.binaryNat).inputSize input.costs +
        input.source + input.target +
        EncodedType.binaryNat.inputSize input.bound + 6 := by
  change Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType.inputSize
      (input.graph,
        (input.costs, (input.source, (input.target, input.bound)))) = _
  simp [Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType,
    binaryNatListEncodedType, PairOfPaths.binaryNatListEncodedType]
  omega

theorem graph_inputSize_le_structured_inputSize
    (input : Presentation.TwoDisjointBoundedPaths.Input) :
    graphStructuredEncodedType.inputSize input.graph ≤
      Presentation.TwoDisjointBoundedPaths.structuredEncodedType.inputSize input := by
  rw [structured_inputSize_eq]
  omega

theorem certificate_inputSize_le_poly
    (input : Presentation.TwoDisjointBoundedPaths.Input)
    (left right : List Nat)
    (leftPath : Presentation.TwoDisjointBoundedPaths.EdgeIndexPath
      input.graph input.source input.target left)
    (rightPath : Presentation.TwoDisjointBoundedPaths.EdgeIndexPath
      input.graph input.source input.target right) :
    certificateEncodedType.inputSize
        (PairOfPathsCertificate.certificate
          input.graph.edges.length left right) ≤
      20 *
          (Presentation.TwoDisjointBoundedPaths.structuredEncodedType.inputSize input) ^ 2 +
        20 := by
  let edgeCount := input.graph.edges.length
  let inputSize :=
    Presentation.TwoDisjointBoundedPaths.structuredEncodedType.inputSize input
  have leftLength := path_length_le_edgeCount
    input.graph input.source input.target left leftPath
  have rightLength := path_length_le_edgeCount
    input.graph input.source input.target right rightPath
  have leftBounds := edgeChain_indices_bound
    input.graph input.source input.target left leftPath.2
  have rightBounds := edgeChain_indices_bound
    input.graph input.source input.target right rightPath.2
  have values := certificate_values_lt edgeCount left right
    leftLength rightLength leftBounds rightBounds
  have certificateSize :=
    ComplexityReduction.Problems.Karp21.HittingSetStandardTM.boundedNatList_inputSize_le
      (edgeCount + 1)
      (PairOfPathsCertificate.certificate edgeCount left right) values
  have certificateLength :
      (PairOfPathsCertificate.certificate edgeCount left right).length =
        2 * (edgeCount + 1) := by
    rw [PairOfPathsCertificate.certificate, List.length_append,
      PairOfPathsCertificate.pathBlock_length edgeCount left leftLength,
      PairOfPathsCertificate.pathBlock_length edgeCount right rightLength]
    omega
  have edgeListLength : edgeCount ≤
      edgeListStructuredEncodedType.inputSize input.graph.edges := by
    simpa [edgeCount, edgeListEncodedType, edgeEncodedType] using
      Clique.encodedList_length_le_inputSize edgeEncodedType input.graph.edges
  have edgeSuccSuccGraph : edgeCount + 2 ≤
      graphStructuredEncodedType.inputSize input.graph := by
    rw [ComplexityReduction.Karp21.VertexCover.graphStructured_inputSize_eq]
    omega
  have graphSize : graphStructuredEncodedType.inputSize input.graph ≤ inputSize := by
    simpa [inputSize] using graph_inputSize_le_structured_inputSize input
  have edgeSuccSucc : edgeCount + 2 ≤ inputSize :=
    edgeSuccSuccGraph.trans graphSize
  have edgeSucc : edgeCount + 1 ≤ inputSize := by omega
  calc
    certificateEncodedType.inputSize
        (PairOfPathsCertificate.certificate edgeCount left right)
        ≤ (PairOfPathsCertificate.certificate edgeCount left right).length *
            (edgeCount + 2) := by
          simpa [certificateEncodedType, setStructuredEncodedType] using certificateSize
    _ = (2 * (edgeCount + 1)) * (edgeCount + 2) := by rw [certificateLength]
    _ ≤ (2 * inputSize) * inputSize :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 edgeSucc) edgeSuccSucc
    _ ≤ 20 * inputSize ^ 2 + 20 := by nlinarith

/-! ### Complete direct-TM checker -/

def inputToTuple (input : Presentation.TwoDisjointBoundedPaths.Input) :
    Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType.Carrier :=
  (input.graph, (input.costs, (input.source, (input.target, input.bound))))

private theorem inputToTuple_encode
    (input : Presentation.TwoDisjointBoundedPaths.Input) :
    Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType.encode
        (inputToTuple input) =
      Presentation.TwoDisjointBoundedPaths.structuredEncodedType.encode input :=
  rfl

private noncomputable def inputToTupleTMBackedMap :
    TMBackedCostedMap
      Presentation.TwoDisjointBoundedPaths.structuredEncodedType
      Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType
      inputToTuple :=
  TMBackedCostedMap.ofEncodingEquiv
    Presentation.TwoDisjointBoundedPaths.structuredEncodedType
    Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType inputToTuple
    (Equiv.refl
      Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType.Symbol)
    (by
      intro input
      change Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType.encode
          (inputToTuple input) =
        (Presentation.TwoDisjointBoundedPaths.structuredEncodedType.encode input).map id
      simp [inputToTuple_encode])

private theorem and_tmPolyTime
    {X : EncodedType} {left right : X.Carrier → Bool}
    (leftTM : TMPolyTimeMap X EncodedType.bool left)
    (rightTM : TMPolyTimeMap X EncodedType.bool right) :
    TMPolyTimeMap X EncodedType.bool
      (fun input => graphBoolAndPair (left input, right input)) := by
  have paired := TMPolyTimeMap.prod_mk leftTM rightTM
  have composed := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime paired
  simpa [Function.comp] using composed

set_option maxHeartbeats 1000000 in
/-- The complete verifier is one direct-TM polynomial-time Boolean computation. -/
theorem finiteVerify_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod
        Presentation.TwoDisjointBoundedPaths.structuredEncodedType
        certificateEncodedType)
      EncodedType.bool
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        finiteVerify input.1 input.2) := by
  let InputTail := EncodedType.prod binaryNatListEncodedType
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat EncodedType.binaryNat))
  let TerminalTail := EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat EncodedType.binaryNat)
  let TargetBound := EncodedType.prod EncodedType.nat EncodedType.binaryNat
  let X := EncodedType.prod
    Presentation.TwoDisjointBoundedPaths.structuredEncodedType
    certificateEncodedType
  have instanceTM : TMPolyTimeMap X
      Presentation.TwoDisjointBoundedPaths.structuredEncodedType
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat => input.1) := by
    simpa [X, certificateEncodedType] using
      TMPolyTimeMap.fst
        Presentation.TwoDisjointBoundedPaths.structuredEncodedType
        setStructuredEncodedType
  have certificateTM : TMPolyTimeMap X certificateEncodedType
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat => input.2) := by
    simpa [X, certificateEncodedType] using
      TMPolyTimeMap.snd
        Presentation.TwoDisjointBoundedPaths.structuredEncodedType
        setStructuredEncodedType
  have tupleTM : TMPolyTimeMap X
      Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        inputToTuple input.1) := by
    have composed := TMPolyTimeMap.comp inputToTupleTMBackedMap.tm_polytime instanceTM
    simpa [Function.comp, X] using composed
  have graphTM : TMPolyTimeMap X graphStructuredEncodedType
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        input.1.graph) := by
    have projected := TMPolyTimeMap.fst graphStructuredEncodedType InputTail
    have composed := TMPolyTimeMap.comp projected tupleTM
    simpa [Function.comp, inputToTuple,
      Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType,
      InputTail, TerminalTail, TargetBound, X] using composed
  have inputTailTM : TMPolyTimeMap X InputTail
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        (input.1.costs, (input.1.source, (input.1.target, input.1.bound)))) := by
    have projected := TMPolyTimeMap.snd graphStructuredEncodedType InputTail
    have composed := TMPolyTimeMap.comp projected tupleTM
    simpa [Function.comp, inputToTuple,
      Presentation.TwoDisjointBoundedPaths.tupleStructuredEncodedType,
      InputTail, TerminalTail, TargetBound, X] using composed
  have costsTM : TMPolyTimeMap X binaryNatListEncodedType
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        input.1.costs) := by
    have projected := TMPolyTimeMap.fst binaryNatListEncodedType TerminalTail
    have composed := TMPolyTimeMap.comp projected inputTailTM
    simpa [Function.comp, InputTail, TerminalTail, X] using composed
  have terminalTailTM : TMPolyTimeMap X TerminalTail
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        (input.1.source, (input.1.target, input.1.bound))) := by
    have projected := TMPolyTimeMap.snd binaryNatListEncodedType TerminalTail
    have composed := TMPolyTimeMap.comp projected inputTailTM
    simpa [Function.comp, InputTail, TerminalTail, X] using composed
  have sourceTM : TMPolyTimeMap X EncodedType.nat
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        input.1.source) := by
    have projected := TMPolyTimeMap.fst EncodedType.nat TargetBound
    have composed := TMPolyTimeMap.comp projected terminalTailTM
    simpa [Function.comp, TerminalTail, TargetBound, X] using composed
  have targetBoundTM : TMPolyTimeMap X TargetBound
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        (input.1.target, input.1.bound)) := by
    have projected := TMPolyTimeMap.snd EncodedType.nat TargetBound
    have composed := TMPolyTimeMap.comp projected terminalTailTM
    simpa [Function.comp, TerminalTail, TargetBound, X] using composed
  have targetTM : TMPolyTimeMap X EncodedType.nat
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        input.1.target) := by
    have projected := TMPolyTimeMap.fst EncodedType.nat EncodedType.binaryNat
    have composed := TMPolyTimeMap.comp projected targetBoundTM
    simpa [Function.comp, TargetBound, X] using composed
  have boundTM : TMPolyTimeMap X EncodedType.binaryNat
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        input.1.bound) := by
    have projected := TMPolyTimeMap.snd EncodedType.nat EncodedType.binaryNat
    have composed := TMPolyTimeMap.comp projected targetBoundTM
    simpa [Function.comp, TargetBound, X] using composed
  have verticesTM : TMPolyTimeMap X EncodedType.nat
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        input.1.graph.vertices) := by
    have composed := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime graphTM
    simpa [Function.comp, X] using composed
  have graphPayloadTM : TMPolyTimeMap X graphPayloadStructuredEncodedType
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        graphPayloadOfGraph input.1.graph) := by
    have composed := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime graphTM
    simpa [Function.comp, X] using composed
  have edgesTM : TMPolyTimeMap X edgeListEncodedType
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        input.1.graph.edges) := by
    have projected := TMPolyTimeMap.fst edgeListEncodedType EncodedType.bool
    have composed := TMPolyTimeMap.comp projected graphPayloadTM
    simpa [Function.comp, graphPayloadOfGraph,
      graphPayloadStructuredEncodedType, X] using composed
  have directedTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        input.1.graph.directed) := by
    have projected := TMPolyTimeMap.snd edgeListEncodedType EncodedType.bool
    have composed := TMPolyTimeMap.comp projected graphPayloadTM
    simpa [Function.comp, graphPayloadOfGraph,
      graphPayloadStructuredEncodedType, X] using composed
  have edgeCountTM : TMPolyTimeMap X EncodedType.nat
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        input.1.graph.edges.length) := by
    have composed := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap edgeEncodedType).tm_polytime edgesTM
    simpa [Function.comp, edgeListEncodedType] using composed
  have costCountTM : TMPolyTimeMap X EncodedType.nat
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        input.1.costs.length) := by
    have composed := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap EncodedType.binaryNat).tm_polytime costsTM
    simpa [Function.comp, binaryNatListEncodedType] using composed
  have parserInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat certificateEncodedType)
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        (input.1.graph.edges.length, input.2)) :=
    TMPolyTimeMap.prod_mk edgeCountTM certificateTM
  have pairTM : TMPolyTimeMap X PairOfPathsCertificate.pathPairEncodedType
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        certificatePair input.1 input.2) := by
    have composed := TMPolyTimeMap.comp
      PairOfPathsCertificate.parsePathPair_tmPolyTime parserInputTM
    simpa [Function.comp, certificatePair, certificateEncodedType] using composed
  have leftTM : TMPolyTimeMap X natListEncodedType
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        (certificatePair input.1 input.2).1) := by
    have projected := TMPolyTimeMap.fst natListEncodedType natListEncodedType
    have composed := TMPolyTimeMap.comp projected pairTM
    simpa [Function.comp, PairOfPathsCertificate.pathPairEncodedType,
      natListEncodedType, certificateEncodedType] using composed
  have rightTM : TMPolyTimeMap X natListEncodedType
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        (certificatePair input.1 input.2).2) := by
    have projected := TMPolyTimeMap.snd natListEncodedType natListEncodedType
    have composed := TMPolyTimeMap.comp projected pairTM
    simpa [Function.comp, PairOfPathsCertificate.pathPairEncodedType,
      natListEncodedType, certificateEncodedType] using composed
  have boundsContextTM : TMPolyTimeMap X IncidenceIRValidation.pairEncoding
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        (input.1.graph.vertices, input.1.graph.vertices)) := by
    simpa [IncidenceIRValidation.pairEncoding] using
      TMPolyTimeMap.prod_mk verticesTM verticesTM
  have boundsInputTM : TMPolyTimeMap X
      (EncodedType.prod IncidenceIRValidation.pairEncoding
        IncidenceIRValidation.pairListEncoding)
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        ((input.1.graph.vertices, input.1.graph.vertices),
          input.1.graph.edges)) :=
    TMPolyTimeMap.prod_mk boundsContextTM edgesTM
  have wellFormedTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        NodeDeletionBipartiteMembership.edgesWithinBoundsBool
          ((input.1.graph.vertices, input.1.graph.vertices),
            input.1.graph.edges)) := by
    have composed := TMPolyTimeMap.comp
      NodeDeletionBipartiteMembership.edgesWithinBoundsBool_tmPolyTime boundsInputTM
    simpa [Function.comp] using composed
  have sourceBoundInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        (input.1.source, input.1.graph.vertices)) :=
    TMPolyTimeMap.prod_mk sourceTM verticesTM
  have sourceBoundTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        natLtBool (input.1.source, input.1.graph.vertices)) := by
    have composed := TMPolyTimeMap.comp natLtBool_tm_polytime sourceBoundInputTM
    simpa [Function.comp] using composed
  have targetBoundInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        (input.1.target, input.1.graph.vertices)) :=
    TMPolyTimeMap.prod_mk targetTM verticesTM
  have targetBoundCheckTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        natLtBool (input.1.target, input.1.graph.vertices)) := by
    have composed := TMPolyTimeMap.comp natLtBool_tm_polytime targetBoundInputTM
    simpa [Function.comp] using composed
  have terminalEqualityInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        (input.1.source, input.1.target)) :=
    TMPolyTimeMap.prod_mk sourceTM targetTM
  have terminalEqualityTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        PairOfPaths.natEqBool (input.1.source, input.1.target)) := by
    have composed := TMPolyTimeMap.comp
      PairOfPaths.natEqBool_tmPolyTime terminalEqualityInputTM
    simpa [Function.comp] using composed
  have terminalsDifferentTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        Bool.not (PairOfPaths.natEqBool (input.1.source, input.1.target))) := by
    have composed := TMPolyTimeMap.comp TMPolyTimeMap.bool_not terminalEqualityTM
    simpa [Function.comp] using composed
  have costLengthInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        (input.1.costs.length, input.1.graph.edges.length)) :=
    TMPolyTimeMap.prod_mk costCountTM edgeCountTM
  have costLengthTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        PairOfPaths.natEqBool
          (input.1.costs.length, input.1.graph.edges.length)) := by
    have composed := TMPolyTimeMap.comp
      PairOfPaths.natEqBool_tmPolyTime costLengthInputTM
    simpa [Function.comp] using composed
  have positiveCostsTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        allCostsPositiveBool input.1.costs) := by
    have composed := TMPolyTimeMap.comp allCostsPositiveBool_tmPolyTime costsTM
    simpa [Function.comp] using composed
  have leftPathInputTM : TMPolyTimeMap X PairOfPaths.edgeChainInputEncodedType
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        (input.1.graph.edges, input.1.source, input.1.target,
          (certificatePair input.1 input.2).1)) := by
    simpa [PairOfPaths.edgeChainInputEncodedType] using
      TMPolyTimeMap.prod_mk edgesTM
        (TMPolyTimeMap.prod_mk sourceTM
          (TMPolyTimeMap.prod_mk targetTM leftTM))
  have leftPathTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        PairOfPaths.edgeIndexPathBool
          (input.1.graph.edges, input.1.source, input.1.target,
            (certificatePair input.1 input.2).1)) := by
    have composed := TMPolyTimeMap.comp
      PairOfPaths.edgeIndexPathBool_tmPolyTime leftPathInputTM
    simpa [Function.comp] using composed
  have rightPathInputTM : TMPolyTimeMap X PairOfPaths.edgeChainInputEncodedType
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        (input.1.graph.edges, input.1.source, input.1.target,
          (certificatePair input.1 input.2).2)) := by
    simpa [PairOfPaths.edgeChainInputEncodedType] using
      TMPolyTimeMap.prod_mk edgesTM
        (TMPolyTimeMap.prod_mk sourceTM
          (TMPolyTimeMap.prod_mk targetTM rightTM))
  have rightPathTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        PairOfPaths.edgeIndexPathBool
          (input.1.graph.edges, input.1.source, input.1.target,
            (certificatePair input.1 input.2).2)) := by
    have composed := TMPolyTimeMap.comp
      PairOfPaths.edgeIndexPathBool_tmPolyTime rightPathInputTM
    simpa [Function.comp] using composed
  have leftCostInputTM : TMPolyTimeMap X PairOfPaths.boundedCostInputEncodedType
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        (input.1.costs, input.1.bound,
          (certificatePair input.1 input.2).1)) := by
    simpa [PairOfPaths.boundedCostInputEncodedType] using
      TMPolyTimeMap.prod_mk costsTM
        (TMPolyTimeMap.prod_mk boundTM leftTM)
  have leftCostTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        PairOfPaths.boundedCostBool
          (input.1.costs, input.1.bound,
            (certificatePair input.1 input.2).1)) := by
    have composed := TMPolyTimeMap.comp
      PairOfPaths.boundedCostBool_tmPolyTime leftCostInputTM
    simpa [Function.comp] using composed
  have rightCostInputTM : TMPolyTimeMap X PairOfPaths.boundedCostInputEncodedType
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        (input.1.costs, input.1.bound,
          (certificatePair input.1 input.2).2)) := by
    simpa [PairOfPaths.boundedCostInputEncodedType] using
      TMPolyTimeMap.prod_mk costsTM
        (TMPolyTimeMap.prod_mk boundTM rightTM)
  have rightCostTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        PairOfPaths.boundedCostBool
          (input.1.costs, input.1.bound,
            (certificatePair input.1 input.2).2)) := by
    have composed := TMPolyTimeMap.comp
      PairOfPaths.boundedCostBool_tmPolyTime rightCostInputTM
    simpa [Function.comp] using composed
  have disjointInputTM : TMPolyTimeMap X
      (EncodedType.prod natListEncodedType natListEncodedType)
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        ((certificatePair input.1 input.2).1,
          (certificatePair input.1 input.2).2)) :=
    TMPolyTimeMap.prod_mk leftTM rightTM
  have disjointTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.TwoDisjointBoundedPaths.Input × List Nat =>
        PairOfPaths.pathsDisjointBool
          ((certificatePair input.1 input.2).1,
            (certificatePair input.1 input.2).2)) := by
    have composed := TMPolyTimeMap.comp
      PairOfPaths.pathsDisjointBool_tmPolyTime disjointInputTM
    simpa [Function.comp] using composed
  have rightCostTailTM := and_tmPolyTime rightCostTM disjointTM
  have leftCostTailTM := and_tmPolyTime leftCostTM rightCostTailTM
  have rightPathTailTM := and_tmPolyTime rightPathTM leftCostTailTM
  have leftPathTailTM := and_tmPolyTime leftPathTM rightPathTailTM
  have positiveTailTM := and_tmPolyTime positiveCostsTM leftPathTailTM
  have costLengthTailTM := and_tmPolyTime costLengthTM positiveTailTM
  have terminalsTailTM := and_tmPolyTime terminalsDifferentTM costLengthTailTM
  have targetBoundTailTM := and_tmPolyTime targetBoundCheckTM terminalsTailTM
  have sourceBoundTailTM := and_tmPolyTime sourceBoundTM targetBoundTailTM
  have wellFormedTailTM := and_tmPolyTime wellFormedTM sourceBoundTailTM
  have allTM := and_tmPolyTime directedTM wellFormedTailTM
  simpa [finiteVerify, X] using allTM

/-! ### Native membership package -/

@[complexity_reduction_ir_typed_primitive]
noncomputable def checkerPrimitive :
    Primitive (StandardInstances.prod problem.representation natListPresentation)
      StandardInstances.bool :=
  Primitive.ofTMPolyTime
    (fun input => finiteVerify input.1 input.2)
    (by
      simpa [problem,
        Presentation.TwoDisjointBoundedPaths.presentedProblem,
        Presentation.TwoDisjointBoundedPaths.structuredPresentation,
        natListPresentation, natListEncodedType, StandardInstances.prod,
        StandardInstances.bool, certificateEncodedType] using finiteVerify_tmPolyTime)

noncomputable def checker :
    PolyProg (StandardInstances.prod problem.representation natListPresentation)
      StandardInstances.bool :=
  .atom checkerPrimitive

@[simp] theorem checker_run (input : problem.Instance × List Nat) :
    checker.run input = finiteVerify input.1 input.2 :=
  rfl

noncomputable def verifierData : NatListVerifierData problem where
  checker := checker
  witnessBound := fun input =>
    20 * problem.representation.encodedType.inputSize input ^ 2 + 20
  witnessBoundPoly := ComplexityReduction.PolynomialTimeBound.intro_with 2 20 20 (by
    intro input
    simp)
  correct := by
    intro input
    change Presentation.TwoDisjointBoundedPaths.IsYes input ↔
      ∃ certificate : List Nat,
        natListEncodedType.inputSize certificate ≤
            20 *
                Presentation.TwoDisjointBoundedPaths.structuredEncodedType.inputSize input ^ 2 +
              20 ∧
          finiteVerify input certificate = true
    constructor
    · intro yes
      rcases yes with
        ⟨directed, wellFormed, sourceBound, targetBound, terminalsDifferent,
          costLength, positiveCosts, left, right, leftPath, rightPath,
          leftCost, rightCost, disjoint⟩
      let certificate := PairOfPathsCertificate.certificate
        input.graph.edges.length left right
      have leftLength := path_length_le_edgeCount
        input.graph input.source input.target left leftPath
      have rightLength := path_length_le_edgeCount
        input.graph input.source input.target right rightPath
      have pairEquality : certificatePair input certificate = (left, right) := by
        simpa [certificatePair, certificate] using
          PairOfPathsCertificate.parsePathPair_certificate
            input.graph.edges.length left right leftLength rightLength
      refine ⟨certificate, ?_, ?_⟩
      · simpa [natListEncodedType, certificateEncodedType, certificate] using
          certificate_inputSize_le_poly input left right leftPath rightPath
      · apply (finiteVerify_eq_true_iff input certificate).2
        rw [pairEquality]
        exact ⟨directed, wellFormed, sourceBound, targetBound,
          terminalsDifferent, costLength, positiveCosts, leftPath, rightPath,
          leftCost, rightCost, disjoint⟩
    · rintro ⟨certificate, _bound, accepted⟩
      exact finiteVerify_sound input certificate accepted
  checkerSound := by
    intro input certificate accepted
    exact finiteVerify_sound input certificate accepted

/-- Exact verifier component exposed to deterministic Optional Authoring. -/
noncomputable def verifier : CertifiedVerifier problem :=
  verifierData.toCertifiedVerifier

/-- Structural certificate for the exact unary-nat-list witness presentation. -/
def witnessPresentation : verifier.witness.StructuralCertificate :=
  natListStructuralCertificate

/-- Checked native decoder discipline indexed by the exact verifier. -/
noncomputable def discipline : CertifiedVerifierEncodingDiscipline verifier :=
  ComplexityReduction.Agent.Hardness.FiniteWitnessNative.discipline verifierData

/-- Discovery-only exact membership template; it grants no capability by itself. -/
@[complexity_reduction_ir_hardness_native_membership_template]
def template : ComplexityReduction.Agent.Hardness.Authoring.NativeMembershipTemplate
    problem verifier witnessPresentation discipline :=
  ⟨True.intro⟩

end TwoDisjointBoundedPathsMembership
end Domain
end ComplexityReduction

assert_standard_axioms
  ComplexityReduction.Domain.TwoDisjointBoundedPathsMembership.costPositiveBool_tmPolyTime,
  ComplexityReduction.Domain.TwoDisjointBoundedPathsMembership.allCostsPositiveBool_tmPolyTime,
  ComplexityReduction.Domain.TwoDisjointBoundedPathsMembership.certificate_inputSize_le_poly,
  ComplexityReduction.Domain.TwoDisjointBoundedPathsMembership.finiteVerify_tmPolyTime,
  ComplexityReduction.Domain.TwoDisjointBoundedPathsMembership.verifier,
  ComplexityReduction.Domain.TwoDisjointBoundedPathsMembership.witnessPresentation,
  ComplexityReduction.Domain.TwoDisjointBoundedPathsMembership.discipline,
  ComplexityReduction.Domain.TwoDisjointBoundedPathsMembership.template
