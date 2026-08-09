/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.Agent.Hardness.FiniteWitnessNative
import ComplexityReduction.Domain.IncidenceIRValidationStandardTM
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.NatPair
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.NatListSplitTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipChromaticNumber
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipFeedbackNodeSetRunner
import ComplexityReduction.Presentation.NodeDeletionBipartite
import ComplexityReduction.Problems.Karp21.HittingSetStandardTM
import ComplexityReduction.Program.ContextListAll
import Mathlib.Tactic

/-!
Native unary-nat-list NP membership for Node Deletion to Bipartite.

The first `graph.vertices` certificate entries form a total `0/1` color table;
the remaining suffix is the deleted-vertex list.  The verifier checks graph
well-formedness, undirectedness, the deletion budget, the two-color alphabet,
and every surviving edge through a reusable context/list all-check.
-/

namespace ComplexityReduction
namespace Domain
namespace NodeDeletionBipartiteMembership

open Encoding
open Certificate
open Program
open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.Karp21
open ComplexityReduction.Karp21.FeedbackNodeSetMembership
open ComplexityReduction.Agent.Hardness.FiniteWitness
open ComplexityReduction.Agent.Hardness.FiniteWitnessNative

abbrev problem : PresentedProblem :=
  Presentation.NodeDeletionBipartite.presentedProblem

abbrev certificateEncodedType : EncodedType := setStructuredEncodedType

abbrev natListEncodedType : EncodedType := natListPresentation.encodedType

/-- Split a flat certificate into `(deleted, colors)`. -/
def certificatePair
    (input : Presentation.NodeDeletionBipartite.Input) (certificate : List Nat) :
    FeedbackNodeSetCertificate :=
  let split := NatListSplit.split (input.graph.vertices, certificate)
  (split.2, split.1)

theorem certificatePair_eq
    (input : Presentation.NodeDeletionBipartite.Input) (certificate : List Nat) :
    certificatePair input certificate =
      (certificate.drop input.graph.vertices, certificate.take input.graph.vertices) := by
  simpa [certificatePair] using
    congrArg (fun pair : List Nat × List Nat => (pair.2, pair.1))
      (NatListSplit.split_eq_splitAt input.graph.vertices certificate)

theorem certificatePair_append_of_colorLength
    (input : Presentation.NodeDeletionBipartite.Input)
    (colors deleted : List Nat) (colorLength : colors.length = input.graph.vertices) :
    certificatePair input (colors ++ deleted) = (deleted, colors) := by
  rw [certificatePair_eq]
  simp [colorLength]

/-- One edge passes when it is deleted at an endpoint or its surviving colors differ. -/
def edgeLegalBool (input : FNSRankContext × (Nat × Nat)) : Bool :=
  graphBoolOrPair
    (Bool.not (fnsEdgeActiveBool input),
      Bool.not
        (decide
          (fnsRankAt (input.1, input.2.1) =
            fnsRankAt (input.1, input.2.2))))

theorem edgeLegalBool_tmPolyTime :
    TMPolyTimeMap fnsEdgeCheckInputEncodedType EncodedType.bool edgeLegalBool := by
  let X := fnsEdgeCheckInputEncodedType
  have context : TMPolyTimeMap X fnsRankContextEncodedType
      (fun input : X.Carrier => input.1) := by
    simpa [X, fnsEdgeCheckInputEncodedType] using
      TMPolyTimeMap.fst fnsRankContextEncodedType edgeStructuredEncodedType
  have edge : TMPolyTimeMap X edgeStructuredEncodedType
      (fun input : X.Carrier => input.2) := by
    simpa [X, fnsEdgeCheckInputEncodedType] using
      TMPolyTimeMap.snd fnsRankContextEncodedType edgeStructuredEncodedType
  have leftVertex : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) edge
    simpa [Function.comp, edgeStructuredEncodedType, X] using composed
  have rightVertex : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat) edge
    simpa [Function.comp, edgeStructuredEncodedType, X] using composed
  have active : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => fnsEdgeActiveBool input) :=
    fnsEdgeActiveBool_tm_polytime
  have inactive : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => Bool.not (fnsEdgeActiveBool input)) := by
    have composed := TMPolyTimeMap.comp TMPolyTimeMap.bool_not active
    simpa [Function.comp] using composed
  have leftInput : TMPolyTimeMap X fnsRankAtInputEncodedType
      (fun input : X.Carrier => (input.1, input.2.1)) :=
    TMPolyTimeMap.prod_mk context leftVertex
  have rightInput : TMPolyTimeMap X fnsRankAtInputEncodedType
      (fun input : X.Carrier => (input.1, input.2.2)) :=
    TMPolyTimeMap.prod_mk context rightVertex
  have leftColor : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => fnsRankAt (input.1, input.2.1)) := by
    have composed := TMPolyTimeMap.comp fnsRankAt_tm_polytime leftInput
    simpa [Function.comp, fnsRankAtInputEncodedType] using composed
  have rightColor : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => fnsRankAt (input.1, input.2.2)) := by
    have composed := TMPolyTimeMap.comp fnsRankAt_tm_polytime rightInput
    simpa [Function.comp, fnsRankAtInputEncodedType] using composed
  have equalityInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : X.Carrier =>
        (fnsRankAt (input.1, input.2.1), fnsRankAt (input.1, input.2.2))) :=
    TMPolyTimeMap.prod_mk leftColor rightColor
  have equality : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        decide
          (fnsRankAt (input.1, input.2.1) =
            fnsRankAt (input.1, input.2.2))) := by
    have composed := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq equalityInput
    simpa [Function.comp] using composed
  have different : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        Bool.not
          (decide
            (fnsRankAt (input.1, input.2.1) =
              fnsRankAt (input.1, input.2.2)))) := by
    have composed := TMPolyTimeMap.comp TMPolyTimeMap.bool_not equality
    simpa [Function.comp] using composed
  have disjunctionInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : X.Carrier =>
        (Bool.not (fnsEdgeActiveBool input),
          Bool.not
            (decide
              (fnsRankAt (input.1, input.2.1) =
                fnsRankAt (input.1, input.2.2))))) :=
    TMPolyTimeMap.prod_mk inactive different
  have composed := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime disjunctionInput
  simpa [Function.comp, edgeLegalBool, X] using composed

theorem edgeLegalBool_eq_true_iff_of_bounds
    (vertices : Nat) (deleted colors : List Nat) (edge : Nat × Nat)
    (leftBound : edge.1 < vertices) (rightBound : edge.2 < vertices) :
    edgeLegalBool ((vertices, (deleted, colors)), edge) = true ↔
      edge.1 ∈ deleted ∨ edge.2 ∈ deleted ∨
        colors.getD edge.1 0 ≠ colors.getD edge.2 0 := by
  have activeIff :
      fnsEdgeActiveBool ((vertices, (deleted, colors)), edge) = true ↔
        edge.1 ∉ deleted ∧ edge.2 ∉ deleted := by
    simpa [leftBound, rightBound] using
      (fnsEdgeActiveBool_eq_true_iff ((vertices, (deleted, colors)), edge))
  have inactiveIff :
      fnsEdgeActiveBool ((vertices, (deleted, colors)), edge) = false ↔
        edge.1 ∈ deleted ∨ edge.2 ∈ deleted := by
    constructor
    · intro inactive
      by_contra neither
      push_neg at neither
      have active := activeIff.mpr neither
      simp [inactive] at active
    · intro removed
      cases active : fnsEdgeActiveBool ((vertices, (deleted, colors)), edge)
      · rfl
      · have neither := activeIff.mp active
        rcases removed with left | right
        · exact False.elim (neither.1 left)
        · exact False.elim (neither.2 right)
  rw [edgeLegalBool, graphBoolOrPair_eq_true_iff]
  simp only [Bool.not_eq_true']
  rw [inactiveIff]
  simp [fnsRankAt, rankOf, MaxCut.natListGetD, or_assoc]

/-- Check every stored edge against one retained deletion/color context. -/
def allEdgesLegalBool
    (input : FNSRankContext × List (Nat × Nat)) : Bool :=
  ContextListAll.executable
    (C := fnsRankContextEncodedType) (X := edgeStructuredEncodedType)
    edgeLegalBool input

theorem allEdgesLegalBool_eq_true_iff
    (context : FNSRankContext) (edges : List (Nat × Nat)) :
    allEdgesLegalBool (context, edges) = true ↔
      ∀ edge ∈ edges, edgeLegalBool (context, edge) = true := by
  exact ContextListAll.executable_eq_true_iff
    (C := fnsRankContextEncodedType) (X := edgeStructuredEncodedType)
    edgeLegalBool context edges

theorem allEdgesLegalBool_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod fnsRankContextEncodedType edgeListStructuredEncodedType)
      EncodedType.bool allEdgesLegalBool := by
  simpa [allEdgesLegalBool] using
    ContextListAll.executable_tmPolyTime
      (C := fnsRankContextEncodedType) (X := edgeStructuredEncodedType)
      edgeLegalBool edgeLegalBool_tmPolyTime

/-- Check that every raw graph edge lies inside the declared vertex range. -/
def edgesWithinBoundsBool
    (input : (Nat × Nat) × List (Nat × Nat)) : Bool :=
  ContextListAll.executable
    (C := IncidenceIRValidation.pairEncoding)
    (X := IncidenceIRValidation.pairEncoding)
    IncidenceIRValidation.pairWithinBoundsBool input

theorem edgesWithinBoundsBool_eq_true_iff
    (vertices : Nat) (edges : List (Nat × Nat)) :
    edgesWithinBoundsBool ((vertices, vertices), edges) = true ↔
      ∀ edge ∈ edges, edge.1 < vertices ∧ edge.2 < vertices := by
  unfold edgesWithinBoundsBool
  constructor
  · intro accepted edge member
    have localCheck :=
      (ContextListAll.executable_eq_true_iff
        (C := IncidenceIRValidation.pairEncoding)
        (X := IncidenceIRValidation.pairEncoding)
        IncidenceIRValidation.pairWithinBoundsBool
        (vertices, vertices) edges).mp accepted edge member
    exact (IncidenceIRValidation.pairWithinBoundsBool_eq_true_iff
      ((vertices, vertices), edge)).mp localCheck
  · intro bounds
    apply (ContextListAll.executable_eq_true_iff
      (C := IncidenceIRValidation.pairEncoding)
      (X := IncidenceIRValidation.pairEncoding)
      IncidenceIRValidation.pairWithinBoundsBool
      (vertices, vertices) edges).mpr
    intro edge member
    exact (IncidenceIRValidation.pairWithinBoundsBool_eq_true_iff
      ((vertices, vertices), edge)).mpr (bounds edge member)

theorem edgesWithinBoundsBool_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod IncidenceIRValidation.pairEncoding
        IncidenceIRValidation.pairListEncoding)
      EncodedType.bool edgesWithinBoundsBool := by
  simpa [edgesWithinBoundsBool] using
    ContextListAll.executable_tmPolyTime
      (C := IncidenceIRValidation.pairEncoding)
      (X := IncidenceIRValidation.pairEncoding)
      IncidenceIRValidation.pairWithinBoundsBool
      IncidenceIRValidation.pairWithinBoundsBool_tmPolyTime

/-- Exact flat-certificate verifier Boolean. -/
def finiteVerify
    (input : Presentation.NodeDeletionBipartite.Input) (certificate : List Nat) : Bool :=
  let pair := certificatePair input certificate
  graphBoolAndPair
    (Bool.not input.graph.directed,
      graphBoolAndPair
        (edgesWithinBoundsBool
          ((input.graph.vertices, input.graph.vertices), input.graph.edges),
          graphBoolAndPair
            (HittingSet.natLeBool (input.graph.vertices, pair.2.length),
              graphBoolAndPair
                (HittingSet.boundedNatListBool (2, pair.2),
                  graphBoolAndPair
                    (HittingSet.natLeBool (pair.1.length, input.budget),
                      allEdgesLegalBool
                        ((input.graph.vertices, pair), input.graph.edges))))))

theorem finiteVerify_eq_true_iff
    (input : Presentation.NodeDeletionBipartite.Input) (certificate : List Nat) :
    finiteVerify input certificate = true ↔
      input.graph.directed = false ∧
        WellFormed input.graph ∧
        input.graph.vertices ≤ (certificatePair input certificate).2.length ∧
        (∀ color ∈ (certificatePair input certificate).2, color < 2) ∧
        (certificatePair input certificate).1.length ≤ input.budget ∧
        ∀ edge ∈ input.graph.edges,
          edgeLegalBool
            ((input.graph.vertices, certificatePair input certificate), edge) = true := by
  rw [finiteVerify, graphBoolAndPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff, graphBoolAndPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff, graphBoolAndPair_eq_true_iff,
    edgesWithinBoundsBool_eq_true_iff,
    HittingSet.natLeBool_eq_true_iff,
    HittingSet.boundedNatListBool_eq_true_iff,
    HittingSet.natLeBool_eq_true_iff,
    allEdgesLegalBool_eq_true_iff]
  simp [WellFormed, EdgeWithinBounds]

/-- Decode the checked finite color alphabet as a total Boolean coloring. -/
def boolColorOf (colors : List Nat) (vertex : Nat) : Bool :=
  decide (colors.getD vertex 0 = 1)

/-- Canonical finite color table generated from a legacy total coloring. -/
def colorTable
    (input : Presentation.NodeDeletionBipartite.Input) (color : Nat → Bool) : List Nat :=
  (List.range input.graph.vertices).map fun vertex => boolToNat (color vertex)

@[simp] theorem colorTable_length
    (input : Presentation.NodeDeletionBipartite.Input) (color : Nat → Bool) :
    (colorTable input color).length = input.graph.vertices := by
  simp [colorTable]

theorem colorTable_getD
    (input : Presentation.NodeDeletionBipartite.Input) (color : Nat → Bool)
    {vertex : Nat} (bound : vertex < input.graph.vertices) :
    (colorTable input color).getD vertex 0 = boolToNat (color vertex) := by
  simpa [colorTable] using
    (ChromaticNumber.getD_range_map_eq
      (f := fun vertex => boolToNat (color vertex)) bound)

theorem colorTable_values_lt_two
    (input : Presentation.NodeDeletionBipartite.Input) (color : Nat → Bool) :
    ∀ value ∈ colorTable input color, value < 2 := by
  intro value member
  rcases List.mem_map.mp member with ⟨vertex, _vertexMember, rfl⟩
  cases color vertex <;> simp [boolToNat]

private theorem checkedColor_lt_two
    {input : Presentation.NodeDeletionBipartite.Input} {certificate : List Nat}
    (lengthOK : input.graph.vertices ≤ (certificatePair input certificate).2.length)
    (valuesOK : ∀ value ∈ (certificatePair input certificate).2, value < 2)
    {vertex : Nat} (bound : vertex < input.graph.vertices) :
    (certificatePair input certificate).2.getD vertex 0 < 2 := by
  let colors := (certificatePair input certificate).2
  have indexBound : vertex < colors.length := lt_of_lt_of_le bound lengthOK
  have member : colors.getD vertex 0 ∈ colors := by
    rw [List.getD_eq_getElem (l := colors) (d := 0) (n := vertex) indexBound]
    exact List.getElem_mem indexBound
  exact valuesOK _ member

private theorem boolColorOf_ne_of_lt_two
    {left right : Nat} (leftBound : left < 2) (rightBound : right < 2)
    (different : left ≠ right) :
    (decide (left = 1) : Bool) ≠ decide (right = 1) := by
  have leftCases : left = 0 ∨ left = 1 := by omega
  have rightCases : right = 0 ∨ right = 1 := by omega
  rcases leftCases with rfl | rfl <;>
    rcases rightCases with rfl | rfl <;> simp_all

/-- Soundness of the flat verifier against the exact public problem semantics. -/
theorem finiteVerify_sound
    (input : Presentation.NodeDeletionBipartite.Input) (certificate : List Nat)
    (accepted : finiteVerify input certificate = true) :
    Presentation.NodeDeletionBipartite.IsYes input := by
  rcases (finiteVerify_eq_true_iff input certificate).1 accepted with
    ⟨undirected, wellFormed, colorLength, colorValues, deletedLength, edgeChecks⟩
  let deletedRaw := (certificatePair input certificate).1
  let colors := (certificatePair input certificate).2
  let deleted := (deletedRaw.filter fun vertex => decide (vertex < input.graph.vertices)).dedup
  refine ⟨undirected, wellFormed, deleted, ?_, ?_, ?_, boolColorOf colors, ?_⟩
  · exact List.nodup_dedup _
  · intro vertex member
    have filtered := List.mem_dedup.mp member
    have condition := (List.mem_filter.mp filtered).2
    simpa using of_decide_eq_true condition
  · have dedupLength : deleted.length ≤
        (deletedRaw.filter fun vertex => decide (vertex < input.graph.vertices)).length :=
      List.Sublist.length_le (List.dedup_sublist _)
    have filterLength :
        (deletedRaw.filter fun vertex => decide (vertex < input.graph.vertices)).length ≤
          deletedRaw.length :=
      List.length_filter_le _ _
    exact dedupLength.trans (filterLength.trans deletedLength)
  · intro edge edgeMember
    have bounds := wellFormed edge edgeMember
    have checked := edgeChecks edge edgeMember
    rcases (edgeLegalBool_eq_true_iff_of_bounds
        input.graph.vertices deletedRaw colors edge bounds.1 bounds.2).1 checked with
      leftDeleted | rightDeleted | different
    · left
      apply List.mem_dedup.mpr
      apply List.mem_filter.mpr
      exact ⟨leftDeleted, by simp [bounds.1]⟩
    · right
      left
      apply List.mem_dedup.mpr
      apply List.mem_filter.mpr
      exact ⟨rightDeleted, by simp [bounds.2]⟩
    · right
      right
      exact boolColorOf_ne_of_lt_two
        (checkedColor_lt_two colorLength colorValues bounds.1)
        (checkedColor_lt_two colorLength colorValues bounds.2)
        different

/-- Completeness: every legacy deletion/coloring witness has a flat certificate. -/
theorem finiteVerify_complete
    (input : Presentation.NodeDeletionBipartite.Input)
    (yes : Presentation.NodeDeletionBipartite.IsYes input) :
    ∃ certificate : List Nat, finiteVerify input certificate = true := by
  rcases yes with
    ⟨undirected, wellFormed, deleted, _deletedNodup, _deletedBounds,
      deletedLength, color, edgeLegal⟩
  let colors := colorTable input color
  refine ⟨colors ++ deleted, ?_⟩
  apply (finiteVerify_eq_true_iff input (colors ++ deleted)).2
  have pairEquality : certificatePair input (colors ++ deleted) = (deleted, colors) :=
    certificatePair_append_of_colorLength input colors deleted (by simp [colors])
  rw [pairEquality]
  refine ⟨undirected, wellFormed, ?_, colorTable_values_lt_two input color,
    deletedLength, ?_⟩
  · simp [colors]
  · intro edge edgeMember
    have bounds := wellFormed edge edgeMember
    apply (edgeLegalBool_eq_true_iff_of_bounds
      input.graph.vertices deleted colors edge bounds.1 bounds.2).2
    rcases edgeLegal edge edgeMember with leftDeleted | rightDeleted | different
    · exact Or.inl leftDeleted
    · exact Or.inr (Or.inl rightDeleted)
    · right
      right
      rw [show colors.getD edge.1 0 = boolToNat (color edge.1) by
          exact colorTable_getD input color bounds.1,
        show colors.getD edge.2 0 = boolToNat (color edge.2) by
          exact colorTable_getD input color bounds.2]
      cases leftColor : color edge.1 <;>
        cases rightColor : color edge.2 <;>
        simp_all [boolToNat]

theorem structured_inputSize_eq
    (input : Presentation.NodeDeletionBipartite.Input) :
    Presentation.NodeDeletionBipartite.structuredEncodedType.inputSize input =
      graphStructuredEncodedType.inputSize input.graph + input.budget + 2 := by
  change Presentation.NodeDeletionBipartite.tupleStructuredEncodedType.inputSize
      (input.graph, input.budget) = _
  simp [Presentation.NodeDeletionBipartite.tupleStructuredEncodedType]
  omega

theorem certificate_inputSize_le_poly
    (input : Presentation.NodeDeletionBipartite.Input)
    {deleted : List Nat} (deletedBounds : VerticesWithinBounds input.graph deleted)
    (deletedLength : deleted.length ≤ input.budget) (color : Nat → Bool) :
    certificateEncodedType.inputSize (colorTable input color ++ deleted) ≤
      10 * (Presentation.NodeDeletionBipartite.structuredEncodedType.inputSize input) ^ 2 + 10 := by
  let inputSize := Presentation.NodeDeletionBipartite.structuredEncodedType.inputSize input
  let colors := colorTable input color
  have colorSize :=
    ComplexityReduction.Problems.Karp21.HittingSetStandardTM.boundedNatList_inputSize_le
      2 colors (by simpa [colors] using colorTable_values_lt_two input color)
  have deletedSize :=
    ComplexityReduction.Problems.Karp21.HittingSetStandardTM.boundedNatList_inputSize_le
      input.graph.vertices deleted deletedBounds
  have appendSize :
      certificateEncodedType.inputSize (colors ++ deleted) =
        certificateEncodedType.inputSize colors + certificateEncodedType.inputSize deleted := by
    simpa [certificateEncodedType, setStructuredEncodedType] using
      Clique.encodedList_inputSize_append EncodedType.nat colors deleted
  have verticesSucc : input.graph.vertices + 1 ≤ inputSize := by
    rw [show inputSize =
      Presentation.NodeDeletionBipartite.structuredEncodedType.inputSize input by rfl,
      structured_inputSize_eq,
      ComplexityReduction.Karp21.VertexCover.graphStructured_inputSize_eq]
    omega
  have budget : input.budget ≤ inputSize := by
    rw [show inputSize =
      Presentation.NodeDeletionBipartite.structuredEncodedType.inputSize input by rfl,
      structured_inputSize_eq]
    omega
  have three : 3 ≤ inputSize := by
    rw [show inputSize =
      Presentation.NodeDeletionBipartite.structuredEncodedType.inputSize input by rfl,
      structured_inputSize_eq,
      ComplexityReduction.Karp21.VertexCover.graphStructured_inputSize_eq]
    omega
  rw [show colorTable input color = colors by rfl, appendSize]
  calc
    certificateEncodedType.inputSize colors + certificateEncodedType.inputSize deleted
        ≤ colors.length * 3 + deleted.length * (input.graph.vertices + 1) :=
          Nat.add_le_add colorSize deletedSize
    _ = input.graph.vertices * 3 + deleted.length * (input.graph.vertices + 1) := by
          simp [colors]
    _ ≤ inputSize * inputSize + inputSize * inputSize := by
          exact Nat.add_le_add
            (Nat.mul_le_mul (Nat.le_trans (Nat.le_succ _) verticesSucc) three)
            (Nat.mul_le_mul (deletedLength.trans budget) verticesSucc)
    _ ≤ 10 * inputSize ^ 2 + 10 := by
          nlinarith

def inputToTuple (input : Presentation.NodeDeletionBipartite.Input) :
    Presentation.NodeDeletionBipartite.tupleStructuredEncodedType.Carrier :=
  (input.graph, input.budget)

private theorem inputToTuple_encode
    (input : Presentation.NodeDeletionBipartite.Input) :
    Presentation.NodeDeletionBipartite.tupleStructuredEncodedType.encode
        (inputToTuple input) =
      Presentation.NodeDeletionBipartite.structuredEncodedType.encode input := by
  rfl

private noncomputable def inputToTupleTMBackedMap :
    TMBackedCostedMap
      Presentation.NodeDeletionBipartite.structuredEncodedType
      Presentation.NodeDeletionBipartite.tupleStructuredEncodedType
      inputToTuple :=
  TMBackedCostedMap.ofEncodingEquiv
    Presentation.NodeDeletionBipartite.structuredEncodedType
    Presentation.NodeDeletionBipartite.tupleStructuredEncodedType
    inputToTuple
    (Equiv.refl Presentation.NodeDeletionBipartite.tupleStructuredEncodedType.Symbol)
    (by
      intro input
      change Presentation.NodeDeletionBipartite.tupleStructuredEncodedType.encode
          (inputToTuple input) =
        (Presentation.NodeDeletionBipartite.structuredEncodedType.encode input).map id
      simp [inputToTuple_encode])

/-- The complete verifier is one direct-TM polynomial-time Boolean computation. -/
theorem finiteVerify_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod Presentation.NodeDeletionBipartite.structuredEncodedType
        certificateEncodedType)
      EncodedType.bool
      (fun input : Presentation.NodeDeletionBipartite.Input × List Nat =>
        finiteVerify input.1 input.2) := by
  let X := EncodedType.prod Presentation.NodeDeletionBipartite.structuredEncodedType
    certificateEncodedType
  have instanceTM : TMPolyTimeMap X
      Presentation.NodeDeletionBipartite.structuredEncodedType
      (fun input : X.Carrier => input.1) := by
    simpa [X, certificateEncodedType] using
      TMPolyTimeMap.fst Presentation.NodeDeletionBipartite.structuredEncodedType
        setStructuredEncodedType
  have certificateTM : TMPolyTimeMap X certificateEncodedType
      (fun input : X.Carrier => input.2) := by
    simpa [X, certificateEncodedType] using
      TMPolyTimeMap.snd Presentation.NodeDeletionBipartite.structuredEncodedType
        setStructuredEncodedType
  have tupleTM : TMPolyTimeMap X
      Presentation.NodeDeletionBipartite.tupleStructuredEncodedType
      (fun input : X.Carrier => inputToTuple input.1) := by
    have composed := TMPolyTimeMap.comp inputToTupleTMBackedMap.tm_polytime instanceTM
    simpa [Function.comp, X] using composed
  have graphTM : TMPolyTimeMap X graphStructuredEncodedType
      (fun input : X.Carrier => input.1.graph) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst graphStructuredEncodedType EncodedType.nat) tupleTM
    simpa [Function.comp, inputToTuple,
      Presentation.NodeDeletionBipartite.tupleStructuredEncodedType, X] using composed
  have budgetTM : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.1.budget) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd graphStructuredEncodedType EncodedType.nat) tupleTM
    simpa [Function.comp, inputToTuple,
      Presentation.NodeDeletionBipartite.tupleStructuredEncodedType, X] using composed
  have verticesTM : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => input.1.graph.vertices) := by
    have composed := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime graphTM
    simpa [Function.comp, X] using composed
  have graphPayloadTM : TMPolyTimeMap X graphPayloadStructuredEncodedType
      (fun input : X.Carrier => graphPayloadOfGraph input.1.graph) := by
    have composed := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime graphTM
    simpa [Function.comp, X] using composed
  have edgesTM : TMPolyTimeMap X edgeListStructuredEncodedType
      (fun input : X.Carrier => input.1.graph.edges) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst edgeListStructuredEncodedType EncodedType.bool) graphPayloadTM
    simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X]
      using composed
  have directedTM : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => input.1.graph.directed) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd edgeListStructuredEncodedType EncodedType.bool) graphPayloadTM
    simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X]
      using composed
  have undirectedTM : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier => Bool.not input.1.graph.directed) := by
    have composed := TMPolyTimeMap.comp TMPolyTimeMap.bool_not directedTM
    simpa [Function.comp] using composed
  have splitInputTM : TMPolyTimeMap X NatListSplit.inputEncodedType
      (fun input : X.Carrier => (input.1.graph.vertices, input.2)) := by
    have pairTM : TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat setStructuredEncodedType)
        (fun input : X.Carrier => (input.1.graph.vertices, input.2)) :=
      TMPolyTimeMap.prod_mk verticesTM certificateTM
    simpa [NatListSplit.inputEncodedType, EncodedListLookup.inputEncodedType,
      certificateEncodedType] using pairTM
  have splitTM : TMPolyTimeMap X NatListSplit.outputEncodedType
      (fun input : X.Carrier =>
        NatListSplit.split (input.1.graph.vertices, input.2)) := by
    have composed := TMPolyTimeMap.comp NatListSplit.split_tm_polytime splitInputTM
    simpa [Function.comp] using composed
  have colorsTM : TMPolyTimeMap X setStructuredEncodedType
      (fun input : X.Carrier =>
        (NatListSplit.split (input.1.graph.vertices, input.2)).1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst setStructuredEncodedType setStructuredEncodedType) splitTM
    simpa [Function.comp, NatListSplit.outputEncodedType, X] using composed
  have deletedTM : TMPolyTimeMap X setStructuredEncodedType
      (fun input : X.Carrier =>
        (NatListSplit.split (input.1.graph.vertices, input.2)).2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd setStructuredEncodedType setStructuredEncodedType) splitTM
    simpa [Function.comp, NatListSplit.outputEncodedType, X] using composed
  have pairTM : TMPolyTimeMap X feedbackNodeSetCertificateEncodedType
      (fun input : X.Carrier => certificatePair input.1 input.2) := by
    have paired : TMPolyTimeMap X feedbackNodeSetCertificateEncodedType
        (fun input : X.Carrier =>
          ((NatListSplit.split (input.1.graph.vertices, input.2)).2,
            (NatListSplit.split (input.1.graph.vertices, input.2)).1)) := by
      simpa [feedbackNodeSetCertificateEncodedType,
        partitionWeightsStructuredEncodedType] using
        TMPolyTimeMap.prod_mk deletedTM colorsTM
    simpa [certificatePair] using paired
  have colorsLengthTM : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => (certificatePair input.1 input.2).2.length) := by
    have composed := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime colorsTM
    simpa [Function.comp, certificatePair, setStructuredEncodedType, X] using composed
  have deletedLengthTM : TMPolyTimeMap X EncodedType.nat
      (fun input : X.Carrier => (certificatePair input.1 input.2).1.length) := by
    have composed := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime deletedTM
    simpa [Function.comp, certificatePair, setStructuredEncodedType, X] using composed
  have boundsContextTM : TMPolyTimeMap X IncidenceIRValidation.pairEncoding
      (fun input : X.Carrier =>
        (input.1.graph.vertices, input.1.graph.vertices)) := by
    simpa [IncidenceIRValidation.pairEncoding] using
      TMPolyTimeMap.prod_mk verticesTM verticesTM
  have boundsInputTM : TMPolyTimeMap X
      (EncodedType.prod IncidenceIRValidation.pairEncoding
        IncidenceIRValidation.pairListEncoding)
      (fun input : X.Carrier =>
        ((input.1.graph.vertices, input.1.graph.vertices), input.1.graph.edges)) := by
    simpa [IncidenceIRValidation.pairListEncoding] using
      TMPolyTimeMap.prod_mk boundsContextTM edgesTM
  have boundsOKTM : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        edgesWithinBoundsBool
          ((input.1.graph.vertices, input.1.graph.vertices), input.1.graph.edges)) := by
    have composed := TMPolyTimeMap.comp edgesWithinBoundsBool_tmPolyTime boundsInputTM
    simpa [Function.comp] using composed
  have colorLengthInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : X.Carrier =>
        (input.1.graph.vertices, (certificatePair input.1 input.2).2.length)) :=
    TMPolyTimeMap.prod_mk verticesTM colorsLengthTM
  have colorLengthOKTM : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        HittingSet.natLeBool
          (input.1.graph.vertices, (certificatePair input.1 input.2).2.length)) := by
    have composed := TMPolyTimeMap.comp HittingSet.natLeBool_tm_polytime
      colorLengthInputTM
    simpa [Function.comp] using composed
  have twoTM : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (2 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (2 : Nat)
  have colorValuesInputTM : TMPolyTimeMap X
      HittingSet.boundedNatInstructionInputEncodedType
      (fun input : X.Carrier => ((2 : Nat), (certificatePair input.1 input.2).2)) := by
    have paired : TMPolyTimeMap X
        (EncodedType.prod EncodedType.nat setStructuredEncodedType)
        (fun input : X.Carrier =>
          ((2 : Nat), (NatListSplit.split (input.1.graph.vertices, input.2)).1)) :=
      TMPolyTimeMap.prod_mk twoTM colorsTM
    simpa [HittingSet.boundedNatInstructionInputEncodedType, certificatePair] using paired
  have colorValuesOKTM : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        HittingSet.boundedNatListBool
          ((2 : Nat), (certificatePair input.1 input.2).2)) := by
    have composed := TMPolyTimeMap.comp HittingSet.boundedNatListBool_tm_polytime
      colorValuesInputTM
    simpa [Function.comp] using composed
  have deletionBudgetInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : X.Carrier =>
        ((certificatePair input.1 input.2).1.length, input.1.budget)) :=
    TMPolyTimeMap.prod_mk deletedLengthTM budgetTM
  have deletionBudgetOKTM : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        HittingSet.natLeBool
          ((certificatePair input.1 input.2).1.length, input.1.budget)) := by
    have composed := TMPolyTimeMap.comp HittingSet.natLeBool_tm_polytime
      deletionBudgetInputTM
    simpa [Function.comp] using composed
  have edgeContextTM : TMPolyTimeMap X fnsRankContextEncodedType
      (fun input : X.Carrier =>
        (input.1.graph.vertices, certificatePair input.1 input.2)) := by
    simpa [fnsRankContextEncodedType] using TMPolyTimeMap.prod_mk verticesTM pairTM
  have edgeInputTM : TMPolyTimeMap X
      (EncodedType.prod fnsRankContextEncodedType edgeListStructuredEncodedType)
      (fun input : X.Carrier =>
        ((input.1.graph.vertices, certificatePair input.1 input.2),
          input.1.graph.edges)) :=
    TMPolyTimeMap.prod_mk edgeContextTM edgesTM
  have edgesOKTM : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        allEdgesLegalBool
          ((input.1.graph.vertices, certificatePair input.1 input.2),
            input.1.graph.edges)) := by
    have composed := TMPolyTimeMap.comp allEdgesLegalBool_tmPolyTime edgeInputTM
    simpa [Function.comp] using composed
  have budgetEdgesInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : X.Carrier =>
        (HittingSet.natLeBool
            ((certificatePair input.1 input.2).1.length, input.1.budget),
          allEdgesLegalBool
            ((input.1.graph.vertices, certificatePair input.1 input.2),
              input.1.graph.edges))) :=
    TMPolyTimeMap.prod_mk deletionBudgetOKTM edgesOKTM
  have budgetEdgesTM : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        graphBoolAndPair
          (HittingSet.natLeBool
              ((certificatePair input.1 input.2).1.length, input.1.budget),
            allEdgesLegalBool
              ((input.1.graph.vertices, certificatePair input.1 input.2),
                input.1.graph.edges))) := by
    have composed := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime budgetEdgesInputTM
    simpa [Function.comp] using composed
  have valuesTailInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : X.Carrier =>
        (HittingSet.boundedNatListBool (2, (certificatePair input.1 input.2).2),
          graphBoolAndPair
            (HittingSet.natLeBool
                ((certificatePair input.1 input.2).1.length, input.1.budget),
              allEdgesLegalBool
                ((input.1.graph.vertices, certificatePair input.1 input.2),
                  input.1.graph.edges)))) :=
    TMPolyTimeMap.prod_mk colorValuesOKTM budgetEdgesTM
  have valuesTailTM : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        graphBoolAndPair
          (HittingSet.boundedNatListBool (2, (certificatePair input.1 input.2).2),
            graphBoolAndPair
              (HittingSet.natLeBool
                  ((certificatePair input.1 input.2).1.length, input.1.budget),
                allEdgesLegalBool
                  ((input.1.graph.vertices, certificatePair input.1 input.2),
                    input.1.graph.edges)))) := by
    have composed := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime valuesTailInputTM
    simpa [Function.comp] using composed
  have lengthTailInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : X.Carrier =>
        (HittingSet.natLeBool
            (input.1.graph.vertices, (certificatePair input.1 input.2).2.length),
          graphBoolAndPair
            (HittingSet.boundedNatListBool (2, (certificatePair input.1 input.2).2),
              graphBoolAndPair
                (HittingSet.natLeBool
                    ((certificatePair input.1 input.2).1.length, input.1.budget),
                  allEdgesLegalBool
                    ((input.1.graph.vertices, certificatePair input.1 input.2),
                      input.1.graph.edges))))) :=
    TMPolyTimeMap.prod_mk colorLengthOKTM valuesTailTM
  have lengthTailTM : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        graphBoolAndPair
          (HittingSet.natLeBool
              (input.1.graph.vertices, (certificatePair input.1 input.2).2.length),
            graphBoolAndPair
              (HittingSet.boundedNatListBool (2, (certificatePair input.1 input.2).2),
                graphBoolAndPair
                  (HittingSet.natLeBool
                      ((certificatePair input.1 input.2).1.length, input.1.budget),
                    allEdgesLegalBool
                      ((input.1.graph.vertices, certificatePair input.1 input.2),
                        input.1.graph.edges))))) := by
    have composed := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime lengthTailInputTM
    simpa [Function.comp] using composed
  have boundsTailInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : X.Carrier =>
        (edgesWithinBoundsBool
            ((input.1.graph.vertices, input.1.graph.vertices), input.1.graph.edges),
          graphBoolAndPair
            (HittingSet.natLeBool
                (input.1.graph.vertices, (certificatePair input.1 input.2).2.length),
              graphBoolAndPair
                (HittingSet.boundedNatListBool (2, (certificatePair input.1 input.2).2),
                  graphBoolAndPair
                    (HittingSet.natLeBool
                        ((certificatePair input.1 input.2).1.length, input.1.budget),
                      allEdgesLegalBool
                        ((input.1.graph.vertices, certificatePair input.1 input.2),
                          input.1.graph.edges)))))) :=
    TMPolyTimeMap.prod_mk boundsOKTM lengthTailTM
  have boundsTailTM : TMPolyTimeMap X EncodedType.bool
      (fun input : X.Carrier =>
        graphBoolAndPair
          (edgesWithinBoundsBool
              ((input.1.graph.vertices, input.1.graph.vertices), input.1.graph.edges),
            graphBoolAndPair
              (HittingSet.natLeBool
                  (input.1.graph.vertices, (certificatePair input.1 input.2).2.length),
                graphBoolAndPair
                  (HittingSet.boundedNatListBool (2, (certificatePair input.1 input.2).2),
                    graphBoolAndPair
                      (HittingSet.natLeBool
                          ((certificatePair input.1 input.2).1.length, input.1.budget),
                        allEdgesLegalBool
                          ((input.1.graph.vertices, certificatePair input.1 input.2),
                            input.1.graph.edges)))))) := by
    have composed := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime boundsTailInputTM
    simpa [Function.comp] using composed
  have allInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : X.Carrier =>
        (Bool.not input.1.graph.directed,
          graphBoolAndPair
            (edgesWithinBoundsBool
                ((input.1.graph.vertices, input.1.graph.vertices), input.1.graph.edges),
              graphBoolAndPair
                (HittingSet.natLeBool
                    (input.1.graph.vertices, (certificatePair input.1 input.2).2.length),
                  graphBoolAndPair
                    (HittingSet.boundedNatListBool
                        (2, (certificatePair input.1 input.2).2),
                      graphBoolAndPair
                        (HittingSet.natLeBool
                            ((certificatePair input.1 input.2).1.length, input.1.budget),
                          allEdgesLegalBool
                            ((input.1.graph.vertices, certificatePair input.1 input.2),
                              input.1.graph.edges))))))) :=
    TMPolyTimeMap.prod_mk undirectedTM boundsTailTM
  have allTM := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime allInputTM
  simpa [Function.comp, finiteVerify, X] using allTM

/-- The exact direct-TM-backed checker primitive. -/
@[complexity_reduction_ir_typed_primitive]
noncomputable def checkerPrimitive :
    Primitive (StandardInstances.prod problem.representation natListPresentation)
      StandardInstances.bool :=
  Primitive.ofTMPolyTime
    (fun input => finiteVerify input.1 input.2)
    (by
      simpa [problem,
        Presentation.NodeDeletionBipartite.presentedProblem,
        Presentation.NodeDeletionBipartite.structuredPresentation,
        natListPresentation, natListEncodedType, StandardInstances.prod,
        StandardInstances.bool, certificateEncodedType] using finiteVerify_tmPolyTime)

/-- The one checker program used by the certified verifier and its compiled TM. -/
noncomputable def checker :
    PolyProg (StandardInstances.prod problem.representation natListPresentation)
      StandardInstances.bool :=
  .atom checkerPrimitive

@[simp] theorem checker_run
    (input : problem.Instance × List Nat) :
    checker.run input = finiteVerify input.1 input.2 :=
  rfl

noncomputable def verifierData : NatListVerifierData problem where
  checker := checker
  witnessBound := fun input =>
    10 * problem.representation.encodedType.inputSize input ^ 2 + 10
  witnessBoundPoly := ComplexityReduction.PolynomialTimeBound.intro_with 2 10 10 (by
    intro input
    simp)
  correct := by
    intro input
    change Presentation.NodeDeletionBipartite.IsYes input ↔
      ∃ candidate : List Nat,
        natListEncodedType.inputSize candidate ≤
            10 * Presentation.NodeDeletionBipartite.structuredEncodedType.inputSize input ^ 2 +
              10 ∧
          finiteVerify input candidate = true
    constructor
    · rintro ⟨undirected, wellFormed, deleted, deletedNodup, deletedBounds,
        deletedLength, color, edgeLegal⟩
      let colors := colorTable input color
      refine ⟨colors ++ deleted, ?_, ?_⟩
      · simpa [colors, certificateEncodedType, natListEncodedType] using
          certificate_inputSize_le_poly input deletedBounds deletedLength color
      · apply (finiteVerify_eq_true_iff input (colors ++ deleted)).2
        have pairEquality : certificatePair input (colors ++ deleted) = (deleted, colors) :=
          certificatePair_append_of_colorLength input colors deleted (by simp [colors])
        rw [pairEquality]
        refine ⟨undirected, wellFormed, ?_, colorTable_values_lt_two input color,
          deletedLength, ?_⟩
        · simp [colors]
        · intro edge edgeMember
          have bounds := wellFormed edge edgeMember
          apply (edgeLegalBool_eq_true_iff_of_bounds
            input.graph.vertices deleted colors edge bounds.1 bounds.2).2
          rcases edgeLegal edge edgeMember with leftDeleted | rightDeleted | different
          · exact Or.inl leftDeleted
          · exact Or.inr (Or.inl rightDeleted)
          · right
            right
            rw [show colors.getD edge.1 0 = boolToNat (color edge.1) by
                exact colorTable_getD input color bounds.1,
              show colors.getD edge.2 0 = boolToNat (color edge.2) by
                exact colorTable_getD input color bounds.2]
            cases leftColor : color edge.1 <;>
              cases rightColor : color edge.2 <;>
              simp_all [boolToNat]
    · rintro ⟨candidate, _bound, accepted⟩
      exact finiteVerify_sound input candidate accepted
  checkerSound := by
    intro input candidate accepted
    change Presentation.NodeDeletionBipartite.IsYes input
    exact finiteVerify_sound input candidate accepted

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

end NodeDeletionBipartiteMembership
end Domain
end ComplexityReduction

assert_standard_axioms
  ComplexityReduction.Domain.NodeDeletionBipartiteMembership.edgeLegalBool_tmPolyTime,
  ComplexityReduction.Domain.NodeDeletionBipartiteMembership.allEdgesLegalBool_tmPolyTime,
  ComplexityReduction.Domain.NodeDeletionBipartiteMembership.edgesWithinBoundsBool_tmPolyTime,
  ComplexityReduction.Domain.NodeDeletionBipartiteMembership.finiteVerify_tmPolyTime,
  ComplexityReduction.Domain.NodeDeletionBipartiteMembership.certificate_inputSize_le_poly,
  ComplexityReduction.Domain.NodeDeletionBipartiteMembership.verifier,
  ComplexityReduction.Domain.NodeDeletionBipartiteMembership.witnessPresentation,
  ComplexityReduction.Domain.NodeDeletionBipartiteMembership.discipline,
  ComplexityReduction.Domain.NodeDeletionBipartiteMembership.template
