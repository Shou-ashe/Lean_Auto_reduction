/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.Agent.Hardness.FiniteWitnessNative
import ComplexityReduction.Domain.NodeDeletionBipartiteMembership
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ListLookupTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.ExactWrapper
import ComplexityReduction.Presentation.MostNeighbors
import ComplexityReduction.Program.ContextListAll
import ComplexityReduction.Program.ContextListAny
import Mathlib.Tactic

/-!
Native unary-nat-list NP membership for Most Neighbors.

The certificate is the exact total three-value assignment from the public
presentation.  Marker counting is implemented as a reusable indicator-map
followed by the standard direct-TM unary list sum.  External support uses a
nested universal-over-vertices / existential-over-edges checker, retaining the
assignment as explicit context throughout.
-/

namespace ComplexityReduction
namespace Domain
namespace MostNeighborsMembership

open Encoding
open Certificate
open Program
open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.Karp21
open ComplexityReduction.Agent.Hardness.FiniteWitness
open ComplexityReduction.Agent.Hardness.FiniteWitnessNative

abbrev problem : PresentedProblem :=
  Presentation.MostNeighbors.presentedProblem

abbrev certificateEncodedType : EncodedType := setStructuredEncodedType

abbrev natListEncodedType : EncodedType := natListPresentation.encodedType

abbrev edgeEncodedType : EncodedType := edgeStructuredEncodedType

abbrev edgeListEncodedType : EncodedType := edgeListStructuredEncodedType

/-- Boolean equality on unary naturals. -/
def natEqBool (input : Nat × Nat) : Bool :=
  decide (input.1 = input.2)

@[simp] theorem natEqBool_eq_true_iff (input : Nat × Nat) :
    natEqBool input = true ↔ input.1 = input.2 := by
  simp [natEqBool]

theorem natEqBool_tmPolyTime :
    TMPolyTimeMap (EncodedType.prod EncodedType.nat EncodedType.nat)
      EncodedType.bool natEqBool := by
  simpa [natEqBool] using TMPolyTimeMap.nat_eq

/-! ### Reusable marker counting -/

/-- A unary `1` exactly for the public outside-neighbour marker. -/
def outsideIndicator (value : Nat) : Nat :=
  boolToNat (decide (value = Presentation.MostNeighbors.outsideMarker))

@[simp] theorem outsideIndicator_eq_one_iff (value : Nat) :
    outsideIndicator value = 1 ↔
      value = Presentation.MostNeighbors.outsideMarker := by
  by_cases marker : value = Presentation.MostNeighbors.outsideMarker
  · simp [outsideIndicator, marker, boolToNat]
  · simp [outsideIndicator, marker, boolToNat]

theorem outsideIndicator_tmPolyTime :
    TMPolyTimeMap EncodedType.nat EncodedType.nat outsideIndicator := by
  let X := EncodedType.nat
  have value : TMPolyTimeMap X EncodedType.nat (fun value : Nat => value) :=
    TMPolyTimeMap.id X
  have marker : TMPolyTimeMap X EncodedType.nat
      (fun _value : Nat => Presentation.MostNeighbors.outsideMarker) :=
    TMPolyTimeMap.const X EncodedType.nat Presentation.MostNeighbors.outsideMarker
  have equalityInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun value : Nat =>
        (value, Presentation.MostNeighbors.outsideMarker)) :=
    TMPolyTimeMap.prod_mk value marker
  have equality : TMPolyTimeMap X EncodedType.bool
      (fun value : Nat =>
        decide (value = Presentation.MostNeighbors.outsideMarker)) := by
    have composed := TMPolyTimeMap.comp TMPolyTimeMap.nat_eq equalityInput
    simpa [Function.comp] using composed
  have composed := TMPolyTimeMap.comp boolToNat_tm_polytime equality
  simpa [Function.comp, outsideIndicator] using composed

/-- Count occurrences of the outside marker by direct-TM map plus unary sum. -/
def outsideCount (assignment : List Nat) : Nat :=
  Partition.natListSum (assignment.map outsideIndicator)

theorem outsideCount_eq_countP (assignment : List Nat) :
    outsideCount assignment =
      assignment.countP fun value =>
        decide (value = Presentation.MostNeighbors.outsideMarker) := by
  rw [outsideCount, Partition.natListSum_eq_sum]
  induction assignment with
  | nil => simp
  | cons value rest inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, List.countP_cons]
      by_cases marker : value = Presentation.MostNeighbors.outsideMarker
      · simp [outsideIndicator, marker, inductionHypothesis, boolToNat, Nat.add_comm]
      · simp [outsideIndicator, marker, inductionHypothesis, boolToNat]

theorem outsideCount_tmPolyTime :
    TMPolyTimeMap natListEncodedType EncodedType.nat outsideCount := by
  have indicators : TMPolyTimeMap natListEncodedType natListEncodedType
      (fun assignment : List Nat => assignment.map outsideIndicator) := by
    simpa [natListEncodedType, natListPresentation, setStructuredEncodedType] using
      TMPolyTimeMap.list_map outsideIndicator_tmPolyTime
  have composed := TMPolyTimeMap.comp Partition.natListSum_tm_polytime indicators
  simpa [Function.comp, outsideCount, natListEncodedType, natListPresentation,
    setStructuredEncodedType] using composed

private theorem range_map_getD (assignment : List Nat) :
    (List.range assignment.length).map
        (fun index => assignment.getD index 0) = assignment := by
  apply List.ext_get
  · simp
  · intro index leftBound rightBound
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [List.getElem_map, List.getElem_range]
    exact List.getD_eq_getElem (l := assignment) (d := 0) (n := index) rightBound

/-- The executable marker count is exactly the public finite-set cardinality. -/
theorem outsideVertices_card_eq_outsideCount_of_length
    (input : Presentation.MostNeighbors.Input) (assignment : List Nat)
    (lengthEquality : assignment.length = input.graph.vertices) :
    (Presentation.MostNeighbors.outsideVertices input assignment).card =
      outsideCount assignment := by
  let predicate : Nat → Bool := fun value =>
    decide (value = Presentation.MostNeighbors.outsideMarker)
  let indexPredicate : Nat → Bool := fun index =>
    predicate (assignment.getD index 0)
  have rangeNodup : (List.range input.graph.vertices).Nodup :=
    List.nodup_range
  have filteredNodup :
      ((List.range input.graph.vertices).filter indexPredicate).Nodup :=
    rangeNodup.filter _
  have toFinsetEquality :
      ((List.range input.graph.vertices).filter indexPredicate).toFinset =
        Presentation.MostNeighbors.outsideVertices input assignment := by
    ext vertex
    simp [indexPredicate, predicate, Presentation.MostNeighbors.outsideVertices,
      Presentation.MostNeighbors.assignmentValue]
  rw [← toFinsetEquality, List.toFinset_card_of_nodup filteredNodup,
    outsideCount_eq_countP]
  rw [← lengthEquality] at filteredNodup ⊢
  conv_rhs =>
    rw [← range_map_getD assignment]
  rw [List.countP_map, List.countP_eq_length_filter]
  rfl

/-! ### Existential edge support -/

/-- Retained assignment and the outside vertex currently being checked. -/
def supportContextEncodedType : EncodedType :=
  EncodedType.prod natListEncodedType EncodedType.nat

/-- Exact input codec for one context-indexed raw graph edge. -/
def edgeSupportInputEncodedType : EncodedType :=
  EncodedType.prod supportContextEncodedType edgeEncodedType

/-- Total assignment lookup through the reusable encoded-list scanner. -/
def assignmentAt (input : List Nat × Nat) : Nat :=
  input.1.getD input.2 0

theorem assignmentAt_tmPolyTime :
    TMPolyTimeMap (EncodedType.prod natListEncodedType EncodedType.nat)
      EncodedType.nat assignmentAt := by
  simpa [assignmentAt, natListEncodedType, natListPresentation,
    setStructuredEncodedType, Karp21.EncodedListLookup.getD] using
      (Karp21.EncodedListLookup.getD_tm_polytime EncodedType.nat (0 : Nat))

/-- One raw edge supports the outside vertex in either stored orientation. -/
def edgeSupportsBool (input : (List Nat × Nat) × (Nat × Nat)) : Bool :=
  graphBoolOrPair
    (graphBoolAndPair
      (natEqBool (input.2.1, input.1.2),
        natEqBool
          (assignmentAt (input.1.1, input.2.2),
            Presentation.MostNeighbors.selectedMarker)),
      graphBoolAndPair
        (natEqBool (input.2.2, input.1.2),
          natEqBool
            (assignmentAt (input.1.1, input.2.1),
              Presentation.MostNeighbors.selectedMarker)))

theorem edgeSupportsBool_eq_true_iff
    (assignment : List Nat) (vertex : Nat) (edge : Nat × Nat) :
    edgeSupportsBool ((assignment, vertex), edge) = true ↔
      (edge.1 = vertex ∧
          Presentation.MostNeighbors.assignmentValue assignment edge.2 =
            Presentation.MostNeighbors.selectedMarker) ∨
        (edge.2 = vertex ∧
          Presentation.MostNeighbors.assignmentValue assignment edge.1 =
            Presentation.MostNeighbors.selectedMarker) := by
  simp [edgeSupportsBool, graphBoolOrPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff, natEqBool_eq_true_iff,
    assignmentAt, Presentation.MostNeighbors.assignmentValue]

theorem edgeSupportsBool_tmPolyTime :
    TMPolyTimeMap edgeSupportInputEncodedType EncodedType.bool edgeSupportsBool := by
  let X := edgeSupportInputEncodedType
  have context : TMPolyTimeMap X supportContextEncodedType
      (fun input : (List Nat × Nat) × (Nat × Nat) => input.1) := by
    simpa [X, edgeSupportInputEncodedType] using
      TMPolyTimeMap.fst supportContextEncodedType edgeEncodedType
  have edge : TMPolyTimeMap X edgeEncodedType
      (fun input : (List Nat × Nat) × (Nat × Nat) => input.2) := by
    simpa [X, edgeSupportInputEncodedType] using
      TMPolyTimeMap.snd supportContextEncodedType edgeEncodedType
  have assignment : TMPolyTimeMap X natListEncodedType
      (fun input : (List Nat × Nat) × (Nat × Nat) => input.1.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst natListEncodedType EncodedType.nat) context
    simpa [Function.comp, supportContextEncodedType, X] using composed
  have vertex : TMPolyTimeMap X EncodedType.nat
      (fun input : (List Nat × Nat) × (Nat × Nat) => input.1.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd natListEncodedType EncodedType.nat) context
    simpa [Function.comp, supportContextEncodedType, X] using composed
  have left : TMPolyTimeMap X EncodedType.nat
      (fun input : (List Nat × Nat) × (Nat × Nat) => input.2.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst EncodedType.nat EncodedType.nat) edge
    simpa [Function.comp, edgeEncodedType, X] using composed
  have right : TMPolyTimeMap X EncodedType.nat
      (fun input : (List Nat × Nat) × (Nat × Nat) => input.2.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat EncodedType.nat) edge
    simpa [Function.comp, edgeEncodedType, X] using composed
  have leftVertexInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : (List Nat × Nat) × (Nat × Nat) =>
        (input.2.1, input.1.2)) :=
    TMPolyTimeMap.prod_mk left vertex
  have leftVertexEq : TMPolyTimeMap X EncodedType.bool
      (fun input : (List Nat × Nat) × (Nat × Nat) =>
        natEqBool (input.2.1, input.1.2)) := by
    have composed := TMPolyTimeMap.comp natEqBool_tmPolyTime leftVertexInput
    simpa [Function.comp] using composed
  have rightVertexInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : (List Nat × Nat) × (Nat × Nat) =>
        (input.2.2, input.1.2)) :=
    TMPolyTimeMap.prod_mk right vertex
  have rightVertexEq : TMPolyTimeMap X EncodedType.bool
      (fun input : (List Nat × Nat) × (Nat × Nat) =>
        natEqBool (input.2.2, input.1.2)) := by
    have composed := TMPolyTimeMap.comp natEqBool_tmPolyTime rightVertexInput
    simpa [Function.comp] using composed
  have leftLookupInput : TMPolyTimeMap X
      (EncodedType.prod natListEncodedType EncodedType.nat)
      (fun input : (List Nat × Nat) × (Nat × Nat) =>
        (input.1.1, input.2.1)) :=
    TMPolyTimeMap.prod_mk assignment left
  have leftValue : TMPolyTimeMap X EncodedType.nat
      (fun input : (List Nat × Nat) × (Nat × Nat) =>
        assignmentAt (input.1.1, input.2.1)) := by
    have composed := TMPolyTimeMap.comp assignmentAt_tmPolyTime leftLookupInput
    simpa [Function.comp] using composed
  have rightLookupInput : TMPolyTimeMap X
      (EncodedType.prod natListEncodedType EncodedType.nat)
      (fun input : (List Nat × Nat) × (Nat × Nat) =>
        (input.1.1, input.2.2)) :=
    TMPolyTimeMap.prod_mk assignment right
  have rightValue : TMPolyTimeMap X EncodedType.nat
      (fun input : (List Nat × Nat) × (Nat × Nat) =>
        assignmentAt (input.1.1, input.2.2)) := by
    have composed := TMPolyTimeMap.comp assignmentAt_tmPolyTime rightLookupInput
    simpa [Function.comp] using composed
  have selected : TMPolyTimeMap X EncodedType.nat
      (fun _input : (List Nat × Nat) × (Nat × Nat) =>
        Presentation.MostNeighbors.selectedMarker) :=
    TMPolyTimeMap.const X EncodedType.nat Presentation.MostNeighbors.selectedMarker
  have leftSelectedInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : (List Nat × Nat) × (Nat × Nat) =>
        (assignmentAt (input.1.1, input.2.1),
          Presentation.MostNeighbors.selectedMarker)) :=
    TMPolyTimeMap.prod_mk leftValue selected
  have leftSelected : TMPolyTimeMap X EncodedType.bool
      (fun input : (List Nat × Nat) × (Nat × Nat) =>
        natEqBool
          (assignmentAt (input.1.1, input.2.1),
            Presentation.MostNeighbors.selectedMarker)) := by
    have composed := TMPolyTimeMap.comp natEqBool_tmPolyTime leftSelectedInput
    simpa [Function.comp] using composed
  have rightSelectedInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : (List Nat × Nat) × (Nat × Nat) =>
        (assignmentAt (input.1.1, input.2.2),
          Presentation.MostNeighbors.selectedMarker)) :=
    TMPolyTimeMap.prod_mk rightValue selected
  have rightSelected : TMPolyTimeMap X EncodedType.bool
      (fun input : (List Nat × Nat) × (Nat × Nat) =>
        natEqBool
          (assignmentAt (input.1.1, input.2.2),
            Presentation.MostNeighbors.selectedMarker)) := by
    have composed := TMPolyTimeMap.comp natEqBool_tmPolyTime rightSelectedInput
    simpa [Function.comp] using composed
  have firstConjunctionInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : (List Nat × Nat) × (Nat × Nat) =>
        (natEqBool (input.2.1, input.1.2),
          natEqBool
            (assignmentAt (input.1.1, input.2.2),
              Presentation.MostNeighbors.selectedMarker))) :=
    TMPolyTimeMap.prod_mk leftVertexEq rightSelected
  have firstConjunction : TMPolyTimeMap X EncodedType.bool
      (fun input : (List Nat × Nat) × (Nat × Nat) =>
        graphBoolAndPair
          (natEqBool (input.2.1, input.1.2),
            natEqBool
              (assignmentAt (input.1.1, input.2.2),
                Presentation.MostNeighbors.selectedMarker))) := by
    have composed := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime
      firstConjunctionInput
    simpa [Function.comp] using composed
  have secondConjunctionInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : (List Nat × Nat) × (Nat × Nat) =>
        (natEqBool (input.2.2, input.1.2),
          natEqBool
            (assignmentAt (input.1.1, input.2.1),
              Presentation.MostNeighbors.selectedMarker))) :=
    TMPolyTimeMap.prod_mk rightVertexEq leftSelected
  have secondConjunction : TMPolyTimeMap X EncodedType.bool
      (fun input : (List Nat × Nat) × (Nat × Nat) =>
        graphBoolAndPair
          (natEqBool (input.2.2, input.1.2),
            natEqBool
              (assignmentAt (input.1.1, input.2.1),
                Presentation.MostNeighbors.selectedMarker))) := by
    have composed := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime
      secondConjunctionInput
    simpa [Function.comp] using composed
  have disjunctionInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : (List Nat × Nat) × (Nat × Nat) =>
        (graphBoolAndPair
          (natEqBool (input.2.1, input.1.2),
            natEqBool
              (assignmentAt (input.1.1, input.2.2),
                Presentation.MostNeighbors.selectedMarker)),
          graphBoolAndPair
            (natEqBool (input.2.2, input.1.2),
              natEqBool
                (assignmentAt (input.1.1, input.2.1),
                  Presentation.MostNeighbors.selectedMarker)))) :=
    TMPolyTimeMap.prod_mk firstConjunction secondConjunction
  have composed := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime disjunctionInput
  simpa [Function.comp, edgeSupportsBool, X] using composed

/-- Existential support scan over one explicit edge list. -/
def someEdgeSupportsBool
    (input : (List Nat × Nat) × List (Nat × Nat)) : Bool :=
  ContextListAny.executable
    (C := supportContextEncodedType) (X := edgeEncodedType)
    edgeSupportsBool input

theorem someEdgeSupportsBool_eq_true_iff
    (context : List Nat × Nat) (edges : List (Nat × Nat)) :
    someEdgeSupportsBool (context, edges) = true ↔
      ∃ edge ∈ edges, edgeSupportsBool (context, edge) = true := by
  exact ContextListAny.executable_eq_true_iff
    (C := supportContextEncodedType) (X := edgeEncodedType)
    edgeSupportsBool context edges

theorem someEdgeSupportsBool_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod supportContextEncodedType edgeListEncodedType)
      EncodedType.bool someEdgeSupportsBool := by
  simpa [someEdgeSupportsBool] using
    ContextListAny.executable_tmPolyTime
      (C := supportContextEncodedType) (X := edgeEncodedType)
      edgeSupportsBool edgeSupportsBool_tmPolyTime

/-! ### Universal outside-vertex support -/

def vertexContextEncodedType : EncodedType :=
  EncodedType.prod natListEncodedType edgeListEncodedType

def vertexSupportInputEncodedType : EncodedType :=
  EncodedType.prod vertexContextEncodedType EncodedType.nat

/-- Non-outside vertices pass immediately; outside vertices need one support edge. -/
def vertexLegalBool (input : (List Nat × List (Nat × Nat)) × Nat) : Bool :=
  graphBoolOrPair
    (Bool.not
      (natEqBool
        (assignmentAt (input.1.1, input.2),
          Presentation.MostNeighbors.outsideMarker)),
      someEdgeSupportsBool ((input.1.1, input.2), input.1.2))

theorem vertexLegalBool_eq_true_iff
    (assignment : List Nat) (edges : List (Nat × Nat)) (vertex : Nat) :
    vertexLegalBool ((assignment, edges), vertex) = true ↔
      Presentation.MostNeighbors.assignmentValue assignment vertex ≠
          Presentation.MostNeighbors.outsideMarker ∨
        ∃ edge ∈ edges, edgeSupportsBool ((assignment, vertex), edge) = true := by
  rw [vertexLegalBool, graphBoolOrPair_eq_true_iff]
  simp only [Bool.not_eq_true']
  rw [someEdgeSupportsBool_eq_true_iff]
  simp [natEqBool, assignmentAt, Presentation.MostNeighbors.assignmentValue]

theorem vertexLegalBool_tmPolyTime :
    TMPolyTimeMap vertexSupportInputEncodedType EncodedType.bool vertexLegalBool := by
  let X := vertexSupportInputEncodedType
  have context : TMPolyTimeMap X vertexContextEncodedType
      (fun input : (List Nat × List (Nat × Nat)) × Nat => input.1) := by
    simpa [X, vertexSupportInputEncodedType] using
      TMPolyTimeMap.fst vertexContextEncodedType EncodedType.nat
  have vertex : TMPolyTimeMap X EncodedType.nat
      (fun input : (List Nat × List (Nat × Nat)) × Nat => input.2) := by
    simpa [X, vertexSupportInputEncodedType] using
      TMPolyTimeMap.snd vertexContextEncodedType EncodedType.nat
  have assignment : TMPolyTimeMap X natListEncodedType
      (fun input : (List Nat × List (Nat × Nat)) × Nat => input.1.1) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst natListEncodedType edgeListEncodedType) context
    simpa [Function.comp, vertexContextEncodedType, X] using composed
  have edges : TMPolyTimeMap X edgeListEncodedType
      (fun input : (List Nat × List (Nat × Nat)) × Nat => input.1.2) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd natListEncodedType edgeListEncodedType) context
    simpa [Function.comp, vertexContextEncodedType, X] using composed
  have lookupInput : TMPolyTimeMap X
      (EncodedType.prod natListEncodedType EncodedType.nat)
      (fun input : (List Nat × List (Nat × Nat)) × Nat =>
        (input.1.1, input.2)) :=
    TMPolyTimeMap.prod_mk assignment vertex
  have value : TMPolyTimeMap X EncodedType.nat
      (fun input : (List Nat × List (Nat × Nat)) × Nat =>
        assignmentAt (input.1.1, input.2)) := by
    have composed := TMPolyTimeMap.comp assignmentAt_tmPolyTime lookupInput
    simpa [Function.comp] using composed
  have marker : TMPolyTimeMap X EncodedType.nat
      (fun _input : (List Nat × List (Nat × Nat)) × Nat =>
        Presentation.MostNeighbors.outsideMarker) :=
    TMPolyTimeMap.const X EncodedType.nat Presentation.MostNeighbors.outsideMarker
  have markerInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : (List Nat × List (Nat × Nat)) × Nat =>
        (assignmentAt (input.1.1, input.2),
          Presentation.MostNeighbors.outsideMarker)) :=
    TMPolyTimeMap.prod_mk value marker
  have isOutside : TMPolyTimeMap X EncodedType.bool
      (fun input : (List Nat × List (Nat × Nat)) × Nat =>
        natEqBool
          (assignmentAt (input.1.1, input.2),
            Presentation.MostNeighbors.outsideMarker)) := by
    have composed := TMPolyTimeMap.comp natEqBool_tmPolyTime markerInput
    simpa [Function.comp] using composed
  have notOutside : TMPolyTimeMap X EncodedType.bool
      (fun input : (List Nat × List (Nat × Nat)) × Nat =>
        Bool.not
          (natEqBool
            (assignmentAt (input.1.1, input.2),
              Presentation.MostNeighbors.outsideMarker))) := by
    have composed := TMPolyTimeMap.comp TMPolyTimeMap.bool_not isOutside
    simpa [Function.comp] using composed
  have supportContext : TMPolyTimeMap X supportContextEncodedType
      (fun input : (List Nat × List (Nat × Nat)) × Nat =>
        (input.1.1, input.2)) := by
    simpa [supportContextEncodedType] using TMPolyTimeMap.prod_mk assignment vertex
  have supportInput : TMPolyTimeMap X
      (EncodedType.prod supportContextEncodedType edgeListEncodedType)
      (fun input : (List Nat × List (Nat × Nat)) × Nat =>
        ((input.1.1, input.2), input.1.2)) :=
    TMPolyTimeMap.prod_mk supportContext edges
  have supported : TMPolyTimeMap X EncodedType.bool
      (fun input : (List Nat × List (Nat × Nat)) × Nat =>
        someEdgeSupportsBool ((input.1.1, input.2), input.1.2)) := by
    have composed := TMPolyTimeMap.comp someEdgeSupportsBool_tmPolyTime supportInput
    simpa [Function.comp] using composed
  have disjunctionInput : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : (List Nat × List (Nat × Nat)) × Nat =>
        (Bool.not
          (natEqBool
            (assignmentAt (input.1.1, input.2),
              Presentation.MostNeighbors.outsideMarker)),
          someEdgeSupportsBool ((input.1.1, input.2), input.1.2))) :=
    TMPolyTimeMap.prod_mk notOutside supported
  have composed := TMPolyTimeMap.comp graphBoolOrPair_tm_polytime disjunctionInput
  simpa [Function.comp, vertexLegalBool, X] using composed

/-- Check every in-range vertex against the same assignment and edge list. -/
def allOutsideSupportedBool
    (input : (List Nat × List (Nat × Nat)) × List Nat) : Bool :=
  ContextListAll.executable
    (C := vertexContextEncodedType) (X := EncodedType.nat)
    vertexLegalBool input

theorem allOutsideSupportedBool_eq_true_iff
    (context : List Nat × List (Nat × Nat)) (vertices : List Nat) :
    allOutsideSupportedBool (context, vertices) = true ↔
      ∀ vertex ∈ vertices, vertexLegalBool (context, vertex) = true := by
  exact ContextListAll.executable_eq_true_iff
    (C := vertexContextEncodedType) (X := EncodedType.nat)
    vertexLegalBool context vertices

theorem allOutsideSupportedBool_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod vertexContextEncodedType
        (EncodedType.list EncodedType.nat))
      EncodedType.bool allOutsideSupportedBool := by
  simpa [allOutsideSupportedBool] using
    ContextListAll.executable_tmPolyTime
      (C := vertexContextEncodedType) (X := EncodedType.nat)
      vertexLegalBool vertexLegalBool_tmPolyTime

/-! ### Exact verifier semantics -/

/-- Exact flat-certificate verifier Boolean. -/
def finiteVerify
    (input : Presentation.MostNeighbors.Input) (assignment : List Nat) : Bool :=
  graphBoolAndPair
    (Bool.not input.graph.directed,
      graphBoolAndPair
        (NodeDeletionBipartiteMembership.edgesWithinBoundsBool
          ((input.graph.vertices, input.graph.vertices), input.graph.edges),
          graphBoolAndPair
            (natEqBool (assignment.length, input.graph.vertices),
              graphBoolAndPair
                (HittingSet.boundedNatListBool (3, assignment),
                  graphBoolAndPair
                    (HittingSet.natLeBool
                      (input.threshold, outsideCount assignment),
                      allOutsideSupportedBool
                        ((assignment, input.graph.edges),
                          List.range input.graph.vertices))))))

theorem finiteVerify_eq_true_iff
    (input : Presentation.MostNeighbors.Input) (assignment : List Nat) :
    finiteVerify input assignment = true ↔
      input.graph.directed = false ∧
        WellFormed input.graph ∧
        assignment.length = input.graph.vertices ∧
        (∀ value ∈ assignment, value < 3) ∧
        input.threshold ≤ outsideCount assignment ∧
        ∀ vertex, vertex < input.graph.vertices →
          vertexLegalBool ((assignment, input.graph.edges), vertex) = true := by
  rw [finiteVerify, graphBoolAndPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff, graphBoolAndPair_eq_true_iff,
    graphBoolAndPair_eq_true_iff, graphBoolAndPair_eq_true_iff,
    NodeDeletionBipartiteMembership.edgesWithinBoundsBool_eq_true_iff,
    natEqBool_eq_true_iff, HittingSet.boundedNatListBool_eq_true_iff,
    HittingSet.natLeBool_eq_true_iff,
    allOutsideSupportedBool_eq_true_iff]
  simp [WellFormed, EdgeWithinBounds]

/-- Soundness against the exact public finite assignment semantics. -/
theorem finiteVerify_sound
    (input : Presentation.MostNeighbors.Input) (assignment : List Nat)
    (accepted : finiteVerify input assignment = true) :
    Presentation.MostNeighbors.IsYes input := by
  rcases (finiteVerify_eq_true_iff input assignment).1 accepted with
    ⟨undirected, wellFormed, assignmentLength, values, threshold, supported⟩
  refine ⟨undirected, wellFormed, assignment, assignmentLength, values, ?_, ?_⟩
  · rw [outsideVertices_card_eq_outsideCount_of_length input assignment assignmentLength]
    exact threshold
  · intro vertex vertexBound outsideValue
    have legal := supported vertex vertexBound
    rcases (vertexLegalBool_eq_true_iff assignment input.graph.edges vertex).1 legal with
      notOutside | support
    · exact False.elim (notOutside outsideValue)
    · rcases support with ⟨edge, edgeMember, edgeSupport⟩
      have bounds := wellFormed edge edgeMember
      rcases (edgeSupportsBool_eq_true_iff assignment vertex edge).1 edgeSupport with
        ⟨leftEq, selectedValue⟩ | ⟨rightEq, selectedValue⟩
      · refine ⟨edge.2, bounds.2, selectedValue, ?_⟩
        unfold HasUndirectedEdge
        apply Or.inr
        rw [← leftEq]
        exact edgeMember
      · refine ⟨edge.1, bounds.1, selectedValue, ?_⟩
        unfold HasUndirectedEdge
        apply Or.inl
        rw [← rightEq]
        exact edgeMember

/-- Completeness: the public assignment itself is accepted as a certificate. -/
theorem finiteVerify_complete
    (input : Presentation.MostNeighbors.Input)
    (yes : Presentation.MostNeighbors.IsYes input) :
    ∃ assignment : List Nat, finiteVerify input assignment = true := by
  rcases yes with ⟨undirected, wellFormed, assignment, witness⟩
  rcases witness with ⟨assignmentLength, values, threshold, supported⟩
  refine ⟨assignment, (finiteVerify_eq_true_iff input assignment).2 ?_⟩
  refine ⟨undirected, wellFormed, assignmentLength, values, ?_, ?_⟩
  · rw [← outsideVertices_card_eq_outsideCount_of_length input assignment assignmentLength]
    exact threshold
  · intro vertex vertexBound
    apply (vertexLegalBool_eq_true_iff assignment input.graph.edges vertex).2
    by_cases outsideValue :
        Presentation.MostNeighbors.assignmentValue assignment vertex =
          Presentation.MostNeighbors.outsideMarker
    · right
      rcases supported vertex vertexBound outsideValue with
        ⟨selected, selectedBound, selectedValue, adjacent⟩
      rcases adjacent with forward | reverse
      · exact ⟨(selected, vertex), forward,
          (edgeSupportsBool_eq_true_iff assignment vertex (selected, vertex)).2
            (Or.inr ⟨rfl, selectedValue⟩)⟩
      · exact ⟨(vertex, selected), reverse,
          (edgeSupportsBool_eq_true_iff assignment vertex (vertex, selected)).2
            (Or.inl ⟨rfl, selectedValue⟩)⟩
    · exact Or.inl outsideValue

/-! ### Polynomial certificate bound and complete direct-TM checker -/

theorem structured_inputSize_eq
    (input : Presentation.MostNeighbors.Input) :
    Presentation.MostNeighbors.structuredEncodedType.inputSize input =
      graphStructuredEncodedType.inputSize input.graph + input.threshold + 2 := by
  change Presentation.MostNeighbors.tupleStructuredEncodedType.inputSize
      (input.graph, input.threshold) = _
  simp [Presentation.MostNeighbors.tupleStructuredEncodedType]
  omega

theorem certificate_inputSize_le_poly
    (input : Presentation.MostNeighbors.Input) (assignment : List Nat)
    (lengthEquality : assignment.length = input.graph.vertices)
    (values : ∀ value ∈ assignment, value < 3) :
    certificateEncodedType.inputSize assignment ≤
      10 * (Presentation.MostNeighbors.structuredEncodedType.inputSize input) ^ 2 + 10 := by
  let inputSize := Presentation.MostNeighbors.structuredEncodedType.inputSize input
  have assignmentSize :=
    ComplexityReduction.Problems.Karp21.HittingSetStandardTM.boundedNatList_inputSize_le
      3 assignment values
  have verticesSucc : input.graph.vertices + 1 ≤ inputSize := by
    rw [show inputSize =
      Presentation.MostNeighbors.structuredEncodedType.inputSize input by rfl,
      structured_inputSize_eq,
      ComplexityReduction.Karp21.VertexCover.graphStructured_inputSize_eq]
    omega
  have four : 4 ≤ inputSize := by
    rw [show inputSize =
      Presentation.MostNeighbors.structuredEncodedType.inputSize input by rfl,
      structured_inputSize_eq,
      ComplexityReduction.Karp21.VertexCover.graphStructured_inputSize_eq]
    omega
  calc
    certificateEncodedType.inputSize assignment
        ≤ assignment.length * 4 := by
          simpa [certificateEncodedType, setStructuredEncodedType] using assignmentSize
    _ = input.graph.vertices * 4 := by rw [lengthEquality]
    _ ≤ inputSize * inputSize :=
      Nat.mul_le_mul (Nat.le_trans (Nat.le_succ _) verticesSucc) four
    _ ≤ 10 * inputSize ^ 2 + 10 := by nlinarith

def inputToTuple (input : Presentation.MostNeighbors.Input) :
    Presentation.MostNeighbors.tupleStructuredEncodedType.Carrier :=
  (input.graph, input.threshold)

private theorem inputToTuple_encode
    (input : Presentation.MostNeighbors.Input) :
    Presentation.MostNeighbors.tupleStructuredEncodedType.encode
        (inputToTuple input) =
      Presentation.MostNeighbors.structuredEncodedType.encode input :=
  rfl

private noncomputable def inputToTupleTMBackedMap :
    TMBackedCostedMap Presentation.MostNeighbors.structuredEncodedType
      Presentation.MostNeighbors.tupleStructuredEncodedType inputToTuple :=
  TMBackedCostedMap.ofEncodingEquiv
    Presentation.MostNeighbors.structuredEncodedType
    Presentation.MostNeighbors.tupleStructuredEncodedType inputToTuple
    (Equiv.refl Presentation.MostNeighbors.tupleStructuredEncodedType.Symbol)
    (by
      intro input
      change Presentation.MostNeighbors.tupleStructuredEncodedType.encode
          (inputToTuple input) =
        (Presentation.MostNeighbors.structuredEncodedType.encode input).map id
      simp [inputToTuple_encode])

/-- The complete verifier is one direct-TM polynomial-time Boolean computation. -/
theorem finiteVerify_tmPolyTime :
    TMPolyTimeMap
      (EncodedType.prod Presentation.MostNeighbors.structuredEncodedType
        certificateEncodedType)
      EncodedType.bool
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        finiteVerify input.1 input.2) := by
  let X := EncodedType.prod Presentation.MostNeighbors.structuredEncodedType
    certificateEncodedType
  have instanceTM : TMPolyTimeMap X
      Presentation.MostNeighbors.structuredEncodedType
      (fun input : Presentation.MostNeighbors.Input × List Nat => input.1) := by
    simpa [X, certificateEncodedType] using
      TMPolyTimeMap.fst Presentation.MostNeighbors.structuredEncodedType
        setStructuredEncodedType
  have assignmentTM : TMPolyTimeMap X certificateEncodedType
      (fun input : Presentation.MostNeighbors.Input × List Nat => input.2) := by
    simpa [X, certificateEncodedType] using
      TMPolyTimeMap.snd Presentation.MostNeighbors.structuredEncodedType
        setStructuredEncodedType
  have tupleTM : TMPolyTimeMap X
      Presentation.MostNeighbors.tupleStructuredEncodedType
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        inputToTuple input.1) := by
    have composed := TMPolyTimeMap.comp inputToTupleTMBackedMap.tm_polytime instanceTM
    simpa [Function.comp, X] using composed
  have graphTM : TMPolyTimeMap X graphStructuredEncodedType
      (fun input : Presentation.MostNeighbors.Input × List Nat => input.1.graph) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst graphStructuredEncodedType EncodedType.nat) tupleTM
    simpa [Function.comp, inputToTuple,
      Presentation.MostNeighbors.tupleStructuredEncodedType, X] using composed
  have thresholdTM : TMPolyTimeMap X EncodedType.nat
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        input.1.threshold) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd graphStructuredEncodedType EncodedType.nat) tupleTM
    simpa [Function.comp, inputToTuple,
      Presentation.MostNeighbors.tupleStructuredEncodedType, X] using composed
  have verticesTM : TMPolyTimeMap X EncodedType.nat
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        input.1.graph.vertices) := by
    have composed := TMPolyTimeMap.comp graphVerticesTMBackedMap.tm_polytime graphTM
    simpa [Function.comp, X] using composed
  have graphPayloadTM : TMPolyTimeMap X graphPayloadStructuredEncodedType
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        graphPayloadOfGraph input.1.graph) := by
    have composed := TMPolyTimeMap.comp graphPayloadTMBackedMap.tm_polytime graphTM
    simpa [Function.comp, X] using composed
  have edgesTM : TMPolyTimeMap X edgeListEncodedType
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        input.1.graph.edges) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.fst edgeListEncodedType EncodedType.bool) graphPayloadTM
    simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X]
      using composed
  have directedTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        input.1.graph.directed) := by
    have composed := TMPolyTimeMap.comp
      (TMPolyTimeMap.snd edgeListEncodedType EncodedType.bool) graphPayloadTM
    simpa [Function.comp, graphPayloadOfGraph, graphPayloadStructuredEncodedType, X]
      using composed
  have undirectedTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        Bool.not input.1.graph.directed) := by
    have composed := TMPolyTimeMap.comp TMPolyTimeMap.bool_not directedTM
    simpa [Function.comp] using composed
  have assignmentLengthTM : TMPolyTimeMap X EncodedType.nat
      (fun input : Presentation.MostNeighbors.Input × List Nat => input.2.length) := by
    have composed := TMPolyTimeMap.comp
      (HittingSet.listLengthTMBackedMap EncodedType.nat).tm_polytime assignmentTM
    simpa [Function.comp, certificateEncodedType, setStructuredEncodedType] using composed
  have boundsContextTM : TMPolyTimeMap X
      IncidenceIRValidation.pairEncoding
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        (input.1.graph.vertices, input.1.graph.vertices)) := by
    simpa [IncidenceIRValidation.pairEncoding] using
      TMPolyTimeMap.prod_mk verticesTM verticesTM
  have boundsInputTM : TMPolyTimeMap X
      (EncodedType.prod
        IncidenceIRValidation.pairEncoding
        IncidenceIRValidation.pairListEncoding)
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        ((input.1.graph.vertices, input.1.graph.vertices), input.1.graph.edges)) :=
    TMPolyTimeMap.prod_mk boundsContextTM edgesTM
  have boundsTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        NodeDeletionBipartiteMembership.edgesWithinBoundsBool
          ((input.1.graph.vertices, input.1.graph.vertices), input.1.graph.edges)) := by
    have composed := TMPolyTimeMap.comp
      NodeDeletionBipartiteMembership.edgesWithinBoundsBool_tmPolyTime boundsInputTM
    simpa [Function.comp] using composed
  have lengthInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        (input.2.length, input.1.graph.vertices)) :=
    TMPolyTimeMap.prod_mk assignmentLengthTM verticesTM
  have lengthTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        natEqBool (input.2.length, input.1.graph.vertices)) := by
    have composed := TMPolyTimeMap.comp natEqBool_tmPolyTime lengthInputTM
    simpa [Function.comp] using composed
  have threeTM : TMPolyTimeMap X EncodedType.nat
      (fun _input : Presentation.MostNeighbors.Input × List Nat => (3 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (3 : Nat)
  have valuesInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat certificateEncodedType)
      (fun input : Presentation.MostNeighbors.Input × List Nat => ((3 : Nat), input.2)) :=
    TMPolyTimeMap.prod_mk threeTM assignmentTM
  have valuesTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        HittingSet.boundedNatListBool (3, input.2)) := by
    have composed := TMPolyTimeMap.comp HittingSet.boundedNatListBool_tm_polytime
      valuesInputTM
    simpa [Function.comp, certificateEncodedType, setStructuredEncodedType] using composed
  have outsideCountTM : TMPolyTimeMap X EncodedType.nat
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        outsideCount input.2) := by
    have composed := TMPolyTimeMap.comp outsideCount_tmPolyTime assignmentTM
    simpa [Function.comp, certificateEncodedType] using composed
  have thresholdInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        (input.1.threshold, outsideCount input.2)) :=
    TMPolyTimeMap.prod_mk thresholdTM outsideCountTM
  have thresholdCheckTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        HittingSet.natLeBool (input.1.threshold, outsideCount input.2)) := by
    have composed := TMPolyTimeMap.comp HittingSet.natLeBool_tm_polytime
      thresholdInputTM
    simpa [Function.comp] using composed
  have vertexRangeTM : TMPolyTimeMap X (EncodedType.list EncodedType.nat)
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        List.range input.1.graph.vertices) := by
    have composed := TMPolyTimeMap.comp natRange_tm_polytime verticesTM
    simpa [Function.comp] using composed
  have vertexContextTM : TMPolyTimeMap X vertexContextEncodedType
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        (input.2, input.1.graph.edges)) := by
    simpa [vertexContextEncodedType, certificateEncodedType] using
      TMPolyTimeMap.prod_mk assignmentTM edgesTM
  have supportInputTM : TMPolyTimeMap X
      (EncodedType.prod vertexContextEncodedType
        (EncodedType.list EncodedType.nat))
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        ((input.2, input.1.graph.edges), List.range input.1.graph.vertices)) :=
    TMPolyTimeMap.prod_mk vertexContextTM vertexRangeTM
  have supportTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        allOutsideSupportedBool
          ((input.2, input.1.graph.edges), List.range input.1.graph.vertices)) := by
    have composed := TMPolyTimeMap.comp allOutsideSupportedBool_tmPolyTime supportInputTM
    simpa [Function.comp] using composed
  have thresholdTailInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        (HittingSet.natLeBool (input.1.threshold, outsideCount input.2),
          allOutsideSupportedBool
            ((input.2, input.1.graph.edges), List.range input.1.graph.vertices))) :=
    TMPolyTimeMap.prod_mk thresholdCheckTM supportTM
  have thresholdTailTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        graphBoolAndPair
          (HittingSet.natLeBool (input.1.threshold, outsideCount input.2),
            allOutsideSupportedBool
              ((input.2, input.1.graph.edges), List.range input.1.graph.vertices))) := by
    have composed := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime thresholdTailInputTM
    simpa [Function.comp] using composed
  have valuesTailInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        (HittingSet.boundedNatListBool (3, input.2),
          graphBoolAndPair
            (HittingSet.natLeBool (input.1.threshold, outsideCount input.2),
              allOutsideSupportedBool
                ((input.2, input.1.graph.edges),
                  List.range input.1.graph.vertices)))) :=
    TMPolyTimeMap.prod_mk valuesTM thresholdTailTM
  have valuesTailTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        graphBoolAndPair
          (HittingSet.boundedNatListBool (3, input.2),
            graphBoolAndPair
              (HittingSet.natLeBool (input.1.threshold, outsideCount input.2),
                allOutsideSupportedBool
                  ((input.2, input.1.graph.edges),
                    List.range input.1.graph.vertices)))) := by
    have composed := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime valuesTailInputTM
    simpa [Function.comp] using composed
  have lengthTailInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        (natEqBool (input.2.length, input.1.graph.vertices),
          graphBoolAndPair
            (HittingSet.boundedNatListBool (3, input.2),
              graphBoolAndPair
                (HittingSet.natLeBool (input.1.threshold, outsideCount input.2),
                  allOutsideSupportedBool
                    ((input.2, input.1.graph.edges),
                      List.range input.1.graph.vertices))))) :=
    TMPolyTimeMap.prod_mk lengthTM valuesTailTM
  have lengthTailTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        graphBoolAndPair
          (natEqBool (input.2.length, input.1.graph.vertices),
            graphBoolAndPair
              (HittingSet.boundedNatListBool (3, input.2),
                graphBoolAndPair
                  (HittingSet.natLeBool (input.1.threshold, outsideCount input.2),
                    allOutsideSupportedBool
                      ((input.2, input.1.graph.edges),
                        List.range input.1.graph.vertices))))) := by
    have composed := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime lengthTailInputTM
    simpa [Function.comp] using composed
  have boundsTailInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        (NodeDeletionBipartiteMembership.edgesWithinBoundsBool
          ((input.1.graph.vertices, input.1.graph.vertices), input.1.graph.edges),
          graphBoolAndPair
            (natEqBool (input.2.length, input.1.graph.vertices),
              graphBoolAndPair
                (HittingSet.boundedNatListBool (3, input.2),
                  graphBoolAndPair
                    (HittingSet.natLeBool (input.1.threshold, outsideCount input.2),
                      allOutsideSupportedBool
                        ((input.2, input.1.graph.edges),
                          List.range input.1.graph.vertices)))))) :=
    TMPolyTimeMap.prod_mk boundsTM lengthTailTM
  have boundsTailTM : TMPolyTimeMap X EncodedType.bool
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        graphBoolAndPair
          (NodeDeletionBipartiteMembership.edgesWithinBoundsBool
            ((input.1.graph.vertices, input.1.graph.vertices), input.1.graph.edges),
            graphBoolAndPair
              (natEqBool (input.2.length, input.1.graph.vertices),
                graphBoolAndPair
                  (HittingSet.boundedNatListBool (3, input.2),
                    graphBoolAndPair
                      (HittingSet.natLeBool (input.1.threshold, outsideCount input.2),
                        allOutsideSupportedBool
                          ((input.2, input.1.graph.edges),
                            List.range input.1.graph.vertices)))))) := by
    have composed := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime boundsTailInputTM
    simpa [Function.comp] using composed
  have allInputTM : TMPolyTimeMap X
      (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun input : Presentation.MostNeighbors.Input × List Nat =>
        (Bool.not input.1.graph.directed,
          graphBoolAndPair
            (NodeDeletionBipartiteMembership.edgesWithinBoundsBool
              ((input.1.graph.vertices, input.1.graph.vertices), input.1.graph.edges),
              graphBoolAndPair
                (natEqBool (input.2.length, input.1.graph.vertices),
                  graphBoolAndPair
                    (HittingSet.boundedNatListBool (3, input.2),
                      graphBoolAndPair
                        (HittingSet.natLeBool (input.1.threshold, outsideCount input.2),
                          allOutsideSupportedBool
                            ((input.2, input.1.graph.edges),
                              List.range input.1.graph.vertices))))))) :=
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
      simpa [problem, Presentation.MostNeighbors.presentedProblem,
        Presentation.MostNeighbors.structuredPresentation,
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
    change Presentation.MostNeighbors.IsYes input ↔
      ∃ assignment : List Nat,
        natListEncodedType.inputSize assignment ≤
            10 * Presentation.MostNeighbors.structuredEncodedType.inputSize input ^ 2 + 10 ∧
          finiteVerify input assignment = true
    constructor
    · intro yes
      rcases yes with ⟨undirected, wellFormed, assignment, witness⟩
      rcases witness with ⟨assignmentLength, values, threshold, supported⟩
      refine ⟨assignment, ?_, ?_⟩
      · simpa [certificateEncodedType, natListEncodedType] using
          certificate_inputSize_le_poly input assignment assignmentLength values
      · exact (finiteVerify_eq_true_iff input assignment).2
          ⟨undirected, wellFormed, assignmentLength, values,
            by
              rw [← outsideVertices_card_eq_outsideCount_of_length
                input assignment assignmentLength]
              exact threshold,
            by
              intro vertex vertexBound
              apply (vertexLegalBool_eq_true_iff
                assignment input.graph.edges vertex).2
              by_cases outsideValue :
                  Presentation.MostNeighbors.assignmentValue assignment vertex =
                    Presentation.MostNeighbors.outsideMarker
              · right
                rcases supported vertex vertexBound outsideValue with
                  ⟨selected, _selectedBound, selectedValue, adjacent⟩
                rcases adjacent with forward | reverse
                · exact ⟨(selected, vertex), forward,
                    (edgeSupportsBool_eq_true_iff
                      assignment vertex (selected, vertex)).2
                      (Or.inr ⟨rfl, selectedValue⟩)⟩
                · exact ⟨(vertex, selected), reverse,
                    (edgeSupportsBool_eq_true_iff
                      assignment vertex (vertex, selected)).2
                      (Or.inl ⟨rfl, selectedValue⟩)⟩
              · exact Or.inl outsideValue⟩
    · rintro ⟨assignment, _bound, accepted⟩
      exact finiteVerify_sound input assignment accepted
  checkerSound := by
    intro input assignment accepted
    exact finiteVerify_sound input assignment accepted

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

end MostNeighborsMembership
end Domain
end ComplexityReduction

assert_standard_axioms
  ComplexityReduction.Domain.MostNeighborsMembership.outsideCount_tmPolyTime,
  ComplexityReduction.Domain.MostNeighborsMembership.edgeSupportsBool_tmPolyTime,
  ComplexityReduction.Domain.MostNeighborsMembership.someEdgeSupportsBool_tmPolyTime,
  ComplexityReduction.Domain.MostNeighborsMembership.vertexLegalBool_tmPolyTime,
  ComplexityReduction.Domain.MostNeighborsMembership.allOutsideSupportedBool_tmPolyTime,
  ComplexityReduction.Domain.MostNeighborsMembership.finiteVerify_tmPolyTime,
  ComplexityReduction.Domain.MostNeighborsMembership.certificate_inputSize_le_poly,
  ComplexityReduction.Domain.MostNeighborsMembership.verifier,
  ComplexityReduction.Domain.MostNeighborsMembership.witnessPresentation,
  ComplexityReduction.Domain.MostNeighborsMembership.discipline,
  ComplexityReduction.Domain.MostNeighborsMembership.template
