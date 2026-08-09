/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Encoding.StandardInstances
import ComplexityReduction.Presentation.Graph

/-!
Exact finite presentation of the Most Neighbors decision problem.

A value `1` in the finite assignment marks a selected vertex, `2` marks a
claimed external neighbour, and `0` marks every remaining vertex.  The
external-neighbour claims are checked against the explicit undirected graph.
This is equivalent to the usual pair of finite sets `(S, outside)` while
keeping the witness carrier structural and directly encodable.
-/

namespace ComplexityReduction
namespace Presentation
namespace MostNeighbors

open Encoding
open ComplexityReduction.Combinatorics.Graph

/-- An undirected graph and the requested external-neighbour threshold. -/
structure Input where
  graph : GraphInput
  threshold : Nat
  deriving Repr

/-- Complete graph-plus-unary-threshold layout. -/
def structuredShape : CodecShape :=
  .prod Graph.structuredShape .unaryNat

/-- Tuple payload used by the faithful custom wrapper encoder. -/
def tupleStructuredEncodedType : EncodedType :=
  EncodedType.prod
    ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
    EncodedType.nat

/-- Concrete finite-alphabet encoder for the graph and threshold fields. -/
def structuredEncodedType : EncodedType where
  Carrier := Input
  Symbol := tupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun input => tupleStructuredEncodedType.encode (input.graph, input.threshold)

theorem tupleStructuredEncodedType_encode_injective :
    Function.Injective tupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType_encode_injective
    EncodedType.nat_encode_injective

theorem structuredEncodedType_encode_injective :
    Function.Injective structuredEncodedType.encode := by
  intro left right equality
  have payloadEquality :
      (left.graph, left.threshold) = (right.graph, right.threshold) :=
    tupleStructuredEncodedType_encode_injective (by
      simpa [structuredEncodedType] using equality)
  cases left
  cases right
  simp at payloadEquality
  rcases payloadEquality with ⟨rfl, rfl⟩
  rfl

/-- The exact faithful, user-selected presentation of the custom input wrapper. -/
def structuredPresentation : LawfulEncodedType where
  encodedType := structuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨structuredEncodedType_encode_injective⟩

/-- Marker used for a vertex placed in the selected set. -/
def selectedMarker : Nat := 1

/-- Marker used for a claimed external neighbour. -/
def outsideMarker : Nat := 2

/-- Total assignment lookup; missing entries are treated as unselected. -/
def assignmentValue (assignment : List Nat) (vertex : Nat) : Nat :=
  assignment.getD vertex 0

/-- The finite set of vertices explicitly claimed as external neighbours. -/
def outsideVertices (input : Input) (assignment : List Nat) : Finset Nat :=
  (Finset.range input.graph.vertices).filter fun vertex =>
    assignmentValue assignment vertex = outsideMarker

/-- One claimed outside vertex has a selected undirected neighbour. -/
def OutsideSupported (input : Input) (assignment : List Nat) (vertex : Nat) : Prop :=
  ∃ selected,
    selected < input.graph.vertices ∧
      assignmentValue assignment selected = selectedMarker ∧
      HasUndirectedEdge input.graph selected vertex

/-- Canonical finite witness for at least the requested external neighbourhood. -/
def Witness (input : Input) (assignment : List Nat) : Prop :=
  assignment.length = input.graph.vertices ∧
    (∀ value ∈ assignment, value < 3) ∧
    input.threshold ≤ (outsideVertices input assignment).card ∧
    ∀ vertex,
      vertex < input.graph.vertices →
      assignmentValue assignment vertex = outsideMarker →
      OutsideSupported input assignment vertex

/-- Most Neighbors over a well-formed finite undirected graph. -/
def IsYes (input : Input) : Prop :=
  input.graph.directed = false ∧
    WellFormed input.graph ∧
    ∃ assignment : List Nat, Witness input assignment

/-- The predicate at the exact finite structured presentation. -/
def problemAt : ProblemAt structuredPresentation where
  isYes := IsYes

/-- The public V2 Most Neighbors endpoint. -/
@[complexity_reduction_ir_typed_problem]
def presentedProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation problemAt

@[simp] theorem presentedProblem_accepts (input : presentedProblem.Instance) :
    presentedProblem.accepts input ↔ IsYes input :=
  Iff.rfl

@[simp] theorem presentedProblem_representation :
    presentedProblem.representation = structuredPresentation :=
  rfl

@[simp] theorem presentedProblem_representationIdentity :
    presentedProblem.representationIdentity = structuredShape.identity :=
  rfl

end MostNeighbors
end Presentation
end ComplexityReduction
