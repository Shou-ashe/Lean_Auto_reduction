/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Encoding.StandardInstances
import ComplexityReduction.Presentation.Graph

/-!
Exact finite presentation of the directed weighted Seeing Set problem.

The legacy statement supplied an integer-valued function on vertices.  The
public endpoint replaces that non-finite carrier with an explicit integer
list whose length equals the graph vertex count.  Lookup is total through
`List.getD`, while the semantic validity conjunct guarantees every selected
in-range vertex reads the corresponding stored weight.
-/

namespace ComplexityReduction
namespace Presentation
namespace SeeingSet

open Encoding
open ComplexityReduction.Combinatorics.Graph

/-- A finite directed weighted Seeing Set instance. -/
structure Input where
  graph : GraphInput
  weights : List Int
  targets : List Nat
  budget : Int
  deriving Repr

/-- The sign-and-unary-magnitude identity used by the established integer encoder. -/
def unaryIntegerShape : CodecShape :=
  .prod .bool .unaryNat

/-- One explicit unary integer presentation. -/
def unaryIntegerPresentation : LawfulEncodedType where
  encodedType := ComplexityReduction.EncodedType.int
  representation := unaryIntegerShape.identity
  faithful := ⟨ComplexityReduction.EncodedType.int_encode_injective⟩

/-- The complete graph, weight-list, target-list, and budget layout. -/
def structuredShape : CodecShape :=
  .prod Graph.structuredShape
    (.prod (.list unaryIntegerShape) (.prod (.list .unaryNat) unaryIntegerShape))

/-- Tuple payload used by the faithful custom wrapper encoder. -/
def tupleStructuredEncodedType : EncodedType :=
  EncodedType.prod
    ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
    (EncodedType.prod (EncodedType.list EncodedType.int)
      (EncodedType.prod (EncodedType.list EncodedType.nat) EncodedType.int))

/-- Concrete finite-alphabet encoder for all Seeing Set fields. -/
def structuredEncodedType : EncodedType where
  Carrier := Input
  Symbol := tupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun input =>
    tupleStructuredEncodedType.encode
      (input.graph, (input.weights, (input.targets, input.budget)))

theorem tupleStructuredEncodedType_encode_injective :
    Function.Injective tupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType_encode_injective
    (EncodedType.prod_encode_injective
      (EncodedType.list_encode_injective EncodedType.int_encode_injective)
      (EncodedType.prod_encode_injective
        (EncodedType.list_encode_injective EncodedType.nat_encode_injective)
        EncodedType.int_encode_injective))

theorem structuredEncodedType_encode_injective :
    Function.Injective structuredEncodedType.encode := by
  intro left right equality
  have payloadEquality :
      (left.graph, (left.weights, (left.targets, left.budget))) =
        (right.graph, (right.weights, (right.targets, right.budget))) :=
    tupleStructuredEncodedType_encode_injective (by
      simpa [structuredEncodedType] using equality)
  cases left
  cases right
  simp at payloadEquality
  rcases payloadEquality with ⟨rfl, rfl, rfl, rfl⟩
  rfl

/-- The exact faithful, user-selected presentation of the custom input wrapper. -/
def structuredPresentation : LawfulEncodedType where
  encodedType := structuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨structuredEncodedType_encode_injective⟩

/-- Reflexive/transitive directed reachability in the explicit edge relation. -/
inductive DirectedReachable (graph : GraphInput) : Nat → Nat → Prop
  | refl (vertex : Nat) : DirectedReachable graph vertex vertex
  | step {source next target : Nat} :
      HasDirectedEdge graph source next →
      DirectedReachable graph next target →
      DirectedReachable graph source target

/-- A selected vertex sees a target when it reaches it by a directed path. -/
def Sees (graph : GraphInput) (selected : List Nat) (target : Nat) : Prop :=
  ∃ source ∈ selected, DirectedReachable graph source target

/-- Total weight of the finite selected list. -/
def selectedWeight (weights : List Int) (selected : List Nat) : Int :=
  (selected.map fun vertex => weights.getD vertex 0).sum

/-- The exact finite witness predicate from the qualifying-exam statement. -/
def Witness (input : Input) (selected : List Nat) : Prop :=
  selected.Nodup ∧
    VerticesWithinBounds input.graph selected ∧
    selectedWeight input.weights selected ≤ input.budget ∧
    ∀ target ∈ input.targets, Sees input.graph selected target

/-- Directed weighted Seeing Set with explicit finite weights and targets. -/
def IsYes (input : Input) : Prop :=
  input.graph.directed = true ∧
    input.weights.length = input.graph.vertices ∧
    input.targets.Nodup ∧
    VerticesWithinBounds input.graph input.targets ∧
    ∃ selected : List Nat, Witness input selected

/-- The predicate at the exact finite structured presentation. -/
def problemAt : ProblemAt structuredPresentation where
  isYes := IsYes

/-- The public V2 Seeing Set endpoint. -/
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

end SeeingSet
end Presentation
end ComplexityReduction
