/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Presentation.Graph

/-!
Exact finite presentation of Node Deletion to Bipartite.

The graph is required to be a well-formed undirected finite graph.  A witness
is the deleted vertex list together with a total Boolean coloring; every edge
whose endpoints both survive must have different colors.
-/

namespace ComplexityReduction
namespace Presentation
namespace NodeDeletionBipartite

open Encoding
open ComplexityReduction.Combinatorics.Graph

/-- A graph and deletion budget. -/
structure Input where
  graph : GraphInput
  budget : Nat
  deriving Repr

/-- Complete graph-plus-unary-budget layout. -/
def structuredShape : CodecShape :=
  .prod Graph.structuredShape .unaryNat

/-- Tuple payload used by the faithful custom wrapper encoder. -/
def tupleStructuredEncodedType : EncodedType :=
  EncodedType.prod
    ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
    EncodedType.nat

/-- Concrete finite-alphabet encoder for the graph and budget fields. -/
def structuredEncodedType : EncodedType where
  Carrier := Input
  Symbol := tupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun input => tupleStructuredEncodedType.encode (input.graph, input.budget)

theorem tupleStructuredEncodedType_encode_injective :
    Function.Injective tupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType_encode_injective
    EncodedType.nat_encode_injective

theorem structuredEncodedType_encode_injective :
    Function.Injective structuredEncodedType.encode := by
  intro left right equality
  have payloadEquality :
      (left.graph, left.budget) = (right.graph, right.budget) :=
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

/-- A surviving edge is properly two-colored. -/
def SurvivingEdgeProper
    (deleted : List Nat) (color : Nat → Bool) (edge : Nat × Nat) : Prop :=
  edge.1 ∈ deleted ∨ edge.2 ∈ deleted ∨ color edge.1 ≠ color edge.2

/-- Legacy deletion-list plus total-coloring witness. -/
def Witness (input : Input) (deleted : List Nat) : Prop :=
  deleted.Nodup ∧
    VerticesWithinBounds input.graph deleted ∧
    deleted.length ≤ input.budget ∧
    ∃ color : Nat → Bool,
      ∀ edge ∈ input.graph.edges, SurvivingEdgeProper deleted color edge

/-- Delete at most the budgeted vertices so the remaining graph is bipartite. -/
def IsYes (input : Input) : Prop :=
  input.graph.directed = false ∧
    WellFormed input.graph ∧
    ∃ deleted : List Nat, Witness input deleted

/-- The predicate at the exact finite structured presentation. -/
def problemAt : ProblemAt structuredPresentation where
  isYes := IsYes

/-- The public V2 Node Deletion to Bipartite endpoint. -/
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

end NodeDeletionBipartite
end Presentation
end ComplexityReduction
