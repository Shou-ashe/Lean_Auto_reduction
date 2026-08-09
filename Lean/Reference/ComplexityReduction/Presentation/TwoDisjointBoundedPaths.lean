/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Encoding.StandardInstances
import ComplexityReduction.Presentation.Graph

/-!
Exact finite presentation of two edge-disjoint bounded-cost directed paths.

Costs are stored in a list aligned with the explicit graph edge list.  A path
is represented by a list of edge indices, which preserves parallel edges and
makes edge-disjointness a finite list property.  Every accepted input has
positive costs, well-formed directed edges, distinct in-range terminals, and
two simple edge-index paths whose individual costs are within the bound.
-/

namespace ComplexityReduction
namespace Presentation
namespace TwoDisjointBoundedPaths

open Encoding
open ComplexityReduction.Combinatorics.Graph

/-- A finite directed graph, aligned positive costs, terminals, and bound. -/
structure Input where
  graph : GraphInput
  costs : List Nat
  source : Nat
  target : Nat
  bound : Nat
  deriving Repr

/-- Complete graph, binary cost-list, unary terminals, and binary-bound layout. -/
def structuredShape : CodecShape :=
  .prod Graph.structuredShape
    (.prod (.list .binaryNat) (.prod .unaryNat (.prod .unaryNat .binaryNat)))

/-- Tuple payload used by the faithful custom wrapper encoder. -/
def tupleStructuredEncodedType : EncodedType :=
  EncodedType.prod
    ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType
    (EncodedType.prod (EncodedType.list EncodedType.binaryNat)
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.binaryNat)))

/-- Concrete finite-alphabet encoder for every public input field. -/
def structuredEncodedType : EncodedType where
  Carrier := Input
  Symbol := tupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun input =>
    tupleStructuredEncodedType.encode
      (input.graph, (input.costs, (input.source, (input.target, input.bound))))

theorem tupleStructuredEncodedType_encode_injective :
    Function.Injective tupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    ComplexityReduction.Combinatorics.Graph.graphStructuredEncodedType_encode_injective
    (EncodedType.prod_encode_injective
      (EncodedType.list_encode_injective EncodedType.binaryNat_encode_injective)
      (EncodedType.prod_encode_injective EncodedType.nat_encode_injective
        (EncodedType.prod_encode_injective
          EncodedType.nat_encode_injective EncodedType.binaryNat_encode_injective)))

theorem structuredEncodedType_encode_injective :
    Function.Injective structuredEncodedType.encode := by
  intro left right equality
  have payloadEquality :
      (left.graph, (left.costs, (left.source, (left.target, left.bound)))) =
        (right.graph, (right.costs, (right.source, (right.target, right.bound)))) :=
    tupleStructuredEncodedType_encode_injective (by
      simpa [structuredEncodedType] using equality)
  cases left
  cases right
  simp at payloadEquality
  rcases payloadEquality with ⟨rfl, rfl, rfl, rfl, rfl⟩
  rfl

/-- The exact faithful, user-selected presentation of the custom input wrapper. -/
def structuredPresentation : LawfulEncodedType where
  encodedType := structuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨structuredEncodedType_encode_injective⟩

/-- Total lookup of one indexed edge. -/
def edgeAt (graph : GraphInput) (index : Nat) : Nat × Nat :=
  graph.edges.getD index (0, 0)

/-- A finite edge-index sequence forms a directed chain between two vertices. -/
def EdgeChain (graph : GraphInput) : Nat → List Nat → Nat → Prop
  | current, [], target => current = target
  | current, index :: rest, target =>
      index < graph.edges.length ∧
        (edgeAt graph index).1 = current ∧
        EdgeChain graph (edgeAt graph index).2 rest target

/-- A path is an edge-simple directed chain. -/
def EdgeIndexPath (graph : GraphInput) (source target : Nat) (path : List Nat) : Prop :=
  path.Nodup ∧ EdgeChain graph source path target

/-- Cost of one edge-index path under the aligned cost list. -/
def pathCost (costs : List Nat) (path : List Nat) : Nat :=
  (path.map fun index => costs.getD index 0).sum

/-- Two edge-index paths share no encoded edge. -/
def EdgeDisjoint (left right : List Nat) : Prop :=
  ∀ index ∈ left, index ∉ right

/-- Two edge-disjoint directed paths, each with cost at most the bound. -/
def IsYes (input : Input) : Prop :=
  input.graph.directed = true ∧
    WellFormed input.graph ∧
    input.source < input.graph.vertices ∧
    input.target < input.graph.vertices ∧
    input.source ≠ input.target ∧
    input.costs.length = input.graph.edges.length ∧
    (∀ cost ∈ input.costs, 0 < cost) ∧
    ∃ left right : List Nat,
      EdgeIndexPath input.graph input.source input.target left ∧
        EdgeIndexPath input.graph input.source input.target right ∧
        pathCost input.costs left ≤ input.bound ∧
        pathCost input.costs right ≤ input.bound ∧
        EdgeDisjoint left right

/-- The predicate at the exact finite structured presentation. -/
def problemAt : ProblemAt structuredPresentation where
  isYes := IsYes

/-- The public V2 Two Disjoint Bounded Paths endpoint. -/
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

end TwoDisjointBoundedPaths
end Presentation
end ComplexityReduction
