/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Graph

/-!
An exact public presentation of the Independent Set decision problem.

An instance is a graph plus a requested size `k`.  It is accepted when the
graph contains a vertex subset of at least `k` mutually non-adjacent vertices.
Illegal or degenerate inputs (k above the vertex count, edges outside the
vertex range) admit no witness and are No instances.

This module owns only the problem/presentation boundary.  It contains no
hardness theorem, final route, or target-specific gadget.
-/

namespace ComplexityReduction

open Encoding
open ComplexityReduction.Combinatorics.Graph

namespace IndependentSet

/-- A vertex list is pairwise non-adjacent in the undirected graph sense. -/
def PairwiseNonAdjacent (g : GraphInput) (vs : List Nat) : Prop :=
  ∀ u ∈ vs, ∀ v ∈ vs, u ≠ v → ¬ HasUndirectedEdge g u v

/-- An independent-set instance: an undirected graph plus a requested size. -/
structure IndependentSetInput where
  graph : GraphInput
  k : Nat
  deriving Repr

namespace IndependentSetInput

/-- The instance is accepted when the graph has at least `k` pairwise non-adjacent vertices. -/
def accepted (I : IndependentSetInput) : Prop :=
  ∃ vs : List Nat,
    vs.length ≥ I.k ∧ vs.Nodup ∧
      VerticesWithinBounds I.graph vs ∧ PairwiseNonAdjacent I.graph vs

/-- The empty vertex set is always an independent set of size zero. -/
theorem accepted_empty_k (I : IndependentSetInput) :
    accepted { graph := I.graph, k := 0 } := by
  refine ⟨[], ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro v hv
    simp at hv
  · intro u hu
    simp at hu

end IndependentSetInput

end IndependentSet

namespace Presentation
namespace IndependentSet

open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.IndependentSet

/-- The complete ordered layout of an independent-set instance: graph plus size. -/
def independentSetShape : CodecShape :=
  .prod Graph.structuredShape .unaryNat

/-- Tuple-shaped finite-alphabet payload for one independent-set instance. -/
def independentSetTupleEncodedType : EncodedType :=
  EncodedType.prod Graph.structuredPresentation.encodedType EncodedType.nat

/-- Concrete finite-alphabet encoding of the exact independent-set carrier. -/
def independentSetEncodedType : EncodedType where
  Carrier := IndependentSetInput
  Symbol := independentSetTupleEncodedType.Symbol
  finite_symbol := independentSetTupleEncodedType.finite_symbol
  encode := fun I => independentSetTupleEncodedType.encode (I.graph, I.k)

/-- The exact independent-set encoding is faithful. -/
theorem independentSetEncodedType_encode_injective :
    Function.Injective independentSetEncodedType.encode := by
  intro I J henc
  have htuple : (I.graph, I.k) = (J.graph, J.k) :=
    (EncodedType.prod_encode_injective
      Graph.structuredPresentation.faithful.encode_injective
      EncodedType.nat_encode_injective) (by
      simpa [independentSetEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

/-- Canonical lawful exact independent-set representation. -/
def structuredPresentation : LawfulEncodedType where
  encodedType := independentSetEncodedType
  representation := independentSetShape.identity
  faithful := ⟨independentSetEncodedType_encode_injective⟩

@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = independentSetEncodedType :=
  rfl

@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = independentSetShape.identity :=
  rfl

/-- The represented carrier is exactly the public independent-set syntax. -/
theorem structuredPresentation_carrier_eq_IndependentSetInput :
    structuredPresentation.Carrier = IndependentSetInput :=
  rfl

/-- The exact independent-set semantic predicate at the selected representation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := IndependentSetInput.accepted

/-- Canonical exact public independent-set endpoint. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = independentSetShape.identity :=
  rfl

@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ IndependentSetInput.accepted input :=
  Iff.rfl

@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ IndependentSetInput.accepted input :=
  Iff.rfl

assert_standard_axioms
  independentSetEncodedType_encode_injective,
  structuredProblem_accepts,
  structuredProblemAt_isYes,
  IndependentSetInput.accepted_empty_k

end IndependentSet
end Presentation
end ComplexityReduction
