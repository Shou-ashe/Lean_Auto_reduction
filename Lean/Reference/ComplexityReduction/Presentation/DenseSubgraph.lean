/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Graph

/-!
An exact public presentation of the Dense Subgraph decision problem.

An instance is a graph plus two unary natural parameters `a` and `b`.  It is
accepted when the graph has a vertex subset of at least `a` vertices whose
induced edge count (edges with both endpoints inside the subset) is at least
`b`.  All counts are natural numbers; `a + b` never overflows the Nat
semantics, and parameter values above the input size simply make the instance
a No instance.  Degenerate inputs (b = 0 or a = 0) are handled by the same
witness semantics: the empty subset is a valid witness whenever the bounds
are met.

This module owns only the problem/presentation boundary.  It contains no
hardness theorem, final route, or target-specific gadget.
-/

namespace ComplexityReduction

open Encoding
open ComplexityReduction.Combinatorics.Graph

namespace DenseSubgraph

/-- The number of graph edges whose endpoints both lie in a vertex subset. -/
def InducedEdgeCount (g : GraphInput) (vs : List Nat) : Nat :=
  (g.edges.filter fun e => decide (e.1 ∈ vs) && decide (e.2 ∈ vs)).length

/-- A dense-subgraph instance: a graph plus vertex/edge lower bounds. -/
structure DenseSubgraphInput where
  graph : GraphInput
  a : Nat
  b : Nat
  deriving Repr

namespace DenseSubgraphInput

/-- The instance is accepted when some vertex subset meets both lower bounds. -/
def accepted (I : DenseSubgraphInput) : Prop :=
  ∃ vs : List Nat,
    vs.Nodup ∧ VerticesWithinBounds I.graph vs ∧
      vs.length ≥ I.a ∧ InducedEdgeCount I.graph vs ≥ I.b

/-- The empty vertex subset always satisfies both zero lower bounds. -/
theorem accepted_zero_bounds (I : DenseSubgraphInput) :
    accepted { graph := I.graph, a := 0, b := 0 } := by
  refine ⟨[], ?_, ?_, ?_, ?_⟩
  · simp
  · intro v hv
    simp at hv
  · simp
  · simp

end DenseSubgraphInput

end DenseSubgraph

namespace Presentation
namespace DenseSubgraph

open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.DenseSubgraph

/-- The complete ordered layout of a dense-subgraph instance. -/
def denseSubgraphShape : CodecShape :=
  .prod Graph.structuredShape (.prod .unaryNat .unaryNat)

/-- Nested-product finite-alphabet payload for one dense-subgraph instance. -/
def denseSubgraphTupleEncodedType : EncodedType :=
  EncodedType.prod Graph.structuredPresentation.encodedType
    (EncodedType.prod EncodedType.nat EncodedType.nat)

/-- Concrete finite-alphabet encoding of the exact dense-subgraph carrier. -/
def denseSubgraphEncodedType : EncodedType where
  Carrier := DenseSubgraphInput
  Symbol := denseSubgraphTupleEncodedType.Symbol
  finite_symbol := denseSubgraphTupleEncodedType.finite_symbol
  encode := fun I => denseSubgraphTupleEncodedType.encode (I.graph, (I.a, I.b))

/-- The exact dense-subgraph encoding is faithful. -/
theorem denseSubgraphEncodedType_encode_injective :
    Function.Injective denseSubgraphEncodedType.encode := by
  intro I J henc
  have htuple : (I.graph, (I.a, I.b)) = (J.graph, (J.a, J.b)) :=
    (EncodedType.prod_encode_injective
      Graph.structuredPresentation.faithful.encode_injective
      (EncodedType.prod_encode_injective
        EncodedType.nat_encode_injective
        EncodedType.nat_encode_injective)) (by
      simpa [denseSubgraphEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl, rfl⟩
  rfl

/-- Canonical lawful exact dense-subgraph representation. -/
def structuredPresentation : LawfulEncodedType where
  encodedType := denseSubgraphEncodedType
  representation := denseSubgraphShape.identity
  faithful := ⟨denseSubgraphEncodedType_encode_injective⟩

@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = denseSubgraphEncodedType :=
  rfl

@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = denseSubgraphShape.identity :=
  rfl

/-- The represented carrier is exactly the public dense-subgraph syntax. -/
theorem structuredPresentation_carrier_eq_DenseSubgraphInput :
    structuredPresentation.Carrier = DenseSubgraphInput :=
  rfl

/-- The exact dense-subgraph semantic predicate at the selected representation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := DenseSubgraphInput.accepted

/-- Canonical exact public dense-subgraph endpoint. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = denseSubgraphShape.identity :=
  rfl

@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ DenseSubgraphInput.accepted input :=
  Iff.rfl

@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ DenseSubgraphInput.accepted input :=
  Iff.rfl

assert_standard_axioms
  denseSubgraphEncodedType_encode_injective,
  structuredProblem_accepts,
  structuredProblemAt_isYes,
  DenseSubgraphInput.accepted_zero_bounds

end DenseSubgraph
end Presentation
end ComplexityReduction
