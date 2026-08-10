/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Graph

/-!
An exact public presentation of the Dominating Set decision problem.

An instance is a graph plus a budget `k`.  It is accepted when the graph has
a dominating set of at most `k` vertices: every vertex of the graph either
lies in the set or is adjacent (undirected) to a set member.  Degenerate
graphs are covered by the same semantics: an empty graph with zero vertices
has the empty dominating set, and a single isolated vertex requires itself in
the dominating set.

This module owns only the problem/presentation boundary.  It contains no
hardness theorem, final route, or target-specific gadget.
-/

namespace ComplexityReduction

open Encoding
open ComplexityReduction.Combinatorics.Graph

namespace DominatingSet

/-- A set of vertices dominates one vertex when the vertex is a member or adjacent to a member. -/
def Dominates (g : GraphInput) (ds : List Nat) (v : Nat) : Prop :=
  v ∈ ds ∨ ∃ u ∈ ds, HasUndirectedEdge g u v

/-- A dominating-set instance: an undirected graph plus a budget. -/
structure DominatingSetInput where
  graph : GraphInput
  k : Nat
  deriving Repr

namespace DominatingSetInput

/-- The instance is accepted when at most `k` vertices dominate the whole graph. -/
def accepted (I : DominatingSetInput) : Prop :=
  ∃ ds : List Nat,
    ds.length ≤ I.k ∧ ds.Nodup ∧ VerticesWithinBounds I.graph ds ∧
      ∀ v, v < I.graph.vertices → Dominates I.graph ds v

/-- An empty graph with zero vertices is dominated by the empty set. -/
theorem accepted_empty_graph (I : DominatingSetInput) :
    accepted { graph := { vertices := 0, edges := [], directed := false }, k := 0 } := by
  refine ⟨[], ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro v hv
    simp at hv
  · intro v hv
    exact False.elim (Nat.not_lt_zero v hv)

/-- Every dominating-set witness is vertex-bounded. -/
theorem accepted_vertices_bounded (I : DominatingSetInput) :
    accepted I → ∃ ds : List Nat, ds.Nodup ∧ VerticesWithinBounds I.graph ds := by
  rintro ⟨ds, _, hnodup, hbounds, _⟩
  exact ⟨ds, hnodup, hbounds⟩

end DominatingSetInput

end DominatingSet

namespace Presentation
namespace DominatingSet

open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.DominatingSet

/-- The complete ordered layout of a dominating-set instance: graph plus budget. -/
def dominatingSetShape : CodecShape :=
  .prod Graph.structuredShape .unaryNat

/-- Tuple-shaped finite-alphabet payload for one dominating-set instance. -/
def dominatingSetTupleEncodedType : EncodedType :=
  EncodedType.prod Graph.structuredPresentation.encodedType EncodedType.nat

/-- Concrete finite-alphabet encoding of the exact dominating-set carrier. -/
def dominatingSetEncodedType : EncodedType where
  Carrier := DominatingSetInput
  Symbol := dominatingSetTupleEncodedType.Symbol
  finite_symbol := dominatingSetTupleEncodedType.finite_symbol
  encode := fun I => dominatingSetTupleEncodedType.encode (I.graph, I.k)

/-- The exact dominating-set encoding is faithful. -/
theorem dominatingSetEncodedType_encode_injective :
    Function.Injective dominatingSetEncodedType.encode := by
  intro I J henc
  have htuple : (I.graph, I.k) = (J.graph, J.k) :=
    (EncodedType.prod_encode_injective
      Graph.structuredPresentation.faithful.encode_injective
      EncodedType.nat_encode_injective) (by
      simpa [dominatingSetEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

/-- Canonical lawful exact dominating-set representation. -/
def structuredPresentation : LawfulEncodedType where
  encodedType := dominatingSetEncodedType
  representation := dominatingSetShape.identity
  faithful := ⟨dominatingSetEncodedType_encode_injective⟩

@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = dominatingSetEncodedType :=
  rfl

@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = dominatingSetShape.identity :=
  rfl

/-- The represented carrier is exactly the public dominating-set syntax. -/
theorem structuredPresentation_carrier_eq_DominatingSetInput :
    structuredPresentation.Carrier = DominatingSetInput :=
  rfl

/-- The exact dominating-set semantic predicate at the selected representation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := DominatingSetInput.accepted

/-- Canonical exact public dominating-set endpoint. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = dominatingSetShape.identity :=
  rfl

@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ DominatingSetInput.accepted input :=
  Iff.rfl

@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ DominatingSetInput.accepted input :=
  Iff.rfl

assert_standard_axioms
  dominatingSetEncodedType_encode_injective,
  structuredProblem_accepts,
  structuredProblemAt_isYes,
  DominatingSetInput.accepted_empty_graph

end DominatingSet
end Presentation
end ComplexityReduction
