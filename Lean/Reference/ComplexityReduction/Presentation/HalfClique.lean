/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Graph

/-!
An exact public presentation of the Half-Clique decision problem.

A half-clique instance is a graph together with a size threshold.  The
instance is accepted when the graph contains a vertex subset of at least the
threshold size that is pairwise adjacent (an undirected clique of size >= k).

Threshold semantics: the threshold is an explicit unary natural field, so a
reduction may target half-clique thresholds such as `ceil (|V| / 2)` or any
other polynomial-size parameter without changing the endpoint.  Illegal or
degenerate inputs (threshold larger than the vertex count, or edges outside
the vertex range) simply admit no satisfying witness and are therefore No
instances; no separate error value is introduced.

This module owns only the problem/presentation boundary.  It contains no
hardness theorem, final route, or target-specific gadget.
-/

namespace ComplexityReduction

open Encoding
open ComplexityReduction.Combinatorics.Graph

namespace HalfClique

/-- A half-clique instance: an undirected graph plus a clique-size threshold. -/
structure HalfCliqueInput where
  graph : GraphInput
  threshold : Nat
  deriving Repr

namespace HalfCliqueInput

/-- The instance is accepted when the graph has a clique of at least the threshold size. -/
def accepted (I : HalfCliqueInput) : Prop :=
  ∃ vs : List Nat,
    vs.length ≥ I.threshold ∧ vs.Nodup ∧
      VerticesWithinBounds I.graph vs ∧ PairwiseAdjacent I.graph vs

/-- A duplicate-free vertex list whose members stay below a bound has bounded length. -/
theorem bounded_nodup_length_le (vs : List Nat) (m : Nat)
    (hnodup : vs.Nodup) (hbounds : ∀ v ∈ vs, v < m) : vs.length ≤ m := by
  have hcard : vs.toFinset.card = vs.length := List.toFinset_card_of_nodup hnodup
  have hsub : vs.toFinset ⊆ Finset.range m := by
    intro v hv
    exact Finset.mem_range.mpr (hbounds v (List.mem_toFinset.mp hv))
  have hle := Finset.card_le_card hsub
  simpa [hcard] using hle

/-- Illegal inputs (threshold above the vertex count) have no accepting witness. -/
theorem accepted_threshold_below_vertex_count (I : HalfCliqueInput)
    (h : I.threshold > I.graph.vertices) : ¬ accepted I := by
  rintro ⟨vs, hlen, hnodup, hbounds, _⟩
  have hle : vs.length ≤ I.graph.vertices :=
    bounded_nodup_length_le vs I.graph.vertices hnodup hbounds
  have hgt : I.graph.vertices < vs.length := lt_of_lt_of_le h hlen
  omega

/-- Membership probe: the empty vertex set is always a clique of size zero. -/
theorem accepted_empty_threshold (I : HalfCliqueInput) :
    accepted { graph := I.graph, threshold := 0 } := by
  refine ⟨[], ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro v hv
    simp at hv
  · intro u hu
    simp at hu

end HalfCliqueInput

end HalfClique

namespace Presentation
namespace HalfClique

open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.HalfClique

/-- The complete ordered layout of a half-clique instance: graph plus threshold. -/
def halfCliqueShape : CodecShape :=
  .prod Graph.structuredShape .unaryNat

/-- Tuple-shaped finite-alphabet payload for one half-clique instance. -/
def halfCliqueTupleEncodedType : EncodedType :=
  EncodedType.prod Graph.structuredPresentation.encodedType EncodedType.nat

/-- Concrete finite-alphabet encoding of the exact half-clique carrier. -/
def halfCliqueEncodedType : EncodedType where
  Carrier := HalfCliqueInput
  Symbol := halfCliqueTupleEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => halfCliqueTupleEncodedType.encode (I.graph, I.threshold)

/-- The half-clique carrier projection is injective. -/
theorem halfCliqueTupleEncodedType_encode_injective :
    Function.Injective halfCliqueTupleEncodedType.encode :=
  EncodedType.prod_encode_injective
    Graph.structuredPresentation.faithful.encode_injective
    EncodedType.nat_encode_injective

/-- The exact half-clique encoding is faithful. -/
theorem halfCliqueEncodedType_encode_injective :
    Function.Injective halfCliqueEncodedType.encode := by
  intro I J henc
  have htuple : (I.graph, I.threshold) = (J.graph, J.threshold) :=
    halfCliqueTupleEncodedType_encode_injective (by
      simpa [halfCliqueEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

/-- Canonical lawful exact half-clique representation. -/
def structuredPresentation : LawfulEncodedType where
  encodedType := halfCliqueEncodedType
  representation := halfCliqueShape.identity
  faithful := ⟨halfCliqueEncodedType_encode_injective⟩

@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = halfCliqueEncodedType :=
  rfl

@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = halfCliqueShape.identity :=
  rfl

/-- The represented carrier is exactly the public half-clique syntax. -/
theorem structuredPresentation_carrier_eq_HalfCliqueInput :
    structuredPresentation.Carrier = HalfCliqueInput :=
  rfl

/-- The exact half-clique semantic predicate at the selected representation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := HalfCliqueInput.accepted

/-- Canonical exact public half-clique endpoint. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = halfCliqueShape.identity :=
  rfl

@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ HalfCliqueInput.accepted input :=
  Iff.rfl

@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ HalfCliqueInput.accepted input :=
  Iff.rfl

assert_standard_axioms
  halfCliqueEncodedType_encode_injective,
  structuredProblem_accepts,
  structuredProblemAt_isYes,
  HalfCliqueInput.accepted_empty_threshold

end HalfClique
end Presentation
end ComplexityReduction
