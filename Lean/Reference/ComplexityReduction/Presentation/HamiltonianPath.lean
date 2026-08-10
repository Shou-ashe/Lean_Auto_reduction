/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.AxiomGate
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Graph

/-!
An exact public presentation of the Hamiltonian Path decision problem.

An instance is an undirected graph.  It is accepted when there is a path that
visits every vertex exactly once: a duplicate-free vertex list of the full
vertex count in which consecutive members are adjacent.  Edge cases follow
the same semantics: an empty graph (zero vertices) has the empty path, and a
single-vertex graph has the one-vertex path.

This module owns only the problem/presentation boundary.  It contains no
hardness theorem, final route, or target-specific gadget.
-/

namespace ComplexityReduction

open Encoding
open ComplexityReduction.Combinatorics.Graph

namespace HamiltonianPath

/-- Consecutive members of a vertex list are adjacent in the undirected graph. -/
def PathEdgesOk (g : GraphInput) (path : List Nat) : Prop :=
  ∀ pair ∈ path.zip path.tail, HasUndirectedEdge g pair.1 pair.2

/-- A Hamiltonian-path instance: one undirected graph. -/
structure HamiltonianPathInput where
  graph : GraphInput
  deriving Repr

namespace HamiltonianPathInput

/-- The instance is accepted when the graph has a path visiting every vertex once. -/
def accepted (I : HamiltonianPathInput) : Prop :=
  ∃ path : List Nat,
    path.length = I.graph.vertices ∧ path.Nodup ∧
      VerticesWithinBounds I.graph path ∧ PathEdgesOk I.graph path

/-- The empty graph has the empty Hamiltonian path. -/
theorem accepted_empty_graph :
    accepted { graph := { vertices := 0, edges := [], directed := false } } := by
  refine ⟨[], ?_, ?_, ?_, ?_⟩
  · rfl
  · simp
  · intro v hv
    simp at hv
  · simp [PathEdgesOk]

/-- Every Hamiltonian-path witness is vertex-bounded. -/
theorem accepted_vertices_bounded (I : HamiltonianPathInput) :
    accepted I → ∃ path : List Nat, path.Nodup ∧ VerticesWithinBounds I.graph path := by
  rintro ⟨path, _, hnodup, hbounds, _⟩
  exact ⟨path, hnodup, hbounds⟩

end HamiltonianPathInput

end HamiltonianPath

namespace Presentation
namespace HamiltonianPath

open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.HamiltonianPath

/-- The complete ordered layout of a Hamiltonian-path instance: a plain graph. -/
def hamiltonianPathShape : CodecShape :=
  Graph.structuredShape

/-- Concrete finite-alphabet encoding of the exact Hamiltonian-path carrier. -/
def hamiltonianPathEncodedType : EncodedType where
  Carrier := HamiltonianPathInput
  Symbol := Graph.structuredPresentation.encodedType.Symbol
  finite_symbol := Graph.structuredPresentation.encodedType.finite_symbol
  encode := fun I => Graph.structuredPresentation.encodedType.encode I.graph

/-- The exact Hamiltonian-path encoding is faithful. -/
theorem hamiltonianPathEncodedType_encode_injective :
    Function.Injective hamiltonianPathEncodedType.encode := by
  intro I J henc
  have hgraph : I.graph = J.graph :=
    Graph.structuredPresentation.faithful.encode_injective (by
      simpa [hamiltonianPathEncodedType] using henc)
  cases I
  cases J
  cases hgraph
  rfl

/-- Canonical lawful exact Hamiltonian-path representation. -/
def structuredPresentation : LawfulEncodedType where
  encodedType := hamiltonianPathEncodedType
  representation := hamiltonianPathShape.identity
  faithful := ⟨hamiltonianPathEncodedType_encode_injective⟩

@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = hamiltonianPathEncodedType :=
  rfl

@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = hamiltonianPathShape.identity :=
  rfl

/-- The represented carrier is exactly the public Hamiltonian-path syntax. -/
theorem structuredPresentation_carrier_eq_HamiltonianPathInput :
    structuredPresentation.Carrier = HamiltonianPathInput :=
  rfl

/-- The exact Hamiltonian-path semantic predicate at the selected representation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := HamiltonianPathInput.accepted

/-- Canonical exact public Hamiltonian-path endpoint. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = hamiltonianPathShape.identity :=
  rfl

@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ HamiltonianPathInput.accepted input :=
  Iff.rfl

@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ HamiltonianPathInput.accepted input :=
  Iff.rfl

assert_standard_axioms
  hamiltonianPathEncodedType_encode_injective,
  structuredProblem_accepts,
  structuredProblemAt_isYes,
  HamiltonianPathInput.accepted_empty_graph

end HamiltonianPath
end Presentation
end ComplexityReduction
