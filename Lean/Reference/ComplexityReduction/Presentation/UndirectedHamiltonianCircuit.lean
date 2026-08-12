/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.Graph.Digraph
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Graph
import ComplexityReduction.Presentation.GraphTM

/-!
Canonical V2 presentation of the structured Karp21 Undirected Hamiltonian Circuit endpoint.

`UndirectedHamiltonianCircuitInput` is a custom one-field wrapper around a graph.  Its encoder
deliberately reuses the exact graph encoder, but the wrapper remains a distinct carrier and
therefore a distinct representation identity.  This is an explicit, user-selected lawful
presentation: it exports no structural certificate or automatic-presentation admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace UndirectedHamiltonianCircuit

open Encoding
open ComplexityReduction.Combinatorics.Graph

/-- The complete graph layout of an Undirected Hamiltonian Circuit input. -/
def structuredShape : CodecShape :=
  Graph.structuredShape

/--
The exact lawful V2 presentation of CR's structured Undirected Hamiltonian Circuit encoder.

The carrier is a custom wrapper rather than the graph carrier itself, so this faithful
presentation intentionally remains user-locked despite sharing its encoded payload layout.
-/
def structuredPresentation : LawfulEncodedType where
  encodedType := undirectedHamiltonianCircuitStructuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨undirectedHamiltonianCircuitStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's structured Undirected Hamiltonian Circuit encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = undirectedHamiltonianCircuitStructuredEncodedType :=
  rfl

/-- The representation identity records the complete undirected-graph layout. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The presentation carrier is exactly CR's Undirected Hamiltonian Circuit wrapper syntax. -/
theorem structuredPresentation_carrier_eq_UndirectedHamiltonianCircuitInput :
    structuredPresentation.Carrier = UndirectedHamiltonianCircuitInput :=
  rfl

/-- The only encoder exposed by this presentation is CR's established structured encoder. -/
@[simp]
theorem structuredPresentation_encode (input : structuredPresentation.Carrier) :
    structuredPresentation.encode input = undirectedHamiltonianCircuitStructuredEncodedType.encode input :=
  rfl

/-- The existing Undirected Hamiltonian Circuit predicate at its exact lawful V2 presentation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := UndirectedHamiltonianCircuit

/-- The canonical V2 endpoint for CR's structured Karp21 Undirected Hamiltonian Circuit problem. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

/-- The endpoint is indexed by the exact selected Undirected Hamiltonian Circuit presentation. -/
@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

/-- The endpoint retains the complete undirected-graph representation identity. -/
@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = structuredShape.identity :=
  rfl

/-- The compatibility backend endpoint is exactly CR's structured decision problem. -/
@[simp]
theorem structuredProblem_backendEndpoint_eq_legacy :
    structuredProblem.backendEndpoint = undirectedHamiltonianCircuitStructuredDecisionProblem :=
  rfl

/-- The presented predicate is definitionally CR's Undirected Hamiltonian Circuit semantics. -/
@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ UndirectedHamiltonianCircuit input :=
  Iff.rfl

/-- The typed endpoint accepts exactly the existing Undirected Hamiltonian Circuit instances. -/
@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ UndirectedHamiltonianCircuit input :=
  Iff.rfl

/-- Route-free codec projection from the public wrapper to its graph payload. -/
theorem graphProjection_tmPolyTime :
    TMPolyTimeMap structuredProblem.representation.encodedType graphStructuredEncodedType
      (fun input : structuredProblem.Instance => input.graph) := by
  exact TMPolyTimeMap.of_encodingEquiv
    structuredProblem.representation.encodedType graphStructuredEncodedType _
    (Equiv.refl graphStructuredEncodedType.Symbol) (by
      intro input
      change graphStructuredEncodedType.encode input.graph =
        List.map id (graphStructuredEncodedType.encode input.graph)
      rw [List.map_id])

/-- Route-free codec wrapper from a graph payload to the public endpoint carrier. -/
theorem ofGraph_tmPolyTime :
    TMPolyTimeMap graphStructuredEncodedType structuredProblem.representation.encodedType
      (fun graph : GraphInput => ({ graph := graph } : UndirectedHamiltonianCircuitInput)) := by
  exact TMPolyTimeMap.of_encodingEquiv
    graphStructuredEncodedType structuredProblem.representation.encodedType _
    (Equiv.refl graphStructuredEncodedType.Symbol) (by
      intro graph
      change graphStructuredEncodedType.encode graph =
        List.map id (graphStructuredEncodedType.encode graph)
      rw [List.map_id])

end UndirectedHamiltonianCircuit
end Presentation
end ComplexityReduction
