/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.Graph.Digraph
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Graph
import ComplexityReduction.Presentation.GraphTM

/-!
Canonical V2 presentation of the structured Karp21 Directed Hamiltonian Circuit endpoint.

`DirectedHamiltonianCircuitInput` is a custom one-field wrapper around a directed graph.  Its
encoder deliberately reuses the exact graph encoder, but the wrapper remains a distinct carrier
and therefore a distinct representation identity.  This is an explicit, user-selected lawful
presentation: it exports no structural certificate or automatic-presentation admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace DirectedHamiltonianCircuit

open Encoding
open ComplexityReduction.Combinatorics.Graph

/-- The complete graph layout of a Directed Hamiltonian Circuit input. -/
def structuredShape : CodecShape :=
  Graph.structuredShape

/--
The exact lawful V2 presentation of CR's structured Directed Hamiltonian Circuit encoder.

The carrier is a custom wrapper rather than the graph carrier itself, so this faithful
presentation intentionally remains user-locked despite sharing its encoded payload layout.
-/
def structuredPresentation : LawfulEncodedType where
  encodedType := directedHamiltonianCircuitStructuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨directedHamiltonianCircuitStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's structured Directed Hamiltonian Circuit encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = directedHamiltonianCircuitStructuredEncodedType :=
  rfl

/-- The representation identity records the complete directed-graph layout. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The presentation carrier is exactly CR's Directed Hamiltonian Circuit wrapper syntax. -/
theorem structuredPresentation_carrier_eq_DirectedHamiltonianCircuitInput :
    structuredPresentation.Carrier = DirectedHamiltonianCircuitInput :=
  rfl

/-- The only encoder exposed by this presentation is CR's established structured encoder. -/
@[simp]
theorem structuredPresentation_encode (input : structuredPresentation.Carrier) :
    structuredPresentation.encode input = directedHamiltonianCircuitStructuredEncodedType.encode input :=
  rfl

/-- The existing Directed Hamiltonian Circuit predicate at its exact lawful V2 presentation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := DirectedHamiltonianCircuit

/-- The canonical V2 endpoint for CR's structured Karp21 Directed Hamiltonian Circuit problem. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

/-- The endpoint is indexed by the exact selected Directed Hamiltonian Circuit presentation. -/
@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

/-- The endpoint retains the complete directed-graph representation identity. -/
@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = structuredShape.identity :=
  rfl

/-- The compatibility backend endpoint is exactly CR's structured decision problem. -/
@[simp]
theorem structuredProblem_backendEndpoint_eq_legacy :
    structuredProblem.backendEndpoint = directedHamiltonianCircuitStructuredDecisionProblem :=
  rfl

/-- The presented predicate is definitionally CR's Directed Hamiltonian Circuit semantics. -/
@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ DirectedHamiltonianCircuit input :=
  Iff.rfl

/-- The typed endpoint accepts exactly the existing Directed Hamiltonian Circuit instances. -/
@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ DirectedHamiltonianCircuit input :=
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
      (fun graph : GraphInput => ({ graph := graph } : DirectedHamiltonianCircuitInput)) := by
  exact TMPolyTimeMap.of_encodingEquiv
    graphStructuredEncodedType structuredProblem.representation.encodedType _
    (Equiv.refl graphStructuredEncodedType.Symbol) (by
      intro graph
      change graphStructuredEncodedType.encode graph =
        List.map id (graphStructuredEncodedType.encode graph)
      rw [List.map_id])

end DirectedHamiltonianCircuit
end Presentation
end ComplexityReduction
