/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.Graph.WeightedGraph
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Graph

/-!
Canonical V2 presentation of the structured Karp21 Steiner Tree endpoint.

`ComplexityReduction` already supplies the exact finite-alphabet encoder,
faithfulness theorem, semantic predicate, and encoded decision problem.  The
carrier is nevertheless a custom `SteinerTreeInput` wrapper, so this leaf
records an explicit user-selected codec identity and intentionally exports no
structural certificate or automatic-presentation admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace SteinerTree

open Encoding
open ComplexityReduction.Combinatorics.Graph

/-- The ordered layout of a weighted graph: vertices, weighted edges, and directedness. -/
def weightedGraphStructuredShape : CodecShape :=
  .prod .unaryNat
    (.prod (.list (.prod .unaryNat (.prod .unaryNat .unaryNat))) .bool)

/-- The complete weighted-graph, terminal-list, and unary weight-bound layout of a Steiner Tree
input. -/
def structuredShape : CodecShape :=
  .prod weightedGraphStructuredShape (.prod (.list .unaryNat) .unaryNat)

/--
The exact lawful V2 presentation of CR's structured Steiner Tree encoder.

This faithful custom wrapper is intentionally user-locked: the standard
product layout describes its encoded payload, not its structure carrier.
-/
def structuredPresentation : LawfulEncodedType where
  encodedType := steinerTreeStructuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨steinerTreeStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's structured Steiner Tree encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = steinerTreeStructuredEncodedType :=
  rfl

/-- The representation identity records every weighted graph, terminal, and bound field. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The presentation carrier is exactly the existing Karp21 Steiner Tree syntax. -/
theorem structuredPresentation_carrier_eq_SteinerTreeInput :
    structuredPresentation.Carrier = SteinerTreeInput :=
  rfl

/-- The only encoder exposed by this presentation is CR's established structured encoder. -/
@[simp]
theorem structuredPresentation_encode (input : structuredPresentation.Carrier) :
    structuredPresentation.encode input = steinerTreeStructuredEncodedType.encode input :=
  rfl

/-- The existing Steiner Tree predicate at its exact lawful V2 presentation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := SteinerTree

/-- The canonical V2 endpoint for CR's structured Karp21 Steiner Tree problem. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

/-- The endpoint is indexed by the exact selected Steiner Tree presentation. -/
@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

/-- The endpoint retains the complete weighted Steiner Tree representation identity. -/
@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = structuredShape.identity :=
  rfl

/-- The compatibility backend endpoint is exactly CR's established structured decision problem. -/
@[simp]
theorem structuredProblem_backendEndpoint_eq_legacy :
    structuredProblem.backendEndpoint = steinerTreeStructuredDecisionProblem :=
  rfl

/-- The presented predicate is definitionally CR's Steiner Tree semantics. -/
@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ SteinerTree input :=
  Iff.rfl

/-- The typed endpoint accepts exactly the existing Steiner Tree instances. -/
@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ SteinerTree input :=
  Iff.rfl

end SteinerTree
end Presentation
end ComplexityReduction
