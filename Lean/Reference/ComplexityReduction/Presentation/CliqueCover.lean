/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Graph

/-!
Canonical V2 presentation of the structured Karp21 Clique Cover endpoint.

`ComplexityReduction` already supplies the exact finite-alphabet encoder,
faithfulness theorem, semantic predicate, and encoded decision problem.  The
carrier is nevertheless a custom `CliqueCoverInput` wrapper, so this leaf
records an explicit user-selected codec identity and intentionally exports no
structural certificate or automatic-presentation admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace CliqueCover

open Encoding
open ComplexityReduction.Combinatorics.Graph

/-- The complete graph-and-unary-block-bound layout of a Clique Cover input. -/
def structuredShape : CodecShape :=
  .prod Graph.structuredShape .unaryNat

/--
The exact lawful V2 presentation of CR's structured Clique Cover encoder.

This faithful custom wrapper is intentionally user-locked: the standard
product layout describes its encoded payload, not its structure carrier.
-/
def structuredPresentation : LawfulEncodedType where
  encodedType := cliqueCoverStructuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨cliqueCoverStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's structured Clique Cover encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = cliqueCoverStructuredEncodedType :=
  rfl

/-- The representation identity records the graph payload and unary block-bound fields. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The presentation carrier is exactly the existing Karp21 Clique Cover syntax. -/
theorem structuredPresentation_carrier_eq_CliqueCoverInput :
    structuredPresentation.Carrier = CliqueCoverInput :=
  rfl

/-- The only encoder exposed by this presentation is CR's established structured encoder. -/
@[simp]
theorem structuredPresentation_encode (input : structuredPresentation.Carrier) :
    structuredPresentation.encode input = cliqueCoverStructuredEncodedType.encode input :=
  rfl

/-- The existing Clique Cover predicate at its exact lawful V2 presentation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := CliqueCover

/-- The canonical V2 endpoint for CR's structured Karp21 Clique Cover problem. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

/-- The endpoint is indexed by the exact selected Clique Cover presentation. -/
@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

/-- The endpoint retains the complete graph-and-block-bound representation identity. -/
@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = structuredShape.identity :=
  rfl

/-- The compatibility backend endpoint is exactly CR's established structured decision problem. -/
@[simp]
theorem structuredProblem_backendEndpoint_eq_legacy :
    structuredProblem.backendEndpoint = cliqueCoverStructuredDecisionProblem :=
  rfl

/-- The presented predicate is definitionally CR's Clique Cover semantics. -/
@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ CliqueCover input :=
  Iff.rfl

/-- The typed endpoint accepts exactly the existing Clique Cover instances. -/
@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ CliqueCover input :=
  Iff.rfl

end CliqueCover
end Presentation
end ComplexityReduction
