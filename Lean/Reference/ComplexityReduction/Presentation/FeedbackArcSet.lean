/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FeedbackArcSet
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Graph

/-!
Canonical V2 presentation of the structured Karp21 Feedback Arc Set endpoint.

`ComplexityReduction` already supplies the exact finite-alphabet encoder,
faithfulness theorem, semantic predicate, and encoded decision problem.  The
carrier is nevertheless a custom `FeedbackArcSetInput` wrapper, so this leaf
records an explicit user-selected codec identity and intentionally exports no
structural certificate or automatic-presentation admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace FeedbackArcSet

open Encoding
open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.Karp21.FeedbackArcSet

/-- The complete graph-and-unary-deletion-budget layout of a Feedback Arc Set input. -/
def structuredShape : CodecShape :=
  .prod Graph.structuredShape .unaryNat

/--
The exact lawful V2 presentation of CR's structured Feedback Arc Set encoder.

This faithful custom wrapper is intentionally user-locked: the standard
product layout describes its encoded payload, not its structure carrier.
-/
def structuredPresentation : LawfulEncodedType where
  encodedType := feedbackArcSetStructuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨feedbackArcSetStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's structured Feedback Arc Set encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = feedbackArcSetStructuredEncodedType :=
  rfl

/-- The representation identity records the graph payload and unary deletion-budget fields. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The presentation carrier is exactly the existing Karp21 Feedback Arc Set syntax. -/
theorem structuredPresentation_carrier_eq_FeedbackArcSetInput :
    structuredPresentation.Carrier = FeedbackArcSetInput :=
  rfl

/-- The only encoder exposed by this presentation is CR's established structured encoder. -/
@[simp]
theorem structuredPresentation_encode (input : structuredPresentation.Carrier) :
    structuredPresentation.encode input = feedbackArcSetStructuredEncodedType.encode input :=
  rfl

/-- The existing Feedback Arc Set predicate at its exact lawful V2 presentation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := FeedbackArcSet

/-- The canonical V2 endpoint for CR's structured Karp21 Feedback Arc Set problem. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

/-- The endpoint is indexed by the exact selected Feedback Arc Set presentation. -/
@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

/-- The endpoint retains the complete graph-and-deletion-budget representation identity. -/
@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = structuredShape.identity :=
  rfl

/-- The compatibility backend endpoint is exactly CR's established structured decision problem. -/
@[simp]
theorem structuredProblem_backendEndpoint_eq_legacy :
    structuredProblem.backendEndpoint = feedbackArcSetStructuredDecisionProblem :=
  rfl

/-- The presented predicate is definitionally CR's Feedback Arc Set semantics. -/
@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ FeedbackArcSet input :=
  Iff.rfl

/-- The typed endpoint accepts exactly the existing Feedback Arc Set instances. -/
@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ FeedbackArcSet input :=
  Iff.rfl

end FeedbackArcSet
end Presentation
end ComplexityReduction
