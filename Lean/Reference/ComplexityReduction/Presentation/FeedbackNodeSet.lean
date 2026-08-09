/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.FeedbackNodeSet
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Graph

/-!
Canonical V2 presentation of the structured Karp21 Feedback Node Set endpoint.

`ComplexityReduction` already supplies the exact finite-alphabet encoder,
faithfulness theorem, semantic predicate, and encoded decision problem.  The
carrier is nevertheless a custom `FeedbackNodeSetInput` wrapper, so this leaf
records an explicit user-selected codec identity and intentionally exports no
structural certificate or automatic-presentation admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace FeedbackNodeSet

open Encoding
open ComplexityReduction.Combinatorics.Graph
open ComplexityReduction.Karp21.FeedbackNodeSet

/-- The complete graph-and-unary-deletion-budget layout of a Feedback Node Set input. -/
def structuredShape : CodecShape :=
  .prod Graph.structuredShape .unaryNat

/--
The exact lawful V2 presentation of CR's structured Feedback Node Set encoder.

This faithful custom wrapper is intentionally user-locked: the standard
product layout describes its encoded payload, not its structure carrier.
-/
def structuredPresentation : LawfulEncodedType where
  encodedType := feedbackNodeSetStructuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨feedbackNodeSetStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's structured Feedback Node Set encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = feedbackNodeSetStructuredEncodedType :=
  rfl

/-- The representation identity records the graph payload and unary deletion-budget fields. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The presentation carrier is exactly the existing Karp21 Feedback Node Set syntax. -/
theorem structuredPresentation_carrier_eq_FeedbackNodeSetInput :
    structuredPresentation.Carrier = FeedbackNodeSetInput :=
  rfl

/-- The only encoder exposed by this presentation is CR's established structured encoder. -/
@[simp]
theorem structuredPresentation_encode (input : structuredPresentation.Carrier) :
    structuredPresentation.encode input = feedbackNodeSetStructuredEncodedType.encode input :=
  rfl

/-- The existing Feedback Node Set predicate at its exact lawful V2 presentation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := FeedbackNodeSet

/-- The canonical V2 endpoint for CR's structured Karp21 Feedback Node Set problem. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

/-- The endpoint is indexed by the exact selected Feedback Node Set presentation. -/
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
    structuredProblem.backendEndpoint = feedbackNodeSetStructuredDecisionProblem :=
  rfl

/-- The presented predicate is definitionally CR's Feedback Node Set semantics. -/
@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ FeedbackNodeSet input :=
  Iff.rfl

/-- The typed endpoint accepts exactly the existing Feedback Node Set instances. -/
@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ FeedbackNodeSet input :=
  Iff.rfl

end FeedbackNodeSet
end Presentation
end ComplexityReduction
