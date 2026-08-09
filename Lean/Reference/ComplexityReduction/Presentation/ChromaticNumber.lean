/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.Graph

/-!
Canonical V2 presentation of the structured Karp21 Chromatic Number endpoint.

`ComplexityReduction` already supplies the exact finite-alphabet encoder,
faithfulness theorem, semantic predicate, and encoded decision problem.  The
carrier is nevertheless a custom `ChromaticNumberInput` wrapper, so this leaf
records an explicit user-selected codec identity and intentionally exports no
structural certificate or automatic-presentation admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace ChromaticNumber

open Encoding
open ComplexityReduction.Combinatorics.Graph

/-- The complete graph-and-unary-colour-bound layout of a Chromatic Number input. -/
def structuredShape : CodecShape :=
  .prod Graph.structuredShape .unaryNat

/--
The exact lawful V2 presentation of CR's structured Chromatic Number encoder.

This faithful custom wrapper is intentionally user-locked: the standard
product layout describes its encoded payload, not its structure carrier.
-/
def structuredPresentation : LawfulEncodedType where
  encodedType := chromaticNumberStructuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨chromaticNumberStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's structured Chromatic Number encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = chromaticNumberStructuredEncodedType :=
  rfl

/-- The representation identity records the graph payload and unary colour-bound fields. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The presentation carrier is exactly the existing Karp21 Chromatic Number syntax. -/
theorem structuredPresentation_carrier_eq_ChromaticNumberInput :
    structuredPresentation.Carrier = ChromaticNumberInput :=
  rfl

/-- The only encoder exposed by this presentation is CR's established structured encoder. -/
@[simp]
theorem structuredPresentation_encode (input : structuredPresentation.Carrier) :
    structuredPresentation.encode input = chromaticNumberStructuredEncodedType.encode input :=
  rfl

/-- The existing Chromatic Number predicate at its exact lawful V2 presentation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := ChromaticNumber

/-- The canonical V2 endpoint for CR's structured Karp21 Chromatic Number problem. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

/-- The endpoint is indexed by the exact selected Chromatic Number presentation. -/
@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

/-- The endpoint retains the complete graph-and-colour-bound representation identity. -/
@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = structuredShape.identity :=
  rfl

/-- The compatibility backend endpoint is exactly CR's established structured decision problem. -/
@[simp]
theorem structuredProblem_backendEndpoint_eq_legacy :
    structuredProblem.backendEndpoint = chromaticNumberStructuredDecisionProblem :=
  rfl

/-- The presented predicate is definitionally CR's Chromatic Number semantics. -/
@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ ChromaticNumber input :=
  Iff.rfl

/-- The typed endpoint accepts exactly the existing Chromatic Number instances. -/
@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ ChromaticNumber input :=
  Iff.rfl

end ChromaticNumber
end Presentation
end ComplexityReduction
