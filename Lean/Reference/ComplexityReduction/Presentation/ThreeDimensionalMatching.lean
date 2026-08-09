/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeDimensionalMatching
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem

/-!
Canonical V2 presentation of the structured Karp21 Three-Dimensional Matching endpoint.

`ThreeDimensionalMatchingInput` is a custom five-field wrapper.  Its exact
structured finite-alphabet encoder has a standard-shaped payload, but the
wrapper carrier remains distinct from that payload.  This leaf therefore
records an explicit, user-selected lawful presentation and deliberately
exports no structural certificate or automatic-presentation admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace ThreeDimensionalMatching

open Encoding
open ComplexityReduction.Combinatorics

/-- The unary-Nat layout of one ordered X/Y/Z triple. -/
def tripleShape : CodecShape :=
  .prod .unaryNat (.prod .unaryNat .unaryNat)

/-- The complete ordered layout of a structured Three-Dimensional Matching input. -/
def structuredShape : CodecShape :=
  .prod .unaryNat
    (.prod .unaryNat
      (.prod .unaryNat
        (.prod (.list tripleShape) .unaryNat)))

/--
The exact lawful V2 presentation of CR's structured Three-Dimensional Matching encoder.

The carrier is a custom wrapper rather than the nested product denoted by
`structuredShape`; faithful encoding evidence consequently does not make this
an automatically selectable structural presentation.
-/
def structuredPresentation : LawfulEncodedType where
  encodedType := threeDimensionalMatchingStructuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨threeDimensionalMatchingStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's structured Three-Dimensional Matching encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = threeDimensionalMatchingStructuredEncodedType :=
  rfl

/-- The representation identity retains every ordered size, triple-family, and bound field. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The presentation carrier is exactly the existing Karp21 Three-Dimensional Matching syntax. -/
theorem structuredPresentation_carrier_eq_ThreeDimensionalMatchingInput :
    structuredPresentation.Carrier = ThreeDimensionalMatchingInput :=
  rfl

/-- The only encoder exposed by this presentation is CR's established structured encoder. -/
@[simp]
theorem structuredPresentation_encode (input : structuredPresentation.Carrier) :
    structuredPresentation.encode input = threeDimensionalMatchingStructuredEncodedType.encode input :=
  rfl

/-- The existing Three-Dimensional Matching predicate at its exact lawful V2 presentation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := ThreeDimensionalMatching

/-- The canonical V2 endpoint for CR's structured Karp21 Three-Dimensional Matching problem. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

/-- The endpoint is indexed by the exact selected Three-Dimensional Matching presentation. -/
@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

/-- The endpoint retains the complete Three-Dimensional Matching representation identity. -/
@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = structuredShape.identity :=
  rfl

/-- The compatibility backend endpoint is exactly CR's structured decision problem. -/
@[simp]
theorem structuredProblem_backendEndpoint_eq_legacy :
    structuredProblem.backendEndpoint = threeDimensionalMatchingStructuredDecisionProblem :=
  rfl

/-- The presented predicate is definitionally CR's Three-Dimensional Matching semantics. -/
@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ ThreeDimensionalMatching input :=
  Iff.rfl

/-- The typed endpoint accepts exactly the existing Three-Dimensional Matching instances. -/
@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ ThreeDimensionalMatching input :=
  Iff.rfl

end ThreeDimensionalMatching
end Presentation
end ComplexityReduction
