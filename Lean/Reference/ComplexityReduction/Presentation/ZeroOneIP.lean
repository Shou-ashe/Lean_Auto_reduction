/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem

/-!
Canonical V2 presentation of the structured Karp21 0-1 Integer Programming endpoint.

The selected encoder is exactly
`zeroOneIntegerProgrammingStructuredDecisionProblem`.  Its
`IntegerProgrammingInput` carrier is a custom record around the variable-count
and constraint-list payload.  The shape below retains the sign-and-unary-magnitude
layout of every integer coefficient and bound, but this custom wrapper has no
closed `StructuralRepresentationOrigin`; the presentation is intentionally
user-locked and exports neither a structural certificate nor automatic admission.

The existing structured 3SAT-to-0-1-IP direct-TM construction is deliberately
not imported as V2 route evidence here: its axiom audit contains `native_decide`.
This presentation remains useful as the exact typed target of that fail-closed
capability request and of any later standard-axiom audited route.
-/

namespace ComplexityReduction
namespace Presentation
namespace ZeroOneIP

open Encoding
open ComplexityReduction.Combinatorics

/-- The sign-tag followed by unary-magnitude layout of one unary encoded integer. -/
def unaryIntegerShape : CodecShape :=
  .prod .bool .unaryNat

/-- The ordered row-of-coefficients and bound layout of one linear inequality. -/
def constraintShape : CodecShape :=
  .prod (.list unaryIntegerShape) unaryIntegerShape

/-- The complete variable-count and ordered-constraint-list layout of structured 0-1 IP. -/
def structuredShape : CodecShape :=
  .prod .unaryNat (.list constraintShape)

/--
The exact lawful V2 presentation of CR's structured 0-1 Integer Programming encoder.

`IntegerProgrammingInput` is a custom record, not the nested product denoted by
`structuredShape`.  Its faithful legacy encoder therefore remains explicitly
selected rather than automatically admitted as a structural presentation.
-/
def structuredPresentation : LawfulEncodedType where
  encodedType := integerProgrammingStructuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨integerProgrammingStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's structured 0-1 IP encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = integerProgrammingStructuredEncodedType :=
  rfl

/-- The identity records the variable count, every coefficient, and every constraint bound. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The presentation carrier is exactly CR's existing integer-programming record syntax. -/
theorem structuredPresentation_carrier_eq_IntegerProgrammingInput :
    structuredPresentation.Carrier = IntegerProgrammingInput :=
  rfl

/-- The only executable encoder exposed here is CR's established structured 0-1 IP encoder. -/
@[simp]
theorem structuredPresentation_encode (input : structuredPresentation.Carrier) :
    structuredPresentation.encode input = integerProgrammingStructuredEncodedType.encode input :=
  rfl

/-- The existing 0-1 integer-programming predicate at its exact lawful V2 presentation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := ZeroOneIntegerProgramming

/-- The canonical V2 endpoint for CR's structured Karp21 0-1 Integer Programming problem. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

/-- The endpoint is indexed by the exact selected structured 0-1 IP presentation. -/
@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

/-- The endpoint retains the complete integer-programming representation identity. -/
@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = structuredShape.identity :=
  rfl

/-- The compatibility backend endpoint is exactly CR's structured 0-1 IP decision problem. -/
@[simp]
theorem structuredProblem_backendEndpoint_eq_legacy :
    structuredProblem.backendEndpoint = zeroOneIntegerProgrammingStructuredDecisionProblem :=
  rfl

/-- The presented predicate is definitionally CR's 0-1 integer-programming semantics. -/
@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ ZeroOneIntegerProgramming input :=
  Iff.rfl

/-- The typed endpoint accepts exactly CR's established 0-1 IP instances. -/
@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ ZeroOneIntegerProgramming input :=
  Iff.rfl

end ZeroOneIP
end Presentation
end ComplexityReduction
