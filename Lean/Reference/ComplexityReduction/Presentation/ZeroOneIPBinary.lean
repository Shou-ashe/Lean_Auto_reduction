/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP.StructuredTM.UnaryToBinary
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.ZeroOneIP

/-!
Canonical V2 presentation of CR's binary-numeric structured 0-1 Integer
Programming endpoint.

`ZeroOneIP.zeroOneIPStructuredToBinaryStructuredTMKarpReduction` preserves
the `IntegerProgrammingInput` carrier and its semantic predicate while moving
the variable count, every integer coefficient, and every constraint bound to
their binary codecs.  The representation identity below records that full
layout, so the shared carrier cannot collapse the binary endpoint with the
unary presentation.  Since the carrier remains a custom record, this
presentation is explicitly user-locked and exports neither a structural
certificate nor automatic-admission evidence.
-/

namespace ComplexityReduction
namespace Presentation
namespace ZeroOneIPBinary

open Encoding
open ComplexityReduction.Combinatorics

/-- The sign-tag followed by binary-magnitude layout of one binary encoded integer. -/
def binaryIntegerShape : CodecShape :=
  .prod .bool .binaryNat

/-- The ordered binary coefficient row and binary bound layout of one linear inequality. -/
def binaryConstraintShape : CodecShape :=
  .prod (.list binaryIntegerShape) binaryIntegerShape

/-- The full binary variable-count and ordered binary-constraint-list layout of 0-1 IP. -/
def binaryStructuredShape : CodecShape :=
  .prod .binaryNat (.list binaryConstraintShape)

/--
The exact lawful V2 presentation of CR's binary-numeric structured 0-1 IP
encoder.  The established injectivity theorem proves lawfulness only:
`IntegerProgrammingInput` is not the product carrier described by
`binaryStructuredShape`, so this declaration deliberately remains user-locked.
-/
def binaryStructuredPresentation : LawfulEncodedType where
  encodedType := integerProgrammingBinaryStructuredEncodedType
  representation := binaryStructuredShape.identity
  faithful := ⟨integerProgrammingBinaryStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's binary structured 0-1 IP encoder. -/
@[simp]
theorem binaryStructuredPresentation_encodedType :
    binaryStructuredPresentation.encodedType = integerProgrammingBinaryStructuredEncodedType :=
  rfl

/-- The identity records binary variable counts, coefficients, and bounds. -/
@[simp]
theorem binaryStructuredPresentation_representation :
    binaryStructuredPresentation.representation = binaryStructuredShape.identity :=
  rfl

/-- The presentation carrier is exactly CR's established integer-programming record syntax. -/
theorem binaryStructuredPresentation_carrier_eq_IntegerProgrammingInput :
    binaryStructuredPresentation.Carrier = IntegerProgrammingInput :=
  rfl

/-- The only executable encoder exposed here is CR's binary structured 0-1 IP encoder. -/
@[simp]
theorem binaryStructuredPresentation_encode (input : binaryStructuredPresentation.Carrier) :
    binaryStructuredPresentation.encode input =
      integerProgrammingBinaryStructuredEncodedType.encode input :=
  rfl

/-- Binary and unary 0-1 IP presentations retain distinct full representation identities. -/
theorem binaryStructuredPresentation_representation_ne_structuredPresentation :
    binaryStructuredPresentation.representation ≠ ZeroOneIP.structuredPresentation.representation := by
  rw [binaryStructuredPresentation_representation, ZeroOneIP.structuredPresentation_representation]
  exact CodecShape.identity_ne_of_shape_ne (by decide)

/-- The existing 0-1 integer-programming predicate at CR's exact binary presentation. -/
def binaryStructuredProblemAt : ProblemAt binaryStructuredPresentation where
  isYes := ZeroOneIntegerProgramming

/-- The canonical V2 endpoint for CR's binary-numeric structured 0-1 IP problem. -/
@[complexity_reduction_ir_typed_problem]
def binaryStructuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt binaryStructuredPresentation binaryStructuredProblemAt

/-- The endpoint is indexed by the exact selected binary 0-1 IP presentation. -/
@[simp]
theorem binaryStructuredProblem_representation :
    binaryStructuredProblem.representation = binaryStructuredPresentation :=
  rfl

/-- The endpoint retains its full binary variable-count, coefficient, and bound identity. -/
@[simp]
theorem binaryStructuredProblem_representationIdentity :
    binaryStructuredProblem.representationIdentity = binaryStructuredShape.identity :=
  rfl

/-- The unary and binary endpoints retain distinct representation identities. -/
theorem binaryStructuredProblem_representationIdentity_ne_structuredProblem_representationIdentity :
    binaryStructuredProblem.representationIdentity ≠
      ZeroOneIP.structuredProblem.representationIdentity := by
  simpa using binaryStructuredPresentation_representation_ne_structuredPresentation

/-- The compatibility backend endpoint is exactly CR's binary structured 0-1 IP endpoint. -/
@[simp]
theorem binaryStructuredProblem_backendEndpoint_eq_legacy :
    binaryStructuredProblem.backendEndpoint = zeroOneIntegerProgrammingBinaryStructuredDecisionProblem :=
  rfl

/-- The binary presented predicate is definitionally CR's 0-1 integer-programming semantics. -/
@[simp]
theorem binaryStructuredProblemAt_isYes (input : binaryStructuredPresentation.Carrier) :
    binaryStructuredProblemAt.isYes input ↔ ZeroOneIntegerProgramming input :=
  Iff.rfl

/-- The typed binary endpoint accepts exactly CR's established 0-1 IP instances. -/
@[simp]
theorem binaryStructuredProblem_accepts (input : binaryStructuredProblem.Instance) :
    binaryStructuredProblem.accepts input ↔ ZeroOneIntegerProgramming input :=
  Iff.rfl

end ZeroOneIPBinary
end Presentation
end ComplexityReduction
