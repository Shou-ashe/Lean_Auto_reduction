/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.StructuredTM.UnaryToBinary
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.MaxCut

/-!
Canonical V2 presentation of CR's binary-numeric structured Max Cut endpoint.

`MaxCut.maxCutStructuredToBinaryStructuredTMKarpReduction` preserves the
semantic `MaxCutInput` instance and changes only its threshold encoding from
unary to binary.  This leaf binds the exact binary target encoder and
decision-problem endpoint to a representation identity that retains that
change.  Since `MaxCutInput` remains a custom wrapper, the presentation is
explicitly user-locked and intentionally provides neither a structural
certificate nor automatic-presentation admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace MaxCutBinary

open Encoding
open ComplexityReduction.Combinatorics.Graph

/-- The complete graph-and-binary-cut-threshold layout of a Max Cut input. -/
def binaryStructuredShape : CodecShape :=
  .prod Graph.structuredShape .binaryNat

/--
The exact lawful V2 presentation of CR's binary-numeric structured Max Cut encoder.

The carrier remains the custom `MaxCutInput` wrapper rather than the product carrier
denoted by `binaryStructuredShape`.  The reused injectivity theorem proves lawfulness
only; it does not make this presentation eligible for structural auto-admission.
-/
def binaryStructuredPresentation : LawfulEncodedType where
  encodedType := maxCutBinaryStructuredEncodedType
  representation := binaryStructuredShape.identity
  faithful := ⟨maxCutBinaryStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's binary structured Max Cut encoder. -/
@[simp]
theorem binaryStructuredPresentation_encodedType :
    binaryStructuredPresentation.encodedType = maxCutBinaryStructuredEncodedType :=
  rfl

/-- The representation identity records the binary threshold rather than the unary one. -/
@[simp]
theorem binaryStructuredPresentation_representation :
    binaryStructuredPresentation.representation = binaryStructuredShape.identity :=
  rfl

/-- The presentation carrier is exactly CR's established `MaxCutInput` wrapper syntax. -/
theorem binaryStructuredPresentation_carrier_eq_MaxCutInput :
    binaryStructuredPresentation.Carrier = MaxCutInput :=
  rfl

/-- The only encoder exposed by this presentation is CR's binary structured encoder. -/
@[simp]
theorem binaryStructuredPresentation_encode (input : binaryStructuredPresentation.Carrier) :
    binaryStructuredPresentation.encode input = maxCutBinaryStructuredEncodedType.encode input :=
  rfl

/-- A shared carrier does not collapse the unary and binary Max Cut representation identities. -/
theorem binaryStructuredShape_identity_ne_structuredShape_identity :
    binaryStructuredShape.identity ≠ MaxCut.structuredShape.identity := by
  apply CodecShape.identity_ne_of_shape_ne
  intro shapeEquality
  change CodecShape.prod Graph.structuredShape CodecShape.binaryNat =
    CodecShape.prod Graph.structuredShape CodecShape.unaryNat at shapeEquality
  apply CodecShape.unaryNat_identity_ne_binaryNat_identity
  exact congrArg CodecShape.identity (CodecShape.prod.inj shapeEquality).2.symm

/-- The binary-numeric Max Cut predicate at its exact lawful V2 presentation. -/
def binaryStructuredProblemAt : ProblemAt binaryStructuredPresentation where
  isYes := MaxCut

/-- The canonical V2 endpoint for CR's binary-numeric structured Max Cut problem. -/
@[complexity_reduction_ir_typed_problem]
def binaryStructuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt binaryStructuredPresentation binaryStructuredProblemAt

/-- The endpoint is indexed by the exact selected binary Max Cut presentation. -/
@[simp]
theorem binaryStructuredProblem_representation :
    binaryStructuredProblem.representation = binaryStructuredPresentation :=
  rfl

/-- The endpoint retains the complete graph-and-binary-threshold representation identity. -/
@[simp]
theorem binaryStructuredProblem_representationIdentity :
    binaryStructuredProblem.representationIdentity = binaryStructuredShape.identity :=
  rfl

/-- The unary and binary presented endpoints retain distinct representation identities. -/
theorem binaryStructuredProblem_representationIdentity_ne_structuredProblem_representationIdentity :
    binaryStructuredProblem.representationIdentity ≠ MaxCut.structuredProblem.representationIdentity := by
  simpa using binaryStructuredShape_identity_ne_structuredShape_identity

/-- The compatibility backend endpoint is exactly CR's binary structured Max Cut decision problem. -/
@[simp]
theorem binaryStructuredProblem_backendEndpoint_eq_legacy :
    binaryStructuredProblem.backendEndpoint = maxCutBinaryStructuredDecisionProblem :=
  rfl

/-- The presented predicate is definitionally CR's Max Cut semantics. -/
@[simp]
theorem binaryStructuredProblemAt_isYes (input : binaryStructuredPresentation.Carrier) :
    binaryStructuredProblemAt.isYes input ↔ MaxCut input :=
  Iff.rfl

/-- The typed endpoint accepts exactly the existing binary structured Max Cut instances. -/
@[simp]
theorem binaryStructuredProblem_accepts (input : binaryStructuredProblem.Instance) :
    binaryStructuredProblem.accepts input ↔ MaxCut input :=
  Iff.rfl

end MaxCutBinary
end Presentation
end ComplexityReduction
