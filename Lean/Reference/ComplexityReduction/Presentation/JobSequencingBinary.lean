/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.JobSequencingBinaryStructuredTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Presentation.JobSequencing

/-!
Canonical V2 presentation of CR's binary-numeric structured Job Sequencing endpoint.

`Knapsack.knapsackToJobSequencingBinaryStructuredTMKarpReduction` targets
`jobSequencingBinaryStructuredDecisionProblem`. Its carrier is the same custom
`JobSequencingInput` wrapper as the unary structured endpoint, while every job
field and the target profit use the binary-natural codec. The complete binary
shape below records that distinction, so a shared carrier cannot collapse the
two representations. This presentation is explicitly user-locked: it exports
no structural certificate or automatic-presentation admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace JobSequencingBinary

open Encoding
open ComplexityReduction.Combinatorics

/-- The ordered binary-natural layout of one Job Sequencing job. -/
def binaryJobShape : CodecShape :=
  .prod .binaryNat (.prod .binaryNat .binaryNat)

/-- The complete ordered binary layout of jobs and target profit in one input. -/
def binaryStructuredShape : CodecShape :=
  .prod (.list binaryJobShape) .binaryNat

/--
The exact lawful V2 presentation of CR's binary-numeric structured Job
Sequencing encoder. `JobSequencingInput` is a custom wrapper rather than the
nested product denoted by `binaryStructuredShape`, so faithfulness establishes
lawfulness only and cannot admit this endpoint structurally.
-/
def binaryStructuredPresentation : LawfulEncodedType where
  encodedType := jobSequencingBinaryStructuredEncodedType
  representation := binaryStructuredShape.identity
  faithful := ⟨jobSequencingBinaryStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's binary structured Job Sequencing encoder. -/
@[simp]
theorem binaryStructuredPresentation_encodedType :
    binaryStructuredPresentation.encodedType = jobSequencingBinaryStructuredEncodedType :=
  rfl

/-- The representation identity records binary codecs for every job field and target profit. -/
@[simp]
theorem binaryStructuredPresentation_representation :
    binaryStructuredPresentation.representation = binaryStructuredShape.identity :=
  rfl

/-- The binary structured presentation has CR's established Job Sequencing wrapper carrier. -/
theorem binaryStructuredPresentation_carrier_eq_JobSequencingInput :
    binaryStructuredPresentation.Carrier = JobSequencingInput :=
  rfl

/-- The only encoder exposed by this presentation is CR's binary structured encoder. -/
@[simp]
theorem binaryStructuredPresentation_encode (input : binaryStructuredPresentation.Carrier) :
    binaryStructuredPresentation.encode input =
      jobSequencingBinaryStructuredEncodedType.encode input :=
  rfl

/-- Binary and unary Job Sequencing presentations retain distinct complete identities. -/
theorem binaryStructuredPresentation_representation_ne_structuredPresentation :
    binaryStructuredPresentation.representation ≠ JobSequencing.structuredPresentation.representation := by
  rw [binaryStructuredPresentation_representation, JobSequencing.structuredPresentation_representation]
  exact CodecShape.identity_ne_of_shape_ne (by decide)

/-- The existing Job Sequencing predicate at CR's exact binary structured presentation. -/
def binaryStructuredProblemAt : ProblemAt binaryStructuredPresentation where
  isYes := JobSequencing

/-- The canonical V2 endpoint for CR's binary-numeric structured Job Sequencing problem. -/
@[complexity_reduction_ir_typed_problem]
def binaryStructuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt binaryStructuredPresentation binaryStructuredProblemAt

/-- The endpoint is indexed by the exact selected binary Job Sequencing presentation. -/
@[simp]
theorem binaryStructuredProblem_representation :
    binaryStructuredProblem.representation = binaryStructuredPresentation :=
  rfl

/-- The endpoint retains the complete binary Job Sequencing representation identity. -/
@[simp]
theorem binaryStructuredProblem_representationIdentity :
    binaryStructuredProblem.representationIdentity = binaryStructuredShape.identity :=
  rfl

/-- The unary and binary presented endpoints retain distinct representation identities. -/
theorem binaryStructuredProblem_representationIdentity_ne_structuredProblem_representationIdentity :
    binaryStructuredProblem.representationIdentity ≠
      JobSequencing.structuredProblem.representationIdentity := by
  simpa using binaryStructuredPresentation_representation_ne_structuredPresentation

/-- The compatibility backend endpoint is exactly CR's binary structured decision problem. -/
@[simp]
theorem binaryStructuredProblem_backendEndpoint_eq_legacy :
    binaryStructuredProblem.backendEndpoint = jobSequencingBinaryStructuredDecisionProblem :=
  rfl

/-- The presented binary fixed-representation predicate is definitionally CR's semantics. -/
@[simp]
theorem binaryStructuredProblemAt_isYes (input : binaryStructuredPresentation.Carrier) :
    binaryStructuredProblemAt.isYes input ↔ JobSequencing input :=
  Iff.rfl

/-- The typed binary endpoint accepts exactly the existing Job Sequencing instances. -/
@[simp]
theorem binaryStructuredProblem_accepts (input : binaryStructuredProblem.Instance) :
    binaryStructuredProblem.accepts input ↔ JobSequencing input :=
  Iff.rfl

end JobSequencingBinary
end Presentation
end ComplexityReduction
