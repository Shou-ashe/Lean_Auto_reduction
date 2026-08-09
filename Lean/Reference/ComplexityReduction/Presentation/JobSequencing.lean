/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.JobSequencingStructuredTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem

/-!
Canonical V2 presentation of the structured Karp21 Job Sequencing endpoint.

`knapsackToJobSequencingStructuredTMKarpReduction` targets exactly
`jobSequencingStructuredDecisionProblem`.  Its `JobSequencingInput` carrier is
a custom two-field wrapper around the list-of-jobs and target-profit payload,
so this is an explicit user-selected presentation: it deliberately exports no
structural certificate or automatic-presentation admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace JobSequencing

open Encoding
open ComplexityReduction.Combinatorics

/-- The ordered unary layout of one Job Sequencing job. -/
def jobShape : CodecShape :=
  .prod .unaryNat (.prod .unaryNat .unaryNat)

/-- The complete ordered layout of jobs and target profit in a structured Job Sequencing input. -/
def structuredShape : CodecShape :=
  .prod (.list jobShape) .unaryNat

/--
The exact lawful V2 presentation of CR's structured Job Sequencing encoder.

The carrier is the custom `JobSequencingInput` wrapper rather than the nested
product denoted by `structuredShape`; faithful encoding evidence therefore
does not make this an automatically selectable structural presentation.
-/
def structuredPresentation : LawfulEncodedType where
  encodedType := jobSequencingStructuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨jobSequencingStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's structured Job Sequencing encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = jobSequencingStructuredEncodedType :=
  rfl

/-- The representation identity records every job field and the target-profit field. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The presentation carrier is exactly CR's Job Sequencing wrapper syntax. -/
theorem structuredPresentation_carrier_eq_JobSequencingInput :
    structuredPresentation.Carrier = JobSequencingInput :=
  rfl

/-- The only encoder exposed by this presentation is CR's established structured encoder. -/
@[simp]
theorem structuredPresentation_encode (input : structuredPresentation.Carrier) :
    structuredPresentation.encode input = jobSequencingStructuredEncodedType.encode input :=
  rfl

/-- The existing Job Sequencing predicate at its exact lawful V2 presentation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := JobSequencing

/-- The canonical V2 endpoint for CR's structured Karp21 Job Sequencing problem. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

/-- The endpoint is indexed by the exact selected Job Sequencing presentation. -/
@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

/-- The endpoint retains the complete ordered Job Sequencing representation identity. -/
@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = structuredShape.identity :=
  rfl

/-- The compatibility backend endpoint is exactly CR's direct-TM target endpoint. -/
@[simp]
theorem structuredProblem_backendEndpoint_eq_legacy :
    structuredProblem.backendEndpoint = jobSequencingStructuredDecisionProblem :=
  rfl

/-- The presented predicate is definitionally CR's Job Sequencing semantics. -/
@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ JobSequencing input :=
  Iff.rfl

/-- The typed endpoint accepts exactly the existing Job Sequencing instances. -/
@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ JobSequencing input :=
  Iff.rfl

end JobSequencing
end Presentation
end ComplexityReduction
