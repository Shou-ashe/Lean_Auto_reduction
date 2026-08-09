/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition.StructuredTM.UnaryToBinary
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Presentation.Partition

/-!
Canonical V2 presentation of CR's binary-numeric structured Partition endpoint.

`Partition.partitionStructuredToBinaryStructuredTMKarpReduction` targets
`partitionBinaryStructuredDecisionProblem`.  Although its carrier is the same
`PartitionInput` wrapper as the unary structured presentation, its list
elements use the binary-natural codec.  The explicit binary shape therefore
has a different representation identity.  As with the unary wrapper, this
presentation is user-locked: no structural certificate or automatic-admission
evidence is exported.
-/

namespace ComplexityReduction
namespace Presentation
namespace PartitionBinary

open Encoding
open ComplexityReduction.Combinatorics

/-- The complete binary-natural weight-list layout of a structured Partition input. -/
def structuredShape : CodecShape :=
  .list .binaryNat

/--
The exact lawful V2 presentation of CR's binary-numeric structured Partition
encoder.  `PartitionInput` remains a custom wrapper rather than the list
carrier denoted by `structuredShape`, so its faithfulness evidence does not
admit automatic structural selection.
-/
def structuredPresentation : LawfulEncodedType where
  encodedType := partitionBinaryStructuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨partitionBinaryStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's binary structured Partition encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = partitionBinaryStructuredEncodedType :=
  rfl

/-- The representation identity records the ordered binary-natural weight-list layout. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The binary structured presentation has the established Partition wrapper carrier. -/
theorem structuredPresentation_carrier_eq_PartitionInput :
    structuredPresentation.Carrier = PartitionInput :=
  rfl

/-- The only encoder exposed by this presentation is CR's binary structured encoder. -/
@[simp]
theorem structuredPresentation_encode (input : structuredPresentation.Carrier) :
    structuredPresentation.encode input = partitionBinaryStructuredEncodedType.encode input :=
  rfl

/-- Binary and unary Partition presentations retain distinct full representation identities. -/
theorem structuredPresentation_representation_ne_unary :
    structuredPresentation.representation ≠ Partition.structuredPresentation.representation := by
  rw [structuredPresentation_representation, Partition.structuredPresentation_representation]
  exact CodecShape.identity_ne_of_shape_ne (by decide)

/-- The existing Partition predicate at CR's exact binary structured presentation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := Partition

/-- The canonical V2 endpoint for CR's binary-numeric structured Partition problem. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

/-- The endpoint is indexed by the exact selected binary Partition presentation. -/
@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

/-- The endpoint retains the full binary-natural weight-list representation identity. -/
@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = structuredShape.identity :=
  rfl

/-- The compatibility backend endpoint is exactly CR's binary structured Partition endpoint. -/
@[simp]
theorem structuredProblem_backendEndpoint_eq_legacy :
    structuredProblem.backendEndpoint = partitionBinaryStructuredDecisionProblem :=
  rfl

/-- The presented fixed-representation predicate is definitionally CR's Partition semantics. -/
@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ Partition input :=
  Iff.rfl

/-- The typed binary endpoint accepts exactly the existing Partition instances. -/
@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ Partition input :=
  Iff.rfl

end PartitionBinary
end Presentation
end ComplexityReduction
