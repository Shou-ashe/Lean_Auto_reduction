/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.MaxCut.StructuredTM.Assembly
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem

/-!
Canonical V2 presentation of the exact structured Partition endpoint used by
`MaxCut.partitionToMaxCutStructuredTMKarpReduction`.

`PartitionInput` is a custom one-field wrapper around a list of unary natural
weights.  Its selected legacy encoder is therefore the structured
finite-alphabet encoder, not the raw or binary-numeric variants.  The payload
layout is recorded completely, while the wrapper remains an explicit,
user-selected presentation: this file intentionally exports no structural
certificate or automatic-presentation admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace Partition

open Encoding
open ComplexityReduction.Combinatorics

/-- The complete unary-weight-list layout of a structured Partition input. -/
def structuredShape : CodecShape :=
  .list .unaryNat

/--
The exact lawful V2 presentation of the source endpoint of CR's direct
structured Partition-to-MaxCut TM reduction.

The carrier is a custom wrapper rather than the list denoted by
`structuredShape`; faithful encoding evidence consequently does not make this
an automatically selectable structural presentation.
-/
def structuredPresentation : LawfulEncodedType where
  encodedType := partitionStructuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨partitionStructuredEncodedType_encode_injective⟩

/-- The presentation exposes exactly CR's direct-TM source encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = partitionStructuredEncodedType :=
  rfl

/-- The representation identity records the full ordered unary weight-list layout. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The presentation carrier is exactly CR's `PartitionInput` wrapper syntax. -/
theorem structuredPresentation_carrier_eq_PartitionInput :
    structuredPresentation.Carrier = PartitionInput :=
  rfl

/-- The only encoder exposed by this presentation is CR's established structured encoder. -/
@[simp]
theorem structuredPresentation_encode (input : structuredPresentation.Carrier) :
    structuredPresentation.encode input = partitionStructuredEncodedType.encode input :=
  rfl

/-- The existing Partition predicate at its exact lawful V2 presentation. -/
def structuredProblemAt : ProblemAt structuredPresentation where
  isYes := Partition

/-- The canonical V2 endpoint for the source of CR's structured Partition-to-MaxCut route. -/
@[complexity_reduction_ir_typed_problem]
def structuredProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation structuredProblemAt

/-- The endpoint is indexed by the exact selected Partition presentation. -/
@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

/-- The endpoint retains the complete unary-weight-list representation identity. -/
@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = structuredShape.identity :=
  rfl

/-- The compatibility backend endpoint is exactly the source endpoint of CR's direct TM route. -/
@[simp]
theorem structuredProblem_backendEndpoint_eq_legacy :
    structuredProblem.backendEndpoint = partitionStructuredDecisionProblem :=
  rfl

/-- The presented predicate is definitionally CR's Partition semantics. -/
@[simp]
theorem structuredProblemAt_isYes (input : structuredPresentation.Carrier) :
    structuredProblemAt.isYes input ↔ Partition input :=
  Iff.rfl

/-- The typed endpoint accepts exactly the existing Partition instances. -/
@[simp]
theorem structuredProblem_accepts (input : structuredProblem.Instance) :
    structuredProblem.accepts input ↔ Partition input :=
  Iff.rfl

end Partition
end Presentation
end ComplexityReduction
