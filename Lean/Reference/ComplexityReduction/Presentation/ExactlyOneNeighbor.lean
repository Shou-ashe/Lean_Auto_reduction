/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Presentation.Graph
import ComplexityReduction.Legacy.IR.Domains.Graph.Combinatorics.ExactlyOneNeighbor

/-!
The exact V2 presentation of the legacy existential-witness
Exactly-One-Neighbor problem.

This endpoint accepts an `ExactlyOneNeighborInput` exactly when an existential
list witness satisfies the legacy EON predicate. It is intentionally distinct
from the fixed-role `Presentation.RoleGraph` endpoint: that endpoint consumes
an erased role graph and reads selectable-role data from the input relation.
No identity egress, executable adapter, primitive, TM, or certificate is
declared here.
-/

namespace ComplexityReduction
namespace Presentation
namespace ExactlyOneNeighbor

open Encoding

/-- The complete layout identity of a graph plus its required-vertex witness interface. -/
def structuredShape : CodecShape :=
  .prod Graph.structuredShape (.list .unaryNat)

/--
The exact faithful structured presentation of `ExactlyOneNeighborInput`.

The carrier is a custom wrapper around the graph/list payload, so injectivity
does not manufacture structural automatic-presentation admission.
-/
def structuredPresentation : LawfulEncodedType where
  encodedType := _root_.ComplexityReduction.exactlyOneNeighborStructuredEncodedType
  representation := structuredShape.identity
  faithful := ⟨_root_.ComplexityReduction.exactlyOneNeighborStructuredEncodedType_encode_injective⟩

@[simp] theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType =
      _root_.ComplexityReduction.exactlyOneNeighborStructuredEncodedType :=
  rfl

@[simp] theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The presentation carrier is exactly the legacy existential EON input type. -/
theorem structuredPresentation_carrier_eq_ExactlyOneNeighborInput :
    structuredPresentation.Carrier = _root_.ComplexityReduction.ExactlyOneNeighborInput :=
  rfl

/-- The exact EON semantic predicate at this particular lawful presentation. -/
def problemAt : ProblemAt structuredPresentation where
  isYes := _root_.ComplexityReduction.ExactlyOneNeighborYes

/-- The canonical V2 endpoint for existential-witness Exactly-One-Neighbor. -/
@[complexity_reduction_ir_typed_problem]
def presentedProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt structuredPresentation problemAt

@[simp] theorem presentedProblem_representation :
    presentedProblem.representation = structuredPresentation :=
  rfl

@[simp] theorem presentedProblem_backendEndpoint_instance :
    presentedProblem.backendEndpoint.Instance =
      _root_.ComplexityReduction.exactlyOneNeighborStructuredEncodedType :=
  rfl

@[simp] theorem presentedProblem_representationIdentity :
    presentedProblem.representationIdentity = structuredShape.identity :=
  rfl

/-- The V2 endpoint exposes the original existential witness-list predicate verbatim. -/
@[simp] theorem presentedProblem_accepts (input : presentedProblem.Instance) :
    presentedProblem.accepts input ↔
      ∃ witness : List Nat,
        _root_.ComplexityReduction.ExactlyOneNeighborWitness input witness :=
  Iff.rfl

/-- The presented endpoint's predicate is exactly `ExactlyOneNeighborYes`, not a fixed-role predicate. -/
@[simp] theorem presentedProblem_accepts_legacy (input : presentedProblem.Instance) :
    presentedProblem.accepts input ↔ _root_.ComplexityReduction.ExactlyOneNeighborYes input :=
  Iff.rfl

end ExactlyOneNeighbor
end Presentation
end ComplexityReduction
