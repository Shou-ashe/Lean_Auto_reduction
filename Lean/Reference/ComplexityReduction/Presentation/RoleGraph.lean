/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Presentation.UniversalRelIR
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Legacy.IR.Views.RoleGraphView

/-!
Compatibility names for the RoleGraph identity route's erased-interchange
presentation.

The canonical encoder, faithfulness proof, representation identity, and
well-formedness presentation are owned by `Presentation.UniversalRelIR`.
These definitionally transparent aliases preserve existing RoleGraph route
endpoints without maintaining a second codec or proof implementation.
-/

namespace ComplexityReduction
namespace Presentation
namespace RoleGraph

open Encoding

/-- Compatibility name for the canonical relation-tuple encoding. -/
abbrev relationTupleEncodedType : ComplexityReduction.EncodedType :=
  UniversalRelIR.relationTupleEncodedType

/-- Compatibility name for the canonical relation-tuple-family encoding. -/
abbrev relationTupleFamilyEncodedType : ComplexityReduction.EncodedType :=
  UniversalRelIR.relationTupleFamilyEncodedType

/-- Compatibility name for the canonical relation-table encoding. -/
abbrev relationTableEncodedType : ComplexityReduction.EncodedType :=
  UniversalRelIR.relationTableEncodedType

/-- Compatibility name for the canonical finite sort-size encoding. -/
abbrev sortSizeListEncodedType : ComplexityReduction.EncodedType :=
  UniversalRelIR.sortSizeListEncodedType

/-- Compatibility name for the canonical relation-signature encoding. -/
abbrev relSigEncodedType : ComplexityReduction.EncodedType :=
  UniversalRelIR.relSigEncodedType

/-- Compatibility name for the canonical relation-signature-list encoding. -/
abbrev relSigListEncodedType : ComplexityReduction.EncodedType :=
  UniversalRelIR.relSigListEncodedType

/-- Compatibility name for the canonical UniversalRelIR payload encoding. -/
abbrev universalRelIRPayloadEncodedType : ComplexityReduction.EncodedType :=
  UniversalRelIR.payloadEncodedType

/-- Compatibility name for the canonical UniversalRelIR product encoding. -/
abbrev universalRelIRProductEncodedType : ComplexityReduction.EncodedType :=
  UniversalRelIR.productEncodedType

/-- Compatibility name for the canonical faithful erased-carrier encoding. -/
abbrev universalRelIREncodedType : ComplexityReduction.EncodedType :=
  UniversalRelIR.encodedType

/-- Faithfulness is supplied only by the canonical UniversalRelIR presentation leaf. -/
theorem universalRelIREncodedType_encode_injective :
    Function.Injective universalRelIREncodedType.encode :=
  UniversalRelIR.encodedType_encode_injective

/-- Compatibility name for the canonical explicit representation identity. -/
abbrev representationShape : CodecShape :=
  UniversalRelIR.representationShape

/-- Compatibility name for the canonical lawful UniversalRelIR representation. -/
abbrev lawfulRepresentation : LawfulEncodedType :=
  UniversalRelIR.lawfulRepresentation

/-- The RoleGraph compatibility representation is definitionally the canonical interchange one. -/
@[simp]
theorem lawfulRepresentation_eq_universalRelIR :
    lawfulRepresentation = UniversalRelIR.lawfulRepresentation :=
  rfl

/-- The compatibility representation retains the canonical custom interchange encoder. -/
@[simp]
theorem lawfulRepresentation_encodedType :
    lawfulRepresentation.encodedType = universalRelIREncodedType :=
  rfl

/-- The compatibility representation retains the complete canonical layout identity. -/
@[simp]
theorem lawfulRepresentation_representation :
    lawfulRepresentation.representation = representationShape.identity :=
  rfl

/-- Compatibility name for the canonical well-formedness endpoint predicate. -/
abbrev wellFormedProblemAt : ProblemAt lawfulRepresentation :=
  UniversalRelIR.wellFormedProblemAt

/--
The only endpoint type exposed by the RoleGraph compatibility spelling.

It is an abbreviation of `UniversalRelIR.CanonicalEndpoint`, not a new
same-carrier presentation index.  Consequently compatibility consumers can
only receive the endpoint already fixed by the canonical erased-interchange
presentation.
-/
abbrev CanonicalEndpoint : Type :=
  UniversalRelIR.CanonicalEndpoint

/--
The RoleGraph compatibility endpoint is a one-way projection of the canonical
UniversalRelIR well-formedness endpoint.
-/
def wellFormedEndpoint : CanonicalEndpoint :=
  UniversalRelIR.canonicalWellFormedEndpoint

/-- The compatibility endpoint is definitionally the canonical endpoint, not a rebuilt predicate. -/
@[simp]
theorem wellFormedEndpoint_eq_universalRelIRCanonical :
    wellFormedEndpoint = UniversalRelIR.canonicalWellFormedEndpoint :=
  rfl

/-
This family-local spelling deliberately aliases the single canonical
UniversalRelIR endpoint rather than rebuilding an encoder or representation.
Its elaborated type is the concrete `PresentedProblem` capability recognized
by the registry; the tag does not create a second codec identity.
-/
/-- Compatibility name for the canonical presented well-formedness problem. -/
@[complexity_reduction_ir_typed_problem]
abbrev wellFormedPresentedProblem : PresentedProblem :=
  UniversalRelIR.wellFormedPresentedProblem

/-- The RoleGraph endpoint is definitionally the canonical interchange endpoint. -/
@[simp]
theorem wellFormedPresentedProblem_eq_universalRelIR :
    wellFormedPresentedProblem = UniversalRelIR.wellFormedPresentedProblem :=
  rfl

/-- The RoleGraph presented endpoint projects to the one canonical endpoint value. -/
@[simp]
theorem wellFormedPresentedProblem_endpoint_eq_wellFormedEndpoint :
    wellFormedPresentedProblem.endpoint = wellFormedEndpoint :=
  rfl

/-- The endpoint retains precisely the RoleGraph compatibility representation. -/
@[simp]
theorem wellFormedPresentedProblem_representation :
    wellFormedPresentedProblem.representation = lawfulRepresentation :=
  rfl

/-- The endpoint cannot silently select a different interchange codec. -/
@[simp]
theorem wellFormedPresentedProblem_backendEndpoint_instance :
    wellFormedPresentedProblem.backendEndpoint.Instance = universalRelIREncodedType :=
  rfl

/-- The endpoint retains the full canonical representation identity. -/
@[simp]
theorem wellFormedPresentedProblem_representationIdentity :
    wellFormedPresentedProblem.representationIdentity = representationShape.identity :=
  rfl

/-- The compatibility endpoint keeps the exact representation identity of its canonical owner. -/
theorem wellFormedEndpoint_representationIdentity_exact :
    lawfulRepresentation.representationIdentity =
      UniversalRelIR.lawfulRepresentation.representationIdentity :=
  rfl

/-- RoleGraph's compatibility predicate is the canonical interchange predicate. -/
@[simp]
theorem wellFormedProblemAt_isYes (input : lawfulRepresentation.Carrier) :
    wellFormedProblemAt.isYes input ↔
      _root_.ComplexityReduction.UniversalRelIR.WellFormed input :=
  UniversalRelIR.wellFormedProblemAt_isYes input

@[simp]
theorem wellFormedPresentedProblem_accepts (input : lawfulRepresentation.Carrier) :
    wellFormedPresentedProblem.accepts input ↔
      _root_.ComplexityReduction.UniversalRelIR.WellFormed input :=
  UniversalRelIR.wellFormedPresentedProblem_accepts input

/-!
### Exactly-one-neighbour target semantics

`UniversalRelIR` remains an erased interchange carrier, so the particular
role-graph view and its two distinguished roles are semantic data recovered
from an input rather than a route-local codec or a legacy packet.  The target
below is deliberately only a `PresentedProblem`: it supplies no executable
construction, size bound, cost witness, or Turing-machine evidence.
-/

/--
The canonical RoleGraph EON predicate at the erased interchange carrier.

An accepting input is well formed and contains a role-graph view together
with two distinct well-formed roles for which the existing semantic
exactly-one-neighbour predicate holds.  In particular, the target reuses
`RoleGraphView.ExactlyOneNeighborPredicate` verbatim rather than rephrasing
the witness condition in a route-local semantic layer.
-/
def exactlyOneNeighbor (input : lawfulRepresentation.Carrier) : Prop :=
  input.WellFormed ∧
    ∃ (view : _root_.ComplexityReduction.RoleGraphView input)
      (requiredRole selectableRole : _root_.ComplexityReduction.RoleId),
      input.ObjWF view.roleSort requiredRole ∧
        input.ObjWF view.roleSort selectableRole ∧
          requiredRole ≠ selectableRole ∧
            view.ExactlyOneNeighborPredicate requiredRole selectableRole

/-- The EON predicate interpreted at the existing canonical RoleGraph representation. -/
def exactlyOneNeighborProblemAt : ProblemAt lawfulRepresentation where
  isYes := exactlyOneNeighbor

/--
The typed RoleGraph exactly-one-neighbour endpoint.  It shares the one
canonical RoleGraph representation with the well-formedness endpoint, while
remaining a distinct exact semantic endpoint.
-/
@[complexity_reduction_ir_typed_problem]
def exactlyOneNeighborPresentedProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt lawfulRepresentation exactlyOneNeighborProblemAt

/-- The EON endpoint retains exactly the canonical RoleGraph representation. -/
@[simp]
theorem exactlyOneNeighborPresentedProblem_representation :
    exactlyOneNeighborPresentedProblem.representation = lawfulRepresentation :=
  rfl

/-- The EON endpoint's backend projection cannot select a route-local codec. -/
@[simp]
theorem exactlyOneNeighborPresentedProblem_backendEndpoint_instance :
    exactlyOneNeighborPresentedProblem.backendEndpoint.Instance = universalRelIREncodedType :=
  rfl

/-- The EON endpoint retains the complete canonical interchange representation identity. -/
@[simp]
theorem exactlyOneNeighborPresentedProblem_representationIdentity :
    exactlyOneNeighborPresentedProblem.representationIdentity = representationShape.identity :=
  rfl

/-- The presentation-local EON predicate is exactly the canonical semantic predicate. -/
@[simp]
theorem exactlyOneNeighborProblemAt_isYes (input : lawfulRepresentation.Carrier) :
    exactlyOneNeighborProblemAt.isYes input ↔ exactlyOneNeighbor input :=
  Iff.rfl

/-- The typed endpoint accepts precisely the well-formed EON role-graph inputs. -/
@[simp]
theorem exactlyOneNeighborPresentedProblem_accepts
    (input : exactlyOneNeighborPresentedProblem.Instance) :
    exactlyOneNeighborPresentedProblem.accepts input ↔
      input.WellFormed ∧
        ∃ (view : _root_.ComplexityReduction.RoleGraphView input)
          (requiredRole selectableRole : _root_.ComplexityReduction.RoleId),
          input.ObjWF view.roleSort requiredRole ∧
            input.ObjWF view.roleSort selectableRole ∧
              requiredRole ≠ selectableRole ∧
                view.ExactlyOneNeighborPredicate requiredRole selectableRole :=
  Iff.rfl

/-- An EON witness is accepted by the exact typed endpoint without any route evidence. -/
theorem exactlyOneNeighborPresentedProblem_accepts_of_witness
    (input : exactlyOneNeighborPresentedProblem.Instance)
    (wellFormed : input.WellFormed)
    (view : _root_.ComplexityReduction.RoleGraphView input)
    (requiredRole selectableRole : _root_.ComplexityReduction.RoleId)
    (requiredRole_wf : input.ObjWF view.roleSort requiredRole)
    (selectableRole_wf : input.ObjWF view.roleSort selectableRole)
    (roles_distinct : requiredRole ≠ selectableRole)
    (eon : view.ExactlyOneNeighborPredicate requiredRole selectableRole) :
    exactlyOneNeighborPresentedProblem.accepts input :=
  ⟨wellFormed, view, requiredRole, selectableRole, requiredRole_wf,
    selectableRole_wf, roles_distinct, eon⟩

end RoleGraph
end Presentation
end ComplexityReduction
