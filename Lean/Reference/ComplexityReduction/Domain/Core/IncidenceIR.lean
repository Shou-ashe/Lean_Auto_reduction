/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Encoding.Core

/-!
Canonical typed incidence hub for set-family semantics.

`IncidenceIR` stores left and right cardinalities together with an ordered list
of membership pairs.  A right vertex is an index in `Fin rightSize`, not a
set value, so two different right vertices with identical neighborhoods remain
different selectable objects.  This hub is intentionally independent of the
legacy `SetSystemInput` and `ExactCoverInput` wrappers, as well as Program,
Certificate, route, registry, and erased-IR APIs.
-/

namespace ComplexityReduction
namespace Domain

open Encoding

/--
The canonical incidence carrier: left size, right size, and ordered
left/right membership pairs.  The ordered pair list deliberately retains
duplicate pair occurrences and, more importantly, right-vertex indices even
when two right vertices describe extensionally equal sets.
-/
abbrev IncidenceIR : Type := Nat × (Nat × List (Nat × Nat))

namespace IncidenceIR

/-- Construct a canonical incidence value without an intermediate set-system wrapper. -/
def mk (leftSize rightSize : Nat) (membershipPairs : List (Nat × Nat)) : IncidenceIR :=
  (leftSize, (rightSize, membershipPairs))

/-- Number of left vertices. -/
def leftSize (input : IncidenceIR) : Nat :=
  input.1

/-- Number of right vertices; each index is an independently selectable set identity. -/
def rightSize (input : IncidenceIR) : Nat :=
  input.2.1

/-- Ordered raw membership pairs, with no quotienting by right-neighborhood equality. -/
def membershipPairs (input : IncidenceIR) : List (Nat × Nat) :=
  input.2.2

@[simp] theorem mk_leftSize (leftSize rightSize : Nat) (membershipPairs : List (Nat × Nat)) :
    (mk leftSize rightSize membershipPairs).leftSize = leftSize :=
  rfl

@[simp] theorem mk_rightSize (leftSize rightSize : Nat) (membershipPairs : List (Nat × Nat)) :
    (mk leftSize rightSize membershipPairs).rightSize = rightSize :=
  rfl

@[simp] theorem mk_membershipPairs (leftSize rightSize : Nat) (membershipPairs : List (Nat × Nat)) :
    (mk leftSize rightSize membershipPairs).membershipPairs = membershipPairs :=
  rfl

/-- A left vertex with its exact incidence-hub bound. -/
abbrev LeftVertex (input : IncidenceIR) : Type :=
  Fin input.leftSize

/-- A right vertex with its exact incidence-hub bound and independent identity. -/
abbrev RightVertex (input : IncidenceIR) : Type :=
  Fin input.rightSize

/-- Typed membership between one bounded left and one bounded right vertex. -/
def Membership (input : IncidenceIR) (left : input.LeftVertex) (right : input.RightVertex) : Prop :=
  (left.val, right.val) ∈ input.membershipPairs

/--
The raw incidence table is well formed precisely when every stored pair lies
within the two declared bounds.  It deliberately imposes no extensionality or
deduplication condition on right neighborhoods.
-/
def WellFormed (input : IncidenceIR) : Prop :=
  ∀ pair ∈ input.membershipPairs,
    pair.1 < input.leftSize ∧ pair.2 < input.rightSize

/-- Recover a bounded pair from one well-formed raw membership occurrence. -/
def boundedMembershipPair (input : IncidenceIR) (wellFormed : input.WellFormed)
    (pair : Nat × Nat) (member : pair ∈ input.membershipPairs) :
    input.LeftVertex × input.RightVertex :=
  ⟨⟨pair.1, (wellFormed pair member).1⟩, ⟨pair.2, (wellFormed pair member).2⟩⟩

@[simp] theorem boundedMembershipPair_values (input : IncidenceIR) (wellFormed : input.WellFormed)
    (pair : Nat × Nat) (member : pair ∈ input.membershipPairs) :
    ((boundedMembershipPair input wellFormed pair member).1.val,
      (boundedMembershipPair input wellFormed pair member).2.val) = pair :=
  rfl

/-- Equality of right vertices is determined by their retained numeric identities. -/
theorem rightVertex_ext {input : IncidenceIR} {first second : input.RightVertex}
    (value_eq : first.val = second.val) : first = second :=
  Fin.ext value_eq

/--
Exact-cover semantics for the canonical incidence hub.

The selected collection contains bounded right vertices, not their extensionally
defined neighborhoods.  Thus duplicate-looking right sets retain different
identities, while each bounded left vertex must have exactly one selected
incident right vertex.
-/
def ExistsExactCover (input : IncidenceIR) : Prop :=
  input.WellFormed ∧
    ∃ selected : List input.RightVertex,
      selected.Nodup ∧
        ∀ left : input.LeftVertex,
          ∃! right : input.RightVertex, right ∈ selected ∧ input.Membership left right

/-- The canonical unary-natural presentation used for all finite index fields. -/
abbrev indexPresentation : LawfulEncodedType :=
  StandardInstances.unaryNat

/-- Structural admission for an incidence index uses the shared unary-natural certificate. -/
abbrev indexStructuralCertificate : indexPresentation.StructuralCertificate :=
  StandardInstances.unaryNatStructuralCertificate

/-- The ordered representation of one left/right membership pair. -/
abbrev membershipPairPresentation : LawfulEncodedType :=
  StandardInstances.prod indexPresentation indexPresentation

/-- The canonical structural certificate for one membership pair. -/
abbrev membershipPairStructuralCertificate : membershipPairPresentation.StructuralCertificate :=
  StandardInstances.prodStructuralCertificate indexPresentation indexPresentation
    indexStructuralCertificate indexStructuralCertificate

/-- The ordered representation of all raw incidence pairs. -/
abbrev membershipPairsPresentation : LawfulEncodedType :=
  StandardInstances.list membershipPairPresentation

/-- The canonical structural certificate for the ordered pair list. -/
abbrev membershipPairsStructuralCertificate : membershipPairsPresentation.StructuralCertificate :=
  StandardInstances.listStructuralCertificate membershipPairPresentation
    membershipPairStructuralCertificate

/-- The right-size/pair-list suffix of the canonical incidence representation. -/
abbrev rightPayloadPresentation : LawfulEncodedType :=
  StandardInstances.prod indexPresentation membershipPairsPresentation

/-- The canonical structural certificate for the right-size/pair-list suffix. -/
abbrev rightPayloadStructuralCertificate : rightPayloadPresentation.StructuralCertificate :=
  StandardInstances.prodStructuralCertificate indexPresentation membershipPairsPresentation
    indexStructuralCertificate membershipPairsStructuralCertificate

/--
The encoder-bound lawful representation of the canonical incidence carrier.
It is assembled only from standard unary-natural, product, and list codecs;
there is no custom wrapper codec or carrier equivalence.
-/
abbrev lawfulRepresentation : LawfulEncodedType :=
  StandardInstances.prod indexPresentation rightPayloadPresentation

/-- Structural admission for the exact full incidence representation. -/
abbrev lawfulRepresentationStructuralCertificate : lawfulRepresentation.StructuralCertificate :=
  StandardInstances.prodStructuralCertificate indexPresentation rightPayloadPresentation
    indexStructuralCertificate rightPayloadStructuralCertificate

@[simp] theorem lawfulRepresentation_carrier : lawfulRepresentation.Carrier = IncidenceIR :=
  rfl

/-- The complete incidence codec remains reconstructible from its structural certificate. -/
theorem lawfulRepresentationStructuralCertificate_presentation :
    lawfulRepresentationStructuralCertificate.toLawfulEncodedType = lawfulRepresentation :=
  LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq _ _

/-- The exact presented endpoint for canonical incidence exact cover. -/
def exactCoverProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt lawfulRepresentation ⟨ExistsExactCover⟩

/-- The endpoint's yes predicate is precisely the hub-level exact-cover predicate. -/
@[simp] theorem exactCoverProblem_accepts (input : IncidenceIR) :
    exactCoverProblem.accepts input ↔ input.ExistsExactCover :=
  Iff.rfl

/-- The canonical endpoint indexed by the full incidence lawful representation. -/
def exactCoverEndpoint : PresentedProblem.EndpointAt lawfulRepresentation :=
  exactCoverProblem.endpoint

/-- The endpoint exposes the complete encoder-bound codec identity, not a carrier-only identity. -/
@[simp] theorem exactCoverEndpoint_encoderBoundIdentity :
    PresentedProblem.endpointEncoderBoundIdentity exactCoverEndpoint =
      lawfulRepresentation.encoderBoundIdentity :=
  rfl

/-- Automatic presentation selection is justified by the exact composed structural certificate. -/
def exactCoverAutomaticAdmission : PresentedProblem.AutomaticPresentationAdmission exactCoverProblem :=
  PresentedProblem.automaticAdmissionOfStructural lawfulRepresentationStructuralCertificate

end IncidenceIR
end Domain
end ComplexityReduction
