/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core.EncodedType
import ComplexityReduction.Encoding.CodecShape
import ComplexityReduction.Encoding.CodecLayoutIso

/-!
Canonical V2 lawful encoded representations.

`LawfulEncodedType` records a faithfully encoded, explicitly identified
representation. It intentionally does *not* make an injective encoding
eligible for automatic selection: that stronger admission is expressed by the
separate, closed `StructuralRepresentationCertificate` below. In particular,
a bare injectivity proof or arbitrary equivalence cannot manufacture a
structural presentation certificate.
-/

namespace ComplexityReduction
namespace Encoding

/-- Faithfulness of one concrete finite-alphabet encoding. -/
structure FaithfulEncoding (encodedType : ComplexityReduction.EncodedType) : Prop where
  encode_injective : Function.Injective encodedType.encode

namespace FaithfulEncoding

/--
The legacy raw encoding is faithful precisely at subsingleton carriers.

This is the only circumstance in which its always-empty encoder can
be used as faithful representation data.  It does not make arbitrary raw
encodings structurally eligible; that additional admission remains closed in
`StructuralRepresentationOrigin` below.
-/
theorem raw_encode_injective_iff_subsingleton (α : Type) :
    Function.Injective (ComplexityReduction.EncodedType.raw α).encode ↔ Subsingleton α := by
  constructor
  · intro encodeInjective
    constructor
    intro left right
    apply encodeInjective
    rfl
  · intro carrierSubsingleton left right _
    exact carrierSubsingleton.elim left right

/-- A raw encoding on a nontrivial carrier cannot pass the V2 faithfulness gate. -/
theorem raw_not_faithful_of_nontrivial (α : Type) [Nontrivial α] :
    ¬ FaithfulEncoding (ComplexityReduction.EncodedType.raw α) := by
  intro faithful
  have carrierSubsingleton : Subsingleton α :=
    (raw_encode_injective_iff_subsingleton α).mp faithful.encode_injective
  exact not_subsingleton α carrierSubsingleton

/-- Build raw faithfulness only after explicitly establishing a subsingleton carrier. -/
def rawOfSubsingleton (α : Type) [Subsingleton α] :
    FaithfulEncoding (ComplexityReduction.EncodedType.raw α) :=
  ⟨raw_encode_injective_iff_subsingleton α |>.mpr inferInstance⟩

end FaithfulEncoding

/--
Closed origins for representations which may be selected structurally.

Every constructor fixes both the existing `EncodedType` implementation and
the complete `CodecShape.Identity`. This deliberately has no constructor for
an arbitrary encoder, carrier equivalence, or injectivity proof.
-/
inductive StructuralRepresentationOrigin :
    (encodedType : ComplexityReduction.EncodedType) → CodecShape.Identity → Prop where
  | unit :
      StructuralRepresentationOrigin (ComplexityReduction.EncodedType.raw Unit)
        CodecShape.unit.identity
  | bool :
      StructuralRepresentationOrigin ComplexityReduction.EncodedType.bool CodecShape.bool.identity
  | unaryNat :
      StructuralRepresentationOrigin ComplexityReduction.EncodedType.nat CodecShape.unaryNat.identity
  | binaryNat :
      StructuralRepresentationOrigin ComplexityReduction.EncodedType.binaryNat
        CodecShape.binaryNat.identity
  | prod {left right : ComplexityReduction.EncodedType}
      {leftRepresentation rightRepresentation : CodecShape.Identity} :
      StructuralRepresentationOrigin left leftRepresentation →
      StructuralRepresentationOrigin right rightRepresentation →
      StructuralRepresentationOrigin (ComplexityReduction.EncodedType.prod left right)
        (CodecShape.prod leftRepresentation.toShape rightRepresentation.toShape).identity
  | sum {left right : ComplexityReduction.EncodedType}
      {leftRepresentation rightRepresentation : CodecShape.Identity} :
      StructuralRepresentationOrigin left leftRepresentation →
      StructuralRepresentationOrigin right rightRepresentation →
      StructuralRepresentationOrigin (ComplexityReduction.EncodedType.sum left right)
        (CodecShape.sum leftRepresentation.toShape rightRepresentation.toShape).identity
  | list {element : ComplexityReduction.EncodedType} {elementRepresentation : CodecShape.Identity} :
      StructuralRepresentationOrigin element elementRepresentation →
      StructuralRepresentationOrigin (ComplexityReduction.EncodedType.list element)
        (CodecShape.list elementRepresentation.toShape).identity

/--
Structural evidence for one concrete automatically selectable representation.

Both the actual `EncodedType` and its `CodecShape.Identity` are indices of the
certificate. Its closed origin prevents a bare faithful encoding from being
promoted to a structural presentation.
-/
structure StructuralRepresentationCertificate
    (encodedType : ComplexityReduction.EncodedType)
    (representation : CodecShape.Identity) : Prop where
  origin : StructuralRepresentationOrigin encodedType representation
  faithful : FaithfulEncoding encodedType

namespace StructuralRepresentationCertificate

/-- Every structural certificate contains faithful encoding evidence. -/
theorem encode_injective {encodedType : ComplexityReduction.EncodedType}
    {representation : CodecShape.Identity}
    (certificate : StructuralRepresentationCertificate encodedType representation) :
    Function.Injective encodedType.encode :=
  certificate.faithful.encode_injective

end StructuralRepresentationCertificate

namespace StructuralRepresentationOrigin

/--
Recover existence of the canonical audited layout witness from a closed structural origin.

The result is deliberately indexed by the *same* complete representation
identity at both ends.  Atomic origins expose only their identity layout,
while compound origins recurse through the corresponding audited product,
sum, or list layout constructor.  There is no parameter accepting a carrier
equivalence, so an arbitrary `Equiv` cannot manufacture this witness.
-/
theorem structuralLayoutWitness
    {encodedType : ComplexityReduction.EncodedType}
    {representation : CodecShape.Identity} :
    StructuralRepresentationOrigin encodedType representation →
      Nonempty (CodecLayoutIso representation representation)
  | .unit => ⟨CodecLayoutIso.refl CodecShape.unit.identity⟩
  | .bool => ⟨CodecLayoutIso.refl CodecShape.bool.identity⟩
  | .unaryNat => ⟨CodecLayoutIso.refl CodecShape.unaryNat.identity⟩
  | .binaryNat => ⟨CodecLayoutIso.refl CodecShape.binaryNat.identity⟩
  | .prod left right => by
      rcases left.structuralLayoutWitness with ⟨leftLayout⟩
      rcases right.structuralLayoutWitness with ⟨rightLayout⟩
      exact ⟨CodecLayoutIso.prod leftLayout rightLayout⟩
  | .sum left right => by
      rcases left.structuralLayoutWitness with ⟨leftLayout⟩
      rcases right.structuralLayoutWitness with ⟨rightLayout⟩
      exact ⟨CodecLayoutIso.sum leftLayout rightLayout⟩
  | .list element => by
      rcases element.structuralLayoutWitness with ⟨elementLayout⟩
      exact ⟨CodecLayoutIso.list elementLayout⟩

/-- The source endpoint of an origin-derived layout is its exact representation index. -/
@[simp]
theorem structuralLayoutWitness_source
    {encodedType : ComplexityReduction.EncodedType}
    {representation : CodecShape.Identity}
    (origin : StructuralRepresentationOrigin encodedType representation) :
    ∀ layout : CodecLayoutIso representation representation,
      layout.endpointIdentities.source = representation := by
  have _witness := origin.structuralLayoutWitness
  intro layout
  rfl

/-- The target endpoint of an origin-derived layout is its exact representation index. -/
@[simp]
theorem structuralLayoutWitness_target
    {encodedType : ComplexityReduction.EncodedType}
    {representation : CodecShape.Identity}
    (origin : StructuralRepresentationOrigin encodedType representation) :
    ∀ layout : CodecLayoutIso representation representation,
      layout.endpointIdentities.target = representation := by
  have _witness := origin.structuralLayoutWitness
  intro layout
  rfl

/--
The complete endpoint pair of an origin-derived layout is fixed by the
certificate's representation index, not merely by the denoted Lean carrier.
-/
@[simp]
theorem structuralLayoutWitness_endpointIdentities
    {encodedType : ComplexityReduction.EncodedType}
    {representation : CodecShape.Identity}
    (origin : StructuralRepresentationOrigin encodedType representation) :
    ∀ layout : CodecLayoutIso representation representation,
      layout.endpointIdentities = ⟨representation, representation⟩ := by
  have _witness := origin.structuralLayoutWitness
  intro layout
  rfl

end StructuralRepresentationOrigin

namespace StructuralRepresentationCertificate

/--
The audited structural layout retained by a structural certificate.

It is derived solely from the certificate's closed origin.  In particular,
this API has no constructor or argument through which a bare `Equiv` can be
promoted to a presentation-layout witness.
-/
theorem structuralLayoutWitness {encodedType : ComplexityReduction.EncodedType}
    {representation : CodecShape.Identity}
    (certificate : StructuralRepresentationCertificate encodedType representation) :
    Nonempty (CodecLayoutIso representation representation) :=
  certificate.origin.structuralLayoutWitness

/-- A certificate-derived layout has the exact representation identity at its source endpoint. -/
@[simp]
theorem structuralLayoutWitness_source {encodedType : ComplexityReduction.EncodedType}
    {representation : CodecShape.Identity}
    (certificate : StructuralRepresentationCertificate encodedType representation) :
    ∀ layout : CodecLayoutIso representation representation,
      layout.endpointIdentities.source = representation := by
  have _witness := certificate.structuralLayoutWitness
  intro layout
  rfl

/-- A certificate-derived layout has the exact representation identity at its target endpoint. -/
@[simp]
theorem structuralLayoutWitness_target {encodedType : ComplexityReduction.EncodedType}
    {representation : CodecShape.Identity}
    (certificate : StructuralRepresentationCertificate encodedType representation) :
    ∀ layout : CodecLayoutIso representation representation,
      layout.endpointIdentities.target = representation := by
  have _witness := certificate.structuralLayoutWitness
  intro layout
  rfl

/--
Certificate-layout coherence: both layout endpoints are exactly the complete
representation identity already indexed by the certificate.
-/
@[simp]
theorem structuralLayoutWitness_endpointIdentities {encodedType : ComplexityReduction.EncodedType}
    {representation : CodecShape.Identity}
    (certificate : StructuralRepresentationCertificate encodedType representation) :
    ∀ layout : CodecLayoutIso representation representation,
      layout.endpointIdentities = ⟨representation, representation⟩ := by
  have _witness := certificate.structuralLayoutWitness
  intro layout
  rfl

end StructuralRepresentationCertificate

/--
A lawful V2 representation, carrying the exact encoding and its explicit
structural representation identity together with faithful encoding evidence.

This is representation data only. It has no program, semantic theorem,
structural-admission certificate, certificate algebra, trusted capability,
cost evidence, or TM evidence.
-/
structure LawfulEncodedType where
  encodedType : ComplexityReduction.EncodedType
  representation : CodecShape.Identity
  faithful : FaithfulEncoding encodedType

/--
The canonical identity of a lawful representation.

`CodecShape.Identity` remains only the structural-layout component.  This
identity additionally retains the entire concrete `EncodedType`, including
its carrier, alphabet, and encoder, so two faithful encoders cannot acquire
the same representation identity merely by declaring the same shape.
-/
structure EncoderBoundIdentity where
  codec : ComplexityReduction.EncodedType
  structuralIdentity : CodecShape.Identity

namespace EncoderBoundIdentity

/-- Equality of encoder-bound identities preserves their complete concrete codecs. -/
theorem codec_eq_of_eq {left right : EncoderBoundIdentity} (equality : left = right) :
    left.codec = right.codec :=
  congrArg EncoderBoundIdentity.codec equality

/-- Equality of encoder-bound identities preserves their structural-layout components. -/
theorem structuralIdentity_eq_of_eq {left right : EncoderBoundIdentity} (equality : left = right) :
    left.structuralIdentity = right.structuralIdentity :=
  congrArg EncoderBoundIdentity.structuralIdentity equality

/-- Two encoder-bound identities are equal exactly when both of their components are equal. -/
theorem eq_iff (left right : EncoderBoundIdentity) :
    left = right ↔ left.codec = right.codec ∧
      left.structuralIdentity = right.structuralIdentity := by
  constructor
  · intro equality
    exact ⟨codec_eq_of_eq equality, structuralIdentity_eq_of_eq equality⟩
  · rintro ⟨codecEquality, structuralIdentityEquality⟩
    cases left
    cases right
    cases codecEquality
    cases structuralIdentityEquality
    rfl

end EncoderBoundIdentity

namespace StructuralRepresentationCertificate

/--
Reconstruct the uniquely indexed lawful presentation admitted by a structural certificate.

The encoded type and representation identity are parameters of the certificate itself, so this
operation cannot silently substitute a different encoder, including one on the same carrier.
-/
def toLawfulEncodedType {encodedType : ComplexityReduction.EncodedType}
    {representation : CodecShape.Identity}
    (certificate : StructuralRepresentationCertificate encodedType representation) : LawfulEncodedType where
  encodedType := encodedType
  representation := representation
  faithful := certificate.faithful

@[simp]
theorem toLawfulEncodedType_encodedType {encodedType : ComplexityReduction.EncodedType}
    {representation : CodecShape.Identity}
    (certificate : StructuralRepresentationCertificate encodedType representation) :
    certificate.toLawfulEncodedType.encodedType = encodedType :=
  rfl

@[simp]
theorem toLawfulEncodedType_representation {encodedType : ComplexityReduction.EncodedType}
    {representation : CodecShape.Identity}
    (certificate : StructuralRepresentationCertificate encodedType representation) :
    certificate.toLawfulEncodedType.representation = representation :=
  rfl

/--
Two structural admissions can reconstruct the same lawful presentation only when their complete
representation identities agree.  This prevents a same-carrier equality (for example, the
unary and base-two `Nat` carriers) from silently identifying two codecs.
-/
theorem representation_eq_of_toLawfulEncodedType_eq
    {leftEncodedType rightEncodedType : ComplexityReduction.EncodedType}
    {leftRepresentation rightRepresentation : CodecShape.Identity}
    (left : StructuralRepresentationCertificate leftEncodedType leftRepresentation)
    (right : StructuralRepresentationCertificate rightEncodedType rightRepresentation)
    (presentationEquality : left.toLawfulEncodedType = right.toLawfulEncodedType) :
    leftRepresentation = rightRepresentation := by
  simpa only [toLawfulEncodedType_representation] using
    congrArg LawfulEncodedType.representation presentationEquality

/--
Reconstruction from closed structural certificates is coherent exactly at its
two presentation indices.  In particular, certificates for one concrete
encoding cannot be reused as a lawful presentation at a different codec
identity, even when both codec shapes denote the same Lean carrier.

The reverse implication uses no information beyond equality of the indices:
the remaining field is faithful-encoding evidence in `Prop`.  Thus this
theorem rules out cross-indexing at the representation boundary rather than
merely observing equality of the underlying carrier types.
-/
theorem toLawfulEncodedType_eq_iff_indices_eq
    {leftEncodedType rightEncodedType : ComplexityReduction.EncodedType}
    {leftRepresentation rightRepresentation : CodecShape.Identity}
    (left : StructuralRepresentationCertificate leftEncodedType leftRepresentation)
    (right : StructuralRepresentationCertificate rightEncodedType rightRepresentation) :
    left.toLawfulEncodedType = right.toLawfulEncodedType ↔
      leftEncodedType = rightEncodedType ∧ leftRepresentation = rightRepresentation := by
  constructor
  · intro presentationEquality
    constructor
    · simpa only [toLawfulEncodedType_encodedType] using
        congrArg LawfulEncodedType.encodedType presentationEquality
    · exact left.representation_eq_of_toLawfulEncodedType_eq right presentationEquality
  · rintro ⟨encodedTypeEquality, representationEquality⟩
    cases encodedTypeEquality
    cases representationEquality
    rfl

end StructuralRepresentationCertificate

namespace LawfulEncodedType

/--
Mechanically recover the canonical encoder-bound identity of a lawful
representation.  No caller supplies either component independently.
-/
def encoderBoundIdentity (presentation : LawfulEncodedType) : EncoderBoundIdentity where
  codec := presentation.encodedType
  structuralIdentity := presentation.representation

/-- The codec component of a lawful presentation's identity is its exact wrapped codec. -/
@[simp]
theorem encoderBoundIdentity_codec (presentation : LawfulEncodedType) :
    presentation.encoderBoundIdentity.codec = presentation.encodedType :=
  rfl

/-- The structural component of a lawful presentation's identity is its exact shape identity. -/
@[simp]
theorem encoderBoundIdentity_structuralIdentity (presentation : LawfulEncodedType) :
    presentation.encoderBoundIdentity.structuralIdentity = presentation.representation :=
  rfl

/--
An equality of identities supplies equality of both complete codecs and
structural layout identities; equality of carriers alone is intentionally not
among its consequences or hypotheses.
-/
theorem encoderBoundIdentity_eq_iff (left right : LawfulEncodedType) :
    left.encoderBoundIdentity = right.encoderBoundIdentity ↔
      left.encodedType = right.encodedType ∧ left.representation = right.representation :=
  EncoderBoundIdentity.eq_iff _ _

/-- The represented carrier is determined by the wrapped concrete encoding. -/
abbrev Carrier (presentation : LawfulEncodedType) : Type :=
  presentation.encodedType.Carrier

/-- The only encoder exposed by a lawful representation is its wrapped encoder. -/
def encode (presentation : LawfulEncodedType) : presentation.Carrier →
    List presentation.encodedType.Symbol :=
  presentation.encodedType.encode

/-- The only input-size measure available to V2 code is the wrapped encoder length. -/
def inputSize (presentation : LawfulEncodedType) (input : presentation.Carrier) : Nat :=
  presentation.encodedType.inputSize input

@[simp]
theorem inputSize_eq_encode_length (presentation : LawfulEncodedType)
    (input : presentation.Carrier) :
    presentation.inputSize input = (presentation.encode input).length :=
  rfl

/-- Faithfulness entails injectivity of the very same wrapped encoder. -/
theorem encode_injective (presentation : LawfulEncodedType) :
    Function.Injective presentation.encode :=
  presentation.faithful.encode_injective

/-- A V2 encoded word determines its represented input exactly. -/
theorem encode_eq_iff (presentation : LawfulEncodedType)
    (left right : presentation.Carrier) :
    presentation.encode left = presentation.encode right ↔ left = right := by
  constructor
  · intro equality
    exact presentation.encode_injective equality
  · intro equality
    cases equality
    rfl

/-- Recover the exact representation identity bound to this lawful encoding. -/
def representationIdentity (presentation : LawfulEncodedType) : CodecShape.Identity :=
  presentation.representation

theorem representationIdentity_eq_representation (presentation : LawfulEncodedType) :
    presentation.representationIdentity = presentation.representation :=
  rfl

/-- The structural certificate required before automatic presentation selection. -/
abbrev StructuralCertificate (presentation : LawfulEncodedType) : Prop :=
  StructuralRepresentationCertificate presentation.encodedType presentation.representation

/--
Bind a closed structural origin to this exact lawful presentation.

The faithfulness witness is copied from `presentation`, rather than accepted as an unrelated
argument.  Thus every automatic-presentation certificate contains evidence for exactly the
wrapped `EncodedType` and its representation identity.
-/
def structuralCertificateOfOrigin (presentation : LawfulEncodedType)
    (origin : StructuralRepresentationOrigin presentation.encodedType presentation.representation) :
    presentation.StructuralCertificate where
  origin := origin
  faithful := presentation.faithful

/-- A certificate at a presentation carries the presentation's faithful encoding evidence. -/
theorem structuralCertificate_faithful_eq (presentation : LawfulEncodedType)
    (certificate : presentation.StructuralCertificate) : certificate.faithful = presentation.faithful :=
  Subsingleton.elim _ _

/-- A structural certificate reconstructs precisely the presentation at which it was supplied. -/
theorem structuralCertificate_toLawfulEncodedType_eq (presentation : LawfulEncodedType)
    (certificate : presentation.StructuralCertificate) :
    certificate.toLawfulEncodedType = presentation := by
  cases presentation
  simp only [StructuralRepresentationCertificate.toLawfulEncodedType]

end LawfulEncodedType

namespace StructuralRepresentationCertificate

/--
The closed-origin layout witness is coherent with the reconstructed lawful
presentation: both of its exact endpoints are the presentation's complete
representation identity.  Thus a certificate for one codec cannot have its
layout witness silently reused at a same-carrier codec with another identity.
-/
@[simp]
theorem structuralLayoutWitness_toLawfulEncodedType_representationIdentity
    {encodedType : ComplexityReduction.EncodedType}
    {representation : CodecShape.Identity}
    (certificate : StructuralRepresentationCertificate encodedType representation) :
    ∀ layout : CodecLayoutIso representation representation,
      layout.endpointIdentities =
        ⟨certificate.toLawfulEncodedType.representationIdentity,
          certificate.toLawfulEncodedType.representationIdentity⟩ := by
  have _witness := certificate.structuralLayoutWitness
  intro layout
  rfl

end StructuralRepresentationCertificate
end Encoding
end ComplexityReduction
