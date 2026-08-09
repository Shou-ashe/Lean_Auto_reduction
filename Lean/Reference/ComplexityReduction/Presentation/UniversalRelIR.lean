/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core.EncodedType
import ComplexityReduction.Legacy.IR.Core.Basic
import ComplexityReduction.Encoding.PresentedProblem

/-!
Canonical lawful presentation of the erased `UniversalRelIR` interchange carrier.

The encoder below is the existing faithful structured list/product layout used
by the V2 identity smoke route.  It is intentionally explicit rather than a
raw encoding.  Because `RelSig` is a wrapper without a closed generic layout
certificate, this presentation is user-selected only and supplies no
`StructuralRepresentationCertificate` for automatic presentation selection.
-/

namespace ComplexityReduction
namespace Presentation
namespace UniversalRelIR

open Encoding

/-- Encode one relation tuple as a list of unary natural numbers. -/
abbrev relationTupleEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.EncodedType.list ComplexityReduction.EncodedType.nat

/-- Encode one relation's tuple family. -/
abbrev relationTupleFamilyEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.EncodedType.list relationTupleEncodedType

/-- Encode the complete table of relation tuple families. -/
abbrev relationTableEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.EncodedType.list relationTupleFamilyEncodedType

/-- Encode the finite sort-size list. -/
abbrev sortSizeListEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.EncodedType.list ComplexityReduction.EncodedType.nat

/-- Encode a relation signature by its executable arity field. -/
def relSigEncodedType : ComplexityReduction.EncodedType where
  Carrier := _root_.ComplexityReduction.RelSig
  Symbol := relationTupleEncodedType.Symbol
  finite_symbol := relationTupleEncodedType.finite_symbol
  encode := fun signature => relationTupleEncodedType.encode signature.arity

/-- Encode the ordered list of relation signatures. -/
abbrev relSigListEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.EncodedType.list relSigEncodedType

/-- Encode signature and tuple-table payloads as an ordered product. -/
abbrev payloadEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.EncodedType.prod relSigListEncodedType relationTableEncodedType

/-- Encode sort sizes and the complete relation payload as an ordered product. -/
abbrev productEncodedType : ComplexityReduction.EncodedType :=
  ComplexityReduction.EncodedType.prod sortSizeListEncodedType payloadEncodedType

/-- The canonical faithful structured encoding of the erased interchange carrier. -/
def encodedType : ComplexityReduction.EncodedType where
  Carrier := _root_.ComplexityReduction.UniversalRelIR
  Symbol := productEncodedType.Symbol
  finite_symbol := productEncodedType.finite_symbol
  encode := fun input =>
    productEncodedType.encode (input.sortSizes, (input.relSigs, input.relTuples))

private theorem relationTuple_encode_injective :
    Function.Injective relationTupleEncodedType.encode :=
  ComplexityReduction.EncodedType.list_encode_injective
    ComplexityReduction.EncodedType.nat_encode_injective

private theorem relationTupleFamily_encode_injective :
    Function.Injective relationTupleFamilyEncodedType.encode :=
  ComplexityReduction.EncodedType.list_encode_injective relationTuple_encode_injective

private theorem relationTable_encode_injective :
    Function.Injective relationTableEncodedType.encode :=
  ComplexityReduction.EncodedType.list_encode_injective relationTupleFamily_encode_injective

private theorem sortSizeList_encode_injective :
    Function.Injective sortSizeListEncodedType.encode :=
  ComplexityReduction.EncodedType.list_encode_injective
    ComplexityReduction.EncodedType.nat_encode_injective

private theorem relSig_encode_injective : Function.Injective relSigEncodedType.encode := by
  rintro ⟨left⟩ ⟨right⟩ equality
  change relationTupleEncodedType.encode left = relationTupleEncodedType.encode right at equality
  cases relationTuple_encode_injective equality
  rfl

private theorem relSigList_encode_injective :
    Function.Injective relSigListEncodedType.encode :=
  ComplexityReduction.EncodedType.list_encode_injective relSig_encode_injective

private theorem payload_encode_injective : Function.Injective payloadEncodedType.encode :=
  ComplexityReduction.EncodedType.prod_encode_injective
    relSigList_encode_injective relationTable_encode_injective

private theorem product_encode_injective : Function.Injective productEncodedType.encode :=
  ComplexityReduction.EncodedType.prod_encode_injective
    sortSizeList_encode_injective payload_encode_injective

/-- Faithfulness of the canonical structured interchange encoding. -/
theorem encodedType_encode_injective : Function.Injective encodedType.encode := by
  intro left right equality
  change productEncodedType.encode (left.sortSizes, (left.relSigs, left.relTuples)) =
    productEncodedType.encode (right.sortSizes, (right.relSigs, right.relTuples)) at equality
  have components := product_encode_injective equality
  cases left
  cases right
  cases components
  rfl

/-- The complete explicit representation identity of the canonical encoder. -/
def representationShape : CodecShape :=
  .prod
    (.list .unaryNat)
    (.prod
      (.list (.list .unaryNat))
      (.list (.list (.list .unaryNat))))

/-- The exact lawful V2 representation of erased UniversalRelIR interchange data. -/
def lawfulRepresentation : LawfulEncodedType where
  encodedType := encodedType
  representation := representationShape.identity
  faithful := ⟨encodedType_encode_injective⟩

/--
The V2 owner records the pre-existing architectural status of this carrier:
it is an erased/interchange backend rather than an authoring representation
for a fresh route family.
-/
abbrev architectureRole : _root_.ComplexityReduction.UniversalRelIR.ArchitectureRole :=
  _root_.ComplexityReduction.UniversalRelIR.architectureRole

/-- The canonical presentation leaf preserves the erased-backend role of its carrier. -/
theorem architectureRole_is_erasedInterchange :
    architectureRole = .erasedInterchange :=
  _root_.ComplexityReduction.UniversalRelIR.architectureRole_is_erasedInterchange

/--
Any presentation carrying this exact encoder and this exact representation
identity is the one canonical erased-interchange presentation.  The
faithfulness field is propositional, so it cannot create a competing
presentation once the typed representation data agree.
-/
theorem lawfulRepresentation_unique (candidate : LawfulEncodedType)
    (encodedType_eq : candidate.encodedType = encodedType)
    (representation_eq : candidate.representation = representationShape.identity) :
    candidate = lawfulRepresentation := by
  cases candidate with
  | mk candidateEncodedType candidateRepresentation candidateFaithful =>
      cases encodedType_eq
      cases representation_eq
      rfl

/-- The lawful presentation retains exactly this leaf's custom interchange encoded type. -/
@[simp]
theorem lawfulRepresentation_encodedType : lawfulRepresentation.encodedType = encodedType :=
  rfl

/-- The lawful presentation retains the complete explicit custom layout identity. -/
@[simp]
theorem lawfulRepresentation_representation :
    lawfulRepresentation.representation = representationShape.identity :=
  rfl

/-- The carrier of the lawful presentation is exactly the erased interchange carrier. -/
theorem lawfulRepresentation_carrier_eq_universalRelIR :
    lawfulRepresentation.Carrier = _root_.ComplexityReduction.UniversalRelIR :=
  rfl

/-- The only encoder exposed by this presentation is the canonical custom interchange encoder. -/
@[simp]
theorem lawfulRepresentation_encode (input : lawfulRepresentation.Carrier) :
    lawfulRepresentation.encode input = encodedType.encode input :=
  rfl

/-- The canonical well-formedness predicate at the exact erased presentation. -/
def wellFormedProblemAt : ProblemAt lawfulRepresentation where
  isYes := _root_.ComplexityReduction.UniversalRelIR.WellFormed

/--
An explicitly user-locked V2 presented problem for well-formed erased
interchange instances.  This leaf exports no structural-certificate or
automatic-admission declaration for the custom `RelSig` wrapper layout.
-/
def wellFormedPresentedProblem : PresentedProblem :=
  PresentedProblem.ofProblemAt lawfulRepresentation wellFormedProblemAt

/--
The exact typed endpoint exported for the erased-interchange well-formedness
predicate.  Consumers use this endpoint at the canonical
`lawfulRepresentation`; it is not reconstructed from a route-local
`EncodedType`, carrier equality, or bare layout equivalence.
-/
def wellFormedEndpoint : PresentedProblem.EndpointAt lawfulRepresentation :=
  wellFormedPresentedProblem.endpoint

/--
The endpoint type exported by the erased-interchange presentation.

Compatibility leaves may alias values at this type, but they do not receive a
second presentation parameter from which to rebuild the `UniversalRelIR`
encoder.  Thus a consumer which names this API is indexed by the one exact
lawful presentation owned here.
-/
abbrev CanonicalEndpoint : Type :=
  PresentedProblem.EndpointAt lawfulRepresentation

/-- The canonical well-formedness endpoint as seen by compatibility consumers. -/
def canonicalWellFormedEndpoint : CanonicalEndpoint :=
  wellFormedEndpoint

/-- Compatibility consumers see the original endpoint only through the canonical endpoint type. -/
@[simp]
theorem canonicalWellFormedEndpoint_eq_wellFormedEndpoint :
    canonicalWellFormedEndpoint = wellFormedEndpoint :=
  rfl

/--
Reindex an endpoint into the canonical erased-interchange boundary.

The sole admission argument is equality of complete lawful presentations;
neither carrier equality nor equality of the wrapped legacy `EncodedType` is
an input to this API.  This is the one-way endpoint bridge available to
compatibility spelling consumers.
-/
def reindexEndpointToCanonical {candidate : LawfulEncodedType}
    (presentation_eq : candidate = lawfulRepresentation)
    (endpoint : PresentedProblem.EndpointAt candidate) : CanonicalEndpoint :=
  PresentedProblem.reindexEndpoint presentation_eq endpoint

/-- The one-way endpoint bridge preserves the source predicate after exact transport. -/
@[simp]
theorem reindexEndpointToCanonical_isYes {candidate : LawfulEncodedType}
    (presentation_eq : candidate = lawfulRepresentation)
    (endpoint : PresentedProblem.EndpointAt candidate)
    (input : lawfulRepresentation.Carrier) :
    (reindexEndpointToCanonical presentation_eq endpoint).isYes input ↔
      endpoint.isYes (PresentedProblem.transportInstance presentation_eq.symm input) :=
  Iff.rfl

/-- Reindexing an endpoint already at the canonical presentation is definitionally inert. -/
@[simp]
theorem reindexEndpointToCanonical_rfl (endpoint : CanonicalEndpoint) :
    reindexEndpointToCanonical (candidate := lawfulRepresentation) rfl endpoint = endpoint :=
  rfl

/--
Every use of the endpoint bridge simultaneously preserves its complete codec
identity and transports its predicate only along that exact presentation
equality.  This is the public coherence fact for compatibility consumers:
there is no carrier-only or encoder-only bridge overload.
-/
theorem reindexEndpointToCanonical_bridgeCoherence {candidate : LawfulEncodedType}
    (presentation_eq : candidate = lawfulRepresentation)
    (endpoint : PresentedProblem.EndpointAt candidate) :
    candidate.representationIdentity = lawfulRepresentation.representationIdentity ∧
      ∀ input : lawfulRepresentation.Carrier,
        (reindexEndpointToCanonical presentation_eq endpoint).isYes input ↔
          endpoint.isYes (PresentedProblem.transportInstance presentation_eq.symm input) :=
  ⟨PresentedProblem.reindexEndpoint_representationIdentity_eq presentation_eq endpoint,
    fun input => reindexEndpointToCanonical_isYes presentation_eq endpoint input⟩

/-- Exact endpoint reindexing into this leaf preserves the complete codec identity. -/
theorem reindexEndpointToCanonical_representationIdentity_eq {candidate : LawfulEncodedType}
    (presentation_eq : candidate = lawfulRepresentation)
    (endpoint : PresentedProblem.EndpointAt candidate) :
    candidate.representationIdentity = lawfulRepresentation.representationIdentity :=
  PresentedProblem.reindexEndpoint_representationIdentity_eq presentation_eq endpoint

/--
A candidate with a different codec identity is not this canonical lawful
presentation, even when it happens to use the same carrier or encoded type.
-/
theorem canonicalPresentation_ne_of_representationIdentity_ne {candidate : LawfulEncodedType}
    (identity_ne : candidate.representationIdentity ≠
      lawfulRepresentation.representationIdentity) :
    candidate ≠ lawfulRepresentation :=
  PresentedProblem.exactPresentation_ne_of_representationIdentity_ne identity_ne

/--
Even a same-carrier, same-encoder candidate cannot reindex one of its
endpoints into the canonical endpoint when its codec identity differs.

The two equalities are deliberately explicit in the statement: this is the
precise failure mode of a route-local or legacy spelling that copies the
`UniversalRelIR` encoder but invents a distinct `CodecShape.Identity`.
-/
theorem noCanonicalEndpointReindexing_of_sameCarrier_sameEncoder_distinctIdentity
    {candidate : LawfulEncodedType}
    (_carrier_eq : candidate.Carrier = lawfulRepresentation.Carrier)
    (_encodedType_eq : candidate.encodedType = encodedType)
    (identity_ne : candidate.representationIdentity ≠
      lawfulRepresentation.representationIdentity) :
    ¬ ∃ (presentation_eq : candidate = lawfulRepresentation)
        (endpoint : PresentedProblem.EndpointAt candidate),
      reindexEndpointToCanonical presentation_eq endpoint = canonicalWellFormedEndpoint := by
  rintro ⟨presentation_eq, endpoint, _⟩
  exact identity_ne
    (reindexEndpointToCanonical_representationIdentity_eq presentation_eq endpoint)

/--
The typed endpoint is definitionally the original well-formedness predicate
at the single canonical UniversalRelIR presentation.
-/
@[simp]
theorem wellFormedEndpoint_eq_wellFormedProblemAt :
    wellFormedEndpoint = wellFormedProblemAt :=
  rfl

/--
Endpoint evaluation retains the existing UniversalRelIR well-formedness
semantics while remaining indexed by the canonical presentation.
-/
@[simp]
theorem wellFormedEndpoint_isYes (input : lawfulRepresentation.Carrier) :
    wellFormedEndpoint.isYes input ↔
      _root_.ComplexityReduction.UniversalRelIR.WellFormed input :=
  Iff.rfl

/-- The presented endpoint retains exactly the custom lawful representation. -/
@[simp]
theorem wellFormedPresentedProblem_representation :
    wellFormedPresentedProblem.representation = lawfulRepresentation :=
  rfl

/-- The backend endpoint cannot silently substitute another encoded type. -/
@[simp]
theorem wellFormedPresentedProblem_backendEndpoint_instance :
    wellFormedPresentedProblem.backendEndpoint.Instance = encodedType :=
  rfl

/-- The endpoint identity retains the complete custom representation layout. -/
@[simp]
theorem wellFormedPresentedProblem_representationIdentity :
    wellFormedPresentedProblem.representationIdentity = representationShape.identity :=
  rfl

/-- The problem predicate remains aligned with the explicitly locked custom carrier. -/
@[simp]
theorem wellFormedProblemAt_isYes (input : lawfulRepresentation.Carrier) :
    wellFormedProblemAt.isYes input ↔
      _root_.ComplexityReduction.UniversalRelIR.WellFormed input :=
  Iff.rfl

@[simp]
theorem wellFormedPresentedProblem_accepts (input : lawfulRepresentation.Carrier) :
    wellFormedPresentedProblem.accepts input ↔
      _root_.ComplexityReduction.UniversalRelIR.WellFormed input :=
  Iff.rfl

end UniversalRelIR
end Presentation
end ComplexityReduction
