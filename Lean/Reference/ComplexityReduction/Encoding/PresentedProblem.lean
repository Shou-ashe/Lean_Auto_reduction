/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core.EncodedDecisionProblem
import ComplexityReduction.Encoding.LawfulEncodedType
import ComplexityReduction.Encoding.EncoderCoherentView

/-!
Typed semantic problems at lawful V2 representations.

`PresentedProblem` binds a semantic `DecisionProblem` to one complete lawful
representation. The carrier equality is deliberately the MVP alignment:
representations may differ, but they encode the same semantic instance type.
Changing the carrier requires a later typed equivalence certificate, not a
bare `Equiv`.
-/

namespace ComplexityReduction
namespace Encoding

/-- A yes-predicate bound to one exact lawful representation. -/
structure ProblemAt (representation : LawfulEncodedType) where
  isYes : representation.Carrier → Prop

/--
A semantic problem together with the lawful representation at which its
instances are interpreted. This is presentation data only: it supplies
neither a reduction program nor semantic, cost, or Turing-machine evidence.
-/
structure PresentedProblem where
  semantic : ComplexityReduction.DecisionProblem
  representation : LawfulEncodedType
  carrier_eq : representation.Carrier = semantic.Instance

namespace PresentedProblem

/-- The instance type of a problem is fixed by its bound representation. -/
abbrev Instance (problem : PresentedProblem) : Type :=
  problem.representation.Carrier

/-- Recover the structural representation identity of a presented problem. -/
def representationIdentity (problem : PresentedProblem) : CodecShape.Identity :=
  problem.representation.representationIdentity

/--
Recover the complete encoder-bound representation identity of a presented
problem. The legacy `representationIdentity` remains the structural-layout
projection for compatibility; this definition is the canonical identity for
an endpoint whose concrete codec must remain observable.
-/
def encoderBoundRepresentationIdentity (problem : PresentedProblem) : EncoderBoundIdentity :=
  problem.representation.encoderBoundIdentity

/--
The complete identity of a semantic problem at one concrete lawful codec.

Both the semantic decision problem and the encoder-bound representation occur
as fields. No carrier-only or shape-only identity can construct this record.
-/
structure EncoderBoundProblemIdentity where
  semantic : ComplexityReduction.DecisionProblem
  representation : EncoderBoundIdentity

/-- Mechanically derive a problem's identity from its semantic problem and bound presentation. -/
def encoderBoundProblemIdentity (problem : PresentedProblem) : EncoderBoundProblemIdentity where
  semantic := problem.semantic
  representation := problem.encoderBoundRepresentationIdentity

/-- The representation component of a problem identity is its exact lawful codec identity. -/
@[simp]
theorem encoderBoundProblemIdentity_representation (problem : PresentedProblem) :
    problem.encoderBoundProblemIdentity.representation = problem.representation.encoderBoundIdentity :=
  rfl

/-- An exact presented-problem equality preserves its complete encoder-bound identity. -/
theorem encoderBoundProblemIdentity_eq_of_exactProblem_eq
    {source target : PresentedProblem} (problem_eq : source = target) :
    source.encoderBoundProblemIdentity = target.encoderBoundProblemIdentity :=
  congrArg encoderBoundProblemIdentity problem_eq

/-- An exact presented-problem equality preserves its encoder-bound representation component. -/
theorem encoderBoundRepresentationIdentity_eq_of_exactProblem_eq
    {source target : PresentedProblem} (problem_eq : source = target) :
    source.encoderBoundRepresentationIdentity = target.encoderBoundRepresentationIdentity :=
  congrArg encoderBoundRepresentationIdentity problem_eq

/-- The semantic problem identified by this presentation. -/
def semanticProblem (problem : PresentedProblem) : ComplexityReduction.DecisionProblem :=
  problem.semantic

/-- Transport an input from the exact presentation carrier to the semantic instance carrier. -/
def toSemanticInstance (problem : PresentedProblem) (input : problem.Instance) :
    problem.semantic.Instance :=
  problem.carrier_eq ▸ input

/--
The explicit semantic/presentation alignment used by every presentation
predicate.  No bare carrier equivalence is accepted here: the only transport
is the equality stored in the particular `PresentedProblem`.
-/
theorem toSemanticInstance_eq_transport (problem : PresentedProblem) (input : problem.Instance) :
    problem.toSemanticInstance input = problem.carrier_eq ▸ input :=
  rfl

/-- The yes-predicate of a problem, transported to exactly its bound instance type. -/
def accepts (problem : PresentedProblem) : problem.Instance → Prop :=
  fun input => problem.semantic.isYes (problem.toSemanticInstance input)

/-- The presentation predicate is exactly the semantic predicate after its stored alignment. -/
theorem accepts_iff_semantic_isYes (problem : PresentedProblem) (input : problem.Instance) :
    problem.accepts input ↔ problem.semantic.isYes (problem.toSemanticInstance input) :=
  Iff.rfl

/--
The compatibility encoded decision problem at this exact lawful presentation.

This is only a projection of the typed presentation.  It cannot construct a
`PresentedProblem` from a legacy encoded problem, so legacy raw encodings and
metadata do not gain a route into the V2 trusted boundary.
-/
def toEncodedDecisionProblem (problem : PresentedProblem) :
    ComplexityReduction.EncodedDecisionProblem where
  Instance := problem.representation.encodedType
  isYes := problem.accepts

/-- The exact V2 endpoint on which backend compatibility aliases must be interpreted. -/
abbrev backendEndpoint (problem : PresentedProblem) : ComplexityReduction.EncodedDecisionProblem :=
  problem.toEncodedDecisionProblem

@[simp]
theorem toEncodedDecisionProblem_instance (problem : PresentedProblem) :
    problem.toEncodedDecisionProblem.Instance = problem.representation.encodedType :=
  rfl

@[simp]
theorem backendEndpoint_instance (problem : PresentedProblem) :
    problem.backendEndpoint.Instance = problem.representation.encodedType :=
  rfl

@[simp]
theorem backendEndpoint_eq_toEncodedDecisionProblem (problem : PresentedProblem) :
    problem.backendEndpoint = problem.toEncodedDecisionProblem :=
  rfl

@[simp]
theorem toEncodedDecisionProblem_isYes (problem : PresentedProblem) (input : problem.Instance) :
    problem.toEncodedDecisionProblem.isYes input ↔ problem.accepts input :=
  Iff.rfl

/--
The typed endpoint for predicates at a fixed lawful representation.

The representation is an index, so this interface cannot be supplied by a
predicate packaged at a different `LawfulEncodedType` without an explicit
presentation-change layer.
-/
abbrev EndpointAt (representation : LawfulEncodedType) : Type :=
  ProblemAt representation

/--
The complete encoder-bound identity at which an endpoint predicate is indexed.

The endpoint itself supplies no independent identity field: its exact lawful
presentation index is the only source of this value.
-/
def endpointEncoderBoundIdentity {representation : LawfulEncodedType}
    (_endpoint : EndpointAt representation) : EncoderBoundIdentity :=
  representation.encoderBoundIdentity

/-- An endpoint's identity is mechanically the complete identity of its presentation index. -/
@[simp]
theorem endpointEncoderBoundIdentity_eq_lawful {representation : LawfulEncodedType}
    (endpoint : EndpointAt representation) :
    endpointEncoderBoundIdentity endpoint = representation.encoderBoundIdentity :=
  rfl

/-- View a presented problem as the endpoint indexed by its own representation. -/
def endpoint (problem : PresentedProblem) : EndpointAt problem.representation :=
  ⟨problem.accepts⟩

/-- Package a predicate on a fixed representation as the matching semantic presentation. -/
def ofProblemAt (representation : LawfulEncodedType) (problem : ProblemAt representation) :
    PresentedProblem where
  semantic := ⟨representation.Carrier, problem.isYes⟩
  representation := representation
  carrier_eq := rfl

/-- A typed admission for automatic presentation selection. -/
inductive AutomaticPresentationAdmission (problem : PresentedProblem) : Type where
  /-- Automatic selection begins only at a closed structural representation certificate. -/
  | structural (certificate : problem.representation.StructuralCertificate) :
      AutomaticPresentationAdmission problem

namespace AutomaticPresentationAdmission

/-- Every automatic admission exposes the structural certificate from which it was built. -/
def certificate {problem : PresentedProblem} :
    AutomaticPresentationAdmission problem → problem.representation.StructuralCertificate
  | .structural certificate => certificate

end AutomaticPresentationAdmission

/-- Build automatic admission only from an exact structural representation certificate. -/
def automaticAdmissionOfStructural {problem : PresentedProblem}
    (certificate : problem.representation.StructuralCertificate) :
    AutomaticPresentationAdmission problem :=
  .structural certificate

/--
Structural eligibility for a semantic request.  This proposition deliberately
forgets only the certificate's data, not its closed structural origin: the
sole constructor of `AutomaticPresentationAdmission` requires that
certificate.
-/
def StructurallyGeneratedPresentation (problem : PresentedProblem) : Prop :=
  Nonempty (AutomaticPresentationAdmission problem)

/-- Automatic eligibility supplied by an audited encoder-coherent wrapper to a closed target. -/
def EncoderCoherentlyGeneratedPresentation (problem : PresentedProblem) : Prop :=
  ∃ target : LawfulEncodedType,
    Nonempty (EncoderCoherentView.EncoderCoherentAutomaticAdmission problem.representation target)

/-- The complete semantic-source automatic-selection boundary. -/
def AutomaticallySelectablePresentation (problem : PresentedProblem) : Prop :=
  problem.StructurallyGeneratedPresentation ∨ problem.EncoderCoherentlyGeneratedPresentation

/-- An automatic presentation admission is equivalent to having its structural certificate. -/
theorem structurallyGeneratedPresentation_iff (problem : PresentedProblem) :
    problem.StructurallyGeneratedPresentation ↔
      Nonempty problem.representation.StructuralCertificate := by
  constructor
  · rintro ⟨admission⟩
    exact ⟨admission.certificate⟩
  · rintro ⟨certificate⟩
    exact ⟨.structural certificate⟩

/-- A closed structural certificate remains sufficient for automatic selection. -/
theorem automaticallySelectablePresentation_ofStructural (problem : PresentedProblem)
    (structural : problem.StructurallyGeneratedPresentation) :
    problem.AutomaticallySelectablePresentation :=
  .inl structural

/-- An audited encoder-coherent wrapper to a closed target is sufficient for automatic selection. -/
theorem automaticallySelectablePresentation_ofEncoderCoherent (problem : PresentedProblem)
    (coherent : problem.EncoderCoherentlyGeneratedPresentation) :
    problem.AutomaticallySelectablePresentation :=
  .inr coherent

/-- A different representation identity prevents equality of presentation endpoints. -/
theorem representation_ne_of_representationIdentity_ne {source target : PresentedProblem}
    (identityNe : source.representationIdentity ≠ target.representationIdentity) :
    source.representation ≠ target.representation := by
  intro representationEquality
  apply identityNe
  simpa [representationIdentity] using
    congrArg LawfulEncodedType.representationIdentity representationEquality

/--
An exact lawful-presentation equality preserves the complete structural codec
identity.  This is the identity fact consumed by endpoint reindexing: carrier
equalities never occur in its hypotheses.
-/
theorem representationIdentity_eq_of_exactPresentation_eq
    {source target : LawfulEncodedType} (presentation_eq : source = target) :
    source.representationIdentity = target.representationIdentity := by
  simpa only [LawfulEncodedType.representationIdentity_eq_representation] using
    congrArg LawfulEncodedType.representation presentation_eq

/-- Exact presentation equality preserves the complete encoder-bound codec identity. -/
theorem encoderBoundIdentity_eq_of_exactPresentation_eq
    {source target : LawfulEncodedType} (presentation_eq : source = target) :
    source.encoderBoundIdentity = target.encoderBoundIdentity :=
  congrArg LawfulEncodedType.encoderBoundIdentity presentation_eq

/--
Distinct structural identities rule out the exact presentation equality needed
to transport an endpoint.  In particular, sharing a Lean carrier cannot
provide this equality.
-/
theorem exactPresentation_ne_of_representationIdentity_ne
    {source target : LawfulEncodedType}
    (identityNe : source.representationIdentity ≠ target.representationIdentity) :
    source ≠ target := by
  intro presentation_eq
  exact identityNe (representationIdentity_eq_of_exactPresentation_eq presentation_eq)

/-- Different concrete codecs rule out exact presentation equality even at the same shape. -/
theorem exactPresentation_ne_of_encoderBoundIdentity_ne
    {source target : LawfulEncodedType}
    (identityNe : source.encoderBoundIdentity ≠ target.encoderBoundIdentity) :
    source ≠ target := by
  intro presentation_eq
  exact identityNe (encoderBoundIdentity_eq_of_exactPresentation_eq presentation_eq)

/-- Different encoder-bound identities rule out equality of presented problems. -/
theorem problem_ne_of_encoderBoundRepresentationIdentity_ne
    {source target : PresentedProblem}
    (identityNe : source.encoderBoundRepresentationIdentity ≠
      target.encoderBoundRepresentationIdentity) :
    source ≠ target := by
  intro problem_eq
  exact identityNe (encoderBoundRepresentationIdentity_eq_of_exactProblem_eq problem_eq)

/-- A presentation made directly from `ProblemAt` retains exactly the supplied predicate. -/
theorem accepts_ofProblemAt (representation : LawfulEncodedType)
    (problem : ProblemAt representation) (input : representation.Carrier) :
    (ofProblemAt representation problem).accepts input ↔ problem.isYes input :=
  Iff.rfl

/-- `ofProblemAt` preserves its exact representation identity. -/
@[simp]
theorem representationIdentity_ofProblemAt (representation : LawfulEncodedType)
    (problem : ProblemAt representation) :
    (ofProblemAt representation problem).representationIdentity =
      representation.representationIdentity :=
  rfl

/-- The endpoint constructed from a presentation has exactly its transported semantic predicate. -/
theorem endpoint_isYes (problem : PresentedProblem) (input : problem.Instance) :
    problem.endpoint.isYes input ↔ problem.accepts input :=
  Iff.rfl

/--
Transport an instance only along an equality of *complete* lawful
presentations.  In particular, equality of carriers, equality of codec
identities, and a bare Lean `Equiv` are deliberately not inputs to this API.
Presentation changes with different identities must instead be witnessed by a
certificate-layer `CertifiedPresentationChange`.
-/
def transportInstance {source target : LawfulEncodedType}
    (presentation_eq : source = target) (input : source.Carrier) : target.Carrier := by
  cases presentation_eq
  exact input

/-- Transporting along a reflexive exact presentation equality changes no input. -/
@[simp]
theorem transportInstance_rfl (presentation : LawfulEncodedType)
    (input : presentation.Carrier) :
    transportInstance rfl input = input :=
  rfl

/--
Reindex a predicate endpoint only along an equality of its complete lawful
representation.  This is intentionally stricter than a carrier transport:
the endpoint index cannot be changed by an arbitrary function or `Equiv`.
-/
def reindexEndpoint {source target : LawfulEncodedType}
    (presentation_eq : source = target) (endpoint : EndpointAt source) :
    EndpointAt target :=
  ⟨fun input => endpoint.isYes (transportInstance presentation_eq.symm input)⟩

/-- The predicate of a reindexed endpoint is the source predicate after the exact transport. -/
@[simp]
theorem reindexEndpoint_isYes {source target : LawfulEncodedType}
    (presentation_eq : source = target) (endpoint : EndpointAt source)
    (input : target.Carrier) :
    (reindexEndpoint presentation_eq endpoint).isYes input ↔
      endpoint.isYes (transportInstance presentation_eq.symm input) :=
  Iff.rfl

/--
Every endpoint reindexing carries an equality of the complete lawful
presentations, and therefore preserves their structural representation
identity.  This records the admission boundary independently of the endpoint
predicate, which can be extensionally identical at different codecs.
-/
theorem reindexEndpoint_representationIdentity_eq {source target : LawfulEncodedType}
    (presentation_eq : source = target) (_endpoint : EndpointAt source) :
    source.representationIdentity = target.representationIdentity :=
  representationIdentity_eq_of_exactPresentation_eq presentation_eq

/--
Endpoint reindexing preserves the complete encoder-bound identity, because it
requires an equality of complete lawful presentations rather than a carrier or
structural-shape equality.
-/
theorem reindexEndpoint_encoderBoundIdentity_eq {source target : LawfulEncodedType}
    (presentation_eq : source = target) (endpoint : EndpointAt source) :
    endpointEncoderBoundIdentity endpoint =
      endpointEncoderBoundIdentity (reindexEndpoint presentation_eq endpoint) := by
  simpa only [endpointEncoderBoundIdentity_eq_lawful] using
    encoderBoundIdentity_eq_of_exactPresentation_eq presentation_eq

/--
Recover a problem endpoint from automatic admission at the presentation
reconstructed by its structural certificate.  The certificate supplies the
only equality used for this reindexing, so automatic admission cannot be
obtained from a same-carrier codec or a bare equivalence.
-/
def admittedEndpoint {problem : PresentedProblem}
    (admission : AutomaticPresentationAdmission problem) :
    EndpointAt admission.certificate.toLawfulEncodedType :=
  reindexEndpoint
    (LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq
      problem.representation admission.certificate).symm
    problem.endpoint

/--
The structural reconstruction used by `admittedEndpoint` has exactly the
problem's representation identity, not merely the same carrier.
-/
theorem admittedEndpoint_representationIdentity {problem : PresentedProblem}
    (admission : AutomaticPresentationAdmission problem) :
    admission.certificate.toLawfulEncodedType.representationIdentity =
      problem.representationIdentity := by
  simpa only [representationIdentity] using
    congrArg LawfulEncodedType.representationIdentity
      (LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq
        problem.representation admission.certificate)

/--
The predicate recovered from automatic admission is precisely the problem's
predicate after transport along that certificate's exact presentation
equality.
-/
@[simp]
theorem admittedEndpoint_isYes {problem : PresentedProblem}
    (admission : AutomaticPresentationAdmission problem)
    (input : admission.certificate.toLawfulEncodedType.Carrier) :
    (admittedEndpoint admission).isYes input ↔
      problem.accepts
        (transportInstance
          (LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq
            problem.representation admission.certificate).symm input) :=
  Iff.rfl

/--
The result of automatically choosing a representation for one semantic
request.

This is deliberately stronger than returning a bare `PresentedProblem`: an
automatic choice carries the exact semantic endpoint it answers *and* the
`AutomaticPresentationAdmission` whose only constructor contains a closed
structural certificate.  Thus a caller cannot pass a same-carrier codec, a
faithful encoding, or an arbitrary `Equiv` off as an automatically selected
presentation.
-/
structure AutomaticPresentationSelection
    (semantic : ComplexityReduction.DecisionProblem) where
  presentedProblem : PresentedProblem
  semantic_eq : presentedProblem.semantic = semantic
  admission : AutomaticPresentationAdmission presentedProblem

namespace AutomaticPresentationSelection

/-- Package a concrete presented problem as an automatic choice only with its admission. -/
def ofAdmission (problem : PresentedProblem) (admission : AutomaticPresentationAdmission problem) :
    AutomaticPresentationSelection problem.semantic where
  presentedProblem := problem
  semantic_eq := rfl
  admission := admission

/-- The exact lawful representation selected for the semantic request. -/
def representation {semantic : ComplexityReduction.DecisionProblem}
    (selection : AutomaticPresentationSelection semantic) : LawfulEncodedType :=
  selection.presentedProblem.representation

/-- The complete structural representation identity of an automatic selection. -/
def representationIdentity {semantic : ComplexityReduction.DecisionProblem}
    (selection : AutomaticPresentationSelection semantic) : CodecShape.Identity :=
  selection.presentedProblem.representationIdentity

/--
The predicate endpoint recovered from an automatic choice.

Its index is the lawful representation reconstructed from the admission's
structural certificate, rather than a carrier-level substitute.
-/
def endpoint {semantic : ComplexityReduction.DecisionProblem}
    (selection : AutomaticPresentationSelection semantic) :
    EndpointAt selection.admission.certificate.toLawfulEncodedType :=
  admittedEndpoint selection.admission

/-- The representation reconstructed by automatic selection is exactly the selected one. -/
theorem reconstructedRepresentation_eq {semantic : ComplexityReduction.DecisionProblem}
    (selection : AutomaticPresentationSelection semantic) :
    selection.admission.certificate.toLawfulEncodedType = selection.representation :=
  LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq
    selection.presentedProblem.representation selection.admission.certificate

/-- Automatic endpoint reconstruction preserves the selected codec identity exactly. -/
theorem reconstructedRepresentationIdentity_eq {semantic : ComplexityReduction.DecisionProblem}
    (selection : AutomaticPresentationSelection semantic) :
    selection.admission.certificate.toLawfulEncodedType.representationIdentity =
      selection.representationIdentity := by
  simpa only [representation, representationIdentity] using
    admittedEndpoint_representationIdentity selection.admission

/--
Distinct selected codec identities prevent their reconstructed automatic
presentations from being equal, even when the selected carriers coincide.
-/
theorem reconstructedRepresentation_ne_of_representationIdentity_ne
    {sourceSemantic targetSemantic : ComplexityReduction.DecisionProblem}
    (source : AutomaticPresentationSelection sourceSemantic)
    (target : AutomaticPresentationSelection targetSemantic)
    (identityNe : source.representationIdentity ≠ target.representationIdentity) :
    source.admission.certificate.toLawfulEncodedType ≠
      target.admission.certificate.toLawfulEncodedType := by
  intro reconstructionEquality
  apply identityNe
  calc
    source.representationIdentity =
        source.admission.certificate.toLawfulEncodedType.representationIdentity :=
      (source.reconstructedRepresentationIdentity_eq).symm
    _ = target.admission.certificate.toLawfulEncodedType.representationIdentity :=
      congrArg LawfulEncodedType.representationIdentity reconstructionEquality
    _ = target.representationIdentity :=
      target.reconstructedRepresentationIdentity_eq

/-- The admitted endpoint evaluates exactly the selected presentation predicate. -/
theorem endpoint_isYes {semantic : ComplexityReduction.DecisionProblem}
    (selection : AutomaticPresentationSelection semantic)
    (input : selection.admission.certificate.toLawfulEncodedType.Carrier) :
    selection.endpoint.isYes input ↔
      selection.presentedProblem.accepts
        (transportInstance (selection.reconstructedRepresentation_eq).symm input) :=
  admittedEndpoint_isYes selection.admission input

/--
Reindexing an automatically admitted endpoint keeps both parts of its trusted
alignment: the selected semantic request and the complete representation
identity.  The reindexing equality is between lawful presentations, so a
coincidence of Lean carriers cannot supply this theorem's premise.
-/
theorem endpoint_reindex_semanticRepresentationAlignment
    {semantic : ComplexityReduction.DecisionProblem}
    (selection : AutomaticPresentationSelection semantic)
    {target : LawfulEncodedType}
    (presentation_eq : selection.admission.certificate.toLawfulEncodedType = target)
    (input : target.Carrier) :
    selection.presentedProblem.semantic = semantic ∧
      target.representationIdentity = selection.representationIdentity ∧
        ((reindexEndpoint presentation_eq selection.endpoint).isYes input ↔
          selection.presentedProblem.accepts
            (transportInstance (selection.reconstructedRepresentation_eq).symm
              (transportInstance presentation_eq.symm input))) := by
  refine ⟨selection.semantic_eq, ?_, ?_⟩
  · calc
      target.representationIdentity =
          selection.admission.certificate.toLawfulEncodedType.representationIdentity :=
        congrArg LawfulEncodedType.representationIdentity presentation_eq.symm
      _ = selection.representationIdentity :=
        selection.reconstructedRepresentationIdentity_eq
  · rw [reindexEndpoint_isYes, selection.endpoint_isYes]
    rfl

end AutomaticPresentationSelection

end PresentedProblem
end Encoding
end ComplexityReduction
