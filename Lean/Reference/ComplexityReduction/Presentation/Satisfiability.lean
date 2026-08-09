/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Problems.Karp21.Satisfiability

/-!
Canonical V2 presentation bridge for Karp21's structured Satisfiability endpoint.

The older `Problems.Karp21.Satisfiability.cnfSATStructuredProblem` is not a
second CNF target: it is definitionally the exact V2 presentation of CR's
`satisfiabilityStructuredDecisionProblem`.  This leaf gives that generic Karp21
endpoint its presentation-local spelling without constructing another codec,
predicate, or tagged registry candidate.

The `CNF` carrier is a custom syntax wrapper around the apparent nested-list
payload layout.  It remains an explicitly user-selected lawful presentation:
the closed structural-origin language has no constructor for this wrapper, and
this bridge intentionally exports no structural certificate or automatic
presentation admission.
-/

namespace ComplexityReduction
namespace Presentation
namespace Satisfiability

open Encoding

/-! ### Literal and Clause facade -/

/-- The explicit unary-variable/Boolean-polarity layout of the canonical SAT literal codec. -/
abbrev literalShape : CodecShape :=
  Problems.Karp21.Satisfiability.literalStructuredShape

/--
The presentation-local spelling of the unique canonical structured SAT literal
presentation.  This is an alias, not another product codec for the same
carrier.
-/
abbrev literalPresentation : LawfulEncodedType :=
  Problems.Karp21.Satisfiability.literalStructuredPresentation

/-- The literal facade is definitionally the canonical faithful presentation. -/
theorem literalPresentation_eq_canonical :
    literalPresentation = Problems.Karp21.Satisfiability.literalStructuredPresentation :=
  rfl

/-- The literal facade keeps exactly the read-only structured literal encoder. -/
@[simp]
theorem literalPresentation_encodedType :
    literalPresentation.encodedType = ComplexityReduction.Karp21.literalStructuredEncodedType :=
  rfl

/-- The literal facade retains the complete variable/polarity representation identity. -/
@[simp]
theorem literalPresentation_representation :
    literalPresentation.representation = literalShape.identity :=
  rfl

/-- The literal facade carrier is exactly the existing SAT literal syntax. -/
theorem literalPresentation_carrier_eq_Literal :
    literalPresentation.Carrier = ComplexityReduction.SAT.Literal :=
  rfl

/-- The only literal encoder exposed by this facade is the canonical structured encoder. -/
@[simp]
theorem literalPresentation_encode (literal : literalPresentation.Carrier) :
    literalPresentation.encode literal =
      ComplexityReduction.Karp21.literalStructuredEncodedType.encode literal :=
  rfl

/-- The explicit list-of-literals layout of the canonical Clause codec. -/
abbrev clauseShape : CodecShape :=
  Problems.Karp21.Satisfiability.clauseStructuredShape

/--
The presentation-local spelling of the canonical structured Clause presentation.
It reuses the literal facade's canonical layout rather than constructing a
new list codec.
-/
abbrev clausePresentation : LawfulEncodedType :=
  Problems.Karp21.Satisfiability.clauseStructuredPresentation

/-- The Clause facade is definitionally the canonical faithful presentation. -/
theorem clausePresentation_eq_canonical :
    clausePresentation = Problems.Karp21.Satisfiability.clauseStructuredPresentation :=
  rfl

/-- The Clause facade keeps exactly the read-only structured Clause encoder. -/
@[simp]
theorem clausePresentation_encodedType :
    clausePresentation.encodedType = ComplexityReduction.Karp21.clauseStructuredEncodedType :=
  rfl

/-- The Clause facade retains the complete literal-list representation identity. -/
@[simp]
theorem clausePresentation_representation :
    clausePresentation.representation = clauseShape.identity :=
  rfl

/-- The Clause facade carrier is exactly the existing SAT Clause syntax. -/
theorem clausePresentation_carrier_eq_Clause :
    clausePresentation.Carrier = ComplexityReduction.SAT.Clause :=
  rfl

/-- The only Clause encoder exposed by this facade is the canonical structured encoder. -/
@[simp]
theorem clausePresentation_encode (clause : clausePresentation.Carrier) :
    clausePresentation.encode clause =
      ComplexityReduction.Karp21.clauseStructuredEncodedType.encode clause :=
  rfl

/-- The explicit custom-layout identity selected for structured Karp21 satisfiability. -/
abbrev structuredShape : CodecShape :=
  Problems.Karp21.Satisfiability.cnfSATStructuredShape

/--
The exact lawful presentation of CR's structured Satisfiability encoder.

This is a bridge to the one canonical, already attributed V2 problem
declaration rather than a second presentation constructed from the same
carrier.
-/
abbrev structuredPresentation : LawfulEncodedType :=
  Problems.Karp21.Satisfiability.cnfSATStructuredPresentation

/-- The Karp21 structured presentation is exactly the existing canonical CNF presentation. -/
theorem structuredPresentation_eq_canonical :
    structuredPresentation = Problems.Karp21.Satisfiability.cnfSATStructuredPresentation :=
  rfl

/-- The bridge retains exactly CR's faithful structured CNF encoder. -/
@[simp]
theorem structuredPresentation_encodedType :
    structuredPresentation.encodedType = ComplexityReduction.Karp21.cnfStructuredEncodedType :=
  rfl

/-- The bridge retains the complete custom structured-layout identity. -/
@[simp]
theorem structuredPresentation_representation :
    structuredPresentation.representation = structuredShape.identity :=
  rfl

/-- The represented carrier is exactly CR's CNF syntax carrier. -/
theorem structuredPresentation_carrier_eq_CNF :
    structuredPresentation.Carrier = ComplexityReduction.SAT.CNF :=
  rfl

/-- The only executable encoding exposed here is CR's established structured CNF encoder. -/
@[simp]
theorem structuredPresentation_encode (formula : structuredPresentation.Carrier) :
    structuredPresentation.encode formula =
      ComplexityReduction.Karp21.cnfStructuredEncodedType.encode formula :=
  rfl

/-- The exact satisfiability predicate indexed by the canonical structured presentation. -/
abbrev structuredProblemAt : ProblemAt structuredPresentation :=
  Problems.Karp21.Satisfiability.cnfSATStructuredProblemAt

/--
The canonical attributed V2 structured Satisfiability endpoint.

The typed-problem attribute deliberately stays on
`Problems.Karp21.Satisfiability.cnfSATStructuredProblem`, the unique concrete
declaration re-exported by this bridge.  Applying it to this alias would make
a duplicate registry-discovery candidate without supplying new evidence.
-/
abbrev structuredProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.cnfSATStructuredProblem

/-- The generic Karp21 endpoint is definitionally the one canonical V2 SAT endpoint. -/
theorem structuredProblem_eq_canonical :
    structuredProblem = Problems.Karp21.Satisfiability.cnfSATStructuredProblem :=
  rfl

/-- The endpoint remains indexed by exactly the selected structured presentation. -/
@[simp]
theorem structuredProblem_representation :
    structuredProblem.representation = structuredPresentation :=
  rfl

/-- The endpoint preserves the complete custom structured-layout identity. -/
@[simp]
theorem structuredProblem_representationIdentity :
    structuredProblem.representationIdentity = structuredShape.identity :=
  rfl

/--
The V2 backend projection is exactly CR's generic structured Satisfiability
decision problem, not merely an endpoint with a propositionally related
carrier or predicate.
-/
@[simp]
theorem structuredProblem_backendEndpoint_eq_legacy :
    structuredProblem.backendEndpoint =
      ComplexityReduction.Karp21.satisfiabilityStructuredDecisionProblem :=
  rfl

/-- The presentation-local `ProblemAt` predicate is precisely CNF satisfiability. -/
@[simp]
theorem structuredProblemAt_isYes (formula : structuredPresentation.Carrier) :
    structuredProblemAt.isYes formula ↔ ComplexityReduction.SAT.CNF.Satisfiable formula :=
  Iff.rfl

/-- The typed endpoint accepts exactly the established structured Satisfiability instances. -/
@[simp]
theorem structuredProblem_accepts (formula : structuredProblem.Instance) :
    structuredProblem.accepts formula ↔ ComplexityReduction.SAT.CNF.Satisfiable formula :=
  Iff.rfl

/--
Any future automatic admission of the explicitly selected CNF endpoint is
still indexed by this endpoint's full custom representation identity.  This
does not manufacture such an admission: the CNF syntax wrapper has no closed
structural origin.  It records the identity constraint that an admission must
satisfy before its predicate can be used.
-/
theorem structuredProblem_automaticAdmission_representationIdentity
    (admission : PresentedProblem.AutomaticPresentationAdmission structuredProblem) :
    admission.certificate.toLawfulEncodedType.representation = structuredShape.identity := by
  simpa only [structuredProblem_representationIdentity] using
    PresentedProblem.admittedEndpoint_representationIdentity admission

/--
The predicate recovered from an automatic CNF admission is the exact CNF
satisfiability predicate after transport along that admission's certificate.
The transport is induced by equality of the complete V2 presentation, never
by a carrier equality or a bare equivalence.
-/
theorem structuredProblem_automaticAdmission_predicate
    (admission : PresentedProblem.AutomaticPresentationAdmission structuredProblem)
    (formula : admission.certificate.toLawfulEncodedType.Carrier) :
    (PresentedProblem.admittedEndpoint admission).isYes formula ↔
      ComplexityReduction.SAT.CNF.Satisfiable
        (PresentedProblem.transportInstance
          (LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq
            structuredProblem.representation admission.certificate).symm formula) := by
  rw [PresentedProblem.admittedEndpoint_isYes]
  exact structuredProblem_accepts _

/-! ### Bundled 3SAT facade and Boolean witness layout -/

/-- The explicit nested-list layout of the canonical bundled-3SAT codec. -/
abbrev threeSATShape : CodecShape :=
  Problems.Karp21.Satisfiability.threeSATStructuredShape

/--
The presentation-local spelling of the unique canonical bundled-3SAT
presentation.  It is definitionally the problem-family presentation, not a
new codec for the proof-carrying `ThreeCNF` carrier.
-/
abbrev threeSATPresentation : LawfulEncodedType :=
  Problems.Karp21.Satisfiability.threeSATStructuredPresentation

/-- The bundled-3SAT facade is definitionally the canonical faithful presentation. -/
theorem threeSATPresentation_eq_canonical :
    threeSATPresentation = Problems.Karp21.Satisfiability.threeSATStructuredPresentation :=
  rfl

/-- The bundled-3SAT facade keeps exactly the read-only structured encoder. -/
@[simp]
theorem threeSATPresentation_encodedType :
    threeSATPresentation.encodedType = ComplexityReduction.Karp21.threeCNFStructuredEncodedType :=
  rfl

/-- The bundled-3SAT facade retains its complete nested codec identity. -/
@[simp]
theorem threeSATPresentation_representation :
    threeSATPresentation.representation = threeSATShape.identity :=
  rfl

/-- The bundled-3SAT facade carrier is exactly the existing proof-carrying syntax. -/
theorem threeSATPresentation_carrier_eq_ThreeCNF :
    threeSATPresentation.Carrier = ComplexityReduction.SAT.ThreeCNF :=
  rfl

/-- The only bundled-3SAT encoder exposed by this facade is the canonical structured encoder. -/
@[simp]
theorem threeSATPresentation_encode (formula : threeSATPresentation.Carrier) :
    threeSATPresentation.encode formula =
      ComplexityReduction.Karp21.threeCNFStructuredEncodedType.encode formula :=
  rfl

/-- The exact satisfiability predicate for the canonical bundled-3SAT presentation. -/
abbrev threeSATProblemAt : ProblemAt threeSATPresentation :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblemAt

/--
The unique canonical bundled-3SAT `PresentedProblem`.

Its typed-problem attribute deliberately remains on the concrete declaration
in `Problems.Karp21.Satisfiability`; tagging this alias would create only a
duplicate discovery candidate, not a new capability.
-/
abbrev threeSATProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem

/-- The bundled-3SAT endpoint is exactly the canonical typed problem. -/
theorem threeSATProblem_eq_canonical :
    threeSATProblem = Problems.Karp21.Satisfiability.threeSATStructuredProblem :=
  rfl

/-- The bundled-3SAT endpoint remains indexed by exactly the facade presentation. -/
@[simp]
theorem threeSATProblem_representation :
    threeSATProblem.representation = threeSATPresentation :=
  rfl

/-- The bundled-3SAT endpoint preserves the complete nested representation identity. -/
@[simp]
theorem threeSATProblem_representationIdentity :
    threeSATProblem.representationIdentity = threeSATShape.identity :=
  rfl

/--
The V2 backend projection is exactly CR's structured bundled-3SAT decision
problem.  In particular it cannot silently retarget to another endpoint on
the same `ThreeCNF` carrier.
-/
@[simp]
theorem threeSATProblem_backendEndpoint_eq_legacy :
    threeSATProblem.backendEndpoint =
      ComplexityReduction.Karp21.threeSATStructuredDecisionProblem :=
  rfl

/-- The bundled-3SAT endpoint accepts exactly the established satisfiability predicate. -/
@[simp]
theorem threeSATProblem_accepts (formula : threeSATProblem.Instance) :
    threeSATProblem.accepts formula ↔ ComplexityReduction.SAT.ThreeCNF.Satisfiable formula :=
  Iff.rfl

/--
Any automatic admission for bundled-3SAT remains tied to the complete nested
3SAT identity selected by this exact endpoint.  As for CNF, this conditional
alignment theorem grants no structural admission to the custom syntax wrapper.
-/
theorem threeSATProblem_automaticAdmission_representationIdentity
    (admission : PresentedProblem.AutomaticPresentationAdmission threeSATProblem) :
    admission.certificate.toLawfulEncodedType.representation = threeSATShape.identity := by
  simpa only [threeSATProblem_representationIdentity] using
    PresentedProblem.admittedEndpoint_representationIdentity admission

/--
An admitted bundled-3SAT endpoint retains the established semantic predicate
after transport along the certificate's exact presentation equality.
-/
theorem threeSATProblem_automaticAdmission_predicate
    (admission : PresentedProblem.AutomaticPresentationAdmission threeSATProblem)
    (formula : admission.certificate.toLawfulEncodedType.Carrier) :
    (PresentedProblem.admittedEndpoint admission).isYes formula ↔
      ComplexityReduction.SAT.ThreeCNF.Satisfiable
        (PresentedProblem.transportInstance
          (LawfulEncodedType.structuralCertificate_toLawfulEncodedType_eq
            threeSATProblem.representation admission.certificate).symm formula) := by
  rw [PresentedProblem.admittedEndpoint_isYes]
  exact threeSATProblem_accepts _

/-- The canonical finite Boolean assignment layout used as a SAT witness presentation. -/
abbrev finiteAssignmentPresentation : LawfulEncodedType :=
  Problems.Karp21.Satisfiability.finiteAssignmentPresentation

/--
The sole structural admission in this SAT facade: finite Boolean assignments
are assembled by the standard list/Boolean constructors.  The declaration-local
typed-presentation attribute stays on the canonical certificate declaration,
whose elaborated type the registry validator accepts.
-/
abbrev finiteAssignmentStructuralCertificate : finiteAssignmentPresentation.StructuralCertificate :=
  Problems.Karp21.Satisfiability.finiteAssignmentStructuralCertificate

/-- The witness certificate reconstructs exactly the one finite-assignment facade presentation. -/
theorem finiteAssignmentStructuralCertificate_presentation :
    finiteAssignmentStructuralCertificate.toLawfulEncodedType = finiteAssignmentPresentation :=
  Problems.Karp21.Satisfiability.finiteAssignmentStructuralCertificate_presentation

/-
Literal, Clause, CNF, and bundled-3SAT wrappers above remain explicit custom
presentations, so no structural certificate or typed-presentation attribute is
manufactured for them merely from encoder injectivity.
-/

end Satisfiability
end Presentation
end ComplexityReduction
