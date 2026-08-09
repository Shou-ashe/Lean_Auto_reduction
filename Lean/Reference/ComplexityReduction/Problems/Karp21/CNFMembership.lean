/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembership
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.VerifierEncodingDiscipline
import ComplexityReduction.Presentation.Satisfiability
import ComplexityReduction.Protocol.TrustPolicy

/-!
Canonical verifier boundary for structured CNF Satisfiability.

The endpoint is definitionally CR's structured Satisfiability decision
problem.  CR already provides a standard-audited finite-assignment checker,
its direct-TM realization, and its verifier correctness theorem.  This leaf
reuses that evidence in one V2 `CertifiedVerifier` whose checker is one
`PolyProg.atom` over the exact V2 source and witness presentations.

The CNF input syntax is nevertheless an explicitly selected custom wrapper:
it has no V2 closed structural presentation certificate.  The verifier's
backend projection is therefore available, but native membership remains
blocked precisely on the encoding discipline indexed by that same verifier.
Neither the legacy backend theorem nor its discovery attribute can enter the
native accepted branch.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace CNFMembership

open Encoding Certificate Program

/-- The canonical V2 witness presentation for finite Boolean assignments. -/
abbrev structuredWitnessPresentation : LawfulEncodedType :=
  Presentation.Satisfiability.finiteAssignmentPresentation

/-- The structured verifier's exact finite-assignment witness is structurally certified. -/
abbrev structuredWitnessStructuralCertificate :
    structuredWitnessPresentation.StructuralCertificate :=
  Presentation.Satisfiability.finiteAssignmentStructuralCertificate

/--
The existing finite structured-CNF checker, admitted only with its exact
direct-TM realization.  This is the one domain-local atom used by the V2
verifier below; no route-local TM is introduced.
-/
@[complexity_reduction_ir_typed_primitive]
def structuredCheckerPrimitive :
    Primitive
      (StandardInstances.prod Presentation.Satisfiability.structuredPresentation
        structuredWitnessPresentation)
      StandardInstances.bool :=
  Primitive.ofTMPolyTime
    (fun input =>
      ComplexityReduction.Karp21.satisfiabilityStructuredFiniteVerify input.1 input.2)
    (by
      simpa [structuredWitnessPresentation] using
        ComplexityReduction.Karp21.satisfiabilityStructuredFiniteVerify_tm_polytime)

/-- The V2 primitive executes exactly CR's existing structured-CNF checker. -/
@[simp]
theorem structuredCheckerPrimitive_run
    (input : (StandardInstances.prod Presentation.Satisfiability.structuredPresentation
      structuredWitnessPresentation).Carrier) :
    structuredCheckerPrimitive.run input =
      ComplexityReduction.Karp21.satisfiabilityStructuredFiniteVerify input.1 input.2 :=
  rfl

/-- The primitive's direct-TM witness remains indexed by that exact checker executable. -/
theorem structuredCheckerPrimitive_directTM :
    ComplexityReduction.TMPolyTimeMap
      (StandardInstances.prod Presentation.Satisfiability.structuredPresentation
        structuredWitnessPresentation).encodedType
      StandardInstances.bool.encodedType
      (fun input =>
        ComplexityReduction.Karp21.satisfiabilityStructuredFiniteVerify input.1 input.2) := by
  simpa only [structuredCheckerPrimitive_run] using structuredCheckerPrimitive.tmPolyTime

/-- The one canonical V2 checker program for structured CNF satisfiability. -/
def structuredChecker :
    PolyProg
      (StandardInstances.prod Presentation.Satisfiability.structuredPresentation
        structuredWitnessPresentation)
      StandardInstances.bool :=
  .atom structuredCheckerPrimitive

/-- The V2 checker program has exactly the legacy checker denotation. -/
@[simp]
theorem structuredChecker_run
    (input : (StandardInstances.prod Presentation.Satisfiability.structuredPresentation
      structuredWitnessPresentation).Carrier) :
    structuredChecker.run input =
      ComplexityReduction.Karp21.satisfiabilityStructuredFiniteVerify input.1 input.2 :=
  rfl

/--
The canonical V2 structured-CNF verifier.

The legacy verifier already supplies a uniform polynomial certificate bound,
soundness, and direct-TM computation.  Its existential polynomial constants
are selected once inside this noncomputable definition; all fields below are
still indexed by the same V2 `structuredChecker` program.  No legacy encoding
discipline is converted to a V2 discipline here.
-/
@[complexity_reduction_ir_typed_verifier]
noncomputable def structuredVerifier :
    CertifiedVerifier Presentation.Satisfiability.structuredProblem :=
  let legacy := ComplexityReduction.Karp21.satisfiabilityStructuredFiniteTMVerifier
  let degree := legacy.cert_bound.choose
  let degreeSpec := legacy.cert_bound.choose_spec
  let coefficient := degreeSpec.choose
  let coefficientSpec := degreeSpec.choose_spec
  let offset := coefficientSpec.choose
  let bound := coefficientSpec.choose_spec
  {
    witness := structuredWitnessPresentation
    checker := structuredChecker
    witnessBound := fun formula =>
      coefficient *
        Presentation.Satisfiability.structuredPresentation.encodedType.inputSize formula ^ degree +
          offset
    witnessBoundPoly := ComplexityReduction.PolynomialTimeBound.intro_with
      degree coefficient offset (by
        intro formula
        rfl)
    correct := by
      intro formula
      change ComplexityReduction.SAT.CNF.Satisfiable formula ↔
        ∃ candidate : List Bool,
          ComplexityReduction.SAT.finiteAssignmentCertEncodedType.inputSize candidate ≤
              coefficient * ComplexityReduction.Karp21.cnfStructuredEncodedType.inputSize formula ^
                degree + offset ∧
            ComplexityReduction.Karp21.satisfiabilityStructuredFiniteVerify formula candidate = true
      constructor
      · intro accepted
        exact bound formula accepted
      · rintro ⟨candidate, _, accepted⟩
        exact legacy.sound formula candidate accepted
    checkerSound := by
      intro formula candidate accepted
      change List Bool at candidate
      change ComplexityReduction.Karp21.satisfiabilityStructuredFiniteVerify formula candidate = true at accepted
      change ComplexityReduction.SAT.CNF.Satisfiable formula
      exact legacy.sound formula candidate accepted
  }

/-- The verifier retains exactly the canonical V2 finite-assignment witness presentation. -/
@[simp]
theorem structuredVerifier_witness :
    structuredVerifier.witness = structuredWitnessPresentation :=
  rfl

/-- The verifier's witness side has the exact standard structural certificate. -/
theorem structuredVerifier_witnessStructuralCertificate :
    structuredVerifier.witness.StructuralCertificate := by
  simpa only [structuredVerifier_witness] using structuredWitnessStructuralCertificate

/--
Even an exact input structural certificate and the exact witness structural
certificate do not form native authority without a checked-decoder contract
for `structuredVerifier.toTMVerifier`.
-/
theorem structuredVerifier_structuralEvidence_remains_blocked
    (_inputCertificate : Presentation.Satisfiability.structuredProblem.representation.StructuralCertificate) :
    match Protocol.missingNativeVerifierDiscipline structuredVerifier with
    | .accepted _ => False
    | .blocked missing =>
        missing.endpoint = structuredVerifier ∧
          missing.reason = .verifierEncodingDiscipline :=
  Protocol.missingNativeVerifierDiscipline_exact structuredVerifier

/-- The verifier stores the one direct-TM-backed checker program declared above. -/
@[simp]
theorem structuredVerifier_checker_eq_program :
    structuredVerifier.checker = structuredChecker :=
  rfl

/-- The verifier's checker compilation is its stored program compilation. -/
theorem structuredVerifier_checkerTM_exact :
    structuredVerifier.toTMVerifier.verifier_polytime = structuredVerifier.checker.compileTM :=
  CertifiedVerifier.toTMVerifier_polytime structuredVerifier

/--
Registry-export form of the exact V2 verifier's backend projection.

The attribute remains discovery-only: its elaborated type is backend
`TMInNP`, while the proof term is explicitly the one-way projection of the
checker-backed V2 verifier above.
-/
@[complexity_reduction_ir_typed_verifier]
theorem structured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.Satisfiability.structuredProblem.toEncodedDecisionProblem :=
  structuredVerifier.toBackendTMInNP

/-- The exported backend proof is exactly the projection of the one stored V2 verifier. -/
@[simp]
theorem structured_backendTMInNP_export_eq_verifier_projection :
    structured_backendTMInNP_export = structuredVerifier.toBackendTMInNP :=
  rfl

/--
The new V2 projection reuses the same CR backend proposition as the existing
structured-CNF direct-TM membership theorem.  This equality is in `Prop`; it
does not identify or import a legacy encoding-discipline capability.
-/
theorem structured_backendTMInNP_export_eq_legacy :
    structured_backendTMInNP_export =
      ComplexityReduction.Karp21.satisfiabilityStructured_TMInNP :=
  rfl

/-- The presentation-indexed V2 alias for the same backend-only membership theorem. -/
theorem structured_backendTMInNP :
    BackendTMInNP Presentation.Satisfiability.structuredProblem :=
  structured_backendTMInNP_export

/-- The bridge is pinned to exactly CR's structured Satisfiability backend endpoint. -/
@[simp]
theorem structured_backendTMInNP_endpoint :
    Presentation.Satisfiability.structuredProblem.toEncodedDecisionProblem =
      ComplexityReduction.Karp21.satisfiabilityStructuredDecisionProblem :=
  Presentation.Satisfiability.structuredProblem_backendEndpoint_eq_legacy

/--
The exact native request for structured CNF satisfiability.

Its accepted branch requires a `CertifiedVerifierEncodingDiscipline` indexed
by `structuredVerifier`; the verified direct-TM checker alone is deliberately
insufficient because the input CNF wrapper has no V2 structural certificate.
-/
noncomputable def structuredNativeVerifierOutcome :
    Protocol.TrustedNativeVerifierOutcome Presentation.Satisfiability.structuredProblem :=
  Protocol.missingNativeVerifierDiscipline structuredVerifier

/-- The native blocker retains both the exact V2 verifier and discipline reason. -/
theorem structuredNativeVerifierOutcome_exact :
    match structuredNativeVerifierOutcome with
    | .accepted _ => False
    | .blocked missing =>
        missing.endpoint = structuredVerifier ∧
          missing.reason = .verifierEncodingDiscipline :=
  Protocol.missingNativeVerifierDiscipline_exact structuredVerifier

/- Compile-time anchors for the exact verifier-backed backend boundary. -/
#check structured_backendTMInNP_export
#check structured_backendTMInNP
#check structuredVerifier
#check structuredNativeVerifierOutcome
#check ComplexityReduction.Karp21.satisfiabilityStructured_TMInNP

/- A backend membership theorem cannot manufacture the independently indexed discipline. -/
/--
error: Type mismatch
  structured_backendTMInNP_export
has type
  TMInNP Presentation.Satisfiability.structuredProblem.toEncodedDecisionProblem
of sort `Prop` but is expected to have type
  CertifiedVerifierEncodingDiscipline structuredVerifier
of sort `Type 2`
-/
#guard_msgs in
example : CertifiedVerifierEncodingDiscipline structuredVerifier :=
  structured_backendTMInNP_export

/- Nor can backend membership enter the native verifier/discipline capability branch. -/
/--
error: Type mismatch
  structured_backendTMInNP_export
has type
  TMInNP Presentation.Satisfiability.structuredProblem.toEncodedDecisionProblem
but is expected to have type
  NativeTMInNP Presentation.Satisfiability.structuredProblem
-/
#guard_msgs in
example : NativeTMInNP Presentation.Satisfiability.structuredProblem :=
  structured_backendTMInNP_export

/-! The direct checker program and verifier use only the standard Lean axioms. -/
#print axioms structuredCheckerPrimitive_directTM
#print axioms structuredVerifier
#print axioms structuredVerifier_structuralEvidence_remains_blocked

end CNFMembership
end Karp21
end Problems
end ComplexityReduction
