/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATFiniteVerifierTMFormula
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATSuffixDecoderTM
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.TMEncodingDisciplineTemplates
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.Verifier
import ComplexityReduction.Problems.Karp21.Satisfiability
import ComplexityReduction.Protocol.MissingCapability
import ComplexityReduction.Protocol.TrustPolicy

/-!
Typed adapter for the existing structured-3SAT finite assignment verifier.

The adapter reuses the legacy executable checker and its direct-TM proof as one
`PolyProg.atom`.  The structured 3SAT input carrier is a proof-carrying wrapper,
so it has a faithful explicit V2 presentation but no closed structural codec
origin.  Consequently this leaf exports backend membership and a typed missing
encoding-discipline result; it does not manufacture native verifier capability.
-/

namespace ComplexityReduction
namespace Certificate
namespace VerifierAdapter

open Encoding Program

/-- Compatibility alias for the concrete Karp21 structured bundled-3SAT shape. -/
abbrev threeSATStructuredShape : CodecShape :=
  Problems.Karp21.Satisfiability.threeSATStructuredShape

/-- Compatibility alias for the concrete Karp21 structured bundled-3SAT presentation. -/
abbrev threeSATStructuredPresentation : LawfulEncodedType :=
  Problems.Karp21.Satisfiability.threeSATStructuredPresentation

/-- Compatibility alias for the concrete SAT finite-assignment witness presentation. -/
abbrev finiteAssignmentPresentation : LawfulEncodedType :=
  Problems.Karp21.Satisfiability.finiteAssignmentPresentation

/-- Compatibility alias for the exact structural witness-presentation certificate. -/
abbrev finiteAssignmentStructuralCertificate : finiteAssignmentPresentation.StructuralCertificate :=
  Problems.Karp21.Satisfiability.finiteAssignmentStructuralCertificate

/-- Compatibility alias for the concrete Karp21 structured bundled-3SAT endpoint. -/
abbrev threeSATStructuredProblem : PresentedProblem :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem

@[simp]
theorem threeSATStructuredProblem_accepts (formula : threeSATStructuredProblem.Instance) :
    threeSATStructuredProblem.accepts formula ↔
      ComplexityReduction.SAT.ThreeCNF.Satisfiable formula :=
  Problems.Karp21.Satisfiability.threeSATStructuredProblem_accepts formula

/-- The reused direct-TM primitive for the existing finite assignment checker. -/
@[complexity_reduction_ir_typed_primitive]
def threeSATStructuredCheckerPrimitive :
    Primitive
      (StandardInstances.prod threeSATStructuredPresentation finiteAssignmentPresentation)
      StandardInstances.bool :=
  Primitive.ofTMPolyTime
    (fun input => ComplexityReduction.SAT.threeSATStructuredFiniteVerify input.1 input.2)
    (by
      simpa [threeSATStructuredPresentation, finiteAssignmentPresentation] using
        ComplexityReduction.SAT.threeSATStructuredFiniteVerify_tm_polytime)

/-- The primitive executable is exactly the reused finite assignment checker computation. -/
@[simp]
theorem threeSATStructuredCheckerPrimitive_run
    (input : (StandardInstances.prod
      threeSATStructuredPresentation finiteAssignmentPresentation).Carrier) :
    threeSATStructuredCheckerPrimitive.run input =
      ComplexityReduction.SAT.threeSATStructuredFiniteVerify input.1 input.2 :=
  rfl

/-- The primitive direct-TM witness is indexed by that exact reused executable. -/
theorem threeSATStructuredCheckerPrimitive_directTM :
    ComplexityReduction.TMPolyTimeMap
      (StandardInstances.prod
        threeSATStructuredPresentation finiteAssignmentPresentation).encodedType
      StandardInstances.bool.encodedType
      (fun input => ComplexityReduction.SAT.threeSATStructuredFiniteVerify input.1 input.2) := by
  simpa only [threeSATStructuredCheckerPrimitive_run] using
    threeSATStructuredCheckerPrimitive.tmPolyTime

/-- The one canonical V2 checker program, whose atom is the reused direct-TM checker. -/
def threeSATStructuredChecker :
    PolyProg
      (StandardInstances.prod threeSATStructuredPresentation finiteAssignmentPresentation)
      StandardInstances.bool :=
  .atom threeSATStructuredCheckerPrimitive

/-- The V2 checker executes exactly the existing structured-3SAT finite verifier. -/
@[simp]
theorem threeSATStructuredChecker_run
    (input : (StandardInstances.prod
      threeSATStructuredPresentation finiteAssignmentPresentation).Carrier) :
    threeSATStructuredChecker.run input =
      ComplexityReduction.SAT.threeSATStructuredFiniteVerify input.1 input.2 :=
  rfl

/-- The V2 compiler for the checker has the legacy checker function as its exact denotation. -/
theorem threeSATStructuredChecker_compileTM :
    ComplexityReduction.TMPolyTimeMap
      (StandardInstances.prod
        threeSATStructuredPresentation finiteAssignmentPresentation).encodedType
      StandardInstances.bool.encodedType
      (fun input => ComplexityReduction.SAT.threeSATStructuredFiniteVerify input.1 input.2) := by
  simpa only [threeSATStructuredChecker_run] using threeSATStructuredChecker.compileTM

/-- The certified verifier built from the one reused checker program and its existing witnesses. -/
@[complexity_reduction_ir_typed_verifier]
def threeSATStructuredVerifier : CertifiedVerifier threeSATStructuredProblem where
  witness := finiteAssignmentPresentation
  checker := threeSATStructuredChecker
  witnessBound := fun formula =>
    2 * threeSATStructuredPresentation.encodedType.inputSize formula
  witnessBoundPoly := ComplexityReduction.PolynomialTimeBound.intro_with 1 2 0 (by
    intro formula
    change 2 * ComplexityReduction.Karp21.threeCNFStructuredEncodedType.inputSize formula ≤
      2 * (ComplexityReduction.Karp21.threeCNFStructuredEncodedType.inputSize formula) ^ 1 + 0
    simp)
  correct := by
    intro formula
    change ComplexityReduction.SAT.ThreeCNF.Satisfiable formula ↔
      ∃ bits : List Bool,
        ComplexityReduction.SAT.finiteAssignmentCertEncodedType.inputSize bits ≤
          2 * ComplexityReduction.Karp21.threeCNFStructuredEncodedType.inputSize formula ∧
        ComplexityReduction.SAT.threeSATStructuredFiniteVerify formula bits = true
    constructor
    · rintro ⟨assignment, satisfies⟩
      refine ⟨ComplexityReduction.SAT.assignmentPrefix
        (ComplexityReduction.SAT.CNF.varBound formula.clauses) assignment, ?_, ?_⟩
      · simpa using
          ComplexityReduction.SAT.assignmentPrefix_inputSize_le_threeCNFStructured
            formula assignment
      · exact (ComplexityReduction.SAT.threeSATStructuredFiniteVerify_eq_true_iff formula _).2
          (ComplexityReduction.SAT.ThreeCNF.satisfies_finiteAssignment_prefix
            formula assignment satisfies)
    · rintro ⟨bits, _, accepted⟩
      exact ⟨ComplexityReduction.SAT.finiteAssignment bits,
        (ComplexityReduction.SAT.threeSATStructuredFiniteVerify_eq_true_iff formula bits).1
          accepted⟩
  checkerSound := by
    intro formula bits accepted
    exact ⟨ComplexityReduction.SAT.finiteAssignment bits,
      (ComplexityReduction.SAT.threeSATStructuredFiniteVerify_eq_true_iff formula bits).1 accepted⟩

/-- Backend direct-TM NP membership for the structured-3SAT adapter. -/
theorem threeSATStructuredVerifier_backendTMInNP :
    BackendTMInNP threeSATStructuredProblem :=
  threeSATStructuredVerifier.toBackendTMInNP

/--
The adapter's backend membership is exactly the one-way projection of its typed verifier.

No converse adapter is provided: backend `TMInNP` alone cannot recover the structural or
executable encoding-discipline evidence required for a V2 native capability.
-/
theorem threeSATStructuredVerifier_backendTMInNP_eq_projection :
    threeSATStructuredVerifier_backendTMInNP = threeSATStructuredVerifier.toBackendTMInNP :=
  rfl

/--
The existing library's checked-suffix discipline is retained at its original direct-TM verifier.

This is deliberately legacy evidence: it is indexed by
`threeSATStructuredFiniteTMVerifier`, not by the V2 `CertifiedVerifier`.  In particular, merely
finding this package must not create V2-native membership; that admission still requires an exact
`CertifiedVerifierEncodingDiscipline` for the V2 verifier.
-/
noncomputable def threeSATStructuredLegacyEncodingDiscipline :
    ComplexityReduction.SAT.TMVerifierEncodingDiscipline
      ComplexityReduction.SAT.threeSATStructuredFiniteTMVerifier :=
  ComplexityReduction.SAT.TMVerifierEncodingDiscipline.ofBoolListCertificate
    ComplexityReduction.SAT.threeSATStructuredFiniteTMVerifier
    (fun bit : Bool => some bit) none
    ComplexityReduction.SAT.threeSATStructuredFiniteEncodedSuffixDecoder
    id id
    (by
      intro bits
      change
        (ComplexityReduction.SAT.finiteAssignmentCertEncodedType.encode bits).map
            (fun s => some (Sum.inr s)) =
          (ComplexityReduction.SAT.tmVerifierFiniteBoolCertificateSymbols
            (V := ComplexityReduction.SAT.threeSATStructuredFiniteTMVerifier)
            (fun bit : Bool => some bit) none bits).map (fun s => some (Sum.inr s))
      rw [ComplexityReduction.SAT.threeSATStructuredFiniteBoolCertificateSymbols_eq_encode]
      rfl)
    (by
      intro bits
      change
        (ComplexityReduction.SAT.finiteAssignmentCertEncodedType.encode bits).map
            (fun s => some (Sum.inr s)) =
          (ComplexityReduction.SAT.tmVerifierFiniteBoolCertificateSymbols
            (V := ComplexityReduction.SAT.threeSATStructuredFiniteTMVerifier)
            (fun bit : Bool => some bit) none bits).map (fun s => some (Sum.inr s))
      rw [ComplexityReduction.SAT.threeSATStructuredFiniteBoolCertificateSymbols_eq_encode]
      rfl)

/-- The legacy template retains the exact pre-existing encoded suffix decoder. -/
@[simp]
theorem threeSATStructuredLegacyEncodingDiscipline_decoder_eq :
    threeSATStructuredLegacyEncodingDiscipline.checkedSuffixDecoder.decoder =
      ComplexityReduction.SAT.threeSATStructuredFiniteEncodedSuffixDecoder :=
  rfl

/--
The V2 adapter and the reused legacy verifier run the exact same Boolean checker on the exact
same structured-3SAT and finite-assignment carriers.  This is an executable compatibility theorem,
not an equality that transports the legacy encoding discipline into V2.
-/
@[simp]
theorem threeSATStructuredVerifier_toTMVerifier_verify_eq_legacy
    (formula : threeSATStructuredProblem.Instance)
    (bits : finiteAssignmentPresentation.Carrier) :
    threeSATStructuredVerifier.toTMVerifier.verify formula bits =
      ComplexityReduction.SAT.threeSATStructuredFiniteTMVerifier.verify formula bits :=
  rfl

/-- The exact legacy direct-TM verifier and V2 adapter retain the same witness encoded type. -/
@[simp]
theorem threeSATStructuredVerifier_toTMVerifier_cert_eq_legacy :
    threeSATStructuredVerifier.toTMVerifier.Cert =
      ComplexityReduction.SAT.threeSATStructuredFiniteTMVerifier.Cert :=
  rfl

/--
The V2 backend verifier is definitionally the existing structured-3SAT direct verifier.

This is stronger than agreement of Boolean outputs: the verifier record keeps the legacy
certificate representation, executable checker, direct-TM witness, bound, and soundness proof as
the one backend projection of the V2 certified checker.  It still says nothing about native V2
encoding discipline, whose index is the `CertifiedVerifier` rather than this legacy record.
-/
@[simp]
theorem threeSATStructuredVerifier_toTMVerifier_eq_legacy :
    threeSATStructuredVerifier.toTMVerifier =
      ComplexityReduction.SAT.threeSATStructuredFiniteTMVerifier :=
  rfl

/--
The V2 backend verifier retains the exact legacy direct-TM evidence, not merely another proof that
the same function is polynomial time.
-/
@[simp]
theorem threeSATStructuredVerifier_toTMVerifier_polytime_eq_legacy :
    threeSATStructuredVerifier.toTMVerifier.verifier_polytime =
      ComplexityReduction.SAT.threeSATStructuredFiniteTMVerifier.verifier_polytime :=
  rfl

/--
Compiling the canonical V2 checker yields the exact direct-TM witness stored by the legacy
verifier.  Thus executable, program, and backend TM evidence remain indexed by one checker.
-/
@[simp]
theorem threeSATStructuredChecker_compileTM_eq_legacy :
    threeSATStructuredChecker.compileTM =
      ComplexityReduction.SAT.threeSATStructuredFiniteTMVerifier.verifier_polytime :=
  rfl

/-- The V2 backend membership projection is the pre-existing direct-TM membership theorem. -/
@[simp]
theorem threeSATStructuredVerifier_backendTMInNP_eq_legacy :
    threeSATStructuredVerifier_backendTMInNP =
      ComplexityReduction.SAT.threeSATStructuredFinite_TMInNP :=
  rfl

/--
The concrete legacy-to-V2 adapter has one exact provenance chain.

This statement records the only data reused from the existing direct verifier:
the finite-assignment witness presentation, the checker program and its Boolean
denotation, the direct-TM witness, the backend verifier projection, and the
backend membership theorem.  Every equality is at the fixed V2 presentations;
it is not a generic conversion from an arbitrary legacy checker or a bare
backend proposition.
-/
theorem threeSATStructuredVerifier_exactLegacyDirectVerifierProvenance :
    threeSATStructuredVerifier.witness = finiteAssignmentPresentation ∧
    threeSATStructuredVerifier.witness.encodedType =
      ComplexityReduction.SAT.threeSATStructuredFiniteTMVerifier.Cert ∧
    threeSATStructuredVerifier.checker = threeSATStructuredChecker ∧
    (∀ formula : threeSATStructuredProblem.Instance,
      ∀ bits : finiteAssignmentPresentation.Carrier,
        threeSATStructuredVerifier.checker.run (formula, bits) =
          ComplexityReduction.SAT.threeSATStructuredFiniteTMVerifier.verify formula bits) ∧
    threeSATStructuredVerifier.checker.compileTM =
      ComplexityReduction.SAT.threeSATStructuredFiniteTMVerifier.verifier_polytime ∧
    threeSATStructuredVerifier.toTMVerifier =
      ComplexityReduction.SAT.threeSATStructuredFiniteTMVerifier ∧
    threeSATStructuredVerifier_backendTMInNP =
      ComplexityReduction.SAT.threeSATStructuredFinite_TMInNP :=
  ⟨rfl, rfl, rfl, by intro formula bits; rfl, rfl, rfl, rfl⟩

/--
The structured 3SAT wrapper has no closed structural representation origin in this MVP.
The primitive and verifier tags are discovery-only, so they do not alter this backend-only status
or export native verifier capability from this adapter.
-/
def threeSATStructuredVerifierMissingEncodingDiscipline :
    Protocol.MissingCapability (CertifiedVerifier threeSATStructuredProblem) where
  endpoint := threeSATStructuredVerifier
  reason := .verifierEncodingDiscipline

/-- The missing capability remains indexed by the exact adapter verifier. -/
@[simp]
theorem threeSATStructuredVerifierMissingEncodingDiscipline_endpoint :
    threeSATStructuredVerifierMissingEncodingDiscipline.endpoint = threeSATStructuredVerifier :=
  rfl

/-- The adapter's typed failure is specifically missing native encoding discipline, not backend TM. -/
@[simp]
theorem threeSATStructuredVerifierMissingEncodingDiscipline_reason :
    threeSATStructuredVerifierMissingEncodingDiscipline.reason = .verifierEncodingDiscipline :=
  rfl

/--
The canonical native-verifier request for this adapter is blocked at the
shared typed discipline boundary.  This is an outcome, not a native
capability: its accepted branch remains uninhabited by the backend verifier
or by the legacy suffix-discipline package.
-/
def threeSATStructuredVerifierNativeOutcome :
    Protocol.TrustedNativeVerifierOutcome threeSATStructuredProblem :=
  Protocol.missingNativeVerifierDiscipline threeSATStructuredVerifier

/-- The adapter's canonical native outcome is the shared exact-verifier request. -/
@[simp]
theorem threeSATStructuredVerifierNativeOutcome_eq_sharedMissing :
    threeSATStructuredVerifierNativeOutcome =
      Protocol.missingNativeVerifierDiscipline threeSATStructuredVerifier :=
  rfl

/--
The blocked native outcome carries the adapter's named missing-discipline
diagnostic at the same exact verifier index.
-/
@[simp]
theorem threeSATStructuredVerifierNativeOutcome_eq_blocked_missingDiscipline :
    threeSATStructuredVerifierNativeOutcome =
      .blocked threeSATStructuredVerifierMissingEncodingDiscipline :=
  rfl

/--
Eliminating the canonical outcome exposes only the exact adapter verifier and
the closed missing-discipline reason; it cannot yield a native capability.
-/
theorem threeSATStructuredVerifierNativeOutcome_exact :
    match threeSATStructuredVerifierNativeOutcome with
    | .accepted _ => False
    | .blocked missing =>
        missing.endpoint = threeSATStructuredVerifier ∧
          missing.reason = .verifierEncodingDiscipline :=
  Protocol.missingNativeVerifierDiscipline_exact threeSATStructuredVerifier

/--
The two trust levels exported by the concrete adapter remain explicitly
separate.  The first component is ordinary backend direct-TM membership; the
second is a `TrustPolicy` result whose accepted branch has the strictly
different `NativeVerifierCapability` type.  This is an observation of the
fixed adapter, not an admission constructor from metadata, a bare `TMInNP`,
or an arbitrary checker.
-/
structure ThreeSATStructuredVerifierBackendAndNativeOutcome : Type 2 where
  backendTMInNP : BackendTMInNP threeSATStructuredProblem
  nativeOutcome : Protocol.TrustedNativeVerifierOutcome threeSATStructuredProblem

def threeSATStructuredVerifierBackendAndNativeOutcome :
    ThreeSATStructuredVerifierBackendAndNativeOutcome where
  backendTMInNP := threeSATStructuredVerifier_backendTMInNP
  nativeOutcome := threeSATStructuredVerifierNativeOutcome

/--
The concrete result keeps the real CR backend theorem while its native branch
is the exact typed missing-discipline outcome.  In particular the direct-TM
success is never represented as a native accepted branch.
-/
theorem threeSATStructuredVerifierBackendAndNativeOutcome_exact :
    threeSATStructuredVerifierBackendAndNativeOutcome =
      ⟨ComplexityReduction.SAT.threeSATStructuredFinite_TMInNP,
        .blocked threeSATStructuredVerifierMissingEncodingDiscipline⟩ :=
  rfl

/--
Eliminating the combined result distinguishes its two evidence levels without
recovering a native capability from the backend proof.
-/
theorem threeSATStructuredVerifierBackendAndNativeOutcome_discriminated :
    match threeSATStructuredVerifierBackendAndNativeOutcome with
    | ⟨_, .accepted _⟩ => False
    | ⟨backend, .blocked missing⟩ =>
        backend = ComplexityReduction.SAT.threeSATStructuredFinite_TMInNP ∧
          missing.endpoint = threeSATStructuredVerifier ∧
          missing.reason = .verifierEncodingDiscipline :=
  ⟨rfl, rfl, rfl⟩

end VerifierAdapter
end Certificate
end ComplexityReduction
