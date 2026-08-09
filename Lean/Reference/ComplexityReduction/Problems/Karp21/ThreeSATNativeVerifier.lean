/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.CheckedDecoderDiscipline
import ComplexityReduction.Certificate.VerifierAdapter
import ComplexityReduction.Protocol.TrustPolicy

/-!
Native checked-decoder verifier capability for the exact structured-3SAT V2
endpoint.

This leaf does not introduce a checker, direct TM, cost bound, or completeness
claim.  It transports the existing CR checked-suffix discipline only across
the proved equality between the typed verifier's `toTMVerifier` and that exact
legacy verifier, then uses the canonical V2 checked-decoder constructor.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace ThreeSATNativeVerifier

open Certificate

/-- The exact canonical structured-3SAT endpoint selected by this leaf. -/
abbrev threeSATStructuredProblem : Encoding.PresentedProblem :=
  Satisfiability.threeSATStructuredProblem

/-- This is the one existing program-indexed structured-3SAT verifier. -/
abbrev threeSATStructuredVerifier : CertifiedVerifier threeSATStructuredProblem :=
  Certificate.VerifierAdapter.threeSATStructuredVerifier

/-- The family endpoint and verifier are definitionally the adapter's exact endpoint. -/
@[simp]
theorem threeSATStructuredVerifier_exact_adapter :
    threeSATStructuredVerifier = Certificate.VerifierAdapter.threeSATStructuredVerifier :=
  rfl

/-- The exact backend verifier of the typed checker is the existing CR verifier. -/
@[simp]
theorem threeSATStructuredVerifier_toTMVerifier_eq_legacy :
    threeSATStructuredVerifier.toTMVerifier =
      ComplexityReduction.SAT.threeSATStructuredFiniteTMVerifier :=
  Certificate.VerifierAdapter.threeSATStructuredVerifier_toTMVerifier_eq_legacy

/--
The constructed V2 discipline carries CR's real checked-suffix contract at
the exact `toTMVerifier` of the typed structured-3SAT verifier.
-/
@[complexity_reduction_ir_typed_verifier_discipline]
noncomputable def threeSATStructuredCheckedDecoderDiscipline :
    CertifiedVerifierEncodingDiscipline threeSATStructuredVerifier :=
  CheckedDecoderNativeDiscipline.ofBackend (by
    simpa only [threeSATStructuredVerifier_toTMVerifier_eq_legacy] using
      Certificate.VerifierAdapter.threeSATStructuredLegacyEncodingDiscipline)

/-- The stored backend discipline is precisely the reused CR checked decoder. -/
@[simp]
theorem threeSATStructuredCheckedDecoderDiscipline_exact_backend :
    threeSATStructuredCheckedDecoderDiscipline.backendDiscipline =
      Certificate.VerifierAdapter.threeSATStructuredLegacyEncodingDiscipline :=
  rfl

/--
The exact structured-3SAT native verifier capability.

Its declaration type, not this discovery tag, is the authority recognized by
the registry.  The capability contains the same verifier used above and the
discipline indexed by that very verifier.
-/
@[complexity_reduction_ir_typed_verifier]
noncomputable def threeSATStructuredNativeCapability :
    NativeVerifierCapability threeSATStructuredProblem :=
  CheckedDecoderNativeDiscipline.toNativeVerifierCapability
    threeSATStructuredCheckedDecoderDiscipline

/-- The packaged native capability retains the one exact typed verifier. -/
@[simp]
theorem threeSATStructuredNativeCapability_verifier_exact :
    threeSATStructuredNativeCapability.verifier = threeSATStructuredVerifier :=
  rfl

/-- Every constructed capability exposes checked-decoder provenance at that same verifier. -/
theorem threeSATStructuredNativeCapability_checkedDecoderProvenance :
    ∃ backendDiscipline : ComplexityReduction.SAT.TMVerifierEncodingDiscipline
        threeSATStructuredNativeCapability.verifier.toTMVerifier,
      threeSATStructuredNativeCapability.discipline.basis =
        .checkedDecoder backendDiscipline :=
  NativeVerifierCapability.exactDisciplineProvenance threeSATStructuredNativeCapability

/-- The only backend projection is the membership theorem of the packaged verifier. -/
theorem threeSATStructuredNativeCapability_backendProjection :
    threeSATStructuredNativeCapability.toBackendTMInNP =
      threeSATStructuredVerifier.toBackendTMInNP :=
  NativeVerifierCapability.toBackendTMInNP_eq_verifier threeSATStructuredNativeCapability

/-- This projection is the existing direct-TM structured-3SAT membership theorem. -/
@[simp]
theorem threeSATStructuredNativeCapability_backendProjection_eq_legacy :
    threeSATStructuredNativeCapability.toBackendTMInNP =
      Certificate.VerifierAdapter.threeSATStructuredVerifier_backendTMInNP :=
  rfl

/-- Native membership is introduced only from the exact packaged capability above. -/
@[complexity_reduction_ir_typed_native_membership]
theorem threeSATStructuredNativeTMInNP : NativeTMInNP threeSATStructuredProblem :=
  NativeTMInNP.ofCapability threeSATStructuredNativeCapability

/-- A verifier request accepts the exact native capability and no backend-only proxy. -/
noncomputable def threeSATStructuredNativeVerifierOutcome :
    Protocol.TrustedNativeVerifierOutcome threeSATStructuredProblem :=
  Protocol.acceptNativeVerifier threeSATStructuredNativeCapability

/-- The accepted request outcome retains the exact capability declaration. -/
theorem threeSATStructuredNativeVerifierOutcome_exact :
    match threeSATStructuredNativeVerifierOutcome with
    | .accepted capability => capability = threeSATStructuredNativeCapability
    | .blocked _ => False :=
  rfl

end ThreeSATNativeVerifier
end Karp21
end Problems
end ComplexityReduction
