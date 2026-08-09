/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembership
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATTMRootDecoding
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyFiniteBoolCheckedSuffixDecoderTM

/-!
Checked finite-Boolean suffix decoder for the Karp21 structured
Satisfiability verifier.

This file instantiates the reusable finite-Boolean checked-decoder constructor
for `satisfiabilityStructuredFiniteTMVerifier`.  It supplies a checked suffix
package for this concrete verifier only; it does not derive such packages from
ordinary `TMInNP`.
-/

namespace ComplexityReduction
namespace Karp21

/-- The structured Satisfiability verifier uses the project finite Boolean list encoding. -/
theorem satisfiabilityStructuredFiniteBoolCertificateSymbols_eq_encode (bits : List Bool) :
    SAT.tmVerifierFiniteBoolCertificateSymbols
        (V := satisfiabilityStructuredFiniteTMVerifier) (fun b : Bool => some b) none bits =
      SAT.finiteAssignmentCertEncodedType.encode bits := by
  induction bits with
  | nil =>
      rfl
  | cons b bits ih =>
      change
        some b :: none ::
            SAT.tmVerifierFiniteBoolCertificateSymbols
              (V := satisfiabilityStructuredFiniteTMVerifier)
              (fun b : Bool => some b) none bits =
          some b :: none :: SAT.finiteAssignmentCertEncodedType.encode bits
      rw [ih]

/-- The verifier-product certificate suffix is exactly the finite-Boolean suffix stream. -/
theorem satisfiabilityStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols
    (bits : List Bool) :
    SAT.tmVerifierCertificateInputSuffixEncoded satisfiabilityStructuredFiniteTMVerifier bits =
      (SAT.tmVerifierFiniteBoolCertificateSymbols
          (V := satisfiabilityStructuredFiniteTMVerifier)
          (fun b : Bool => some b) none bits).map (fun s => some (Sum.inr s)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded, satisfiabilityStructuredFiniteTMVerifier]
    using congrArg
      (fun xs : List SAT.finiteAssignmentCertEncodedType.Symbol =>
        xs.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType satisfiabilityStructuredFiniteTMVerifier).Symbol)))
      (satisfiabilityStructuredFiniteBoolCertificateSymbols_eq_encode bits).symm

/-- Encoded certificate-suffix decoder for the structured Satisfiability verifier. -/
noncomputable def satisfiabilityStructuredFiniteEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder satisfiabilityStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofCertificateDecoder
    satisfiabilityStructuredFiniteTMVerifier
    SAT.finiteAssignmentCertDecode
    (by
      intro symbols bits h
      exact SAT.finiteAssignmentCertDecode_sound h)
    SAT.finiteAssignmentCertDecode_complete

/-- Checked finite-Boolean suffix decoder for the structured Satisfiability verifier. -/
noncomputable def satisfiabilityStructuredFiniteCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder satisfiabilityStructuredFiniteTMVerifier :=
  SAT.tmVerifierFiniteBoolCheckedSuffixDecoder
    satisfiabilityStructuredFiniteTMVerifier
    (fun b : Bool => some b) none
    satisfiabilityStructuredFiniteEncodedSuffixDecoder
    (fun bits : List Bool => bits)
    (fun bits : List Bool => bits)
    (by
      intro bits
      exact satisfiabilityStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)
    (by
      intro bits
      exact satisfiabilityStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)

/--
The faithful structured Satisfiability verifier carries a checked
finite-Boolean suffix decoder package.
-/
theorem satisfiabilityStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder satisfiabilityStructuredDecisionProblem :=
  ⟨⟨satisfiabilityStructuredFiniteTMVerifier,
      satisfiabilityStructuredFiniteCheckedSuffixDecoder⟩⟩

end Karp21
end ComplexityReduction
