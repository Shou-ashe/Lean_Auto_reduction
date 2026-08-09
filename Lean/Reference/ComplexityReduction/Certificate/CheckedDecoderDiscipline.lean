/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Certificate.VerifierEncodingDiscipline

/-!
Compatibility spelling for the canonical checked-decoder discipline.

This is not a second discipline: the abbreviation below is exactly
`CertifiedVerifierEncodingDiscipline`, whose sole trusted constructor requires
CR's exact `TMVerifierEncodingDiscipline verifier.toTMVerifier` contract.
-/

namespace ComplexityReduction
namespace Certificate

open Encoding

abbrev CheckedDecoderNativeDiscipline {problem : PresentedProblem}
    (verifier : CertifiedVerifier problem) : Type 2 :=
  CertifiedVerifierEncodingDiscipline verifier

namespace CheckedDecoderNativeDiscipline

/-- Construct the canonical discipline from its exact CR checked-decoder contract. -/
def ofBackend {problem : PresentedProblem} {verifier : CertifiedVerifier problem}
    (backendDiscipline :
      ComplexityReduction.SAT.TMVerifierEncodingDiscipline verifier.toTMVerifier) :
    CheckedDecoderNativeDiscipline verifier :=
  CertifiedVerifierEncodingDiscipline.ofCheckedDecoder backendDiscipline

/-- Recover the exact CR discipline carried by the canonical V2 discipline. -/
def backendDiscipline {problem : PresentedProblem} {verifier : CertifiedVerifier problem}
    (discipline : CheckedDecoderNativeDiscipline verifier) :
    ComplexityReduction.SAT.TMVerifierEncodingDiscipline verifier.toTMVerifier :=
  CertifiedVerifierEncodingDiscipline.backendDiscipline discipline

/-- Recover the exact checked suffix decoder. -/
def checkedSuffixDecoder {problem : PresentedProblem} {verifier : CertifiedVerifier problem}
    (discipline : CheckedDecoderNativeDiscipline verifier) :=
  CertifiedVerifierEncodingDiscipline.checkedSuffixDecoder discipline

@[simp]
theorem backendDiscipline_ofBackend {problem : PresentedProblem}
    {verifier : CertifiedVerifier problem}
    (backend :
      ComplexityReduction.SAT.TMVerifierEncodingDiscipline verifier.toTMVerifier) :
    backendDiscipline (ofBackend backend) = backend :=
  CertifiedVerifierEncodingDiscipline.backendDiscipline_ofCheckedDecoder backend

/-- This compatibility spelling is definitionally the canonical discipline. -/
def toCertifiedVerifierEncodingDiscipline {problem : PresentedProblem}
    {verifier : CertifiedVerifier problem}
    (discipline : CheckedDecoderNativeDiscipline verifier) :
    CertifiedVerifierEncodingDiscipline verifier :=
  discipline

/-- Build native verifier capability from canonical checked-decoder discipline. -/
def toNativeVerifierCapability {problem : PresentedProblem}
    {verifier : CertifiedVerifier problem}
    (discipline : CheckedDecoderNativeDiscipline verifier) :
    NativeVerifierCapability problem :=
  NativeVerifierCapability.mk verifier discipline

@[simp]
theorem verifier_toNativeVerifierCapability {problem : PresentedProblem}
    {verifier : CertifiedVerifier problem}
    (discipline : CheckedDecoderNativeDiscipline verifier) :
    discipline.toNativeVerifierCapability.verifier = verifier :=
  rfl

/-- Checked-decoder discipline supplies native membership through its exact capability. -/
theorem toNativeTMInNP {problem : PresentedProblem}
    {verifier : CertifiedVerifier problem}
    (discipline : CheckedDecoderNativeDiscipline verifier) : NativeTMInNP problem :=
  NativeTMInNP.ofCapability discipline.toNativeVerifierCapability

/-- Forgetting native membership remains a one-way backend projection. -/
theorem toBackendTMInNP {problem : PresentedProblem}
    {verifier : CertifiedVerifier problem}
    (discipline : CheckedDecoderNativeDiscipline verifier) : BackendTMInNP problem :=
  discipline.toNativeVerifierCapability.toBackendTMInNP

end CheckedDecoderNativeDiscipline
end Certificate
end ComplexityReduction
