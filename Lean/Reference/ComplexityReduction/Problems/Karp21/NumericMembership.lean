/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembership
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PullbackFiniteBoolSuffixDecodersTM
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.VerifierEncodingDiscipline
import ComplexityReduction.Presentation.Knapsack
import ComplexityReduction.Problems.Karp21.KnapsackNativeVerifier
import ComplexityReduction.Protocol.TrustPolicy

/-!
Canonical numeric Karp21 membership outcomes.

The unary Knapsack endpoint is now served by the standard-audited V2 checker
in `KnapsackNativeVerifier`: its backend projection, native verifier and
checked-decoder discipline all index that exact checker program.  This leaf
keeps the public outcome names stable while making the native branch accepted.
Backend completeness remains an independent fail-closed request.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace NumericMembership

open Certificate

/--
The standard-audited checker projection at exactly the canonical V2 Knapsack
endpoint.
-/
@[complexity_reduction_ir_typed_verifier]
theorem knapsackStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP Presentation.Knapsack.structuredProblem.toEncodedDecisionProblem := by
  exact KnapsackNativeVerifier.structured_backendTMInNP_export

/--
User-facing V2 name for the same exact backend membership proposition.

The abbreviation makes the presentation index explicit, while the attributed
export above retains the canonical backend head needed by the registry
validator.  No converse conversion to `CertifiedVerifier` is provided.
-/
theorem knapsackStructured_backendTMInNP :
    BackendTMInNP Presentation.Knapsack.structuredProblem :=
  knapsackStructured_backendTMInNP_export

/--
The V2 export is definitionally the standard checker projection declared by
`KnapsackNativeVerifier`.
-/
theorem knapsackStructured_backendTMInNP_export_eq_legacy :
    knapsackStructured_backendTMInNP_export =
      KnapsackNativeVerifier.structured_backendTMInNP_export :=
  rfl

/-- The bridge is indexed by CR's established structured Knapsack endpoint. -/
@[simp]
theorem knapsackStructured_backendTMInNP_endpoint :
    Presentation.Knapsack.structuredProblem.toEncodedDecisionProblem =
      ComplexityReduction.Combinatorics.knapsackStructuredDecisionProblem :=
  Presentation.Knapsack.structuredProblem_backendEndpoint_eq_legacy

/--
The exact backend-only membership request for the structured Knapsack
presentation.

Its accepted branch carries only CR's inherited `TMInNP` proof at the exact
V2 presentation.  `PLift` is solely the universe bridge from that proposition
into the type-valued result protocol; it does not turn the theorem into a V2
native verifier or an encoding discipline.
-/
abbrev KnapsackStructuredBackendMembershipOutcome : Type 1 :=
  Protocol.TrustPolicy Encoding.PresentedProblem
    (PLift (BackendTMInNP Presentation.Knapsack.structuredProblem))

/--
Expose the existing theorem only through the backend-membership branch.  This
does not provide a conversion to a V2-native capability: the separately typed
native request below is blocked.
-/
def knapsackStructured_backendMembershipOutcome : KnapsackStructuredBackendMembershipOutcome :=
  .accepted ⟨knapsackStructured_backendTMInNP_export⟩

/--
The exact requested V2-native capability for structured Knapsack membership.

An accepted value must package a certified verifier together with an encoding
discipline at exactly `Presentation.Knapsack.structuredProblem`; bare backend
membership cannot inhabit this branch.
-/
abbrev KnapsackStructuredNativeMembershipOutcome : Type 2 :=
  Protocol.TrustPolicy Encoding.PresentedProblem
    (NativeVerifierCapability Presentation.Knapsack.structuredProblem)

/--
The independently requested backend-completeness capability for structured
Knapsack.  `PLift` merely carries CR's proposition into the `Type`-valued
outcome; it does not weaken the accepted branch's required proof.
-/
abbrev KnapsackStructuredCompletenessOutcome : Type 1 :=
  Protocol.TrustPolicy Encoding.PresentedProblem
    (PLift (ComplexityReduction.TMNPCompleteEnc
      Presentation.Knapsack.structuredProblem.toEncodedDecisionProblem))

/--
Completeness has no corresponding V2 completeness proof.  The existing typed
diagnostic remains for that independent request; it is not used to block the
now-available native verifier capability.
-/
def knapsackStructured_missingTrustedDirectTM :
    Protocol.MissingCapability Encoding.PresentedProblem :=
  .directTM Presentation.Knapsack.structuredProblem

/--
Native Knapsack membership is accepted only through the exact standard V2
verifier/checked-decoder capability, never by converting a bare backend theorem.
-/
noncomputable def knapsackStructured_nativeMembershipOutcome :
    KnapsackStructuredNativeMembershipOutcome :=
  .accepted KnapsackNativeVerifier.structuredNativeCapability

/--
Completeness remains independently fail-closed at the same exact endpoint.
Backend membership is strictly weaker than the required completeness proof.
-/
def knapsackStructured_completenessOutcome : KnapsackStructuredCompletenessOutcome :=
  .blocked knapsackStructured_missingTrustedDirectTM

/--
The direct-TM diagnostic retains precisely the canonical Knapsack endpoint
and the exact missing-capability reason.
-/
theorem knapsackStructured_missingTrustedDirectTM_exact :
    knapsackStructured_missingTrustedDirectTM.endpoint =
        Presentation.Knapsack.structuredProblem ∧
      knapsackStructured_missingTrustedDirectTM.reason = .directTM :=
  ⟨rfl, rfl⟩

/--
The native/completeness blocker is indexed by the full canonical unary
Knapsack representation identity, not merely the shared `KnapsackInput`
carrier.  Hence the backend theorem at this endpoint cannot be repurposed for
the binary presentation or a future codec without a separately typed bridge.
-/
theorem knapsackStructured_missingTrustedDirectTM_representationIdentity :
    knapsackStructured_missingTrustedDirectTM.endpoint.representationIdentity =
      Presentation.Knapsack.structuredShape.identity :=
  rfl

/-- The backend request accepts precisely the inherited backend theorem. -/
theorem knapsackStructured_backendMembershipOutcome_exact :
    match knapsackStructured_backendMembershipOutcome with
    | .accepted membership => membership.down = knapsackStructured_backendTMInNP_export
    | .blocked _ => False :=
  rfl

/-- The native request has no accepted verifier/discipline capability. -/
theorem knapsackStructured_nativeMembershipOutcome_exact :
    match knapsackStructured_nativeMembershipOutcome with
    | .accepted capability => capability = KnapsackNativeVerifier.structuredNativeCapability
    | .blocked _ => False :=
  rfl

/-- The completeness request has no accepted backend-completeness capability. -/
theorem knapsackStructured_completenessOutcome_exact :
    match knapsackStructured_completenessOutcome with
    | .accepted _ => False
    | .blocked missing => missing = knapsackStructured_missingTrustedDirectTM :=
  rfl

/--
Backend and native requests retain distinct result branches: the former can
carry the inherited theorem, while the latter remains blocked at the same
canonical Knapsack presentation until a V2 checker/program chain exists.
-/
theorem knapsackStructured_backend_vs_native_outcome_exact :
    match knapsackStructured_backendMembershipOutcome,
        knapsackStructured_nativeMembershipOutcome with
    | .accepted backend, .accepted capability =>
        backend.down = knapsackStructured_backendTMInNP_export ∧
          capability = KnapsackNativeVerifier.structuredNativeCapability
    | _, _ => False :=
  ⟨rfl, rfl⟩

/--
Native membership and backend-completeness requests fail closed at the same
exact representation-indexed direct-TM boundary.  This does not conflate the
two requested capabilities: it only records that neither can be created from
the accepted backend membership theorem.
-/
theorem knapsackStructured_native_and_completeness_outcomes_exact :
    match knapsackStructured_nativeMembershipOutcome,
        knapsackStructured_completenessOutcome with
    | .accepted capability, .blocked completenessMissing =>
        capability = KnapsackNativeVerifier.structuredNativeCapability ∧
        completenessMissing = knapsackStructured_missingTrustedDirectTM ∧
          completenessMissing.endpoint.representationIdentity =
            Presentation.Knapsack.structuredShape.identity
    | _, _ => False :=
  ⟨rfl, rfl, rfl⟩

/--
Any future accepted native Knapsack branch must package one exact V2 verifier
and the encoding discipline indexed by that same verifier.  Its backend
membership is consequently only the safe projection of that package; it is
not the inherited backend theorem above and provides no converse admission
path from the legacy finite-TM verifier.
-/
theorem knapsackStructured_nativeCapability_exactComponents
    (capability : NativeVerifierCapability Presentation.Knapsack.structuredProblem) :
    ∃ verifier : CertifiedVerifier Presentation.Knapsack.structuredProblem,
      ∃ discipline : CertifiedVerifierEncodingDiscipline verifier,
        capability = NativeVerifierCapability.mk verifier discipline ∧
          capability.toBackendTMInNP = verifier.toBackendTMInNP := by
  rcases capability with ⟨verifier, discipline⟩
  exact ⟨verifier, discipline, rfl, rfl⟩

/--
The native branch's discipline authority, if supplied later, is an exact
checked-decoder contract for its packaged verifier.  In particular the
existing backend `TMInNP` theorem and legacy finite verifier are absent from
this provenance type.
-/
theorem knapsackStructured_nativeCapability_exactDisciplineProvenance
    (capability : NativeVerifierCapability Presentation.Knapsack.structuredProblem) :
    ∃ backendDiscipline :
        ComplexityReduction.SAT.TMVerifierEncodingDiscipline
          capability.verifier.toTMVerifier,
      capability.discipline.basis = .checkedDecoder backendDiscipline :=
  NativeVerifierCapability.exactDisciplineProvenance capability

/- Compile-time anchors for the exact backend-only membership boundary. -/
#check knapsackStructured_backendTMInNP_export
#check knapsackStructured_backendTMInNP
#check ComplexityReduction.Karp21.knapsackStructured_TMInNP
#check knapsackStructured_backendMembershipOutcome
#check knapsackStructured_nativeMembershipOutcome
#check knapsackStructured_completenessOutcome
#check knapsackStructured_nativeCapability_exactComponents
#check knapsackStructured_nativeCapability_exactDisciplineProvenance

/- Backend membership cannot manufacture independent backend NP-completeness evidence. -/
/--
error: Type mismatch
  knapsackStructured_backendTMInNP_export
has type
  TMInNP Presentation.Knapsack.structuredProblem.toEncodedDecisionProblem
but is expected to have type
  TMNPCompleteEnc Presentation.Knapsack.structuredProblem.toEncodedDecisionProblem
-/
#guard_msgs in
example : ComplexityReduction.TMNPCompleteEnc
    Presentation.Knapsack.structuredProblem.toEncodedDecisionProblem :=
  knapsackStructured_backendTMInNP_export

/- Backend membership also cannot manufacture even the V2 backend-verifier object. -/
/--
error: Type mismatch
  knapsackStructured_backendTMInNP_export
has type
  TMInNP Presentation.Knapsack.structuredProblem.toEncodedDecisionProblem
of sort `Prop` but is expected to have type
  CertifiedVerifier Presentation.Knapsack.structuredProblem
of sort `Type 2`
-/
#guard_msgs in
example : CertifiedVerifier Presentation.Knapsack.structuredProblem :=
  knapsackStructured_backendTMInNP_export

/- The legacy finite-TM verifier is likewise not a V2 verifier/discipline capability. -/
/--
error: Type mismatch
  Karp21.knapsackStructuredFiniteTMVerifier
has type
  TMVerifier Combinatorics.knapsackStructuredDecisionProblem
of sort `Type 1` but is expected to have type
  NativeVerifierCapability Presentation.Knapsack.structuredProblem
of sort `Type 2`
-/
#guard_msgs in
example : NativeVerifierCapability Presentation.Knapsack.structuredProblem :=
  ComplexityReduction.Karp21.knapsackStructuredFiniteTMVerifier

/- The backend-only result type cannot be substituted for the native result type. -/
/--
error: Type mismatch
  knapsackStructured_backendMembershipOutcome
has type
  KnapsackStructuredBackendMembershipOutcome
of sort `Type 1` but is expected to have type
  KnapsackStructuredNativeMembershipOutcome
of sort `Type 2`
-/
#guard_msgs in
example : KnapsackStructuredNativeMembershipOutcome :=
  knapsackStructured_backendMembershipOutcome

end NumericMembership
end Karp21
end Problems
end ComplexityReduction
