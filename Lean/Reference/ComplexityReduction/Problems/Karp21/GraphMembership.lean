/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipClique
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.VerifierEncodingDiscipline
import ComplexityReduction.Protocol.TrustPolicy
import ComplexityReduction.Problems.Karp21.GraphAtoms
import ComplexityReduction.Problems.Karp21.CliqueNativeVerifier

/-!
Canonical structured Clique membership outcomes.

The standard-audited V2 checker in `CliqueNativeVerifier` supplies the direct
TM backend projection and the exact verifier-plus-checked-decoder native
capability. Backend completeness remains an independent fail-closed request.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace GraphMembership

open Certificate

/--
The standard-audited checker projection at the exact canonical V2 Clique
endpoint. Registry classification remains backend membership because this
declaration's elaborated type is the backend `TMInNP` proposition.
-/
@[complexity_reduction_ir_typed_verifier]
theorem cliqueStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      GraphAtoms.cliqueStructuredProblem.toEncodedDecisionProblem := by
  exact CliqueNativeVerifier.backendTMInNP_export

/-- The presentation-indexed V2 alias for the same backend-only membership evidence. -/
theorem cliqueStructured_backendTMInNP :
    BackendTMInNP GraphAtoms.cliqueStructuredProblem :=
  cliqueStructured_backendTMInNP_export

/--
The V2 backend export is definitionally the projection of the standard V2
checker, not a conversion from the legacy backend theorem.
-/
theorem cliqueStructured_backendTMInNP_export_eq_legacy :
    cliqueStructured_backendTMInNP_export =
      CliqueNativeVerifier.backendTMInNP_export :=
  rfl

/-- The bridge is fixed to CR's existing structured Clique backend endpoint. -/
@[simp]
theorem cliqueStructured_backendTMInNP_endpoint :
    GraphAtoms.cliqueStructuredProblem.toEncodedDecisionProblem =
      ComplexityReduction.Combinatorics.Graph.cliqueStructuredDecisionProblem :=
  rfl

/--
The exact backend-only request for structured Clique membership.

Its accepted branch deliberately carries only the inherited `TMInNP` proof
at the exact `GraphAtoms` endpoint.  `PLift` is the universe bridge from that
proposition into the `Type`-valued result protocol; it does not turn the proof
into a V2 native verifier or an encoding discipline.
-/
abbrev CliqueStructuredBackendMembershipOutcome : Type 1 :=
  Protocol.TrustPolicy Encoding.PresentedProblem
    (PLift (BackendTMInNP GraphAtoms.cliqueStructuredProblem))

/--
Expose the standard checker projection through the backend-membership result
branch. The separately typed native branch carries the stronger exact V2
verifier-plus-discipline capability.
-/
def cliqueStructured_backendMembershipOutcome : CliqueStructuredBackendMembershipOutcome :=
  .accepted ⟨cliqueStructured_backendTMInNP_export⟩

/--
The exact requested native capability for structured Clique.

Its accepted branch is deliberately the full V2 verifier-plus-discipline
capability, rather than backend membership or a bare verifier.  This keeps
the native boundary indexed by the same `GraphAtoms` presentation as the
backend theorem.
-/
abbrev CliqueStructuredNativeMembershipOutcome : Type 2 :=
  Protocol.TrustPolicy Encoding.PresentedProblem
    (NativeVerifierCapability GraphAtoms.cliqueStructuredProblem)

/--
The exact requested backend-completeness capability for structured Clique.

`PLift` is only the universe bridge required to carry CR's proposition-valued
`TMNPCompleteEnc` in the `Type`-valued trusted-outcome protocol.  An accepted
value still contains that exact proof; backend membership cannot inhabit it.
-/
abbrev CliqueStructuredCompletenessOutcome : Type 1 :=
  Protocol.TrustPolicy Encoding.PresentedProblem
    (PLift (ComplexityReduction.TMNPCompleteEnc
      GraphAtoms.cliqueStructuredProblem.toEncodedDecisionProblem))

/--
Completeness has no corresponding V2 completeness proof. The existing typed
diagnostic remains for that independent request and is not used to block the
available native verifier capability.
-/
def cliqueStructured_missingTrustedDirectTM : Protocol.MissingCapability Encoding.PresentedProblem :=
  .directTM GraphAtoms.cliqueStructuredProblem

/--
Native Clique membership is accepted only through the exact standard V2
verifier/checked-decoder capability, never by converting a bare backend theorem.
-/
noncomputable def cliqueStructured_nativeMembershipOutcome : CliqueStructuredNativeMembershipOutcome :=
  .accepted CliqueNativeVerifier.nativeCapability

/--
Structured Clique completeness is independently fail-closed at the same
exact endpoint.  Its accepted branch would require a complete proof, rather
than the weaker backend membership theorem exported above.
-/
def cliqueStructured_completenessOutcome : CliqueStructuredCompletenessOutcome :=
  .blocked cliqueStructured_missingTrustedDirectTM

/-- The native request records precisely the exact Clique endpoint and direct-TM gap. -/
theorem cliqueStructured_missingTrustedDirectTM_exact :
    cliqueStructured_missingTrustedDirectTM.endpoint = GraphAtoms.cliqueStructuredProblem ∧
      cliqueStructured_missingTrustedDirectTM.reason = .directTM :=
  ⟨rfl, rfl⟩

/--
The native/completeness blocker is indexed by Clique's full graph-plus-budget
codec identity, not merely its `CliqueInput` carrier.  A same-carrier codec
therefore needs a separate typed bridge before it can use this diagnostic.
-/
theorem cliqueStructured_missingTrustedDirectTM_representationIdentity :
    cliqueStructured_missingTrustedDirectTM.endpoint.representationIdentity =
      GraphAtoms.cliqueStructuredShape.identity :=
  rfl

/-- The backend result accepts precisely the inherited backend theorem. -/
theorem cliqueStructured_backendMembershipOutcome_exact :
    match cliqueStructured_backendMembershipOutcome with
    | .accepted membership => membership.down = cliqueStructured_backendTMInNP_export
    | .blocked _ => False :=
  rfl

/-- The native Clique request accepts precisely the standard V2 capability. -/
theorem cliqueStructured_nativeMembershipOutcome_exact :
    match cliqueStructured_nativeMembershipOutcome with
    | .accepted capability => capability = CliqueNativeVerifier.nativeCapability
    | .blocked _ => False :=
  rfl

/-- The completeness request has no accepted backend-completeness capability. -/
theorem cliqueStructured_completenessOutcome_exact :
    match cliqueStructured_completenessOutcome with
    | .accepted _ => False
    | .blocked missing =>
        missing = cliqueStructured_missingTrustedDirectTM :=
  rfl

/--
Backend and native membership retain distinct exact result branches: the
former contains the checker projection, while the latter carries its exact V2
verifier-plus-discipline capability.
-/
theorem cliqueStructured_backend_vs_native_outcome_exact :
    match cliqueStructured_backendMembershipOutcome,
        cliqueStructured_nativeMembershipOutcome with
    | .accepted backend, .accepted capability =>
        backend.down = cliqueStructured_backendTMInNP_export ∧
          capability = CliqueNativeVerifier.nativeCapability
    | _, _ => False :=
  ⟨rfl, rfl⟩

/--
Native membership is accepted while backend completeness remains blocked at
the same exact representation-indexed endpoint. These remain distinct
requested capabilities.
-/
theorem cliqueStructured_native_and_completeness_outcomes_exact :
    match cliqueStructured_nativeMembershipOutcome,
        cliqueStructured_completenessOutcome with
    | .accepted capability, .blocked completenessMissing =>
        capability = CliqueNativeVerifier.nativeCapability ∧
        completenessMissing = cliqueStructured_missingTrustedDirectTM ∧
          completenessMissing.endpoint.representationIdentity =
            GraphAtoms.cliqueStructuredShape.identity
    | _, _ => False :=
  ⟨rfl, rfl, rfl⟩

/--
Any future accepted native Clique branch must package one exact V2 verifier
and the discipline indexed by that same verifier. Its backend membership is
then only the safe projection of that packaged verifier; it is not the
inherited backend theorem above and provides no converse admission path.
-/
theorem cliqueStructured_nativeCapability_exactComponents
    (capability : NativeVerifierCapability GraphAtoms.cliqueStructuredProblem) :
    ∃ verifier : CertifiedVerifier GraphAtoms.cliqueStructuredProblem,
      ∃ discipline : CertifiedVerifierEncodingDiscipline verifier,
        capability = NativeVerifierCapability.mk verifier discipline ∧
          capability.toBackendTMInNP = verifier.toBackendTMInNP := by
  rcases capability with ⟨verifier, discipline⟩
  exact ⟨verifier, discipline, rfl, rfl⟩

/--
Every future native Clique capability carries a checked-decoder discipline at
its exact packaged verifier.  The inherited backend theorem and finite legacy
verifier do not occur in this provenance type.
-/
theorem cliqueStructured_nativeCapability_exactDisciplineProvenance
    (capability : NativeVerifierCapability GraphAtoms.cliqueStructuredProblem) :
    ∃ backendDiscipline :
        ComplexityReduction.SAT.TMVerifierEncodingDiscipline
          capability.verifier.toTMVerifier,
      capability.discipline.basis = .checkedDecoder backendDiscipline :=
  NativeVerifierCapability.exactDisciplineProvenance capability

/- Compile-time anchors for the exact backend-only membership boundary. -/
#check cliqueStructured_backendTMInNP_export
#check cliqueStructured_backendTMInNP
#check ComplexityReduction.Karp21.cliqueStructured_TMInNP
#check cliqueStructured_backendMembershipOutcome
#check cliqueStructured_nativeMembershipOutcome
#check cliqueStructured_completenessOutcome
#check cliqueStructured_nativeCapability_exactComponents
#check cliqueStructured_nativeCapability_exactDisciplineProvenance

/- Backend membership cannot manufacture independent backend NP-completeness evidence. -/
/--
error: Type mismatch
  cliqueStructured_backendTMInNP_export
has type
  TMInNP GraphAtoms.cliqueStructuredProblem.toEncodedDecisionProblem
but is expected to have type
  TMNPCompleteEnc GraphAtoms.cliqueStructuredProblem.toEncodedDecisionProblem
-/
#guard_msgs in
example : ComplexityReduction.TMNPCompleteEnc
    GraphAtoms.cliqueStructuredProblem.toEncodedDecisionProblem :=
  cliqueStructured_backendTMInNP_export

/- Backend membership cannot reconstruct even the V2 checker-bearing verifier object. -/
/--
error: Type mismatch
  cliqueStructured_backendTMInNP_export
has type
  TMInNP GraphAtoms.cliqueStructuredProblem.toEncodedDecisionProblem
of sort `Prop` but is expected to have type
  CertifiedVerifier GraphAtoms.cliqueStructuredProblem
of sort `Type 2`
-/
#guard_msgs in
example : CertifiedVerifier GraphAtoms.cliqueStructuredProblem :=
  cliqueStructured_backendTMInNP_export

/- The backend-only result type cannot be substituted for the native result type. -/
/--
error: Type mismatch
  cliqueStructured_backendMembershipOutcome
has type
  CliqueStructuredBackendMembershipOutcome
of sort `Type 1` but is expected to have type
  CliqueStructuredNativeMembershipOutcome
of sort `Type 2`
-/
#guard_msgs in
example : CliqueStructuredNativeMembershipOutcome :=
  cliqueStructured_backendMembershipOutcome

end GraphMembership
end Karp21
end Problems
end ComplexityReduction
