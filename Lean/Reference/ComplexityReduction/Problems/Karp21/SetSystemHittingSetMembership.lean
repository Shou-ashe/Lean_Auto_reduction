/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetSystem
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.VerifierEncodingDiscipline
import ComplexityReduction.Presentation.SetSystem
import ComplexityReduction.Protocol.TrustPolicy

/-!
Backend direct-TM membership bridge for the canonical structured Hitting Set
endpoint.

The reused legacy proof is backend `TMInNP` evidence at precisely this
presentation endpoint.  It currently depends on `native_decide`, so this leaf
deliberately exports neither a `CertifiedVerifier` nor a V2 native encoding
discipline or `NativeTMInNP` capability.  Native and completeness requests
therefore close over an exact typed direct-TM blocker: the legacy backend
theorem cannot be upgraded through its attribute, theorem name, or any other
metadata.  The declaration attribute is discovery-only; registry
classification validates the elaborated theorem type.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace SetSystemHittingSetMembership

open Certificate

/--
The existing structured Hitting Set direct-TM membership theorem at the exact
canonical V2 SetSystem endpoint.  This is backend direct-TM membership only.
-/
@[complexity_reduction_ir_typed_verifier]
theorem hittingSetStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.SetSystem.hittingSetStructuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.hittingSetStructuredDecisionProblem
  exact ComplexityReduction.Karp21.hittingSetStructured_TMInNP

/-- The presentation-indexed V2 alias for the same backend-only evidence. -/
theorem hittingSetStructured_backendTMInNP :
    BackendTMInNP Presentation.SetSystem.hittingSetStructuredProblem :=
  hittingSetStructured_backendTMInNP_export

/-- The bridge is fixed to CR's existing structured Hitting Set endpoint. -/
@[simp]
theorem hittingSetStructured_backendTMInNP_endpoint :
    Presentation.SetSystem.hittingSetStructuredProblem.toEncodedDecisionProblem =
      ComplexityReduction.Combinatorics.hittingSetStructuredDecisionProblem :=
  Presentation.SetSystem.hittingSetStructuredProblem_backendEndpoint_eq_legacy

/--
The exact requested native capability for canonical structured Hitting Set.

An accepted result contains both a V2 verifier and an encoding discipline
indexed by precisely `hittingSetStructuredProblem`; a backend `TMInNP`
proposition cannot inhabit this branch.
-/
abbrev HittingSetStructuredNativeMembershipOutcome : Type 2 :=
  Protocol.TrustPolicy Encoding.PresentedProblem
    (NativeVerifierCapability Presentation.SetSystem.hittingSetStructuredProblem)

/--
The exact requested backend-completeness capability for canonical structured
Hitting Set.  `PLift` is solely the universe bridge around CR's proposition;
acceptance still requires that exact completeness proof, not backend
membership.
-/
abbrev HittingSetStructuredCompletenessOutcome : Type 1 :=
  Protocol.TrustPolicy Encoding.PresentedProblem
    (PLift (ComplexityReduction.TMNPCompleteEnc
      Presentation.SetSystem.hittingSetStructuredProblem.toEncodedDecisionProblem))

/--
No standard-audited V2 checker/program and direct-TM compilation is available
at this exact structured Hitting Set endpoint.  This diagnostic is typed by
that presentation, rather than by an inherited theorem name or descriptor.
-/
def hittingSetStructured_missingTrustedDirectTM :
    Protocol.MissingCapability Encoding.PresentedProblem :=
  .directTM Presentation.SetSystem.hittingSetStructuredProblem

/--
Native Hitting Set membership fails closed until an exact V2
verifier-plus-discipline chain is supplied.  The inherited backend theorem
cannot populate the accepted branch.
-/
def hittingSetStructured_nativeMembershipOutcome :
    HittingSetStructuredNativeMembershipOutcome :=
  .blocked hittingSetStructured_missingTrustedDirectTM

/--
Backend completeness independently remains closed at the exact same endpoint.
The direct backend membership export above is strictly weaker than its
accepted proof type.
-/
def hittingSetStructured_completenessOutcome :
    HittingSetStructuredCompletenessOutcome :=
  .blocked hittingSetStructured_missingTrustedDirectTM

/-- The native blocker retains exactly the Hitting Set presentation and direct-TM reason. -/
theorem hittingSetStructured_missingTrustedDirectTM_exact :
    hittingSetStructured_missingTrustedDirectTM.endpoint =
        Presentation.SetSystem.hittingSetStructuredProblem ∧
      hittingSetStructured_missingTrustedDirectTM.reason = .directTM :=
  ⟨rfl, rfl⟩

/-- No legacy backend proof can enter the V2 native verifier/discipline branch. -/
theorem hittingSetStructured_nativeMembershipOutcome_exact :
    match hittingSetStructured_nativeMembershipOutcome with
    | .accepted _ => False
    | .blocked missing =>
        missing = hittingSetStructured_missingTrustedDirectTM :=
  rfl

/-- No legacy backend proof can enter the independent completeness branch. -/
theorem hittingSetStructured_completenessOutcome_exact :
    match hittingSetStructured_completenessOutcome with
    | .accepted _ => False
    | .blocked missing =>
        missing = hittingSetStructured_missingTrustedDirectTM :=
  rfl

/- Compile-time anchors for the exact backend-only membership boundary. -/
#check hittingSetStructured_backendTMInNP_export
#check hittingSetStructured_backendTMInNP
#check ComplexityReduction.Karp21.hittingSetStructured_TMInNP
#check hittingSetStructured_nativeMembershipOutcome
#check hittingSetStructured_completenessOutcome

/- A legacy backend theorem cannot manufacture an independent native capability. -/
/--
error: Type mismatch
  hittingSetStructured_backendTMInNP_export
has type
  TMInNP Presentation.SetSystem.hittingSetStructuredProblem.toEncodedDecisionProblem
but is expected to have type
  NativeTMInNP Presentation.SetSystem.hittingSetStructuredProblem
-/
#guard_msgs in
example : NativeTMInNP Presentation.SetSystem.hittingSetStructuredProblem :=
  hittingSetStructured_backendTMInNP_export

/- Backend membership cannot manufacture independent backend NP-completeness evidence. -/
/--
error: Type mismatch
  hittingSetStructured_backendTMInNP_export
has type
  TMInNP Presentation.SetSystem.hittingSetStructuredProblem.toEncodedDecisionProblem
but is expected to have type
  TMNPCompleteEnc Presentation.SetSystem.hittingSetStructuredProblem.toEncodedDecisionProblem
-/
#guard_msgs in
example : ComplexityReduction.TMNPCompleteEnc
    Presentation.SetSystem.hittingSetStructuredProblem.toEncodedDecisionProblem :=
  hittingSetStructured_backendTMInNP_export

end SetSystemHittingSetMembership
end Karp21
end Problems
end ComplexityReduction
