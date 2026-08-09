/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipMaxCut
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.VerifierEncodingDiscipline
import ComplexityReduction.Presentation.MaxCut
import ComplexityReduction.Protocol.TrustPolicy

/-!
Backend direct-TM membership bridge for the canonical structured Max Cut
endpoint.

The existing proof is direct backend `TMInNP` evidence at precisely this V2
presentation endpoint.  Its legacy finite-verifier dependency chain contains
`native_decide` (notably in `PackagedMembershipMaxCut`), so this leaf exports
only the backend proposition.  It does not reconstruct a `CertifiedVerifier`,
encoding discipline, V2 `NativeTMInNP`, completeness, or another TM.  Native
membership and completeness therefore stop at the same exact typed direct-TM
missing-capability boundary: a backend proposition cannot be upgraded through
an attribute, theorem name, or other descriptor metadata.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace MaxCutMembership

open Certificate

/--
The existing structured Max Cut direct-TM membership theorem at the exact
canonical V2 endpoint.  The local tag is discovery-only; it cannot upgrade
this backend evidence to a native capability.
-/
@[complexity_reduction_ir_typed_verifier]
theorem maxCutStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.MaxCut.structuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.Graph.maxCutStructuredDecisionProblem
  exact ComplexityReduction.Karp21.maxCutStructured_TMInNP

/-- The presentation-indexed V2 alias for the same backend-only evidence. -/
theorem maxCutStructured_backendTMInNP :
    BackendTMInNP Presentation.MaxCut.structuredProblem :=
  maxCutStructured_backendTMInNP_export

/-- The bridge is fixed to CR's existing structured Max Cut endpoint. -/
@[simp]
theorem maxCutStructured_backendTMInNP_endpoint :
    Presentation.MaxCut.structuredProblem.toEncodedDecisionProblem =
      ComplexityReduction.Combinatorics.Graph.maxCutStructuredDecisionProblem :=
  Presentation.MaxCut.structuredProblem_backendEndpoint_eq_legacy

/--
The exact requested native capability for the canonical structured Max Cut
presentation.

An accepted value contains a V2 verifier together with an encoding discipline
indexed by exactly `Presentation.MaxCut.structuredProblem`; backend `TMInNP`
evidence cannot inhabit that branch.
-/
abbrev MaxCutStructuredNativeMembershipOutcome : Type 2 :=
  Protocol.TrustPolicy Encoding.PresentedProblem
    (NativeVerifierCapability Presentation.MaxCut.structuredProblem)

/--
The exact requested backend-completeness capability for canonical structured
Max Cut.  `PLift` only carries CR's proposition into the type-valued result;
acceptance still requires that exact completeness proof, never membership
evidence alone.
-/
abbrev MaxCutStructuredCompletenessOutcome : Type 1 :=
  Protocol.TrustPolicy Encoding.PresentedProblem
    (PLift (ComplexityReduction.TMNPCompleteEnc
      Presentation.MaxCut.structuredProblem.toEncodedDecisionProblem))

/--
CR currently supplies backend membership but no standard-audited V2
checker/program and direct-TM compilation for this exact presentation.  The
gap is represented at the shared typed endpoint, without deriving authority
from the inherited theorem, its name, or its discovery attribute.
-/
def maxCutStructured_missingTrustedDirectTM :
    Protocol.MissingCapability Encoding.PresentedProblem :=
  .directTM Presentation.MaxCut.structuredProblem

/--
Native Max Cut membership fails closed until an exact V2
verifier-plus-discipline chain with standard-audited direct-TM evidence is
available.  The inherited backend theorem cannot populate the accepted branch.
-/
def maxCutStructured_nativeMembershipOutcome :
    MaxCutStructuredNativeMembershipOutcome :=
  .blocked maxCutStructured_missingTrustedDirectTM

/--
Completeness independently remains fail-closed at the same exact endpoint.
The direct backend membership theorem is strictly weaker than its accepted
proof type.
-/
def maxCutStructured_completenessOutcome :
    MaxCutStructuredCompletenessOutcome :=
  .blocked maxCutStructured_missingTrustedDirectTM

/-- The direct-TM diagnostic retains exactly the Max Cut presentation and reason. -/
theorem maxCutStructured_missingTrustedDirectTM_exact :
    maxCutStructured_missingTrustedDirectTM.endpoint =
        Presentation.MaxCut.structuredProblem ∧
      maxCutStructured_missingTrustedDirectTM.reason = .directTM :=
  ⟨rfl, rfl⟩

/-- Backend evidence cannot enter the V2 native verifier/discipline branch. -/
theorem maxCutStructured_nativeMembershipOutcome_exact :
    match maxCutStructured_nativeMembershipOutcome with
    | .accepted _ => False
    | .blocked missing =>
        missing = maxCutStructured_missingTrustedDirectTM :=
  rfl

/-- Backend evidence cannot enter the independent completeness branch. -/
theorem maxCutStructured_completenessOutcome_exact :
    match maxCutStructured_completenessOutcome with
    | .accepted _ => False
    | .blocked missing =>
        missing = maxCutStructured_missingTrustedDirectTM :=
  rfl

/- Compile-time anchors for the exact backend-only membership boundary. -/
#check maxCutStructured_backendTMInNP_export
#check maxCutStructured_backendTMInNP
#check ComplexityReduction.Karp21.maxCutStructured_TMInNP
#check maxCutStructured_nativeMembershipOutcome
#check maxCutStructured_completenessOutcome

/- A legacy backend theorem cannot manufacture an independent native capability. -/
/--
error: Type mismatch
  maxCutStructured_backendTMInNP_export
has type
  TMInNP Presentation.MaxCut.structuredProblem.toEncodedDecisionProblem
but is expected to have type
  NativeTMInNP Presentation.MaxCut.structuredProblem
-/
#guard_msgs in
example : NativeTMInNP Presentation.MaxCut.structuredProblem :=
  maxCutStructured_backendTMInNP_export

/- Backend membership cannot manufacture independent backend NP-completeness evidence. -/
/--
error: Type mismatch
  maxCutStructured_backendTMInNP_export
has type
  TMInNP Presentation.MaxCut.structuredProblem.toEncodedDecisionProblem
but is expected to have type
  TMNPCompleteEnc Presentation.MaxCut.structuredProblem.toEncodedDecisionProblem
-/
#guard_msgs in
example : ComplexityReduction.TMNPCompleteEnc
    Presentation.MaxCut.structuredProblem.toEncodedDecisionProblem :=
  maxCutStructured_backendTMInNP_export

/-! The inherited `native_decide` lineage remains observable only at the backend boundary. -/
#print axioms maxCutStructured_backendTMInNP_export

end MaxCutMembership
end Karp21
end Problems
end ComplexityReduction
