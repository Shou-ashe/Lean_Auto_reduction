/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSteinerTree
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.VerifierEncodingDiscipline
import ComplexityReduction.Presentation.SteinerTree
import ComplexityReduction.Protocol.TrustPolicy

/-!
Backend-only direct-TM membership bridge for the canonical structured Steiner
Tree endpoint.

The V2 presentation is definitionally CR's faithful structured Steiner Tree
decision problem.  This leaf exposes CR's existing backend `TMInNP` theorem at
that exact endpoint, but deliberately does not reconstruct a V2 verifier or
encoding discipline.  In particular, any inherited `native_decide` dependency
is recorded by the proof audit as backend-only evidence and cannot promote this
declaration to native membership, a reduction, or completeness.  Native and
completeness requests therefore stop at an exact typed direct-TM blocker: the
legacy theorem's name, attribute, or backend elaborated type cannot create a
trusted verifier-plus-discipline capability.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace SteinerTreeMembership

open Certificate

/--
The existing structured Steiner Tree direct-TM membership theorem at exactly
the canonical V2 presentation endpoint.  The attribute is discovery metadata
only; its elaborated type remains backend membership.
-/
@[complexity_reduction_ir_typed_verifier]
theorem steinerTreeStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.SteinerTree.structuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.Graph.steinerTreeStructuredDecisionProblem
  exact ComplexityReduction.Karp21.SteinerTreeMembership.steinerTreeStructured_TMInNP

/-- The presentation-indexed V2 alias for the same exact backend evidence. -/
theorem steinerTreeStructured_backendTMInNP :
    BackendTMInNP Presentation.SteinerTree.structuredProblem :=
  steinerTreeStructured_backendTMInNP_export

/-- The bridge is fixed to CR's established structured Steiner Tree endpoint. -/
@[simp]
theorem steinerTreeStructured_backendTMInNP_endpoint :
    Presentation.SteinerTree.structuredProblem.toEncodedDecisionProblem =
      ComplexityReduction.Combinatorics.Graph.steinerTreeStructuredDecisionProblem :=
  Presentation.SteinerTree.structuredProblem_backendEndpoint_eq_legacy

/--
The exact requested native capability for the canonical structured Steiner
Tree presentation.

Its accepted branch stores both a V2 verifier and the encoding discipline
indexed by that verifier.  A backend `TMInNP` proposition cannot inhabit this
branch, even when it has the same problem endpoint.
-/
abbrev SteinerTreeStructuredNativeMembershipOutcome : Type 2 :=
  Protocol.TrustPolicy Encoding.PresentedProblem
    (NativeVerifierCapability Presentation.SteinerTree.structuredProblem)

/--
The exact requested backend-completeness capability for structured Steiner
Tree.  `PLift` only carries CR's proposition in the type-valued outcome; an
accepted value still requires the full completeness theorem, not membership.
-/
abbrev SteinerTreeStructuredCompletenessOutcome : Type 1 :=
  Protocol.TrustPolicy Encoding.PresentedProblem
    (PLift (ComplexityReduction.TMNPCompleteEnc
      Presentation.SteinerTree.structuredProblem.toEncodedDecisionProblem))

/--
CR supplies backend membership, but no standard-audited V2 checker/program
with direct-TM compilation for this exact presentation.  Record that gap at
the shared typed endpoint instead of deriving any capability from metadata or
the inherited backend theorem.
-/
def steinerTreeStructured_missingTrustedDirectTM :
    Protocol.MissingCapability Encoding.PresentedProblem :=
  .directTM Presentation.SteinerTree.structuredProblem

/--
Native Steiner Tree membership fails closed until an exact V2
verifier-plus-discipline chain with standard-audited direct-TM evidence exists.
The inherited backend theorem cannot populate the accepted branch.
-/
def steinerTreeStructured_nativeMembershipOutcome :
    SteinerTreeStructuredNativeMembershipOutcome :=
  .blocked steinerTreeStructured_missingTrustedDirectTM

/--
Completeness independently remains fail-closed at the same exact endpoint.
The backend membership export is strictly weaker than the accepted proof type.
-/
def steinerTreeStructured_completenessOutcome :
    SteinerTreeStructuredCompletenessOutcome :=
  .blocked steinerTreeStructured_missingTrustedDirectTM

/-- The missing diagnostic retains exactly the Steiner Tree presentation and direct-TM reason. -/
theorem steinerTreeStructured_missingTrustedDirectTM_exact :
    steinerTreeStructured_missingTrustedDirectTM.endpoint =
        Presentation.SteinerTree.structuredProblem ∧
      steinerTreeStructured_missingTrustedDirectTM.reason = .directTM :=
  ⟨rfl, rfl⟩

/-- No backend membership proof can enter the native verifier/discipline branch. -/
theorem steinerTreeStructured_nativeMembershipOutcome_exact :
    match steinerTreeStructured_nativeMembershipOutcome with
    | .accepted _ => False
    | .blocked missing =>
        missing = steinerTreeStructured_missingTrustedDirectTM :=
  rfl

/-- No backend membership proof can enter the independent completeness branch. -/
theorem steinerTreeStructured_completenessOutcome_exact :
    match steinerTreeStructured_completenessOutcome with
    | .accepted _ => False
    | .blocked missing =>
        missing = steinerTreeStructured_missingTrustedDirectTM :=
  rfl

/- Compile-time anchors for the exact backend-only membership boundary. -/
#check steinerTreeStructured_backendTMInNP_export
#check steinerTreeStructured_backendTMInNP
#check ComplexityReduction.Karp21.SteinerTreeMembership.steinerTreeStructured_TMInNP
#check steinerTreeStructured_nativeMembershipOutcome
#check steinerTreeStructured_completenessOutcome

/- A legacy backend theorem cannot manufacture an independent native capability. -/
/--
error: Type mismatch
  steinerTreeStructured_backendTMInNP_export
has type
  TMInNP Presentation.SteinerTree.structuredProblem.toEncodedDecisionProblem
but is expected to have type
  NativeTMInNP Presentation.SteinerTree.structuredProblem
-/
#guard_msgs in
example : NativeTMInNP Presentation.SteinerTree.structuredProblem :=
  steinerTreeStructured_backendTMInNP_export

/- Backend membership cannot manufacture independent backend NP-completeness evidence. -/
/--
error: Type mismatch
  steinerTreeStructured_backendTMInNP_export
has type
  TMInNP Presentation.SteinerTree.structuredProblem.toEncodedDecisionProblem
but is expected to have type
  TMNPCompleteEnc Presentation.SteinerTree.structuredProblem.toEncodedDecisionProblem
-/
#guard_msgs in
example : ComplexityReduction.TMNPCompleteEnc
    Presentation.SteinerTree.structuredProblem.toEncodedDecisionProblem :=
  steinerTreeStructured_backendTMInNP_export

/-! The following audit intentionally leaves inherited non-standard dependencies
at the backend boundary; this leaf exports no V2 native capability. -/
#print axioms steinerTreeStructured_backendTMInNP_export

end SteinerTreeMembership
end Karp21
end Problems
end ComplexityReduction
