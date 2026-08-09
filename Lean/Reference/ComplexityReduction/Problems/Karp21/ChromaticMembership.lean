/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipChromaticNumber
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.VerifierEncodingDiscipline
import ComplexityReduction.Presentation.ChromaticNumber
import ComplexityReduction.Protocol.TrustPolicy

/-!
Backend-only direct-TM membership bridge for the canonical structured
Chromatic Number endpoint.

This leaf reuses CR's exact structured Chromatic Number `TMInNP` theorem at
the canonical V2 presentation endpoint.  The reused proof has inherited
`native_decide` dependencies, so it remains backend-only: it neither
constructs a V2 verifier/encoding discipline nor admits native membership or
completeness.  The native and completeness requests below are explicitly
fail-closed on the same exact presented endpoint.  A declaration attribute,
theorem name, or backend `TMInNP` proposition cannot populate either accepted
branch.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace ChromaticMembership

open Certificate

/--
The existing structured Chromatic Number membership theorem at exactly the V2
presentation endpoint.  Its declaration-local tag is discovery metadata only;
the elaborated type remains backend direct-TM membership, with inherited
`native_decide` audit dependencies outside native verifier admission.
-/
@[complexity_reduction_ir_typed_verifier]
theorem chromaticNumberStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Presentation.ChromaticNumber.structuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.Graph.chromaticNumberStructuredDecisionProblem
  exact ComplexityReduction.Karp21.chromaticNumberStructured_TMInNP

/-- The presentation-indexed V2 alias for the same Chromatic Number backend evidence. -/
theorem chromaticNumberStructured_backendTMInNP :
    BackendTMInNP Presentation.ChromaticNumber.structuredProblem :=
  chromaticNumberStructured_backendTMInNP_export

/-- The bridge is fixed to CR's exact structured Chromatic Number backend endpoint. -/
@[simp]
theorem chromaticNumberStructured_backendTMInNP_endpoint :
    Presentation.ChromaticNumber.structuredProblem.toEncodedDecisionProblem =
      ComplexityReduction.Combinatorics.Graph.chromaticNumberStructuredDecisionProblem :=
  rfl

/--
The exact requested native capability for the canonical structured Chromatic
Number presentation.

Its accepted branch contains an exact V2 verifier together with the encoding
discipline indexed by that verifier.  A backend `TMInNP` proposition is not a
value of this capability type, even when its endpoint is definitionally the
same problem.
-/
abbrev ChromaticNumberStructuredNativeMembershipOutcome : Type 2 :=
  Protocol.TrustPolicy Encoding.PresentedProblem
    (NativeVerifierCapability Presentation.ChromaticNumber.structuredProblem)

/--
The exact requested backend-completeness capability for the same structured
Chromatic Number endpoint.  `PLift` only carries CR's proposition-valued
completeness theorem through the `Type`-valued trust protocol; acceptance
still requires that full proof, not mere membership.
-/
abbrev ChromaticNumberStructuredCompletenessOutcome : Type 1 :=
  Protocol.TrustPolicy Encoding.PresentedProblem
    (PLift (ComplexityReduction.TMNPCompleteEnc
      Presentation.ChromaticNumber.structuredProblem.toEncodedDecisionProblem))

/--
No standard-audited V2 checker/program with direct-TM compilation currently
exists for this exact Chromatic Number presentation.  Record the shared gap
at the typed endpoint instead of deriving a capability from legacy metadata
or the inherited backend theorem.
-/
def chromaticNumberStructured_missingTrustedDirectTM :
    Protocol.MissingCapability Encoding.PresentedProblem :=
  .directTM Presentation.ChromaticNumber.structuredProblem

/--
Native Chromatic Number membership remains fail-closed until the exact V2
verifier-plus-discipline chain and standard-audited direct-TM evidence are
supplied.  The inherited backend theorem cannot enter the accepted branch.
-/
def chromaticNumberStructured_nativeMembershipOutcome :
    ChromaticNumberStructuredNativeMembershipOutcome :=
  .blocked chromaticNumberStructured_missingTrustedDirectTM

/--
Completeness independently remains fail-closed at that same exact endpoint.
The backend membership export above is strictly weaker than the accepted
completeness proof type.
-/
def chromaticNumberStructured_completenessOutcome :
    ChromaticNumberStructuredCompletenessOutcome :=
  .blocked chromaticNumberStructured_missingTrustedDirectTM

/-- The typed direct-TM diagnostic retains exactly the Chromatic Number presentation. -/
theorem chromaticNumberStructured_missingTrustedDirectTM_exact :
    chromaticNumberStructured_missingTrustedDirectTM.endpoint =
        Presentation.ChromaticNumber.structuredProblem ∧
      chromaticNumberStructured_missingTrustedDirectTM.reason = .directTM :=
  ⟨rfl, rfl⟩

/-- No legacy backend proof can enter the V2 native verifier/discipline branch. -/
theorem chromaticNumberStructured_nativeMembershipOutcome_exact :
    match chromaticNumberStructured_nativeMembershipOutcome with
    | .accepted _ => False
    | .blocked missing =>
        missing = chromaticNumberStructured_missingTrustedDirectTM :=
  rfl

/-- No legacy backend membership proof can enter the independent completeness branch. -/
theorem chromaticNumberStructured_completenessOutcome_exact :
    match chromaticNumberStructured_completenessOutcome with
    | .accepted _ => False
    | .blocked missing =>
        missing = chromaticNumberStructured_missingTrustedDirectTM :=
  rfl

/- Compile-time anchors for the exact backend-only membership boundary. -/
#check chromaticNumberStructured_backendTMInNP_export
#check chromaticNumberStructured_backendTMInNP
#check ComplexityReduction.Karp21.chromaticNumberStructured_TMInNP
#check chromaticNumberStructured_nativeMembershipOutcome
#check chromaticNumberStructured_completenessOutcome

/- A backend membership theorem cannot manufacture a V2 native capability. -/
/--
error: Type mismatch
  chromaticNumberStructured_backendTMInNP_export
has type
  TMInNP Presentation.ChromaticNumber.structuredProblem.toEncodedDecisionProblem
but is expected to have type
  NativeTMInNP Presentation.ChromaticNumber.structuredProblem
-/
#guard_msgs in
example : NativeTMInNP Presentation.ChromaticNumber.structuredProblem :=
  chromaticNumberStructured_backendTMInNP_export

/- Backend membership cannot manufacture independent backend NP-completeness evidence. -/
/--
error: Type mismatch
  chromaticNumberStructured_backendTMInNP_export
has type
  TMInNP Presentation.ChromaticNumber.structuredProblem.toEncodedDecisionProblem
but is expected to have type
  TMNPCompleteEnc Presentation.ChromaticNumber.structuredProblem.toEncodedDecisionProblem
-/
#guard_msgs in
example : ComplexityReduction.TMNPCompleteEnc
    Presentation.ChromaticNumber.structuredProblem.toEncodedDecisionProblem :=
  chromaticNumberStructured_backendTMInNP_export

end ChromaticMembership
end Karp21
end Problems
end ComplexityReduction
