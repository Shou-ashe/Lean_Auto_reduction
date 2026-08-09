/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipVertexCover
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.VerifierEncodingDiscipline
import ComplexityReduction.Protocol.TrustPolicy
import ComplexityReduction.Problems.Karp21.GraphAtoms

/-!
Backend direct-TM membership bridge for the canonical structured Vertex-Cover
endpoint.

This leaf reuses CR's exact structured Vertex-Cover `TMInNP` theorem.  It
does not reconstruct a verifier, introduce an encoding discipline, claim
native membership, or export completeness.  The reused proof has inherited
`native_decide` audit dependencies, so this bridge remains backend-only.  The
native-membership and completeness requests below therefore stop at a shared
typed direct-TM missing-capability boundary: a backend proposition cannot be
upgraded into either trusted capability.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace GraphMembershipVertexCover

open Certificate

/--
The existing structured Vertex-Cover membership theorem at exactly the V2
GraphAtoms endpoint.  The declaration-local tag is discovery metadata only;
the elaborated type remains backend direct-TM membership, with its inherited
`native_decide` audit outside native verifier admission.
-/
@[complexity_reduction_ir_typed_verifier]
theorem vertexCoverStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      GraphAtoms.vertexCoverStructuredProblem.toEncodedDecisionProblem := by
  change ComplexityReduction.TMInNP
    ComplexityReduction.Combinatorics.Graph.vertexCoverStructuredDecisionProblem
  exact ComplexityReduction.Karp21.vertexCoverStructured_TMInNP

/-- The presentation-indexed V2 alias for the same Vertex-Cover backend evidence. -/
theorem vertexCoverStructured_backendTMInNP :
    BackendTMInNP GraphAtoms.vertexCoverStructuredProblem :=
  vertexCoverStructured_backendTMInNP_export

/-- The bridge is fixed to CR's exact structured Vertex-Cover backend endpoint. -/
@[simp]
theorem vertexCoverStructured_backendTMInNP_endpoint :
    GraphAtoms.vertexCoverStructuredProblem.toEncodedDecisionProblem =
      ComplexityReduction.Combinatorics.Graph.vertexCoverStructuredDecisionProblem :=
  rfl

/--
The exact backend-only membership request for the structured Vertex-Cover
presentation.

Its accepted branch carries only CR's inherited `TMInNP` proof at the exact
V2 endpoint.  `PLift` is the universe bridge required by the result protocol;
it does not turn backend membership into a V2 verifier or an encoding
discipline.
-/
abbrev VertexCoverStructuredBackendMembershipOutcome : Type 1 :=
  Protocol.TrustPolicy Encoding.PresentedProblem
    (PLift (BackendTMInNP GraphAtoms.vertexCoverStructuredProblem))

/--
Expose the inherited Vertex-Cover theorem only through the backend-membership
result branch.  The separately typed native request below remains blocked,
so this definition provides no backend-to-native conversion.
-/
def vertexCoverStructured_backendMembershipOutcome :
    VertexCoverStructuredBackendMembershipOutcome :=
  .accepted ⟨vertexCoverStructured_backendTMInNP_export⟩

/--
The exact requested native capability for the structured Vertex-Cover
presentation.

The accepted branch is a V2 verifier together with an encoding discipline,
not a backend membership proposition.  Its endpoint is the same canonical
GraphAtoms presentation as the reused theorem above.
-/
abbrev VertexCoverStructuredNativeMembershipOutcome : Type 2 :=
  Protocol.TrustPolicy Encoding.PresentedProblem
    (NativeVerifierCapability GraphAtoms.vertexCoverStructuredProblem)

/--
The exact requested backend-completeness capability for structured
Vertex-Cover.  `PLift` merely bridges CR's proposition-valued completeness
claim into the `Type`-valued outcome; acceptance still requires that exact
proof and cannot be supplied by backend membership.
-/
abbrev VertexCoverStructuredCompletenessOutcome : Type 1 :=
  Protocol.TrustPolicy Encoding.PresentedProblem
    (PLift (ComplexityReduction.TMNPCompleteEnc
      GraphAtoms.vertexCoverStructuredProblem.toEncodedDecisionProblem))

/--
CR currently supplies backend membership but no standard-audited V2
checker/program with a direct-TM compilation for this exact presentation.
Represent that absence at the common typed boundary, without consulting
theorem names or registry metadata.
-/
def vertexCoverStructured_missingTrustedDirectTM :
    Protocol.MissingCapability Encoding.PresentedProblem :=
  .directTM GraphAtoms.vertexCoverStructuredProblem

/--
Native Vertex-Cover membership remains fail-closed until a certified checker,
its encoding discipline, and standard-audited direct-TM evidence are supplied.
The inherited backend `TMInNP` theorem cannot inhabit this accepted branch.
-/
def vertexCoverStructured_nativeMembershipOutcome :
    VertexCoverStructuredNativeMembershipOutcome :=
  .blocked vertexCoverStructured_missingTrustedDirectTM

/--
Completeness remains independently fail-closed at the same exact endpoint.
The weaker backend membership theorem cannot manufacture a completeness proof.
-/
def vertexCoverStructured_completenessOutcome :
    VertexCoverStructuredCompletenessOutcome :=
  .blocked vertexCoverStructured_missingTrustedDirectTM

/-- The missing direct-TM diagnostic retains the exact Vertex-Cover endpoint. -/
theorem vertexCoverStructured_missingTrustedDirectTM_exact :
    vertexCoverStructured_missingTrustedDirectTM.endpoint =
        GraphAtoms.vertexCoverStructuredProblem ∧
      vertexCoverStructured_missingTrustedDirectTM.reason = .directTM :=
  ⟨rfl, rfl⟩

/-- The backend request accepts precisely CR's inherited backend theorem. -/
theorem vertexCoverStructured_backendMembershipOutcome_exact :
    match vertexCoverStructured_backendMembershipOutcome with
    | .accepted membership => membership.down = vertexCoverStructured_backendTMInNP_export
    | .blocked _ => False :=
  rfl

/-- No native verifier/discipline capability is accepted from backend evidence. -/
theorem vertexCoverStructured_nativeMembershipOutcome_exact :
    match vertexCoverStructured_nativeMembershipOutcome with
    | .accepted _ => False
    | .blocked missing =>
        missing = vertexCoverStructured_missingTrustedDirectTM :=
  rfl

/-- No backend-completeness capability is accepted from backend membership. -/
theorem vertexCoverStructured_completenessOutcome_exact :
    match vertexCoverStructured_completenessOutcome with
    | .accepted _ => False
    | .blocked missing =>
        missing = vertexCoverStructured_missingTrustedDirectTM :=
  rfl

/--
Backend and native requests retain distinct result branches at the same
exact Vertex-Cover presentation: backend membership may carry CR's theorem,
whereas native admission remains blocked until a V2 checker/program and
discipline chain exists.
-/
theorem vertexCoverStructured_backend_vs_native_outcome_exact :
    match vertexCoverStructured_backendMembershipOutcome,
        vertexCoverStructured_nativeMembershipOutcome with
    | .accepted backend, .blocked missing =>
        backend.down = vertexCoverStructured_backendTMInNP_export ∧
          missing = vertexCoverStructured_missingTrustedDirectTM
    | _, _ => False :=
  ⟨rfl, rfl⟩

/- Compile-time anchors for the exact backend-only membership boundary. -/
#check vertexCoverStructured_backendTMInNP_export
#check vertexCoverStructured_backendTMInNP
#check ComplexityReduction.Karp21.vertexCoverStructured_TMInNP
#check vertexCoverStructured_backendMembershipOutcome
#check vertexCoverStructured_nativeMembershipOutcome
#check vertexCoverStructured_completenessOutcome

/- Backend membership cannot manufacture independent backend NP-completeness evidence. -/
/--
error: Type mismatch
  vertexCoverStructured_backendTMInNP_export
has type
  TMInNP GraphAtoms.vertexCoverStructuredProblem.toEncodedDecisionProblem
but is expected to have type
  TMNPCompleteEnc GraphAtoms.vertexCoverStructuredProblem.toEncodedDecisionProblem
-/
#guard_msgs in
example : ComplexityReduction.TMNPCompleteEnc
    GraphAtoms.vertexCoverStructuredProblem.toEncodedDecisionProblem :=
  vertexCoverStructured_backendTMInNP_export

/- The backend-only result type cannot be substituted for the native result type. -/
/--
error: Type mismatch
  vertexCoverStructured_backendMembershipOutcome
has type
  VertexCoverStructuredBackendMembershipOutcome
of sort `Type 1` but is expected to have type
  VertexCoverStructuredNativeMembershipOutcome
of sort `Type 2`
-/
#guard_msgs in
example : VertexCoverStructuredNativeMembershipOutcome :=
  vertexCoverStructured_backendMembershipOutcome

end GraphMembershipVertexCover
end Karp21
end Problems
end ComplexityReduction
