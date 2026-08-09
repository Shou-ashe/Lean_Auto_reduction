/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Certificate.VerifierAdapter
import ComplexityReduction.Problems.Karp21.ThreeSATNativeVerifier
import ComplexityReduction.Protocol.TrustPolicy

/-!
SAT-family membership boundary for the exact V2 structured-3SAT endpoint.

The only executable evidence reused here is the canonical typed finite-assignment verifier from
`Certificate.VerifierAdapter`.  This leaf fixes its presentation, checker, semantic outcome, and
backend-membership projection at the SAT family endpoint.  The same verifier is returned in a
typed native-capability outcome supplied by the one production checked-decoder endpoint.  Backend
membership remains a separate one-way projection; no legacy metadata, descriptor, or backend
theorem can fill the native-capability branch.
-/

namespace ComplexityReduction
namespace Problems
namespace Karp21
namespace SATMembership

open Certificate

/--
The structured-3SAT adapter endpoint is definitionally the exact canonical satisfiability
presentation selected by this V2 problem family.
-/
@[simp]
theorem threeSATStructured_backendTMInNP_endpoint :
    Certificate.VerifierAdapter.threeSATStructuredProblem =
      Satisfiability.threeSATStructuredProblem :=
  rfl

/--
The SAT family uses the existing checker-backed verifier at exactly its own structured-3SAT
presentation.  This is a family-local alias, not a second checker or verifier construction.
-/
abbrev threeSATStructuredVerifier :
    CertifiedVerifier Satisfiability.threeSATStructuredProblem :=
  Certificate.VerifierAdapter.threeSATStructuredVerifier

/-- The family-local verifier alias is definitionally the one canonical V2 adapter verifier. -/
@[simp]
theorem threeSATStructuredVerifier_exact_adapter :
    threeSATStructuredVerifier = Certificate.VerifierAdapter.threeSATStructuredVerifier :=
  rfl

/-- The verifier keeps the finite Boolean-assignment presentation selected by the SAT family. -/
@[simp]
theorem threeSATStructuredVerifier_witness_exact :
    threeSATStructuredVerifier.witness = Satisfiability.finiteAssignmentPresentation :=
  rfl

/-- The verifier stores exactly the adapter's one checker program. -/
@[simp]
theorem threeSATStructuredVerifier_checker_exact :
    threeSATStructuredVerifier.checker = Certificate.VerifierAdapter.threeSATStructuredChecker :=
  rfl

/--
The SAT membership checker executes the reused finite structured-3SAT checker on the exact
presented input and witness carriers.
-/
@[simp]
theorem threeSATStructuredVerifier_checker_run
    (formula : Satisfiability.threeSATStructuredProblem.Instance)
    (candidate : Satisfiability.finiteAssignmentPresentation.Carrier) :
    threeSATStructuredVerifier.checker.run (formula, candidate) =
      ComplexityReduction.SAT.threeSATStructuredFiniteVerify formula candidate :=
  Certificate.VerifierAdapter.threeSATStructuredChecker_run (formula, candidate)

/--
The SAT membership semantics and verifier outcome are aligned through the exact stored checker
program and its bound; this is the verifier's certified completeness theorem, not a separate
membership predicate or metadata claim.
-/
theorem threeSATStructuredVerifier_accepts_iff_bounded_checker
    (formula : Satisfiability.threeSATStructuredProblem.Instance) :
    Satisfiability.threeSATStructuredProblem.accepts formula ↔
      ∃ candidate, threeSATStructuredVerifier.witness.encodedType.inputSize candidate ≤
          threeSATStructuredVerifier.witnessBound formula ∧
        threeSATStructuredVerifier.checker.run (formula, candidate) = true :=
  threeSATStructuredVerifier.accepts_iff_exists_bounded_checker formula

/--
Registry-export form of the canonical structured-3SAT verifier's backend membership projection.

The elaborated head is the existing `ComplexityReduction.TMInNP`, so the registry can classify it
as backend membership from its type alone.  The verifier attribute is discovery-only and does not
confer native encoding discipline or any stronger capability.
-/
@[complexity_reduction_ir_typed_verifier]
theorem threeSATStructured_backendTMInNP_export :
    ComplexityReduction.TMInNP
      Certificate.VerifierAdapter.threeSATStructuredProblem.toEncodedDecisionProblem :=
  Certificate.VerifierAdapter.threeSATStructuredVerifier_backendTMInNP

/- The SAT family endpoint above identifies this registry export with its exact presentation. -/

/-- The SAT family backend theorem is the one-way projection of its exact stored verifier. -/
@[simp]
theorem threeSATStructured_backendTMInNP_export_eq_verifier_projection :
    threeSATStructured_backendTMInNP_export = threeSATStructuredVerifier.toBackendTMInNP :=
  rfl

/--
Presentation-indexed SAT-family form of the same backend membership evidence.  This one-way
projection remains distinct from the separate native verifier outcome below.
-/
theorem threeSATStructured_backendTMInNP :
    BackendTMInNP Satisfiability.threeSATStructuredProblem :=
  threeSATStructuredVerifier.toBackendTMInNP

/-- The registry-export theorem is exactly the existing verifier's backend projection. -/
@[simp]
theorem threeSATStructured_backendTMInNP_export_eq_projection :
    threeSATStructured_backendTMInNP_export =
      Certificate.VerifierAdapter.threeSATStructuredVerifier.toBackendTMInNP :=
  rfl

/--
The family-local native-verifier outcome is the production checked-decoder
outcome at the exact same structured-3SAT endpoint.  This is an alias only:
the discipline and native capability are owned by `ThreeSATNativeVerifier`.
-/
noncomputable def threeSATStructuredNativeVerifierOutcome :
    Protocol.TrustedNativeVerifierOutcome Satisfiability.threeSATStructuredProblem :=
  ThreeSATNativeVerifier.threeSATStructuredNativeVerifierOutcome

/-- The typed SAT native outcome preserves the exact production native capability. -/
theorem threeSATStructuredNativeVerifierOutcome_exact :
    match threeSATStructuredNativeVerifierOutcome with
    | .accepted capability =>
        capability = ThreeSATNativeVerifier.threeSATStructuredNativeCapability
    | .blocked _ => False :=
  ThreeSATNativeVerifier.threeSATStructuredNativeVerifierOutcome_exact

/-- The family-local spelling is exactly the production checked-decoder outcome. -/
theorem threeSATStructuredNativeVerifierOutcome_exact_adapter_boundary :
    threeSATStructuredNativeVerifierOutcome =
      ThreeSATNativeVerifier.threeSATStructuredNativeVerifierOutcome :=
  rfl

end SATMembership
end Karp21
end Problems
end ComplexityReduction
