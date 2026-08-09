/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Certificate.VerifierEncodingDiscipline
import ComplexityReduction.Certificate.Reduction
import ComplexityReduction.Protocol.MissingCapability

/-!
Minimal typed trust-policy boundary for V2 construction requests.

The generic `TrustPolicy` is only a typed result boundary.  The canonical
`TrustedReductionOutcome` and `TrustedNativeVerifierOutcome` below select its
accepted input types explicitly, so a metadata-shaped value cannot be used as
a trusted route or native verifier capability.
-/

namespace ComplexityReduction
namespace Protocol

universe u v w z

/--
The only outcomes of requesting a V2 construction at this boundary.

`TypedInput` is deliberately a caller-supplied type rather than a metadata field.  Accepting such
an input only records that it reached this typed boundary; it does not validate the input or grant
any trusted capability.  Later shared certificate and registry layers must impose their own
elaborated type checks before an accepted input can be used as an edge.
-/
inductive TrustPolicy (Endpoint : Type u) (TypedInput : Type v) where
  | accepted (input : TypedInput)
  | blocked (missing : MissingCapability Endpoint)

open Encoding Certificate

/-- The singleton endpoint token for one exact requested source/target presentation pair. -/
inductive ReductionEndpoint (source target : PresentedProblem) : Type 2 where
  | exact : ReductionEndpoint source target

/--
A route outcome whose accepted branch contains one canonical certificate at
the exact requested source and target presentations.
-/
abbrev TrustedReductionOutcome (source target : PresentedProblem) : Type 2 :=
  TrustPolicy (ReductionEndpoint source target) (CertifiedReduction source target)

/-- Accept only an already-typed canonical reduction at these exact endpoints. -/
def acceptReduction {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) : TrustedReductionOutcome source target :=
  .accepted reduction

/-- Block one exact source/target pair because automatic presentation evidence is missing. -/
def missingReductionPresentation (source target : PresentedProblem) :
    TrustedReductionOutcome source target :=
  .blocked (MissingCapability.lawfulPresentation .exact)

/-- Block one exact source/target pair because its shared primitive is unavailable. -/
def missingReductionPrimitive (source target : PresentedProblem) :
    TrustedReductionOutcome source target :=
  .blocked (MissingCapability.primitive .exact)

/-- Block one exact source/target pair because its semantic proof is unavailable. -/
def missingReductionSemanticProof (source target : PresentedProblem) :
    TrustedReductionOutcome source target :=
  .blocked (MissingCapability.semanticProof .exact)

/-- Block one exact source/target pair because direct-TM evidence is unavailable. -/
def missingReductionDirectTM (source target : PresentedProblem) :
    TrustedReductionOutcome source target :=
  .blocked (MissingCapability.directTM .exact)

/-- The accepted trusted reduction remains exactly the supplied certificate. -/
theorem acceptReduction_exact {source target : PresentedProblem}
    (reduction : CertifiedReduction source target) :
    match acceptReduction reduction with
    | .accepted accepted => accepted = reduction
    | .blocked _ => False :=
  rfl

/--
The primitive blocker retains the singleton token for the exact requested
endpoints and reason.
-/
theorem missingReductionPrimitive_exact (source target : PresentedProblem) :
    match missingReductionPrimitive source target with
    | .accepted _ => False
    | .blocked missing => missing.endpoint = .exact ∧ missing.reason = .primitive :=
  ⟨rfl, rfl⟩

/--
The direct-TM blocker retains the singleton token for the exact requested
endpoints and reason.
-/
theorem missingReductionDirectTM_exact (source target : PresentedProblem) :
    match missingReductionDirectTM source target with
    | .accepted _ => False
    | .blocked missing => missing.endpoint = .exact ∧ missing.reason = .directTM :=
  ⟨rfl, rfl⟩

/-- A native verifier outcome accepts only a verifier paired with its exact encoding discipline. -/
abbrev TrustedNativeVerifierOutcome (problem : PresentedProblem) : Type 2 :=
  TrustPolicy (CertifiedVerifier problem) (NativeVerifierCapability problem)

/-- Accept one exact native verifier capability, never a bare backend verifier. -/
def acceptNativeVerifier {problem : PresentedProblem}
    (capability : NativeVerifierCapability problem) : TrustedNativeVerifierOutcome problem :=
  .accepted capability

/-- Block one exact backend verifier because its native encoding discipline is missing. -/
def missingNativeVerifierDiscipline {problem : PresentedProblem}
    (verifier : CertifiedVerifier problem) : TrustedNativeVerifierOutcome problem :=
  .blocked (MissingCapability.verifierEncodingDiscipline verifier)

/-- The verifier-discipline blocker retains the exact verifier endpoint and closed reason. -/
theorem missingNativeVerifierDiscipline_exact {problem : PresentedProblem}
    (verifier : CertifiedVerifier problem) :
    match missingNativeVerifierDiscipline verifier with
    | .accepted _ => False
    | .blocked missing =>
        missing.endpoint = verifier ∧ missing.reason = .verifierEncodingDiscipline :=
  ⟨rfl, rfl⟩

/-! ### Fail-closed observation boundary -/

/--
The sole Protocol reification of `MissingCapability.blockedWithObservations`
as a trust-policy result.

The descriptor/policy metadata and legacy evidence are passed only to the
already fail-closed Protocol combinator.  They are never inspected as a
capability and therefore cannot select the `.accepted` branch.
-/
def blockedWithObservationsOutcome {Endpoint : Type u} {Metadata : Type v}
    {LegacyEvidence : Sort w} {Capability : Type z}
    (missing : MissingCapability Endpoint) (metadata : Metadata)
    (legacyEvidence : LegacyEvidence) : TrustPolicy Endpoint Capability :=
  match MissingCapability.blockedWithObservations (Capability := Capability)
      missing metadata legacyEvidence with
  | .error blocked => .blocked blocked
  | .ok capability => .accepted capability

/--
The canonical trust-policy reification retains the exact missing diagnostic;
metadata and legacy observations cannot alter its endpoint or closed reason.
-/
@[simp]
theorem blockedWithObservationsOutcome_eq_blocked {Endpoint : Type u} {Metadata : Type v}
    {LegacyEvidence : Sort w} {Capability : Type z}
    (missing : MissingCapability Endpoint) (metadata : Metadata)
    (legacyEvidence : LegacyEvidence) :
    blockedWithObservationsOutcome (Capability := Capability) missing metadata legacyEvidence =
      .blocked missing :=
  rfl

/--
Public Protocol regression: no descriptor or trust-policy metadata, legacy
evidence, or caller-selected capability type can reinterpret a
`blockedWithObservations` result as a successful trusted capability.
-/
theorem blockedWithObservationsOutcome_no_accepted {Endpoint : Type u} {Metadata : Type v}
    {LegacyEvidence : Sort w} {Capability : Type z}
    (missing : MissingCapability Endpoint) (metadata : Metadata)
    (legacyEvidence : LegacyEvidence) :
    ¬ ∃ capability : Capability,
      blockedWithObservationsOutcome (Capability := Capability) missing metadata legacyEvidence =
        .accepted capability := by
  rintro ⟨capability, equality⟩
  rw [blockedWithObservationsOutcome_eq_blocked] at equality
  cases equality

/- Metadata-shaped values cannot inhabit the accepted branch of a trusted reduction outcome. -/
/--
error: Application type mismatch: The argument
  (true, 0)
has type
  Bool × ℕ
of sort `Type` but is expected to have type
  CertifiedReduction source target
of sort `Type 2` in the application
  TrustPolicy.accepted (true, 0)
-/
#guard_msgs in
example {source target : PresentedProblem} : TrustedReductionOutcome source target :=
  .accepted (true, (0 : Nat))

/- A backend verifier alone cannot inhabit the native-capability accepted branch. -/
/--
error: Application type mismatch: The argument
  verifier
has type
  CertifiedVerifier problem
but is expected to have type
  NativeVerifierCapability problem
in the application
  TrustPolicy.accepted verifier
-/
#guard_msgs in
example {problem : PresentedProblem} (verifier : CertifiedVerifier problem) :
    TrustedNativeVerifierOutcome problem :=
  .accepted verifier

end Protocol
end ComplexityReduction
