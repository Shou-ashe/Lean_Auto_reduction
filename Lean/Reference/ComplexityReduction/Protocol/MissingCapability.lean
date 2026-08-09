/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
Typed blocking protocol for incomplete V2 reductions.

This is the single V2 owner for a missing-capability result.  A domain supplies
its own typed endpoint carrier, while this module supplies the closed set of
capability classes that must be present before a trusted route can be formed.
It deliberately contains no declaration names, strings, executable maps,
certificates, cost evidence, or TM evidence.
-/

namespace ComplexityReduction
namespace Protocol

universe u v w z

/-- A trusted route may be blocked only by one of these typed capability classes. -/
inductive MissingCapabilityReason where
  | lawfulPresentation
  | primitive
  | semanticProof
  | executableRelationContract
  | directTM
  | verifierEncodingDiscipline
  | verifierProgram
  | witnessLawfulPresentation
  | unresolvedFamilyPremise
  | noRegistryPath
  | reductionCapability
  | checkerCombinatorPairList
  | checkerCombinatorUnsupported
  | witnessBound
  | soundnessLemma
  | problemToKnownNP
  | nativeMembership
  | nativeCompleteness
  deriving DecidableEq, Repr

/--
A typed blocking result for one domain-supplied endpoint.

`Endpoint` is a domain type selected by the caller; no endpoint identity is
recovered from metadata or a declaration-name string.  This structure records
only why construction must stop and has no operation that can produce a
certificate, trusted capability, program, cost witness, or TM witness.
-/
structure MissingCapability (Endpoint : Type u) where
  endpoint : Endpoint
  reason : MissingCapabilityReason

namespace MissingCapability

/-- Report that automatic use of this exact endpoint lacks lawful presentation evidence. -/
def lawfulPresentation {Endpoint : Type u} (endpoint : Endpoint) : MissingCapability Endpoint :=
  ⟨endpoint, .lawfulPresentation⟩

/-- Report that this exact endpoint lacks the required shared typed primitive. -/
def primitive {Endpoint : Type u} (endpoint : Endpoint) : MissingCapability Endpoint :=
  ⟨endpoint, .primitive⟩

/-- Report that this exact endpoint lacks the semantic correctness proof required by a route. -/
def semanticProof {Endpoint : Type u} (endpoint : Endpoint) : MissingCapability Endpoint :=
  ⟨endpoint, .semanticProof⟩

/-- Report that this exact endpoint lacks executable rows for its relation semantics. -/
def executableRelationContract {Endpoint : Type u} (endpoint : Endpoint) :
    MissingCapability Endpoint :=
  ⟨endpoint, .executableRelationContract⟩

/-- Report that this exact endpoint lacks direct-TM evidence for its executable construction. -/
def directTM {Endpoint : Type u} (endpoint : Endpoint) : MissingCapability Endpoint :=
  ⟨endpoint, .directTM⟩

/-- Report that this exact verifier endpoint lacks native encoding-discipline evidence. -/
def verifierEncodingDiscipline {Endpoint : Type u} (endpoint : Endpoint) :
    MissingCapability Endpoint :=
  ⟨endpoint, .verifierEncodingDiscipline⟩

/-- Report that an exact verifier request lacks its checker program. -/
def verifierProgram {Endpoint : Type u} (endpoint : Endpoint) : MissingCapability Endpoint :=
  ⟨endpoint, .verifierProgram⟩

/-- Report that an exact verifier request lacks lawful witness-presentation evidence. -/
def witnessLawfulPresentation {Endpoint : Type u} (endpoint : Endpoint) :
    MissingCapability Endpoint :=
  ⟨endpoint, .witnessLawfulPresentation⟩

/-- Report an exact endpoint whose parameterized family premise remains unresolved. -/
def unresolvedFamilyPremise {Endpoint : Type u} (endpoint : Endpoint) : MissingCapability Endpoint :=
  ⟨endpoint, .unresolvedFamilyPremise⟩

/-- Report that no validated registry path exists at this exact endpoint. -/
def noRegistryPath {Endpoint : Type u} (endpoint : Endpoint) : MissingCapability Endpoint :=
  ⟨endpoint, .noRegistryPath⟩

/-- Report that no exact program-indexed reduction capability exists at this endpoint. -/
def reductionCapability {Endpoint : Type u} (endpoint : Endpoint) : MissingCapability Endpoint :=
  ⟨endpoint, .reductionCapability⟩

/-- Report that the pair/list finite-witness checker combinator is required. -/
def checkerCombinatorPairList {Endpoint : Type u} (endpoint : Endpoint) :
    MissingCapability Endpoint :=
  ⟨endpoint, .checkerCombinatorPairList⟩

/-- Report a checker shape outside the admitted finite-witness combinator vocabulary. -/
def checkerCombinatorUnsupported {Endpoint : Type u} (endpoint : Endpoint) :
    MissingCapability Endpoint :=
  ⟨endpoint, .checkerCombinatorUnsupported⟩

/-- Report that the exact verifier task has no polynomial witness bound. -/
def witnessBound {Endpoint : Type u} (endpoint : Endpoint) : MissingCapability Endpoint :=
  ⟨endpoint, .witnessBound⟩

/-- Report that the exact checker task lacks its soundness theorem. -/
def soundnessLemma {Endpoint : Type u} (endpoint : Endpoint) : MissingCapability Endpoint :=
  ⟨endpoint, .soundnessLemma⟩

/-- Report that no admitted bridge from the exact problem to known NP is available. -/
def problemToKnownNP {Endpoint : Type u} (endpoint : Endpoint) : MissingCapability Endpoint :=
  ⟨endpoint, .problemToKnownNP⟩

/-- Report missing V2-native membership for this exact selected target. -/
def nativeMembership {Endpoint : Type u} (endpoint : Endpoint) : MissingCapability Endpoint :=
  ⟨endpoint, .nativeMembership⟩

/-- Report missing V2-native completeness for this exact selected target. -/
def nativeCompleteness {Endpoint : Type u} (endpoint : Endpoint) : MissingCapability Endpoint :=
  ⟨endpoint, .nativeCompleteness⟩

/--
The closed result of an audited request whose required primitive is absent.

This is the only reusable boundary combinator for legacy data that has been
audited as lacking a direct-TM realization.  It deliberately accepts an exact
typed endpoint, but *no* legacy evidence and no executable: a cost bound,
packet, theorem name, readiness bit, or arbitrary proposition cannot be
transformed into the polymorphic `Capability` result.  V2 callers instantiate
`Capability` with their exact `Program.Primitive` or program-atom capability.
-/
def missingPrimitiveResult {Endpoint : Type u} {Capability : Type v} (endpoint : Endpoint) :
    Except (MissingCapability Endpoint) Capability :=
  .error (primitive endpoint)

/--
Keep an already-typed missing diagnostic blocked when a caller also carries
arbitrary descriptor metadata and legacy evidence.

The observation arguments deliberately have no capability-bearing role: this
Protocol-level combinator neither examines them nor has a success constructor.
Consequently a theorem name, readiness bit, legacy witness, or any other
observation cannot upgrade `missing` into the caller-selected trusted
`Capability`.  Higher layers may consume a success only after constructing
their own concrete typed capability; they cannot obtain one through this
fail-closed boundary.
-/
def blockedWithObservations {Endpoint : Type u} {Metadata : Type v}
    {LegacyEvidence : Sort w} {Capability : Type z}
    (missing : MissingCapability Endpoint) (_metadata : Metadata)
    (_legacyEvidence : LegacyEvidence) :
    Except (MissingCapability Endpoint) Capability :=
  .error missing

@[simp]
theorem endpoint_lawfulPresentation {Endpoint : Type u} (endpoint : Endpoint) :
    (lawfulPresentation endpoint).endpoint = endpoint :=
  rfl

@[simp]
theorem endpoint_primitive {Endpoint : Type u} (endpoint : Endpoint) :
    (primitive endpoint).endpoint = endpoint :=
  rfl

@[simp]
theorem endpoint_semanticProof {Endpoint : Type u} (endpoint : Endpoint) :
    (semanticProof endpoint).endpoint = endpoint :=
  rfl

@[simp]
theorem endpoint_executableRelationContract {Endpoint : Type u} (endpoint : Endpoint) :
    (executableRelationContract endpoint).endpoint = endpoint :=
  rfl

@[simp]
theorem endpoint_directTM {Endpoint : Type u} (endpoint : Endpoint) :
    (directTM endpoint).endpoint = endpoint :=
  rfl

@[simp]
theorem endpoint_verifierEncodingDiscipline {Endpoint : Type u} (endpoint : Endpoint) :
    (verifierEncodingDiscipline endpoint).endpoint = endpoint :=
  rfl

@[simp]
theorem endpoint_verifierProgram {Endpoint : Type u} (endpoint : Endpoint) :
    (verifierProgram endpoint).endpoint = endpoint :=
  rfl

@[simp]
theorem endpoint_witnessLawfulPresentation {Endpoint : Type u} (endpoint : Endpoint) :
    (witnessLawfulPresentation endpoint).endpoint = endpoint :=
  rfl

@[simp]
theorem reason_lawfulPresentation {Endpoint : Type u} (endpoint : Endpoint) :
    (lawfulPresentation endpoint).reason = .lawfulPresentation :=
  rfl

@[simp]
theorem reason_primitive {Endpoint : Type u} (endpoint : Endpoint) :
    (primitive endpoint).reason = .primitive :=
  rfl

@[simp]
theorem reason_semanticProof {Endpoint : Type u} (endpoint : Endpoint) :
    (semanticProof endpoint).reason = .semanticProof :=
  rfl

@[simp]
theorem reason_executableRelationContract {Endpoint : Type u} (endpoint : Endpoint) :
    (executableRelationContract endpoint).reason = .executableRelationContract :=
  rfl

@[simp]
theorem reason_directTM {Endpoint : Type u} (endpoint : Endpoint) :
    (directTM endpoint).reason = .directTM :=
  rfl

@[simp]
theorem reason_verifierEncodingDiscipline {Endpoint : Type u} (endpoint : Endpoint) :
    (verifierEncodingDiscipline endpoint).reason = .verifierEncodingDiscipline :=
  rfl

@[simp]
theorem reason_verifierProgram {Endpoint : Type u} (endpoint : Endpoint) :
    (verifierProgram endpoint).reason = .verifierProgram :=
  rfl

@[simp]
theorem reason_witnessLawfulPresentation {Endpoint : Type u} (endpoint : Endpoint) :
    (witnessLawfulPresentation endpoint).reason = .witnessLawfulPresentation :=
  rfl

/-- The reusable absent-primitive boundary retains the caller's exact endpoint. -/
theorem missingPrimitiveResult_endpoint {Endpoint : Type u} {Capability : Type v}
    (endpoint : Endpoint) :
    match missingPrimitiveResult (Capability := Capability) endpoint with
    | .error missing => missing.endpoint = endpoint
    | .ok _ => False :=
  rfl

/-- The reusable absent-primitive boundary always records the closed primitive reason. -/
theorem missingPrimitiveResult_reason {Endpoint : Type u} {Capability : Type v}
    (endpoint : Endpoint) :
    match missingPrimitiveResult (Capability := Capability) endpoint with
    | .error missing => missing.reason = .primitive
    | .ok _ => False :=
  rfl

/-- No capability, trusted or otherwise, can be extracted from this closed result. -/
theorem missingPrimitiveResult_no_success {Endpoint : Type u} {Capability : Type v}
    (endpoint : Endpoint) :
    ¬ ∃ capability, missingPrimitiveResult (Capability := Capability) endpoint = .ok capability := by
  rintro ⟨capability, result⟩
  cases result

/-- Metadata and legacy evidence leave the exact missing diagnostic unchanged. -/
@[simp]
theorem blockedWithObservations_error {Endpoint : Type u} {Metadata : Type v}
    {LegacyEvidence : Sort w} {Capability : Type z}
    (missing : MissingCapability Endpoint) (metadata : Metadata)
    (legacyEvidence : LegacyEvidence) :
    blockedWithObservations (Capability := Capability) missing metadata legacyEvidence = .error missing :=
  rfl

/--
No value carried as descriptor metadata or legacy evidence can produce a
success from the Protocol's blocked aggregate boundary.
-/
theorem blockedWithObservations_no_success {Endpoint : Type u} {Metadata : Type v}
    {LegacyEvidence : Sort w} {Capability : Type z}
    (missing : MissingCapability Endpoint) (metadata : Metadata)
    (legacyEvidence : LegacyEvidence) :
    ¬ ∃ capability,
      blockedWithObservations (Capability := Capability) missing metadata legacyEvidence = .ok capability := by
  rintro ⟨capability, result⟩
  cases result

/--
Aggregate negative invariant: regardless of metadata or legacy evidence, an
already missing typed capability has no Protocol-level upgrade path to a
trusted capability.
-/
theorem no_upgrade_from_metadata_or_legacyEvidence {Endpoint : Type u} {Metadata : Type v}
    {LegacyEvidence : Sort w} {Capability : Type z}
    (missing : MissingCapability Endpoint) :
    ∀ (metadata : Metadata) (legacyEvidence : LegacyEvidence),
      ¬ ∃ capability,
        blockedWithObservations (Capability := Capability) missing metadata legacyEvidence = .ok capability := by
  intro metadata legacyEvidence
  exact blockedWithObservations_no_success missing metadata legacyEvidence

/-- Missing diagnostics are equal only when both their exact endpoints and closed reasons agree. -/
@[ext]
theorem ext {Endpoint : Type u} (left right : MissingCapability Endpoint)
    (endpointEquality : left.endpoint = right.endpoint)
    (reasonEquality : left.reason = right.reason) :
    left = right := by
  cases left
  cases right
  cases endpointEquality
  cases reasonEquality
  rfl

end MissingCapability

end Protocol
end ComplexityReduction
