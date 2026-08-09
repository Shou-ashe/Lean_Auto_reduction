/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Benchmark.Hardness.Inputs.Completeness.BackendCompletenessOnly
import Benchmark.Hardness.Inputs.Completeness.MissingTargetMembership
import Benchmark.Hardness.Inputs.Completeness.RegisteredThreeSAT
import Benchmark.Hardness.Inputs.Completeness.TransportedClique
import Benchmark.Hardness.Inputs.Completeness.WrongDirection
import Benchmark.Hardness.Inputs.Membership.RegisteredThreeSAT
import ComplexityReduction.AxiomGate
import ComplexityReduction.Protocol.ClosedResolver
import ComplexityReduction.Registry.Aggregate
import Lean.Elab.Command

/-!
Phase-6 regressions for the exact membership and native-completeness lanes.

The meta-level checks exercise the same closed resolver used by the probe.  The
term-level artifacts separately exercise request indexing, forward completeness
transport, and the final completeness axiom gate.
-/

namespace ComplexityReduction.Agent.Hardness.Regression.Phase6

open Lean Elab Command Meta
open Encoding Certificate Protocol

private def exactPolicy : AutoReductionTrustPolicy :=
  { presentation := .exactUser, requireNativeNP := true }

def inNPRequest (problem : PresentedProblem) : TypedAutoReductionRequest where
  source := .fromPresented problem
  policy := exactPolicy
  objective := .proveInNP problem

def npCompleteRequest (problem : PresentedProblem) : TypedAutoReductionRequest where
  source := .fromPresented problem
  policy := exactPolicy
  objective := .proveNPComplete problem

private def resolveRequest (environment : Environment) (constructor problem : Name) :
    TermElabM (Except ClosedResolver.Failure ClosedResolver.ResolvedExactRequest) := do
  let request ← mkAppM constructor #[mkConst problem]
  ClosedResolver.resolveExactRequestDetailed environment request

private def controlledDefEq (left right : Expr) : MetaM Bool := do
  isDefEq (← whnf left) (← whnf right)

run_cmd do
  let environment ← getEnv
  Command.liftTermElabM do
    match ← resolveRequest environment ``inNPRequest
        ``Benchmark.Hardness.Inputs.Membership.RegisteredThreeSAT.source with
    | .ok resolved =>
        unless resolved.evidenceKind == .nativeMembership do
          throwError "registered membership returned {repr resolved.evidenceKind}"
        unless resolved.path?.isNone do
          throwError "registered membership unexpectedly returned a reduction path"
        unless resolved.membershipDeclaration? == some
            ``ComplexityReduction.Problems.Karp21.ThreeSATNativeVerifier.threeSATStructuredNativeTMInNP do
          throwError "registered membership returned the wrong declaration"
    | .error failure =>
        throwError "registered membership resolution failed: {repr failure}"

    match ← resolveRequest environment ``npCompleteRequest
        ``Benchmark.Hardness.Inputs.Completeness.RegisteredThreeSAT.source with
    | .ok resolved =>
        unless resolved.evidenceKind == .registeredCompleteness do
          throwError "registered completeness returned {repr resolved.evidenceKind}"
        unless resolved.path?.isNone do
          throwError "registered completeness unexpectedly returned a reduction path"
        unless resolved.completenessDeclaration? == some
            ``Certificate.NativeCookLevin.canonicalThreeSATNativeCompleteness do
          throwError "registered completeness returned the wrong declaration"
    | .error failure =>
        throwError "registered completeness resolution failed: {repr failure}"

    match ← resolveRequest environment ``npCompleteRequest
        ``Benchmark.Hardness.Inputs.Completeness.TransportedClique.source with
    | .ok resolved =>
        unless resolved.evidenceKind == .transportedCompleteness do
          throwError "transported completeness returned {repr resolved.evidenceKind}"
        let some path := resolved.path?
          | throwError "transported completeness omitted its forward path"
        unless path.atoms.length == 1 do
          throwError "transported completeness used {path.atoms.length} atoms"
        let some provenance := path.atomicProvenance.head?
          | throwError "transported completeness omitted atomic provenance"
        unless provenance.declaration == ``Routes.ThreeSATToClique.sharedGadget do
          throwError "transported completeness selected {provenance.declaration}"
        unless provenance.role? == some .sharedGadget do
          throwError "transported completeness selected the wrong component role"
        unless resolved.membershipDeclaration? == some
            ``Problems.Karp21.CliqueNativeVerifier.nativeTMInNP do
          throwError "transported completeness returned the wrong target membership"
        unless resolved.completenessDeclaration? == some
            ``Certificate.NativeCookLevin.canonicalThreeSATNativeCompleteness do
          throwError "transported completeness returned the wrong hub certificate"
        let some hub := resolved.hub?
          | throwError "transported completeness omitted its hub"
        unless ← controlledDefEq hub
            (mkConst ``Problems.Karp21.Satisfiability.threeSATStructuredProblem) do
          throwError "transported completeness returned the wrong hub endpoint"
    | .error failure =>
        throwError "transported completeness resolution failed: {repr failure}"

    match ← resolveRequest environment ``npCompleteRequest
        ``Benchmark.Hardness.Inputs.Completeness.MissingTargetMembership.source with
    | .error (.missingNativeMembership _) => pure ()
    | .error failure =>
        throwError "missing-target-membership returned the wrong failure: {repr failure}"
    | .ok _ => throwError "completeness transport passed without target membership"

    match ← resolveRequest environment ``npCompleteRequest
        ``Benchmark.Hardness.Inputs.Completeness.WrongDirection.source with
    | .error (.missingNativeCompleteness _) => pure ()
    | .error failure =>
        throwError "wrong-direction route returned the wrong failure: {repr failure}"
    | .ok _ => throwError "target-to-hub route was accepted as completeness transport"

    let backendDeclaration :=
      ``Benchmark.Hardness.Inputs.Completeness.BackendCompletenessOnly.backendCompleteness
    match Registry.validateAttributedDeclaration environment backendDeclaration with
    | some entry =>
        match entry.capability with
        | .backendTMNPComplete _ => pure ()
        | capability =>
            throwError "backend completeness was reclassified as {repr capability}"
    | none => throwError "attributed backend completeness was not validated"
    match ← resolveRequest environment ``npCompleteRequest
        ``Benchmark.Hardness.Inputs.Completeness.BackendCompletenessOnly.source with
    | .error (.missingNativeCompleteness _) => pure ()
    | .error failure =>
        throwError "backend completeness returned the wrong failure: {repr failure}"
    | .ok _ => throwError "backend completeness passed the native completeness lane"

noncomputable def registeredMembershipResult :
    TypedAutoReductionResult
      (inNPRequest Benchmark.Hardness.Inputs.Membership.RegisteredThreeSAT.source) :=
  TypedAutoReductionResult.proveInNP exactPolicy rfl
    Problems.Karp21.ThreeSATNativeVerifier.threeSATStructuredNativeTMInNP

noncomputable def registeredCompletenessResult :
    TypedAutoReductionResult
      (npCompleteRequest Benchmark.Hardness.Inputs.Completeness.RegisteredThreeSAT.source) :=
  TypedAutoReductionResult.proveNPComplete exactPolicy rfl
    Certificate.NativeCookLevin.canonicalThreeSATNativeCompleteness

noncomputable def cliqueCompleteness :
    NativeTMNPComplete Benchmark.Hardness.Inputs.Completeness.TransportedClique.source :=
  CompletenessTransport.alongPath
    Certificate.NativeCookLevin.canonicalThreeSATNativeCompleteness
    (CertifiedPath.step Routes.ThreeSATToClique.sharedGadget)
    Problems.Karp21.CliqueNativeVerifier.nativeTMInNP

noncomputable def transportedCompletenessResult :
    TypedAutoReductionResult
      (npCompleteRequest Benchmark.Hardness.Inputs.Completeness.TransportedClique.source) :=
  TypedAutoReductionResult.proveNPComplete exactPolicy rfl cliqueCompleteness

axiom poisonedNativeCompleteness :
  NativeTMNPComplete Benchmark.Hardness.Inputs.Completeness.RegisteredThreeSAT.source

noncomputable def poisonedCompletenessResult :
    TypedAutoReductionResult
      (npCompleteRequest Benchmark.Hardness.Inputs.Completeness.RegisteredThreeSAT.source) :=
  TypedAutoReductionResult.proveNPComplete exactPolicy rfl poisonedNativeCompleteness

noncomputable def poisonedCompletenessArtifact :
    NativeTMNPComplete Benchmark.Hardness.Inputs.Completeness.RegisteredThreeSAT.source :=
  TypedAutoReductionResult.extractNativeCompleteness poisonedCompletenessResult

/--
error: axiom gate rejected ComplexityReduction.Agent.Hardness.Regression.Phase6.poisonedCompletenessArtifact: forbidden axiom ComplexityReduction.Agent.Hardness.Regression.Phase6.poisonedNativeCompleteness
-/
#guard_msgs in
assert_standard_axioms poisonedCompletenessArtifact

end ComplexityReduction.Agent.Hardness.Regression.Phase6

assert_standard_axioms
  ComplexityReduction.Agent.Hardness.Regression.Phase6.registeredMembershipResult,
  ComplexityReduction.Agent.Hardness.Regression.Phase6.registeredCompletenessResult,
  ComplexityReduction.Agent.Hardness.Regression.Phase6.cliqueCompleteness,
  ComplexityReduction.Agent.Hardness.Regression.Phase6.transportedCompletenessResult
