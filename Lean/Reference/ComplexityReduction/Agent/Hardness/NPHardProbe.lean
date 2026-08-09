/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.NPHardResolver
import ComplexityReduction.Agent.Hardness.InputGate
import ComplexityReduction.Registry.HardnessAggregate
import Lean.Elab.Command

/-!
Nonce-bound, read-only probe for the V1 native NP-hardness lane.

All endpoint equality, seed admission, direction checks, and route selection
happen in Lean.  External consumers receive only observational provenance and
a closed typed failure code; they never infer a route direction from pretty
strings.
-/

namespace ComplexityReduction.Agent.Hardness.NPHardProbe

open Lean Elab Command Meta
open Encoding Certificate Registry
open NPHardResolver

private def schemaVersion := "hardness_np_hard_probe_v1"
private def marker := "HARDNESS_NP_HARD"
private def maximumRenderedChars := 2048

private def oneLine (value : String) : String :=
  ((((value.replace "\n" " ").replace "\r" " ").replace "\t" " ").take
    maximumRenderedChars).toString

private def renderEndpoint (endpoint : Expr) : MetaM String := do
  let rendered ← withOptions (fun options => options.setBool `pp.fullNames true)
    (ppExpr (← whnf endpoint))
  return oneLine rendered.pretty

private def endpointNodeId (endpoint : Expr) : MetaM String := do
  let normalized ← whnf endpoint
  return s!"lean-whnf:{normalized.hash}"

private def emit (nonce kind : String) (fields : List String := []) : MetaM Unit :=
  logInfo m!"{marker}\t{schemaVersion}\t{nonce}\t{kind}\t{String.intercalate "\t" fields}"

private def request (problem : PresentedProblem) : Protocol.TypedNPHardRequestV1 where
  problem := problem

private def emitSeeds {environment : Environment} (nonce fingerprint : String)
    (entries : List (ValidatedEntry environment)) : MetaM Unit := do
  for entry in entries do
    match entry.capability with
    | .nativeTMNPHard endpoint =>
        let some problem ← InputGate.canonicalPresentedHandle? entries endpoint
          | continue
        emit nonce "seed" [
          problem.declaration.toString,
          ← endpointNodeId endpoint,
          entry.candidate.toString,
          "native_hardness",
          fingerprint]
    | .nativeTMNPComplete endpoint =>
        let some problem ← InputGate.canonicalPresentedHandle? entries endpoint
          | continue
        emit nonce "seed" [
          problem.declaration.toString,
          ← endpointNodeId endpoint,
          entry.candidate.toString,
          "native_completeness_projection",
          fingerprint]
    | _ => pure ()

private def emitResolved (nonce requestId : String)
    (resolved : ResolvedNPHardRequestV1) : MetaM Unit := do
  let atoms := resolved.atomicRouteProvenance.map fun atom => atom.declaration.toString
  let roles := resolved.atomicRouteProvenance.map fun atom =>
    atom.role?.map toString |>.getD "unannotated"
  let finalCompositionCount := resolved.atomicRouteProvenance.countP fun atom =>
    atom.role? == some .finalComposition
  let uniqueDependencyCount :=
    (resolved.atomicRouteProvenance.map fun atom => atom.declaration).dedup.length
  emit nonce "resolved" [
    requestId,
    resolved.evidenceKind.label,
    resolved.hubDeclaration?.map Name.toString |>.getD "",
    resolved.hardnessDeclaration?.map Name.toString |>.getD "",
    resolved.completenessDeclaration?.map Name.toString |>.getD "",
    String.intercalate "," atoms,
    String.intercalate "," roles,
    toString finalCompositionCount,
    toString uniqueDependencyCount,
    resolved.registryFingerprint,
    "hardness_seed_to_problem"]
  emit nonce "reverse_audit" [requestId, "false", resolved.registryFingerprint]

private def emitFailure (nonce : String) (resolverFailure : NPHardFailureV1) : MetaM Unit := do
  emit nonce "failure" [
    resolverFailure.requestId,
    resolverFailure.code.label,
    String.intercalate "," <| resolverFailure.declarationHandles.map Name.toString,
    resolverFailure.stableGapId?.getD "",
    oneLine resolverFailure.explanation,
    resolverFailure.registryFingerprint]
  emit nonce "reverse_audit" [
    resolverFailure.requestId,
    toString (resolverFailure.code == .wrongDirectionOnly),
    resolverFailure.registryFingerprint]

private def run (environment : Environment) (nonce : String) (problemName : Name) : MetaM Unit := do
  let problem ← match ← InputGate.presented environment problemName with
    | .ok handle => pure handle
    | .error inputFailure =>
        throwError "NP-hardness input rejected: {repr inputFailure}"
  let entries := Registry.exportValidated environment
  let fingerprint := Registry.registryFingerprint entries
  emit nonce "registry" [fingerprint]
  emit nonce "input" [
    problem.declaration.toString,
    ← endpointNodeId problem.term,
    ← renderEndpoint problem.term,
    fingerprint]
  emitSeeds nonce fingerprint entries
  let requestTerm ← mkAppM ``request #[problem.term]
  match ← resolveNPHardRequestV1 environment requestTerm with
  | .ok resolved => emitResolved nonce s!"lean:{requestTerm.hash}" resolved
  | .error resolverFailure => emitFailure nonce resolverFailure

syntax (name := hardnessAgentProbeNPHardV1)
  "#hardness_agent_probe_np_hard_v1 " str ident : command

elab_rules : command
  | `(#hardness_agent_probe_np_hard_v1 $nonce:str $problem:ident) => do
      let problemName ← resolveGlobalConstNoOverload problem
      let environment ← getEnv
      Command.liftTermElabM <| run environment nonce.getString problemName

end ComplexityReduction.Agent.Hardness.NPHardProbe
