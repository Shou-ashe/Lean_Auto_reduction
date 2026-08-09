/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.InputGate
import ComplexityReduction.Registry.HardnessAggregate
import Lean.Elab.Command

/-!
Read-only export of exact native hardness-target evidence.

The exporter consumes only declarations admitted by the canonical registry
validator.  Candidate attributes discover names, while the declaration's
elaborated type determines whether it is exact native membership or exact
native completeness.  Backend membership/completeness heads are deliberately
ignored.

This first catalog version exports registered evidence only.  Transported
hardness and completeness remain a later, explicitly queried capability so
the catalog does not reveal auxiliary reduction paths.
-/

namespace ComplexityReduction.Agent.Hardness.TargetCatalog

open Lean Elab Command Meta
open Encoding Certificate Registry

private def schemaVersion := "hardness_target_catalog_v1"
private def marker := "HARDNESS_AGENT"
private def maximumRenderedChars := 2048
private def validationSource := "lean_registry_elaborated_type"

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

private def controlledDefEq (first second : Expr) : MetaM Bool := do
  isDefEq (← whnf first) (← whnf second)

private def declarationNamespace : Name → Name
  | .anonymous => .anonymous
  | .str parent _ => parent
  | .num parent _ => parent

private def emit (nonce kind : String) (fields : List String := []) : MetaM Unit :=
  logInfo m!"{marker}\t{schemaVersion}\t{nonce}\t{kind}\t{String.intercalate "\t" fields}"

private def emitTarget (nonce fingerprint : String) (target : InputGate.PresentedHandle)
    (endpoint : Expr) : MetaM Unit := do
  emit nonce "target" [
    target.declaration.toString,
    ← renderEndpoint endpoint,
    ← endpointNodeId endpoint,
    (declarationNamespace target.declaration).toString,
    fingerprint]

private def emitNativeMembershipEvidence (nonce fingerprint : String)
    (target : InputGate.PresentedHandle) (endpoint : Expr) (evidenceDeclaration : Name) :
    MetaM Unit := do
  let declaration := evidenceDeclaration.toString
  emit nonce "evidence" [
    target.declaration.toString,
    ← endpointNodeId endpoint,
    "native_membership",
    declaration,
    declaration,
    declaration,
    "native_np",
    validationSource,
    declaration,
    fingerprint]

private def emitNativeCompletenessEvidence (nonce fingerprint : String)
    (target : InputGate.PresentedHandle) (endpoint : Expr) (evidenceDeclaration : Name) :
    MetaM Unit := do
  let declaration := evidenceDeclaration.toString
  let membershipProjection :=
    ``ComplexityReduction.Certificate.NativeTMNPComplete.nativeMembership
  let membershipProjectionName := membershipProjection.toString
  let membershipTerm := s!"{membershipProjectionName} {declaration}"
  emit nonce "evidence" [
    target.declaration.toString,
    ← endpointNodeId endpoint,
    "native_completeness",
    declaration,
    declaration,
    membershipTerm,
    "native_np,native_np_hard,native_np_complete",
    validationSource,
    String.intercalate "," [declaration, membershipProjectionName],
    fingerprint]

private def targetAlreadyEmitted (emitted : List Expr) (endpoint : Expr) : MetaM Bool :=
  emitted.anyM fun previous => controlledDefEq previous endpoint

private def emitTargetOnce (nonce fingerprint : String)
    (emitted : List Expr) (target : InputGate.PresentedHandle) (endpoint : Expr) :
    MetaM (List Expr) := do
  if ← targetAlreadyEmitted emitted endpoint then
    return emitted
  emitTarget nonce fingerprint target endpoint
  return endpoint :: emitted

private def run (environment : Environment) (nonce : String) : MetaM Unit := do
  let entries := exportValidated environment
  let fingerprint := Registry.registryFingerprint entries
  emit nonce "registry" [fingerprint]
  let mut emittedTargets : List Expr := []
  for entry in entries do
    match entry.capability with
    | .nativeTMInNP endpoint =>
        let some target ← InputGate.canonicalPresentedHandle? entries endpoint
          | continue
        emittedTargets ← emitTargetOnce nonce fingerprint emittedTargets target endpoint
        emitNativeMembershipEvidence nonce fingerprint target endpoint entry.candidate
    | .nativeTMNPComplete endpoint =>
        let some target ← InputGate.canonicalPresentedHandle? entries endpoint
          | continue
        emittedTargets ← emitTargetOnce nonce fingerprint emittedTargets target endpoint
        emitNativeCompletenessEvidence nonce fingerprint target endpoint entry.candidate
    | _ => pure ()

syntax (name := hardnessExportTargetCatalog) "#hardness_export_target_catalog " str : command

elab_rules : command
  | `(#hardness_export_target_catalog $nonce:str) => do
      let environment ← getEnv
      Command.liftTermElabM <| run environment nonce.getString

end ComplexityReduction.Agent.Hardness.TargetCatalog
