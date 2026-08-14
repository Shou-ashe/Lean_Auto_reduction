/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.InputGate
import Lean.Elab.Command

/-!
Typed, read-only theorem discovery for NP-hard proof search.

Entries are selected and unified with Lean `Expr`s.  Rendered strings are only
diagnostic output for the Python search controller; they never establish that
a declaration applies.
-/

namespace ComplexityReduction
namespace Agent
namespace Reduction
namespace TheoremIndex

open Lean Elab Command Meta
open Encoding Certificate

private def schemaVersion := "reduction_theorem_index_v1"
private def marker := "REDUCTION_THEOREM_INDEX"
private def maximumRenderedChars := 4096

private def oneLine (value : String) : String :=
  ((((value.replace "\n" " ").replace "\r" " ").replace "\t" " ").take
    maximumRenderedChars).toString

private def renderExpr (expression : Expr) : MetaM String := do
  let rendered ← withOptions (fun options => options.setBool `pp.fullNames true)
    (ppExpr (← instantiateMVars expression))
  return oneLine rendered.pretty

private def emit (nonce kind : String) (fields : List String := []) : MetaM Unit :=
  logInfo m!"{marker}\t{schemaVersion}\t{nonce}\t{kind}\t{String.intercalate "\t" fields}"

private def nameComponents : Name → List String
  | .anonymous => []
  | .str parent value => nameComponents parent ++ [value]
  | .num parent value => nameComponents parent ++ [toString value]

private def forbiddenComponents : List String :=
  ["Oracles", "Oracle", "Gold", "GoldProofs", "Expected", "HiddenTargets", "Legacy"]

private def allowedPublicName (name : Name) : Bool :=
  !isPrivateName name && !(nameComponents name).any forbiddenComponents.contains

private def declarationModule? (environment : Environment) (declaration : Name) :
    Option Name := do
  let moduleIndex ← environment.getModuleIdxFor? declaration
  environment.header.moduleNames[moduleIndex]?

private def conclusionHead? (type : Expr) : MetaM (Option Name) := do
  forallTelescope type fun _ conclusion => do
    return conclusion.consumeMData.getAppFn.constName?

private def nativeHardnessType (problem : Expr) : MetaM Expr :=
  mkAppM ``NativeTMNPHard #[problem]

private structure Application where
  declaration : Name
  moduleName : Name
  declarationType : Expr
  premises : Array Expr
  result : Expr

private def tryApplication (environment : Environment) (declaration : Name)
    (information : ConstantInfo) (target : Expr) : MetaM (Option Application) := do
  unless allowedPublicName declaration && information.levelParams.isEmpty do
    return none
  let some head ← conclusionHead? information.type | return none
  unless head == ``NativeTMNPHard do
    return none
  let some moduleName := declarationModule? environment declaration | return none
  let state ← saveState
  try
    let theoremTerm ← mkConstWithFreshMVarLevels declaration
    let (arguments, _, conclusion) ← forallMetaTelescope (← inferType theoremTerm)
    unless ← isDefEq (← whnf conclusion) (← whnf target) do
      state.restore
      return none
    let mut premises := #[]
    for argument in arguments do
      let argument ← instantiateMVars argument
      if argument.isMVar then
        match ← argument.mvarId!.getKind with
        | .syntheticOpaque => pure ()
        | _ =>
            let type ← instantiateMVars (← inferType argument)
            premises := premises.push type
    let result ← instantiateMVars (mkAppN theoremTerm arguments)
    return some { declaration, moduleName, declarationType := information.type, premises, result }
  catch _ =>
    state.restore
    return none

private def run (environment : Environment) (nonce : String) (problemName : Name) : MetaM Unit := do
  let problem ← match ← Hardness.InputGate.presented environment problemName with
    | .ok handle => pure handle
    | .error failure => throwError "NP-hard theorem-index input rejected: {repr failure}"
  let target ← nativeHardnessType problem.term
  let mut applications := #[]
  for (declaration, information) in environment.constants.toList do
    if let some application ← tryApplication environment declaration information target then
      applications := applications.push application
  let sortedApplications := applications.qsort fun first second =>
    if first.premises.size == second.premises.size then
      first.declaration.toString < second.declaration.toString
    else
      first.premises.size < second.premises.size
  emit nonce "goal" [problem.declaration.toString, ← renderExpr target,
    toString target.hash, toString sortedApplications.size]
  for application in sortedApplications do
    let applicationType ← inferType application.result
    emit nonce "candidate" [
      application.declaration.toString,
      application.moduleName.toString,
      toString application.premises.size,
      ← renderExpr application.declarationType,
      String.intercalate " || " (← application.premises.toList.mapM renderExpr),
      ← renderExpr applicationType,
      toString applicationType.hash]

syntax (name := reductionProbeNPHardTheorems)
  "#reduction_probe_np_hard_theorems " str ident : command

elab_rules : command
  | `(#reduction_probe_np_hard_theorems $nonce:str $problem:ident) => do
      let problemName ← resolveGlobalConstNoOverload problem
      let environment ← getEnv
      Command.liftTermElabM <| run environment nonce.getString problemName

end TheoremIndex
end Reduction
end Agent
end ComplexityReduction
