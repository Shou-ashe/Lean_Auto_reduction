/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.GenerativeReduction.GoalProbe
import ComplexityReduction.Certificate.CompletenessTransport
import ComplexityReduction.Certificate.Equiv
import ComplexityReduction.Certificate.PresentationChange
import Lean.Elab.Command

/-!
Typed theorem/constructor discovery for the general NP-hard proof frontier.

Textual module recall is non-authoritative.  Every emitted entry was imported,
instantiated with fresh universe metavariables, and unified with the exact root
goal by Lean.  Open premises remain explicit and cannot grant proof authority.
-/

namespace ComplexityReduction.Agent.GenerativeReduction.TheoremIndex

open Lean Elab Command Meta Term
open ComplexityReduction Encoding Certificate

private def schemaVersion := "general_reduction_theorem_index_v1"
private def marker := "GENERAL_REDUCTION_THEOREM_INDEX"
private def maximumRenderedChars := 8192

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
  forallTelescope type fun _ conclusion =>
    pure conclusion.consumeMData.getAppFn.constName?

private def compatibleConclusionHeads (candidate target : Name) : Bool :=
  candidate == target ||
    (candidate == ``Not && target == ``False) ||
    (candidate == ``False && target == ``Not)

private structure Premise where
  kind : String
  type : Expr

private structure Application where
  declaration : Name
  moduleName : Name
  declarationType : Expr
  universeParameters : List Name
  premises : Array Premise
  result : Expr
  conclusionHead : Name

private def premiseKind (type : Expr) : MetaM String := do
  if (← isClass? type).isSome then
    return "typeclass"
  if ← isProp type then
    return "proposition"
  return "data"

private def nativeHardnessType (problem : Expr) : MetaM Expr :=
  mkAppM ``NativeTMNPHard #[problem]

private partial def applyUntilTarget (term type target : Expr)
    (arguments : Array Expr := #[]) : MetaM (Option (Expr × Array Expr)) := do
  let state ← saveState
  try
    if ← isDefEq (← whnf type) (← whnf target) then
      return some (term, arguments)
  catch _ =>
    pure ()
  state.restore
  match ← whnf type with
  | .forallE _ domain body _ =>
      let argument ← mkFreshExprMVar domain
      applyUntilTarget (mkApp term argument) (body.instantiate1 argument)
        target (arguments.push argument)
  | _ =>
      return none

private def tryApplication (environment : Environment) (declaration : Name)
    (information : ConstantInfo) (target : Expr) (targetHead : Name) :
    MetaM (Option Application) := do
  unless allowedPublicName declaration do
    return none
  let some head ← conclusionHead? information.type | return none
  /-
  `Not P` is definitionally `P → False`, but rule instantiation can return
  either spelling depending on how far the theorem telescope was reduced.  A
  purely syntactic head filter therefore hid reflection theorems precisely
  when a dependent premise was rendered as an arrow.  Keep the cheap head
  prefilter, while admitting the two definitionally equivalent spellings;
  `applyUntilTarget` remains the authoritative unification check below.
  -/
  unless compatibleConclusionHeads head targetHead do
    return none
  let some moduleName := declarationModule? environment declaration | return none
  let state ← saveState
  try
    let theoremTerm ← mkConstWithFreshMVarLevels declaration
    let some (result, arguments) ←
        applyUntilTarget theoremTerm (← inferType theoremTerm) target
      | state.restore
        return none
    unless ← isDefEq (← inferType result) target do
      state.restore
      return none
    let mut premises := #[]
    let mut premiseIds : Array MVarId := #[]
    for argument in arguments do
      let argument ← instantiateMVars argument
      for mvarId in ← getMVars argument do
        if !premiseIds.contains mvarId && !(← mvarId.isAssigned) then
          let type ← instantiateMVars (← inferType (mkMVar mvarId))
          premises := premises.push { kind := ← premiseKind type, type }
          premiseIds := premiseIds.push mvarId
    let result ← instantiateMVars result
    return some {
      declaration,
      moduleName,
      declarationType := information.type,
      universeParameters := information.levelParams,
      premises,
      result,
      conclusionHead := head }
  catch _ =>
    state.restore
    return none

private def runTarget (environment : Environment) (nonce label : String) (target : Expr) :
    MetaM Unit := do
  let some targetHead ← conclusionHead? target
    | throwError "general theorem-index target has no constant conclusion head"
  let mut applications := #[]
  for (declaration, information) in environment.constants.toList do
    if let some application ← tryApplication environment declaration information target targetHead then
      applications := applications.push application
  let sortedApplications := applications.qsort fun first second =>
    if first.premises.size == second.premises.size then
      first.declaration.toString < second.declaration.toString
    else
      first.premises.size < second.premises.size
  emit nonce "goal" [label, ← renderExpr target,
    toString target.hash, toString sortedApplications.size]
  for application in sortedApplications do
    let applicationType ← inferType application.result
    let renderedPremises ← application.premises.toList.mapM fun premise => do
      pure s!"{premise.kind}=>{← renderExpr premise.type}"
    emit nonce "candidate" [
      application.declaration.toString,
      application.moduleName.toString,
      String.intercalate "," (application.universeParameters.map toString),
      toString application.premises.size,
      ← renderExpr application.declarationType,
      String.intercalate " || " renderedPremises,
      ← renderExpr applicationType,
      toString applicationType.hash,
      application.conclusionHead.toString,
      application.moduleName.toString]

private def run (environment : Environment) (nonce : String) (problemName : Name) : MetaM Unit := do
  let problem ← match ← ComplexityReduction.Agent.Hardness.InputGate.presented environment problemName with
    | .ok handle => pure handle
    | .error failure => throwError "general theorem-index input rejected: {repr failure}"
  let target ← nativeHardnessType problem.term
  runTarget environment nonce problem.declaration.toString target

syntax (name := generativeReductionProbeNPHardTheorems)
  "#generative_reduction_probe_np_hard_theorems " str ident : command

elab_rules : command
  | `(#generative_reduction_probe_np_hard_theorems $nonce:str $problem:ident) => do
      let problemName ← resolveGlobalConstNoOverload problem
      let environment ← getEnv
      Command.liftTermElabM <| run environment nonce.getString problemName

syntax (name := generativeReductionProbeTypedGoal)
  "#generative_reduction_probe_typed_goal " str term : command

elab_rules : command
  | `(#generative_reduction_probe_typed_goal $nonce:str $target:term) => do
      let environment ← getEnv
      Command.liftTermElabM do
        let target ← Term.elabTerm target none
        Term.synthesizeSyntheticMVarsNoPostponing
        runTarget environment nonce.getString "<typed-goal>" (← instantiateMVars target)

end ComplexityReduction.Agent.GenerativeReduction.TheoremIndex
