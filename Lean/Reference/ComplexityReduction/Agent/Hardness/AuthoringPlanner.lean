/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.Gap
import ComplexityReduction.Agent.Hardness.InputGate
import ComplexityReduction.Agent.Hardness.ModelAuthoring
import ComplexityReduction.Registry.HardnessAggregate
import Lean.Elab.Command
import Lean.Util.FoldConsts

/-!
Lean-certified observations for deterministic NP-hard authoring planning.

This module only classifies public declarations by their elaborated types and
controlled definitional equality.  It cannot register an edge, construct a
certificate, or close a hardness request.  Python may schedule the observations,
but every generated declaration and the final theorem are checked again by Lean.
-/

namespace ComplexityReduction.Agent.Hardness.AuthoringPlanner

open Lean Elab Command Meta
open Encoding Program Certificate Registry

private def schemaVersion := "hardness_np_hard_authoring_observation_v2"
private def marker := "HARDNESS_NP_HARD_PLAN"
private def maximumRenderedChars := 12000

private structure LocalProblem where
  handle : InputGate.PresentedHandle
  representation : Expr
  declarationModule : Name

private def controlledDefEq (first second : Expr) : MetaM Bool := do
  isDefEq (← whnf first) (← whnf second)

private def oneLine (value : String) : String :=
  ((((value.replace "\n" " ").replace "\r" " ").replace "\t" " ").take
    maximumRenderedChars).toString

private def renderExpr (expression : Expr) : MetaM String := do
  let rendered ←
    withOptions (fun options => options.setBool `pp.fullNames true) (ppExpr expression)
  return oneLine rendered.pretty

private def endpointNodeId (endpoint : Expr) : MetaM String := do
  let normalized ← whnf endpoint
  return s!"lean-whnf:{normalized.hash}"

private def emit (nonce kind : String) (fields : List String := []) : MetaM Unit :=
  logInfo m!"{marker}\t{schemaVersion}\t{nonce}\t{kind}\t{String.intercalate "\t" fields}"

private def nameComponents : Name → List String
  | .anonymous => []
  | .str parent value => nameComponents parent ++ [value]
  | .num parent value => nameComponents parent ++ [toString value]

private def parentNamespace : Name → Name
  | .anonymous => .anonymous
  | .str parent _ => parent
  | .num parent _ => parent

private def inNamespace (ownerPrefix candidate : Name) : Bool :=
  let expected := nameComponents ownerPrefix
  let actual := nameComponents candidate
  expected.length < actual.length && actual.take expected.length == expected

private def forbiddenComponents : List String :=
  ["Oracles", "Oracle", "Gold", "GoldProofs", "Expected", "HiddenTargets", "Legacy"]

private def allowedPublicName (name : Name) : Bool :=
  !isPrivateName name && !(nameComponents name).any forbiddenComponents.contains

private def declarationModule? (environment : Environment) (declaration : Name) :
    Option Name := do
  let moduleIndex ← environment.getModuleIdxFor? declaration
  environment.header.moduleNames[moduleIndex]?

private def moduleAllowed (environment : Environment) (allowedModules : List String)
    (declaration : Name) : Bool :=
  match declarationModule? environment declaration with
  | some declarationModule => allowedModules.contains declarationModule.toString
  | none => false

private def registeredProblemNames {environment : Environment}
    (entries : List (ValidatedEntry environment)) : List Name :=
  entries.filterMap fun entry =>
    match entry.capability with
    | .presentedProblem => some entry.candidate
    | _ => none

private def declarationsInAllowedModules (environment : Environment)
    (allowedModules : List String) : List (Name × ConstantInfo) := Id.run do
  let mut declarations := []
  for (moduleName, moduleData) in
      environment.header.moduleNames.toList.zip environment.header.moduleData.toList do
    if allowedModules.contains moduleName.toString then
      for declaration in moduleData.constNames.toList.zip moduleData.constants.toList do
        declarations := declaration :: declarations
  return declarations

private def catalogProblems (environment : Environment) (sourceName : Name)
    (allowedModules : List String) (entries : List (ValidatedEntry environment)) :
    MetaM (List LocalProblem) := do
  let mut problems := []
  let registered := registeredProblemNames entries
  let declarations := declarationsInAllowedModules environment allowedModules
  for (declaration, information) in declarations do
    if allowedPublicName declaration &&
        information.levelParams.isEmpty && !information.type.hasMVar &&
        information.type.consumeMData.isConstOf ``PresentedProblem then
      match ← InputGate.presented environment declaration with
      | .error _ => pure ()
      | .ok handle =>
          let representation ← mkAppM ``PresentedProblem.representation #[handle.term]
          let some declarationModule := declarationModule? environment declaration
            | continue
          problems := problems ++ [{ handle, representation, declarationModule }]
  for declaration in registered do
    if problems.any fun problem => problem.handle.declaration == declaration then
      continue
    let some information := environment.find? declaration
      | continue
    if allowedPublicName declaration && information.levelParams.isEmpty &&
        !information.type.hasMVar &&
        information.type.consumeMData.isConstOf ``PresentedProblem then
      match ← InputGate.presented environment declaration with
      | .error _ => pure ()
      | .ok handle =>
          let representation ← mkAppM ``PresentedProblem.representation #[handle.term]
          let some declarationModule := declarationModule? environment declaration
            | continue
          problems := problems ++ [{ handle, representation, declarationModule }]
  unless problems.any fun problem => problem.handle.declaration == sourceName do
    let source ←
      match ← InputGate.presented environment sourceName with
      | .ok handle => pure handle
      | .error failure => throwError "catalog target rejected: {repr failure}"
    let representation ← mkAppM ``PresentedProblem.representation #[source.term]
    let some declarationModule := declarationModule? environment sourceName
      | throwError "catalog target has no declaration module"
    problems := problems ++ [{ handle := source, representation, declarationModule }]
  return (problems.toArray.qsort fun first second =>
    if first.handle.declaration == sourceName then true
    else if second.handle.declaration == sourceName then false
    else first.handle.declaration.toString < second.handle.declaration.toString).toList

private def problemForEndpoint? (problems : List LocalProblem) (endpoint : Expr) :
    MetaM (Option LocalProblem) := do
  if let .const endpointName _ := endpoint.consumeMData then
    if let some exact := problems.find? fun problem =>
        problem.handle.declaration == endpointName then
      return some exact
  problems.findM? fun problem => controlledDefEq problem.handle.term endpoint

private def problemForRepresentation? (problems : List LocalProblem) (representation : Expr) :
    MetaM (Option LocalProblem) := do
  if let some exact := problems.find? fun problem =>
      problem.representation.consumeMData == representation.consumeMData then
    return some exact
  problems.findM? fun problem => controlledDefEq problem.representation representation

private def exactPolyProgType? (type : Expr) : MetaM (Option (Expr × Expr)) := do
  if type.hasFVar || type.hasMVar || type.hasLooseBVars || type.hasLevelParam then
    return none
  let normalized ← whnf type
  unless normalized.getAppFn.consumeMData.isConstOf ``PolyProg do
    return none
  match normalized.getAppArgs with
  | #[source, target] => return some (source, target)
  | _ => return none

private def relationEndpoints? (type : Expr) (problems : List LocalProblem) :
    MetaM (Option (LocalProblem × LocalProblem)) := do
  forallTelescopeReducing type fun binders body => do
    unless binders.size == 2 && (← whnf body) == .sort .zero do
      return none
    let firstType ← inferType binders[0]!
    let secondType ← inferType binders[1]!
    for first in problems do
      let firstInstance ← mkAppM ``PresentedProblem.Instance #[first.handle.term]
      unless ← controlledDefEq firstType firstInstance do
        continue
      for second in problems do
        let secondInstance ← mkAppM ``PresentedProblem.Instance #[second.handle.term]
        if ← controlledDefEq secondType secondInstance then
          return some (first, second)
    return none

private def emitProblems (nonce fingerprint : String) (problems : List LocalProblem) :
    MetaM Unit := do
  for problem in problems do
    emit nonce "problem" [
      problem.handle.declaration.toString,
      ← endpointNodeId problem.handle.term,
      ← endpointNodeId problem.representation,
      ← renderExpr problem.handle.term,
      ← renderExpr problem.representation,
      problem.declarationModule.toString,
      fingerprint]

private def emitClosureCapabilities (environment : Environment) (allowedModules : List String)
    (nonce fingerprint : String) (problems : List LocalProblem) : MetaM Unit := do
  let declarations := ((declarationsInAllowedModules environment allowedModules).filter
    fun entry => allowedPublicName entry.1).toArray.qsort fun first second =>
      first.1.toString < second.1.toString
  for (declaration, information) in declarations do
    let some declarationModule := declarationModule? environment declaration
      | continue
    let usedConstants := information.getUsedConstantsAsSet
    if usedConstants.contains ``PolyProg then
      match ← exactPolyProgType? information.type with
      | some (sourceRepresentation, targetRepresentation) =>
          let some source ← problemForRepresentation? problems sourceRepresentation
            | continue
          let some target ← problemForRepresentation? problems targetRepresentation
            | continue
          emit nonce "poly_program" [
            declaration.toString,
            source.handle.declaration.toString,
            target.handle.declaration.toString,
            ← endpointNodeId sourceRepresentation,
            ← endpointNodeId targetRepresentation,
            ← renderExpr information.type,
            declarationModule.toString,
            fingerprint]
      | none => pure ()
    else if usedConstants.contains ``PresentedProblem.Instance then
      match ← relationEndpoints? information.type problems with
      | some (source, target) =>
          emit nonce "mapping_relation" [
            declaration.toString,
            source.handle.declaration.toString,
            target.handle.declaration.toString,
            ← renderExpr information.type,
            declarationModule.toString,
            fingerprint]
      | none => pure ()

private def emitGaps (environment : Environment) (allowedModules : List String)
    (nonce fingerprint : String) (problems : List LocalProblem) : MetaM Unit := do
  for gap in Gap.declaredGapObservations environment do
    if moduleAllowed environment allowedModules gap.declaration &&
        allowedPublicName gap.declaration then
      let some source ← problemForEndpoint? problems gap.source
        | continue
      let some target ← problemForEndpoint? problems gap.target
        | continue
      let some declarationModule := declarationModule? environment gap.declaration
        | continue
      emit nonce "gap" [
        gap.declaration.toString,
        Gap.reasonLabel gap.reason,
        Gap.failureCode gap.reason,
        toString gap.role,
        source.handle.declaration.toString,
        target.handle.declaration.toString,
        (Gap.expectedCapabilityHead gap.reason).toString,
        ← endpointNodeId gap.source,
        ← endpointNodeId gap.target,
        declarationModule.toString,
        fingerprint]

private def emitBuiltin (environment : Environment) (nonce fingerprint : String)
    (declaration : Name) : MetaM Unit := do
  let some information := environment.find? declaration
    | return
  let some declarationModule := declarationModule? environment declaration
    | return
  emit nonce "builtin" [declaration.toString, ← renderExpr information.type,
    declarationModule.toString, fingerprint]

private def emitRegisteredReduction (nonce fingerprint : String)
    (problems : List LocalProblem) (certificate capability direction role : String)
    (declarationModule : Name) (term sourceEndpoint targetEndpoint : Expr) : MetaM Unit := do
  let some source ← problemForEndpoint? problems sourceEndpoint
    | return
  let some target ← problemForEndpoint? problems targetEndpoint
    | return
  emit nonce "certified_reduction" [
    certificate,
    ← renderExpr term,
    capability,
    direction,
    role,
    source.handle.declaration.toString,
    target.handle.declaration.toString,
    ← endpointNodeId sourceEndpoint,
    ← endpointNodeId targetEndpoint,
    ← renderExpr (← inferType term),
    declarationModule.toString,
    fingerprint]

private def emitRegisteredCapabilities {environment : Environment}
    (nonce fingerprint : String) (problems : List LocalProblem)
    (entries : List (ValidatedEntry environment)) : MetaM Unit := do
  for entry in entries do
    let some declarationModule := declarationModule? environment entry.candidate
      | continue
    let role := "unannotated"
    match entry.capability with
    | .nativeTMNPHard endpoint =>
        let some problem ← problemForEndpoint? problems endpoint
          | continue
        let information ← inferType (mkConst entry.candidate)
        emit nonce "hardness_seed" [
          problem.handle.declaration.toString,
          ← endpointNodeId endpoint,
          entry.candidate.toString,
          "native_hardness",
          ← renderExpr information,
          declarationModule.toString,
          fingerprint]
    | .nativeTMNPComplete endpoint =>
        let some problem ← problemForEndpoint? problems endpoint
          | continue
        let information ← inferType (mkConst entry.candidate)
        emit nonce "hardness_seed" [
          problem.handle.declaration.toString,
          ← endpointNodeId endpoint,
          entry.candidate.toString,
          "native_completeness_projection",
          ← renderExpr information,
          declarationModule.toString,
          fingerprint]
    | .primitive sourceRepresentation targetRepresentation =>
        let some source ← problemForRepresentation? problems sourceRepresentation
          | continue
        let some target ← problemForRepresentation? problems targetRepresentation
          | continue
        emit nonce "primitive" [
          entry.candidate.toString,
          source.handle.declaration.toString,
          target.handle.declaration.toString,
          ← endpointNodeId sourceRepresentation,
          ← endpointNodeId targetRepresentation,
          ← renderExpr (← inferType (mkConst entry.candidate)),
          declarationModule.toString,
          fingerprint]
    | .certifiedReduction sourceEndpoint targetEndpoint =>
        emitRegisteredReduction nonce fingerprint problems
          entry.candidate.toString "certified_reduction" "forward" role declarationModule
          (mkConst entry.candidate) sourceEndpoint targetEndpoint
    | .certifiedEquiv sourceEndpoint targetEndpoint =>
        let certificate := mkConst entry.candidate
        let forward ← mkAppM ``CertifiedEquiv.forwardReduction #[certificate]
        emitRegisteredReduction nonce fingerprint problems
          entry.candidate.toString "certified_equiv" "forward" role declarationModule
          forward sourceEndpoint targetEndpoint
        let backward ← mkAppM ``CertifiedEquiv.backwardReduction #[certificate]
        emitRegisteredReduction nonce fingerprint problems
          entry.candidate.toString "certified_equiv" "backward" role declarationModule
          backward targetEndpoint sourceEndpoint
    | .certifiedPresentationChange sourceEndpoint targetEndpoint =>
        let certificate := mkConst entry.candidate
        let forward ← mkAppM ``CertifiedPresentationChange.forwardReduction #[certificate]
        emitRegisteredReduction nonce fingerprint problems
          entry.candidate.toString "certified_presentation_change" "forward" role
          declarationModule forward sourceEndpoint targetEndpoint
        let backward ← mkAppM ``CertifiedPresentationChange.backwardReduction #[certificate]
        emitRegisteredReduction nonce fingerprint problems
          entry.candidate.toString "certified_presentation_change" "backward" role
          declarationModule backward targetEndpoint sourceEndpoint
    | _ => pure ()

private def run (environment : Environment) (nonce : String) (sourceName : Name)
    (allowedModulesText : String) :
    MetaM Unit := do
  let source ←
    match ← InputGate.presented environment sourceName with
    | .ok handle => pure handle
    | .error failure => throwError "NP-hard authoring planner rejected input: {repr failure}"
  let ownerPrefix := parentNamespace sourceName
  let entries := exportValidated environment
  let fingerprint := Registry.registryFingerprint entries
  let allowedModules := (allowedModulesText.splitOn ",").filter fun value => !value.isEmpty
  let problems ← catalogProblems environment sourceName allowedModules entries
  unless (problems.any fun problem => problem.handle.declaration == sourceName) do
    throwError "NP-hard authoring planner could not retain the exact input endpoint"
  let some sourceModule := declarationModule? environment sourceName
    | throwError "NP-hard authoring planner could not identify the input module"
  emit nonce "input" [
    sourceName.toString,
    ← endpointNodeId source.term,
    ownerPrefix.toString,
    sourceModule.toString,
    fingerprint]
  emitProblems nonce fingerprint problems
  emitClosureCapabilities environment allowedModules nonce fingerprint problems
  emitGaps environment allowedModules nonce fingerprint problems
  emitRegisteredCapabilities nonce fingerprint problems entries
  emitBuiltin environment nonce fingerprint ``PolyProg.const
  emitBuiltin environment nonce fingerprint ``PolyProg.id
  emitBuiltin environment nonce fingerprint ``PolyProg.pair
  emit nonce "complete" [toString problems.length, fingerprint]

syntax (name := hardnessNPHardAuthoringObserve)
  "#hardness_np_hard_authoring_observe " str ident str : command

elab_rules : command
  | `(#hardness_np_hard_authoring_observe $nonce:str $source:ident $allowedModules:str) => do
      let sourceName ← resolveGlobalConstNoOverload source
      let environment ← getEnv
      Command.liftTermElabM <|
        run environment nonce.getString sourceName allowedModules.getString

end ComplexityReduction.Agent.Hardness.AuthoringPlanner
