/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.Gap
import ComplexityReduction.Agent.Hardness.InputGate
import ComplexityReduction.Agent.Hardness.ModelAuthoring
import ComplexityReduction.Agent.Hardness.AuthoringSources
import ComplexityReduction.Agent.Hardness.ProgramAuthoringSources
import ComplexityReduction.Agent.Hardness.GadgetAuthoringSources
import ComplexityReduction.Agent.Hardness.SuccessorAuthoringSources
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

private def schemaVersion := "hardness_np_hard_authoring_observation_v3"
private def marker := "HARDNESS_NP_HARD_PLAN"
private def declarationTypeSchemaVersion :=
  "hardness_np_hard_declaration_type_observation_v1"
private def declarationTypeMarker := "HARDNESS_NP_HARD_DECL_TYPE"
private def maximumRenderedChars := 12000
private def publicAuthoringSourcesModule : Name :=
  `ComplexityReduction.Agent.Hardness.AuthoringSources
private def publicProgramAuthoringSourcesModule : Name :=
  `ComplexityReduction.Agent.Hardness.ProgramAuthoringSources
private def publicGadgetAuthoringSourcesModule : Name :=
  `ComplexityReduction.Agent.Hardness.GadgetAuthoringSources
private def publicSuccessorAuthoringSourcesModule : Name :=
  `ComplexityReduction.Agent.Hardness.SuccessorAuthoringSources

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

private def problemForBackendEndpoint? (problems : List LocalProblem) (endpoint : Expr) :
    MetaM (Option LocalProblem) := do
  problems.findM? fun problem => do
    let backend ←
      mkAppM ``PresentedProblem.toEncodedDecisionProblem #[problem.handle.term]
    controlledDefEq backend endpoint

private def exactPolyProgType? (type : Expr) : MetaM (Option (Expr × Expr)) := do
  if type.hasFVar || type.hasMVar || type.hasLooseBVars || type.hasLevelParam then
    return none
  let normalized ← whnf type
  unless normalized.getAppFn.consumeMData.isConstOf ``PolyProg do
    return none
  match normalized.getAppArgs with
  | #[source, target] => return some (source, target)
  | _ => return none

private def exactTMKarpReductionType? (type : Expr) : MetaM (Option (Expr × Expr)) := do
  if type.hasFVar || type.hasMVar || type.hasLooseBVars || type.hasLevelParam then
    return none
  let normalized ← whnf type
  unless normalized.getAppFn.consumeMData.isConstOf ``TMKarpReduction do
    return none
  match normalized.getAppArgs with
  | #[source, target] => return some (source, target)
  | _ => return none

private def exactCertifiedReductionType? (type : Expr) : MetaM (Option (Expr × Expr)) := do
  if type.hasFVar || type.hasMVar || type.hasLooseBVars || type.hasLevelParam then
    return none
  let normalized ← whnf type
  unless normalized.getAppFn.consumeMData.isConstOf ``CertifiedReduction do
    return none
  match normalized.getAppArgs with
  | #[source, target] => return some (source, target)
  | _ => return none

private def exactProgramIndexedAdmissionPacketType?
    (type : Expr) : MetaM (Option (Expr × Expr)) := do
  if type.hasFVar || type.hasMVar || type.hasLooseBVars || type.hasLevelParam then
    return none
  let normalized ← whnf type
  unless normalized.getAppFn.consumeMData.isConstOf
      ``ProgramAuthoringSources.ProgramIndexedAdmissionPacket do
    return none
  match normalized.getAppArgs with
  | #[source, target] => return some (source, target)
  | _ => return none

private def exactGadgetIndexedAdmissionPacketType?
    (type : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  if type.hasFVar || type.hasMVar || type.hasLooseBVars || type.hasLevelParam then
    return none
  let normalized ← whnf type
  unless normalized.getAppFn.consumeMData.isConstOf
      ``GadgetAuthoringSources.GadgetIndexedAdmissionPacket do
    return none
  match normalized.getAppArgs with
  | #[source, reference, target] => return some (source, reference, target)
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

private def forwardBoolRepresentationAdapter?
    (source target : LocalProblem) : MetaM (Option (Expr × Expr)) := do
  let boolRepresentation := mkConst ``StandardInstances.bool
  let expectedTargetRepresentation ←
    mkAppM ``StandardInstances.prod #[boolRepresentation, source.representation]
  unless ← controlledDefEq target.representation expectedTargetRepresentation do
    return none

  -- The forward adapter injects the fixed public tag `false`.  At every output
  -- of that adapter, target acceptance must definitionally depend only on the
  -- second projection.  This direction check prevents a discoverable reverse
  -- `snd` from being mistaken for a source-to-target hardness transfer.
  let sourceCarrier ← mkAppM ``PresentedProblem.Instance #[source.handle.term]
  let sourceAccepts ← mkAppM ``PresentedProblem.accepts #[source.handle.term]
  let falseValue := mkConst ``Bool.false
  let injectedTargetAccepts ← withLocalDeclD `input sourceCarrier fun input => do
    let taggedInput ← mkAppM ``Prod.mk #[falseValue, input]
    let body ← mkAppM ``PresentedProblem.accepts #[target.handle.term, taggedInput]
    mkLambdaFVars #[input] body
  unless ← controlledDefEq sourceAccepts injectedTargetAccepts do
    return none

  let tagProgram ← mkAppM ``PolyProg.const
    #[source.representation, boolRepresentation, falseValue]
  let payloadProgram ← mkAppM ``PolyProg.id #[source.representation]
  let program ← mkAppM ``PolyProg.pair #[tagProgram, payloadProgram]
  let exactType ← mkAppM ``PolyProg #[source.representation, target.representation]
  unless ← controlledDefEq (← inferType program) exactType do
    return none
  return some (program, exactType)

private def emitTypedCapabilities (environment : Environment) (allowedModules : List String)
    (nonce fingerprint : String) (problems : List LocalProblem) : MetaM Unit := do
  let mut emittedEndpointPairs : List String := []
  for target in problems do
    unless allowedPublicName target.handle.declaration &&
        moduleAllowed environment allowedModules target.handle.declaration do
      continue
    let some targetModule := declarationModule? environment target.handle.declaration
      | continue
    for source in problems do
      unless allowedPublicName source.handle.declaration &&
          moduleAllowed environment allowedModules source.handle.declaration do
        continue
      let some (witness, exactType) ← forwardBoolRepresentationAdapter? source target
        | continue
      let sourceNode ← endpointNodeId source.handle.term
      let targetNode ← endpointNodeId target.handle.term
      let endpointPair := sourceNode ++ "\u2192" ++ targetNode
      if emittedEndpointPairs.contains endpointPair then
        continue
      emittedEndpointPairs := endpointPair :: emittedEndpointPairs
      emit nonce "typed_capability" [
        "forward_representation_adapter",
        "forward_representation_adapter:" ++ sourceNode ++ ":" ++ targetNode,
        source.handle.declaration.toString,
        target.handle.declaration.toString,
        sourceNode,
        targetNode,
        ← renderExpr witness,
        ← renderExpr exactType,
        targetModule.toString,
        "lean_exact_type_defeq",
        fingerprint]

private structure TMKarpAuthoringCandidate where
  declaration : Name
  declarationModule : Name
  source : LocalProblem
  target : LocalProblem
  witness : Expr
  exactType : Expr

private structure CertifiedSuccessorCandidate where
  declaration : Name
  declarationModule : Name
  source : LocalProblem
  target : LocalProblem
  witness : Expr
  exactType : Expr

private structure ProgramIndexedAuthoringCandidate where
  declaration : Name
  declarationModule : Name
  source : LocalProblem
  target : LocalProblem
  witness : Expr
  exactType : Expr

private structure GadgetIndexedAuthoringCandidate where
  declaration : Name
  declarationModule : Name
  source : LocalProblem
  reference : LocalProblem
  target : LocalProblem
  witness : Expr
  exactType : Expr

private def collectTMKarpAuthoringCandidates (environment : Environment)
    (problems : List LocalProblem) : MetaM (List TMKarpAuthoringCandidate) := do
  let sourceModuleText := publicAuthoringSourcesModule.toString
  let declarations :=
    ((declarationsInAllowedModules environment [sourceModuleText]).filter fun entry =>
      allowedPublicName entry.1).toArray.qsort fun first second =>
        first.1.toString < second.1.toString
  let mut candidates := []
  for (declaration, information) in declarations do
    let some declarationModule := declarationModule? environment declaration
      | continue
    unless declarationModule == publicAuthoringSourcesModule do
      continue
    let some (sourceEndpoint, targetEndpoint) ←
        exactTMKarpReductionType? information.type
      | continue
    let some source ← problemForBackendEndpoint? problems sourceEndpoint
      | continue
    let some target ← problemForBackendEndpoint? problems targetEndpoint
      | continue
    let witness := mkConst declaration
    unless ← controlledDefEq (← inferType witness) information.type do
      continue
    candidates := candidates ++ [{
      declaration,
      declarationModule,
      source,
      target,
      witness,
      exactType := information.type
    }]
  return candidates

/--
Collect raw reductions that are admissible only as predecessors of a separately
certified successor.  The exact module and shared-gadget role form a typed
authority boundary; these declarations are never emitted as direct admissions.
-/
private def collectSuccessorOnlyTMKarpAuthoringCandidates (environment : Environment)
    (problems : List LocalProblem) : MetaM (List TMKarpAuthoringCandidate) := do
  let sourceModuleText := publicSuccessorAuthoringSourcesModule.toString
  let declarations :=
    ((declarationsInAllowedModules environment [sourceModuleText]).filter fun entry =>
      allowedPublicName entry.1).toArray.qsort fun first second =>
        first.1.toString < second.1.toString
  let mut candidates := []
  for (declaration, information) in declarations do
    let some declarationModule := declarationModule? environment declaration
      | continue
    unless declarationModule == publicSuccessorAuthoringSourcesModule do
      continue
    unless Annotations.componentRole? environment declaration == some .sharedGadget do
      continue
    let some (sourceEndpoint, targetEndpoint) ←
        exactTMKarpReductionType? information.type
      | continue
    let some source ← problemForBackendEndpoint? problems sourceEndpoint
      | continue
    let some target ← problemForBackendEndpoint? problems targetEndpoint
      | continue
    let witness := mkConst declaration
    unless ← controlledDefEq (← inferType witness) information.type do
      continue
    let sourceBackend ← mkAppM ``PresentedProblem.toEncodedDecisionProblem
      #[source.handle.term]
    let targetBackend ← mkAppM ``PresentedProblem.toEncodedDecisionProblem
      #[target.handle.term]
    let exactType ← mkAppM ``TMKarpReduction #[sourceBackend, targetBackend]
    unless ← controlledDefEq information.type exactType do
      continue
    candidates := candidates ++ [{
      declaration,
      declarationModule,
      source,
      target,
      witness,
      exactType
    }]
  return candidates

private def eligibleDependentSuccessorRole (environment : Environment)
    (declaration : Name) : Bool :=
  match Annotations.componentRole? environment declaration with
  | some .ingress => false
  | some .finalComposition => false
  | _ => true

private def collectCertifiedSuccessorCandidates {environment : Environment}
    (problems : List LocalProblem) (entries : List (ValidatedEntry environment)) :
    MetaM (List CertifiedSuccessorCandidate) := do
  let sortedEntries := entries.toArray.qsort fun first second =>
    first.candidate.toString < second.candidate.toString
  let mut candidates := []
  for entry in sortedEntries do
    unless allowedPublicName entry.candidate &&
        eligibleDependentSuccessorRole environment entry.candidate do
      continue
    let .certifiedReduction sourceEndpoint targetEndpoint := entry.capability
      | continue
    let some declarationModule := declarationModule? environment entry.candidate
      | continue
    let some source ← problemForEndpoint? problems sourceEndpoint
      | continue
    let some target ← problemForEndpoint? problems targetEndpoint
      | continue
    let some (exactSource, exactTarget) ← exactCertifiedReductionType? entry.elaboratedType
      | continue
    unless ← controlledDefEq exactSource sourceEndpoint do
      continue
    unless ← controlledDefEq exactTarget targetEndpoint do
      continue
    let witness := mkConst entry.candidate
    unless ← controlledDefEq (← inferType witness) entry.elaboratedType do
      continue
    candidates := candidates ++ [{
      declaration := entry.candidate,
      declarationModule,
      source,
      target,
      witness,
      exactType := entry.elaboratedType
    }]
  return candidates

private def collectProgramIndexedAuthoringCandidates (environment : Environment)
    (problems : List LocalProblem) : MetaM (List ProgramIndexedAuthoringCandidate) := do
  let sourceModuleText := publicProgramAuthoringSourcesModule.toString
  let declarations :=
    ((declarationsInAllowedModules environment [sourceModuleText]).filter fun entry =>
      allowedPublicName entry.1).toArray.qsort fun first second =>
        first.1.toString < second.1.toString
  let mut candidates := []
  for (declaration, information) in declarations do
    let some declarationModule := declarationModule? environment declaration
      | continue
    unless declarationModule == publicProgramAuthoringSourcesModule do
      continue
    let some (sourceEndpoint, targetEndpoint) ←
        exactProgramIndexedAdmissionPacketType? information.type
      | continue
    let some source ← problemForEndpoint? problems sourceEndpoint
      | continue
    let some target ← problemForEndpoint? problems targetEndpoint
      | continue
    let witness := mkConst declaration
    unless ← controlledDefEq (← inferType witness) information.type do
      continue
    let exactType ← mkAppM
      ``ProgramAuthoringSources.ProgramIndexedAdmissionPacket
      #[source.handle.term, target.handle.term]
    unless ← controlledDefEq information.type exactType do
      continue
    candidates := candidates ++ [{
      declaration,
      declarationModule,
      source,
      target,
      witness,
      exactType
    }]
  return candidates

private def collectGadgetIndexedAuthoringCandidates (environment : Environment)
    (problems : List LocalProblem) : MetaM (List GadgetIndexedAuthoringCandidate) := do
  let sourceModuleText := publicGadgetAuthoringSourcesModule.toString
  let declarations :=
    ((declarationsInAllowedModules environment [sourceModuleText]).filter fun entry =>
      allowedPublicName entry.1).toArray.qsort fun first second =>
        first.1.toString < second.1.toString
  let mut candidates := []
  for (declaration, information) in declarations do
    let some declarationModule := declarationModule? environment declaration
      | continue
    unless declarationModule == publicGadgetAuthoringSourcesModule do
      continue
    unless Annotations.componentRole? environment declaration == some .sharedGadget do
      continue
    let some (sourceEndpoint, referenceEndpoint, targetEndpoint) ←
        exactGadgetIndexedAdmissionPacketType? information.type
      | continue
    let some source ← problemForEndpoint? problems sourceEndpoint
      | continue
    let some reference ← problemForEndpoint? problems referenceEndpoint
      | continue
    let some target ← problemForEndpoint? problems targetEndpoint
      | continue
    let witness := mkConst declaration
    unless ← controlledDefEq (← inferType witness) information.type do
      continue
    let exactType ← mkAppM
      ``GadgetAuthoringSources.GadgetIndexedAdmissionPacket
      #[source.handle.term, reference.handle.term, target.handle.term]
    unless ← controlledDefEq information.type exactType do
      continue
    candidates := candidates ++ [{
      declaration,
      declarationModule,
      source,
      reference,
      target,
      witness,
      exactType
    }]
  return candidates

private def emitTMKarpCandidate (nonce fingerprint : String)
    (candidate : TMKarpAuthoringCandidate) : MetaM Unit := do
  let sourceNode ← endpointNodeId candidate.source.handle.term
  let targetNode ← endpointNodeId candidate.target.handle.term
  emit nonce "typed_capability" [
    "forward_tmkarp_admission",
    "forward_tmkarp_admission:" ++ sourceNode ++ ":" ++ targetNode,
    candidate.source.handle.declaration.toString,
    candidate.target.handle.declaration.toString,
    sourceNode,
    targetNode,
    ← renderExpr candidate.witness,
    ← renderExpr candidate.exactType,
    candidate.declarationModule.toString,
    "lean_exact_tmkarp_public_source",
    fingerprint]

private def emitSuccessorOnlyTMKarpCandidate (nonce fingerprint : String)
    (candidate : TMKarpAuthoringCandidate) : MetaM Unit := do
  let sourceNode ← endpointNodeId candidate.source.handle.term
  let targetNode ← endpointNodeId candidate.target.handle.term
  emit nonce "typed_capability" [
    "forward_successor_only_tmkarp_admission",
    "forward_successor_only_tmkarp_admission:" ++ sourceNode ++ ":" ++ targetNode,
    candidate.source.handle.declaration.toString,
    candidate.target.handle.declaration.toString,
    sourceNode,
    targetNode,
    ← renderExpr candidate.witness,
    ← renderExpr candidate.exactType,
    candidate.declarationModule.toString,
    "lean_exact_successor_only_tmkarp_shared_source",
    fingerprint]

private def emitCertifiedSuccessorCandidate (nonce fingerprint : String)
    (candidate : CertifiedSuccessorCandidate) : MetaM Unit := do
  let sourceNode ← endpointNodeId candidate.source.handle.term
  let targetNode ← endpointNodeId candidate.target.handle.term
  emit nonce "typed_capability" [
    "forward_certified_successor",
    "forward_certified_successor:" ++ sourceNode ++ ":" ++ targetNode,
    candidate.source.handle.declaration.toString,
    candidate.target.handle.declaration.toString,
    sourceNode,
    targetNode,
    ← renderExpr candidate.witness,
    ← renderExpr candidate.exactType,
    candidate.declarationModule.toString,
    "lean_registry_exact_certified_successor",
    fingerprint]

private def emitProgramIndexedCandidate (nonce fingerprint : String)
    (candidate : ProgramIndexedAuthoringCandidate) : MetaM Unit := do
  let sourceNode ← endpointNodeId candidate.source.handle.term
  let targetNode ← endpointNodeId candidate.target.handle.term
  emit nonce "typed_capability" [
    "forward_program_indexed_admission",
    "forward_program_indexed_admission:" ++ sourceNode ++ ":" ++ targetNode,
    candidate.source.handle.declaration.toString,
    candidate.target.handle.declaration.toString,
    sourceNode,
    targetNode,
    ← renderExpr candidate.witness,
    ← renderExpr candidate.exactType,
    candidate.declarationModule.toString,
    "lean_exact_program_indexed_public_packet",
    fingerprint]

private def emitGadgetIndexedCandidate (nonce fingerprint : String)
    (candidate : GadgetIndexedAuthoringCandidate) : MetaM Unit := do
  let sourceNode ← endpointNodeId candidate.source.handle.term
  let targetNode ← endpointNodeId candidate.target.handle.term
  emit nonce "typed_capability" [
    "forward_gadget_indexed_admission",
    "forward_gadget_indexed_admission:" ++ sourceNode ++ ":" ++ targetNode,
    candidate.source.handle.declaration.toString,
    candidate.target.handle.declaration.toString,
    sourceNode,
    targetNode,
    ← renderExpr candidate.witness,
    ← renderExpr candidate.exactType,
    candidate.declarationModule.toString,
    "lean_exact_gadget_indexed_shared_packet",
    fingerprint]

private def emitProgramIndexedAuthoringCapabilities (environment : Environment)
    (nonce fingerprint : String) (sourceName : Name) (problems : List LocalProblem) :
    MetaM Unit := do
  let candidates ← collectProgramIndexedAuthoringCandidates environment problems
  let directCandidates := candidates.filter fun candidate =>
    candidate.target.handle.declaration == sourceName
  match directCandidates with
  | [candidate] =>
      let admissions ← collectTMKarpAuthoringCandidates environment problems
      let predecessors := admissions.filter fun admission =>
        admission.target.handle.declaration == candidate.source.handle.declaration
      match predecessors with
      | [admission] =>
          emitTMKarpCandidate nonce fingerprint admission
          emitProgramIndexedCandidate nonce fingerprint candidate
      | [] => emitProgramIndexedCandidate nonce fingerprint candidate
      | _ => pure ()
  | _ => pure ()

private def emitGadgetIndexedAuthoringCapabilities (environment : Environment)
    (nonce fingerprint : String) (sourceName : Name) (problems : List LocalProblem) :
    MetaM Unit := do
  let candidates ← collectGadgetIndexedAuthoringCandidates environment problems
  let directCandidates := candidates.filter fun candidate =>
    candidate.target.handle.declaration == sourceName
  match directCandidates with
  | [candidate] => emitGadgetIndexedCandidate nonce fingerprint candidate
  | _ => pure ()

private def emitTMKarpAuthoringCapabilities {environment : Environment}
    (nonce fingerprint : String) (sourceName : Name) (problems : List LocalProblem)
    (entries : List (ValidatedEntry environment)) : MetaM Unit := do
  let admissions ← collectTMKarpAuthoringCandidates environment problems
  let mut emittedEndpointPairs : List String := []
  let directAdmissions := admissions.filter fun candidate =>
    candidate.target.handle.declaration == sourceName
  for candidate in directAdmissions do
    let sourceNode ← endpointNodeId candidate.source.handle.term
    let targetNode ← endpointNodeId candidate.target.handle.term
    let endpointPair := sourceNode ++ "\u2192" ++ targetNode
    if emittedEndpointPairs.contains endpointPair then
      continue
    emittedEndpointPairs := endpointPair :: emittedEndpointPairs
    emitTMKarpCandidate nonce fingerprint candidate

  -- Dependent authoring is admitted only when the public source catalog and
  -- the validated registry determine one complete, endpoint-exact chain.  A
  -- final-composition registry declaration is intentionally ineligible: the
  -- model must compose the admitted raw TM/Karp program with the successor,
  -- rather than borrowing an already assembled whole route.
  unless directAdmissions.isEmpty do
    return
  let successors ← collectCertifiedSuccessorCandidates problems entries
  let chains := admissions.flatMap fun admission =>
    successors.filterMap fun successor =>
      if admission.target.handle.declaration == successor.source.handle.declaration &&
          successor.target.handle.declaration == sourceName then
        some (admission, successor)
      else
        none
  match chains with
  | [(admission, successor)] =>
      emitTMKarpCandidate nonce fingerprint admission
      emitCertifiedSuccessorCandidate nonce fingerprint successor
  | _ => pure ()

/--
Emit a successor-only admission iff the registry determines one exact
admission/successor chain ending at the requested endpoint.  In particular, a
request whose endpoint is the admission target itself receives no capability.
-/
private def emitSuccessorOnlyTMKarpAuthoringCapabilities {environment : Environment}
    (nonce fingerprint : String) (sourceName : Name) (problems : List LocalProblem)
    (entries : List (ValidatedEntry environment)) : MetaM Unit := do
  let admissions ← collectSuccessorOnlyTMKarpAuthoringCandidates environment problems
  let successors ← collectCertifiedSuccessorCandidates problems entries
  let chains := admissions.flatMap fun admission =>
    successors.filterMap fun successor =>
      if admission.target.handle.declaration == successor.source.handle.declaration &&
          successor.target.handle.declaration == sourceName then
        some (admission, successor)
      else
        none
  match chains with
  | [(admission, successor)] =>
      emitSuccessorOnlyTMKarpCandidate nonce fingerprint admission
      emitCertifiedSuccessorCandidate nonce fingerprint successor
  | _ => pure ()

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
    unless allowedPublicName entry.candidate do
      continue
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
  emitTypedCapabilities environment allowedModules nonce fingerprint problems
  emitTMKarpAuthoringCapabilities nonce fingerprint sourceName problems entries
  emitSuccessorOnlyTMKarpAuthoringCapabilities nonce fingerprint sourceName problems entries
  emitProgramIndexedAuthoringCapabilities environment nonce fingerprint sourceName problems
  emitGadgetIndexedAuthoringCapabilities environment nonce fingerprint sourceName problems
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

/-!
Render the kernel-elaborated type of each explicitly requested public
declaration.  This command does not discover or select primitives; Python must
already supply the immutable allowlist whose types are being observed.
-/
syntax (name := hardnessNPHardDeclarationType)
  "#hardness_np_hard_declaration_type " str str term : command

elab_rules : command
  | `(#hardness_np_hard_declaration_type $nonce:str $label:str $term:term) => do
      let declarationType? ← try
        let declaration ← resolveGlobalConstNoOverload term
        pure ((← getEnv).find? declaration |>.map (fun information => information.type))
      catch _ =>
        pure none
      Command.liftTermElabM do
        let exactType ← match declarationType? with
          | some exactType => pure exactType
          | none => inferType (← Term.elabTerm term none)
        let rendered ← renderExpr exactType
        logInfo m!"{declarationTypeMarker}\t{declarationTypeSchemaVersion}\t{nonce.getString}\t{label.getString}\t{rendered}"

end ComplexityReduction.Agent.Hardness.AuthoringPlanner
