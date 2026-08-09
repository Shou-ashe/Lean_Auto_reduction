/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.InputGate
import ComplexityReduction.Agent.Hardness.Gap
import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.Protocol.ClosedResolver
import ComplexityReduction.Registry.HardnessAggregate
import Lean.Elab.Command

/-! Versioned, nonce-bound observational probe output for the hardness agent. -/

namespace ComplexityReduction.Agent.Hardness.Probe

open Lean Elab Command Meta
open Encoding Certificate Registry

private def schemaVersion := "hardness_probe_v1"
private def marker := "HARDNESS_AGENT"

private structure NativeTarget where
  problem : InputGate.PresentedHandle
  membershipDeclaration : Name
  endpoint : Expr

private def controlledDefEq (first second : Expr) : MetaM Bool := do
  isDefEq (← whnf first) (← whnf second)

private def oneLine (value : String) : String :=
  ((value.replace "\n" " ").replace "\r" " ").replace "\t" " "

private def renderEndpoint (endpoint : Expr) : MetaM String := do
  let rendered ← withOptions (fun options => options.setBool `pp.fullNames true) (ppExpr endpoint)
  return oneLine rendered.pretty

private def endpointNodeId (endpoint : Expr) : MetaM String := do
  let normalized ← whnf endpoint
  return s!"lean-whnf:{normalized.hash}"

private def emit (nonce kind : String) (fields : List String := []) : MetaM Unit :=
  logInfo m!"{marker}\t{schemaVersion}\t{nonce}\t{kind}\t{String.intercalate "\t" fields}"

private def nativeTargets {environment : Environment}
    (entries : List (ValidatedEntry environment)) : MetaM (List NativeTarget) := do
  let mut targets := []
  for entry in entries do
    match entry.capability with
    | .nativeTMInNP endpoint =>
        match ← InputGate.canonicalPresentedHandle? entries endpoint with
        | none => pure ()
        | some problem =>
            let duplicate ← targets.findM? fun target =>
              controlledDefEq target.endpoint endpoint
            if duplicate.isNone then
              targets := targets ++ [{
                problem
                membershipDeclaration := entry.candidate
                endpoint
              }]
    | _ => pure ()
  return targets

private def emitSource (nonce : String) (source : InputGate.PresentedHandle) : MetaM Unit := do
  emit nonce "source" [source.declaration.toString, ← renderEndpoint source.term,
    ← endpointNodeId source.term]

private def emitTarget (nonce : String) (target : NativeTarget) : MetaM Unit := do
  emit nonce "target" [target.problem.declaration.toString,
    target.membershipDeclaration.toString, ← renderEndpoint target.endpoint,
    ← endpointNodeId target.endpoint]

private def inventoryCapabilityKind {environment : Environment} :
    ValidatedCertificateEdge environment → String
  | .reduction .. => "certified_reduction"
  | .equiv .. => "certified_equiv"
  | .presentationChange .. => "certified_presentation_change"

/--
Emit the complete validated certificate-edge inventory observed in this Lean
environment.  Every row is observational and fingerprint-bound.  Endpoints
remain exact `Expr`s inside Lean; hashes and pretty strings are diagnostics
for the external catalog only.
-/
private def emitTypedInventory (environment : Environment) (nonce fingerprint : String) :
    MetaM Unit := do
  for edge in validatedCertificateEdges environment do
    let role := edge.componentRole?.map toString |>.getD "unannotated"
    let isFinalFacade := edge.componentRole? == some .finalComposition
    emit nonce "inventory" [
      edge.observation.entry.candidate.toString,
      inventoryCapabilityKind edge,
      role,
      s!"lean:{edge.source.hash}",
      s!"lean:{edge.target.hash}",
      toString isFinalFacade,
      "registered",
      fingerprint,
      ← renderEndpoint edge.source,
      ← renderEndpoint edge.target,
      ← endpointNodeId edge.source,
      ← endpointNodeId edge.target]

private def emitRoute (nonce fingerprint : String)
    (targetDeclaration membershipDeclaration : Name)
    (path? : Option Protocol.ClosedResolver.ResolvedPath)
    (evidenceKind : Protocol.ClosedResolver.EvidenceKind)
    (completenessDeclaration? hubDeclaration? : Option Name := none) : MetaM Unit := do
  let provenance := path?.map (fun path => path.atomicProvenance) |>.getD []
  let declarations := provenance.map fun atom => atom.declaration.toString
  let roles := provenance.map fun atom =>
    match atom.role? with
    | some role => toString role
    | none => "unannotated"
  let finalPenalty := provenance.countP fun atom =>
    atom.role? == some .finalComposition
  let completenessDeclaration := completenessDeclaration?.getD .anonymous
  let hubDeclaration := hubDeclaration?.getD .anonymous
  let routePayload := String.intercalate "|"
    [targetDeclaration.toString, membershipDeclaration.toString,
      String.intercalate "," declarations, fingerprint, evidenceKind.label,
      completenessDeclaration.toString, hubDeclaration.toString]
  emit nonce "route" [s!"lean:{routePayload.hash}", targetDeclaration.toString,
    membershipDeclaration.toString, String.intercalate "," declarations,
    String.intercalate "," roles, toString finalPenalty, evidenceKind.label,
    completenessDeclaration.toString, hubDeclaration.toString]

private def canonicalProblemName? {environment : Environment}
    (entries : List (ValidatedEntry environment)) (preferred : InputGate.PresentedHandle)
    (endpoint : Expr) : MetaM (Option Name) := do
  if ← controlledDefEq preferred.term endpoint then
    return some preferred.declaration
  return (← InputGate.canonicalPresentedHandle? entries endpoint).map (fun handle =>
    handle.declaration)

private def emitResolvedRequest {environment : Environment}
    (nonce fingerprint : String) (entries : List (ValidatedEntry environment))
    (problem : InputGate.PresentedHandle)
    (resolved : Protocol.ClosedResolver.ResolvedExactRequest) : MetaM Unit := do
  let hubDeclaration? ← match resolved.hub? with
    | some hub => canonicalProblemName? entries problem hub
    | none => pure none
  emitRoute nonce fingerprint problem.declaration
    (resolved.membershipDeclaration?.getD .anonymous) resolved.path?
    resolved.evidenceKind resolved.completenessDeclaration? hubDeclaration?

private def gapEndpointHandle? {environment : Environment}
    (entries : List (ValidatedEntry environment))
    (preferred fallback : InputGate.PresentedHandle) (endpoint : Expr) :
    MetaM (Option InputGate.PresentedHandle) := do
  if ← controlledDefEq preferred.term endpoint then
    return some preferred
  if ← controlledDefEq fallback.term endpoint then
    return some fallback
  InputGate.canonicalPresentedHandle? entries endpoint

private def emitGap {environment : Environment} (nonce fingerprint : String)
    (entries : List (ValidatedEntry environment))
    (requestSource requestTarget : InputGate.PresentedHandle)
    (gap : Gap.ClassifiedGap) : MetaM Unit := do
  let some source ← gapEndpointHandle? entries requestSource requestTarget gap.source
    | return
  let some target ← gapEndpointHandle? entries requestTarget requestSource gap.target
    | return
  emit nonce "gap"
    [Gap.reasonLabel gap.reason,
      Gap.failureCode gap.reason,
      toString gap.role,
      source.declaration.toString,
      target.declaration.toString,
      (Gap.expectedCapabilityHead gap.reason).toString,
      ← renderEndpoint gap.source,
      ← renderEndpoint gap.target,
      "lean_gap_classifier",
      fingerprint]

private def classifyAndEmitGap {environment : Environment} (nonce fingerprint : String)
    (entries : List (ValidatedEntry environment))
    (requestSource requestTarget : InputGate.PresentedHandle)
    (failure : Protocol.ClosedResolver.Failure) : MetaM (Option Gap.ClassifiedGap) := do
  match ← Gap.classifyFailure environment failure with
  | some gap =>
      emitGap nonce fingerprint entries requestSource requestTarget gap
      return some gap
  | none => return none

private def emitClosedFamilyInstantiations (environment : Environment)
    (nonce fingerprint : String)
    (role : ReductionComponentRole)
    (source target : InputGate.PresentedHandle) : MetaM Unit := do
  for candidate in ← Authoring.closedReductionFamilyInstantiations
      environment source.term target.term do
    if candidate.role == role then
      emit nonce "family"
        [candidate.familyDeclaration.toString,
          String.intercalate "," <| candidate.argumentDeclarations.map Name.toString,
          toString candidate.role,
          source.declaration.toString,
          target.declaration.toString,
          "lean_parameterized_family_matcher",
          fingerprint]

private def emitExactTemplates
    (nonce fingerprint : String) (kind : Authoring.ExactTemplateKind)
    (source target : InputGate.PresentedHandle)
    (observations : List Authoring.ExactTemplateObservation) : MetaM Unit := do
  for observation in observations do
    emit nonce "template"
      [kind.label,
        observation.templateDeclaration.toString,
        toString observation.role,
        source.declaration.toString,
        target.declaration.toString,
        "lean_exact_authoring_template_matcher",
        fingerprint,
        String.intercalate "," <| observation.componentDeclarations.map Name.toString]

private def emitAuthoringObservations
    (environment : Environment) (nonce fingerprint : String)
    (entries : List (ValidatedEntry environment))
    (requestSource requestTarget : InputGate.PresentedHandle)
    (gap : Gap.ClassifiedGap) : MetaM Unit := do
  let some source ← gapEndpointHandle? entries requestSource requestTarget gap.source
    | return
  let some target ← gapEndpointHandle? entries requestTarget requestSource gap.target
    | return
  match gap.reason with
  | .unresolvedFamilyPremise =>
      emitClosedFamilyInstantiations environment nonce fingerprint gap.role source target
  | .lawfulPresentation =>
      let observations ← Authoring.lawfulPresentationTemplates
        environment gap.role gap.source gap.target
      emitExactTemplates nonce fingerprint .lawfulPresentation
        source target observations
  | .primitive =>
      let observations ← Authoring.primitiveAdmissionTemplates
        environment gap.role gap.source gap.target
      emitExactTemplates nonce fingerprint .primitiveAdmission
        source target observations
      let reductionObservations ← Authoring.programIndexedReductionTemplates
        environment gap.role gap.source gap.target
      emitExactTemplates nonce fingerprint .programIndexedReduction
        source target reductionObservations
  | .semanticProof | .directTM | .noRegistryPath | .reductionCapability =>
      let observations ← Authoring.programIndexedReductionTemplates
        environment gap.role gap.source gap.target
      emitExactTemplates nonce fingerprint .programIndexedReduction
        source target observations
      let modelObservations ← Authoring.programIndexedModelTemplates
        environment gap.role gap.source gap.target
      emitExactTemplates nonce fingerprint .programIndexedModel
        source target modelObservations
  | .verifierProgram | .witnessLawfulPresentation | .verifierEncodingDiscipline |
      .checkerCombinatorPairList | .checkerCombinatorUnsupported | .witnessBound |
      .soundnessLemma | .problemToKnownNP | .nativeMembership =>
      let observations ← Authoring.nativeMembershipTemplates environment gap.source
      emitExactTemplates nonce fingerprint .nativeMembership source target observations
  | _ => pure ()

private def requirePresented (environment : Environment) (declaration : Name) :
    MetaM InputGate.PresentedHandle := do
  match ← InputGate.presented environment declaration with
  | .ok handle => return handle
  | .error failure => throwError "hardness input rejected: {repr failure}"

private def requireValidatedPresented (environment : Environment) (declaration : Name) :
    MetaM InputGate.PresentedHandle := do
  match ← InputGate.validatedPresented environment declaration with
  | .ok handle => return handle
  | .error failure => throwError "hardness target rejected: {repr failure}"

private def exactNativeMembership? (environment : Environment) (target : Expr) :
    MetaM (Option Name) := do
  for entry in exportValidated environment do
    match entry.capability with
    | .nativeTMInNP endpoint =>
        if ← controlledDefEq endpoint target then
          match ← InputGate.nativeMembership environment entry.candidate target with
          | .ok _ => return some entry.candidate
          | .error _ => pure ()
    | _ => pure ()
  return none

private def runInventory (environment : Environment) (nonce : String) (sourceName : Name) :
    MetaM Unit := do
  let source ← requirePresented environment sourceName
  let entries := exportValidated environment
  let fingerprint := Registry.registryFingerprint entries
  emit nonce "registry" [fingerprint]
  emitTypedInventory environment nonce fingerprint
  emitSource nonce source
  for target in ← nativeTargets entries do
    emitTarget nonce target
    match ← Protocol.ClosedResolver.resolvePath environment source.term target.endpoint with
    | .ok path =>
        emitRoute nonce fingerprint target.problem.declaration target.membershipDeclaration
          (some path) .reductionToKnownNP
    | .error failure =>
        discard <| classifyAndEmitGap nonce fingerprint entries source target.problem failure

private def runExplicit (environment : Environment) (nonce : String) (sourceName targetName : Name)
    (requireNativeMembership : Bool)
    (catalogMode : Protocol.ClosedResolver.RouteCatalogMode := .full) : MetaM Unit := do
  let source ← requirePresented environment sourceName
  let target ← requireValidatedPresented environment targetName
  let entries := exportValidated environment
  let fingerprint := Registry.registryFingerprint entries
  emit nonce "registry" [fingerprint]
  emitTypedInventory environment nonce fingerprint
  emitSource nonce source
  let membership? ← exactNativeMembership? environment target.term
  let membershipName := membership?.getD .anonymous
  emit nonce "target" [target.declaration.toString,
    membership?.map (fun name => name.toString) |>.getD "", ← renderEndpoint target.term,
    ← endpointNodeId target.term]
  match ← Protocol.ClosedResolver.resolvePathWithCatalog environment source.term target.term
      catalogMode with
  | .error failure =>
      let gap? ← classifyAndEmitGap nonce fingerprint entries source target failure
      match gap? with
      | some gap => emitAuthoringObservations environment nonce fingerprint entries source target gap
      | none => pure ()
  | .ok path =>
      if requireNativeMembership && membership?.isNone then
        discard <| classifyAndEmitGap nonce fingerprint entries source target
          (.missingNativeMembership target.term)
      else
        emitRoute nonce fingerprint target.declaration membershipName (some path)
          (if requireNativeMembership then .reductionToKnownNP else .reduction)

private def exactPolicy : Protocol.AutoReductionTrustPolicy :=
  { presentation := .exactUser, requireNativeNP := true }

private def inNPRequest (problem : PresentedProblem) : Protocol.TypedAutoReductionRequest where
  source := .fromPresented problem
  policy := exactPolicy
  objective := .proveInNP problem

private def npCompleteRequest (problem : PresentedProblem) :
    Protocol.TypedAutoReductionRequest where
  source := .fromPresented problem
  policy := exactPolicy
  objective := .proveNPComplete problem

private def runCapabilityRequest (environment : Environment) (nonce : String)
    (sourceName requestConstructor : Name) : MetaM Unit := do
  let source ← requirePresented environment sourceName
  let entries := exportValidated environment
  let fingerprint := Registry.registryFingerprint entries
  emit nonce "registry" [fingerprint]
  emitTypedInventory environment nonce fingerprint
  emitSource nonce source
  let membership? ← exactNativeMembership? environment source.term
  emit nonce "target" [source.declaration.toString,
    membership?.map Name.toString |>.getD "", ← renderEndpoint source.term,
    ← endpointNodeId source.term]
  let request ← mkAppM requestConstructor #[source.term]
  match ← Protocol.ClosedResolver.resolveExactRequestDetailed environment request with
  | .ok resolved => emitResolvedRequest nonce fingerprint entries source resolved
  | .error failure =>
      let gap? ← classifyAndEmitGap nonce fingerprint entries source source failure
      match gap? with
      | some gap => emitAuthoringObservations environment nonce fingerprint entries source source gap
      | none => pure ()

syntax (name := hardnessProbe) "#hardness_probe " str ident : command
syntax (name := hardnessProbeTo) "#hardness_probe_to " str ident ident : command
syntax (name := hardnessProbeToFlat) "#hardness_probe_to_flat " str ident ident : command
syntax (name := hardnessProbeToIR) "#hardness_probe_to_ir " str ident ident : command
syntax (name := hardnessProbeToKnownNP) "#hardness_probe_to_known_np " str ident ident : command
syntax (name := hardnessProbeInNP) "#hardness_probe_in_np " str ident : command
syntax (name := hardnessProbeNPComplete) "#hardness_probe_np_complete " str ident : command

elab_rules : command
  | `(#hardness_probe $nonce:str $source:ident) => do
      let sourceName ← resolveGlobalConstNoOverload source
      let environment ← getEnv
      Command.liftTermElabM <| runInventory environment nonce.getString sourceName
  | `(#hardness_probe_to $nonce:str $source:ident $target:ident) => do
      let sourceName ← resolveGlobalConstNoOverload source
      let targetName ← resolveGlobalConstNoOverload target
      let environment ← getEnv
      Command.liftTermElabM <| runExplicit environment nonce.getString sourceName targetName false
  | `(#hardness_probe_to_flat $nonce:str $source:ident $target:ident) => do
      let sourceName ← resolveGlobalConstNoOverload source
      let targetName ← resolveGlobalConstNoOverload target
      let environment ← getEnv
      Command.liftTermElabM <| runExplicit environment nonce.getString sourceName targetName false
        .flatAPI
  | `(#hardness_probe_to_ir $nonce:str $source:ident $target:ident) => do
      let sourceName ← resolveGlobalConstNoOverload source
      let targetName ← resolveGlobalConstNoOverload target
      let environment ← getEnv
      Command.liftTermElabM <| runExplicit environment nonce.getString sourceName targetName false
        .irComponents
  | `(#hardness_probe_to_known_np $nonce:str $source:ident $target:ident) => do
      let sourceName ← resolveGlobalConstNoOverload source
      let targetName ← resolveGlobalConstNoOverload target
      let environment ← getEnv
      Command.liftTermElabM <| runExplicit environment nonce.getString sourceName targetName true
  | `(#hardness_probe_in_np $nonce:str $source:ident) => do
      let sourceName ← resolveGlobalConstNoOverload source
      let environment ← getEnv
      Command.liftTermElabM <| runCapabilityRequest environment nonce.getString sourceName
        ``inNPRequest
  | `(#hardness_probe_np_complete $nonce:str $source:ident) => do
      let sourceName ← resolveGlobalConstNoOverload source
      let environment ← getEnv
      Command.liftTermElabM <| runCapabilityRequest environment nonce.getString sourceName
        ``npCompleteRequest

end ComplexityReduction.Agent.Hardness.Probe
