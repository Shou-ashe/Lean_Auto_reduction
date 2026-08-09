/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Protocol.ClosedResolver
import ComplexityReduction.Protocol.ComponentRequest
import ComplexityReduction.Registry.ParameterizedFamily
import Lean.Attributes
import Lean.Meta.Basic

/-!
Lean-side typed gap classification for the hardness agent.

The classifier keeps the exact elaborated endpoints and the closed
`MissingCapabilityReason` in Lean.  Its output is diagnostic only: it has no
operation that constructs a primitive, certificate, path, membership theorem,
or final request result.  The external runner may serialize and schedule this
information, but the final resolver never consumes that serialization.
-/

namespace ComplexityReduction.Agent.Hardness.Gap

open Lean Meta Encoding Registry

/--
An exact component gap declaration available to public input modules.

The reason, role, and both endpoints are indices.  A declaration of this type
can refine a failed path into a scheduling diagnosis, but it grants no trusted
capability and cannot be converted into a successful resolver result.
-/
inductive DeclaredComponentGap
    (reason : Protocol.MissingCapabilityReason)
    (role : ReductionComponentRole)
    (source target : PresentedProblem) : Type 2 where
  | exact : DeclaredComponentGap reason role source target

/-- Discovery-only marker for an exact typed gap declaration. -/
initialize typedGapAttr : Lean.TagAttribute ←
  Lean.registerTagAttribute `complexity_reduction_ir_typed_gap
    "marks a typed hardness-agent gap declaration; grants no trusted capability"

/-- The exact meta-level endpoint retained by one classified blocker. -/
structure ExactEndpoint where
  role : ReductionComponentRole
  source : Expr
  target : Expr

/-- A classified blocker is the shared closed missing-capability type at one exact endpoint. -/
structure ClassifiedGap where
  missing : Protocol.MissingCapability ExactEndpoint

namespace ClassifiedGap

def reason (gap : ClassifiedGap) : Protocol.MissingCapabilityReason :=
  gap.missing.reason

def role (gap : ClassifiedGap) : ReductionComponentRole :=
  gap.missing.endpoint.role

def source (gap : ClassifiedGap) : Expr :=
  gap.missing.endpoint.source

def target (gap : ClassifiedGap) : Expr :=
  gap.missing.endpoint.target

end ClassifiedGap

private def mkGap (reason : Protocol.MissingCapabilityReason)
    (role : ReductionComponentRole) (source target : Expr) : ClassifiedGap :=
  { missing := { endpoint := { role, source, target }, reason } }

/-- Stable external spelling of the closed reason enum. -/
def reasonLabel : Protocol.MissingCapabilityReason → String
  | .lawfulPresentation => "lawfulPresentation"
  | .primitive => "primitive"
  | .semanticProof => "semanticProof"
  | .executableRelationContract => "executableRelationContract"
  | .directTM => "directTM"
  | .verifierEncodingDiscipline => "verifierEncodingDiscipline"
  | .verifierProgram => "verifierProgram"
  | .witnessLawfulPresentation => "witnessLawfulPresentation"
  | .unresolvedFamilyPremise => "unresolvedFamilyPremise"
  | .noRegistryPath => "noRegistryPath"
  | .reductionCapability => "reductionCapability"
  | .checkerCombinatorPairList => "checkerCombinatorPairList"
  | .checkerCombinatorUnsupported => "checkerCombinatorUnsupported"
  | .witnessBound => "witnessBound"
  | .soundnessLemma => "soundnessLemma"
  | .problemToKnownNP => "problemToKnownNP"
  | .nativeMembership => "nativeMembership"
  | .nativeCompleteness => "nativeCompleteness"

/-- Stable blocked-status code projected from the closed reason enum. -/
def failureCode : Protocol.MissingCapabilityReason → String
  | .lawfulPresentation => "missing_lawful_presentation"
  | .primitive => "missing_primitive"
  | .semanticProof => "missing_semantic_proof"
  | .executableRelationContract => "missing_executable_relation_contract"
  | .directTM => "missing_direct_tm"
  | .verifierEncodingDiscipline => "missing_verifier_discipline"
  | .verifierProgram => "missing_verifier_program"
  | .witnessLawfulPresentation => "missing_witness_lawful_presentation"
  | .unresolvedFamilyPremise => "unresolved_family_premise"
  | .noRegistryPath => "no_registry_path"
  | .reductionCapability => "missing_reduction_capability"
  | .checkerCombinatorPairList => "missing_checker_combinator:pair_list"
  | .checkerCombinatorUnsupported =>
      "missing_checker_combinator:unsupported_local_checker"
  | .witnessBound => "missing_witness_bound"
  | .soundnessLemma => "missing_soundness_lemma"
  | .problemToKnownNP => "missing_problem_to_known_np"
  | .nativeMembership => "missing_native_membership"
  | .nativeCompleteness => "missing_native_completeness"

/-- Canonical capability head expected by a one-gap authoring task. -/
def expectedCapabilityHead : Protocol.MissingCapabilityReason → Name
  | .lawfulPresentation =>
      ``ComplexityReduction.Encoding.StructuralRepresentationCertificate
  | .primitive => ``ComplexityReduction.Program.Primitive
  | .semanticProof => ``ComplexityReduction.Certificate.CertifiedReduction
  | .executableRelationContract => ``ComplexityReduction.Program.PolyProg
  | .directTM => ``ComplexityReduction.TMPolyTimeMap
  | .verifierEncodingDiscipline =>
      ``ComplexityReduction.Certificate.CertifiedVerifierEncodingDiscipline
  | .verifierProgram => ``ComplexityReduction.Certificate.CertifiedVerifier
  | .witnessLawfulPresentation =>
      ``ComplexityReduction.Encoding.StructuralRepresentationCertificate
  | .unresolvedFamilyPremise =>
      ``ComplexityReduction.Registry.ParameterizedCapabilityFamilyObservation
  | .noRegistryPath => ``ComplexityReduction.Certificate.CertifiedReduction
  | .reductionCapability => ``ComplexityReduction.Certificate.CertifiedReduction
  | .checkerCombinatorPairList
  | .checkerCombinatorUnsupported
  | .witnessBound
  | .soundnessLemma => ``ComplexityReduction.Certificate.CertifiedVerifier
  | .problemToKnownNP => ``ComplexityReduction.Certificate.NativeTMInNP
  | .nativeMembership => ``ComplexityReduction.Certificate.NativeTMInNP
  | .nativeCompleteness => ``ComplexityReduction.Certificate.NativeTMNPComplete

private def controlledDefEq (first second : Expr) : MetaM Bool := do
  isDefEq (← whnf first) (← whnf second)

private def candidatesOfAttribute (tag : Lean.TagAttribute) (environment : Environment) :
    Lean.NameSet :=
  let discovered :=
    (Array.range environment.allImportedModuleNames.size).foldl
      (fun candidates moduleIndex =>
        (tag.ext.getModuleEntries environment moduleIndex).foldl
          (fun candidates candidate => candidates.insert candidate) candidates)
      (tag.ext.getState environment)
  discovered.foldl
    (fun candidates candidate =>
      if tag.hasTag environment candidate then candidates.insert candidate else candidates)
    {}

private def declaredGapCandidateNames (environment : Environment) : List Name :=
  Std.TreeSet.toList (candidatesOfAttribute typedGapAttr environment)

private def reasonOfExpr? (expression : Expr) : Option Protocol.MissingCapabilityReason :=
  let expression := expression.consumeMData
  if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.lawfulPresentation then
    some .lawfulPresentation
  else if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.primitive then
    some .primitive
  else if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.semanticProof then
    some .semanticProof
  else if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.executableRelationContract then
    some .executableRelationContract
  else if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.directTM then
    some .directTM
  else if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.verifierEncodingDiscipline then
    some .verifierEncodingDiscipline
  else if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.verifierProgram then
    some .verifierProgram
  else if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.witnessLawfulPresentation then
    some .witnessLawfulPresentation
  else if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.unresolvedFamilyPremise then
    some .unresolvedFamilyPremise
  else if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.noRegistryPath then
    some .noRegistryPath
  else if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.reductionCapability then
    some .reductionCapability
  else if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.checkerCombinatorPairList then
    some .checkerCombinatorPairList
  else if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.checkerCombinatorUnsupported then
    some .checkerCombinatorUnsupported
  else if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.witnessBound then
    some .witnessBound
  else if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.soundnessLemma then
    some .soundnessLemma
  else if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.problemToKnownNP then
    some .problemToKnownNP
  else if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.nativeMembership then
    some .nativeMembership
  else if expression.isConstOf
      ``ComplexityReduction.Protocol.MissingCapabilityReason.nativeCompleteness then
    some .nativeCompleteness
  else
    none

private def roleOfExpr? (expression : Expr) : Option ReductionComponentRole :=
  let expression := expression.consumeMData
  if expression.isConstOf ``ComplexityReduction.ReductionComponentRole.ingress then
    some .ingress
  else if expression.isConstOf ``ComplexityReduction.ReductionComponentRole.sharedGadget then
    some .sharedGadget
  else if expression.isConstOf ``ComplexityReduction.ReductionComponentRole.egress then
    some .egress
  else if expression.isConstOf ``ComplexityReduction.ReductionComponentRole.finalComposition then
    some .finalComposition
  else
    none

private structure DeclaredGapClassification where
  reason : Protocol.MissingCapabilityReason
  role : ReductionComponentRole
  source : Expr
  target : Expr

/--
One public, read-only observation of an attributed exact gap declaration.

The expressions are the elaborated indices of `DeclaredComponentGap`; callers
may inspect them with controlled definitional equality, but the observation
does not grant a registry capability or construct proof evidence.
-/
structure DeclaredGapObservation where
  declaration : Name
  reason : Protocol.MissingCapabilityReason
  role : ReductionComponentRole
  source : Expr
  target : Expr

private def classifyDeclaredGapType? (type : Expr) : Option DeclaredGapClassification := do
  if type.hasFVar || type.hasMVar || type.hasLooseBVars || type.hasLevelParam then
    none
  else
    let normalized := type.consumeMData
    if normalized.getAppFn.consumeMData.isConstOf
        ``ComplexityReduction.Agent.Hardness.Gap.DeclaredComponentGap then
      match normalized.getAppArgs with
      | #[reasonExpression, roleExpression, source, target] =>
          let reason ← reasonOfExpr? reasonExpression
          let role ← roleOfExpr? roleExpression
          some { reason, role, source, target }
      | _ => none
    else
      none

/-- Enumerate every valid public typed-gap declaration in deterministic name order. -/
def declaredGapObservations (environment : Environment) : List DeclaredGapObservation :=
  (declaredGapCandidateNames environment).filterMap fun declaration => do
    let information ← environment.find? declaration
    let classified ← classifyDeclaredGapType? information.type
    some {
      declaration
      reason := classified.reason
      role := classified.role
      source := classified.source
      target := classified.target
    }

private def declaredGap? (environment : Environment) (source target : Expr) :
    MetaM (Option ClassifiedGap) := do
  for observation in declaredGapObservations environment do
    unless ← controlledDefEq observation.source source do
      continue
    unless ← controlledDefEq observation.target target do
      continue
    return some (mkGap observation.reason observation.role source target)
  return none

private structure PresentedCandidate where
  declaration : Name
  endpoint : Expr

private def presentedCandidates (environment : Environment) : List PresentedCandidate :=
  (exportValidated environment).filterMap fun entry =>
    match entry.capability with
    | .presentedProblem => some { declaration := entry.candidate, endpoint := mkConst entry.candidate }
    | _ => none

private def sameSemanticProblem (first second : Expr) : MetaM Bool := do
  let firstSemantic ← mkAppM ``ComplexityReduction.Encoding.PresentedProblem.semantic #[first]
  let secondSemantic ← mkAppM ``ComplexityReduction.Encoding.PresentedProblem.semantic #[second]
  controlledDefEq firstSemantic secondSemantic

/--
Conservatively recognize a presentation mismatch only when a validated exact
problem with the same semantic problem closes the remaining registry path.
Carrier equality alone is never inspected.
-/
private def representationGap? (environment : Environment) (source target : Expr) :
    MetaM (Option ClassifiedGap) := do
  for candidate in presentedCandidates environment do
    unless ← controlledDefEq source candidate.endpoint do
      if ← sameSemanticProblem source candidate.endpoint then
        match ← Protocol.ClosedResolver.resolvePath environment candidate.endpoint target with
        | .ok _ => return some (mkGap .lawfulPresentation .ingress source candidate.endpoint)
        | .error _ => pure ()
  for candidate in presentedCandidates environment do
    unless ← controlledDefEq target candidate.endpoint do
      if ← sameSemanticProblem target candidate.endpoint then
        match ← Protocol.ClosedResolver.resolvePath environment source candidate.endpoint with
        | .ok _ => return some (mkGap .lawfulPresentation .egress candidate.endpoint target)
        | .error _ => pure ()
  return none

private def hasExactVerifierDiscipline {environment : Environment}
    (entries : List (ValidatedEntry environment))
    (problem verifier : Expr) : MetaM Bool := do
  entries.anyM fun entry =>
    match entry.capability with
    | .verifierEncodingDiscipline checkedProblem checkedVerifier => do
        unless ← controlledDefEq checkedProblem problem do
          return false
        controlledDefEq checkedVerifier verifier
    | _ => return false

private def hasBackendVerifierWithoutDiscipline (environment : Environment) (target : Expr) :
    MetaM Bool := do
  let entries := exportValidated environment
  for entry in entries do
    match entry.capability with
    | .backendVerifier problem =>
        if ← controlledDefEq problem target then
          let verifier := mkConst entry.candidate
          unless ← hasExactVerifierDiscipline entries problem verifier do
            return true
    | _ => pure ()
  return false

/--
Map a closed-resolver failure to a typed scheduling gap when that mapping is
reliable.  Configuration and malformed-request failures remain ordinary
failures.  An unrefined missing path stays `noRegistryPath`.
-/
def classifyFailure (environment : Environment) :
    Protocol.ClosedResolver.Failure → MetaM (Option ClassifiedGap)
  | .noRegistryPath source target => do
      match ← declaredGap? environment source target with
      | some gap => return some gap
      | none =>
          match ← representationGap? environment source target with
          | some gap => return some gap
          | none => return some (mkGap .noRegistryPath .finalComposition source target)
  | .missingNativeMembership target => do
      match ← declaredGap? environment target target with
      | some gap => return some gap
      | none =>
          let reason ←
            if ← hasBackendVerifierWithoutDiscipline environment target then
              pure Protocol.MissingCapabilityReason.verifierEncodingDiscipline
            else
              pure Protocol.MissingCapabilityReason.nativeMembership
          return some (mkGap reason .finalComposition target target)
  | .missingNativeCompleteness target =>
      return some (mkGap .nativeCompleteness .finalComposition target target)
  | .aggregateNotImported
  | .malformedRequest _
  | .unsupportedRequest _
  | .sourceObjectiveMismatch _ _ => return none

end ComplexityReduction.Agent.Hardness.Gap
