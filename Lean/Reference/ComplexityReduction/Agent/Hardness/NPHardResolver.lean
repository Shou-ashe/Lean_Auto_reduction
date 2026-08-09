/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Protocol.NPHard
import ComplexityReduction.Protocol.ClosedResolver
import Lean.Elab.Term

/-!
Deterministic V1 resolver for exact native NP-hardness requests.

The requested problem is only ever a search target.  Seeds come from exact
validated `NativeTMNPHard` declarations or the hardness projection of exact
validated `NativeTMNPComplete` declarations.  Route atoms are supplied by the
closed registry resolver and are revalidated before entering the result term.
-/

namespace ComplexityReduction.Agent.Hardness.NPHardResolver

open Lean Elab Term Meta
open Encoding Certificate Registry

/-- The closed failure-code vocabulary frozen by the V1 NP-hardness protocol. -/
inductive NPHardFailureCodeV1 where
  | aggregateNotImported
  | malformedNPHardRequest
  | inputNotPresentedProblem
  | inputOpenOrPolymorphic
  | noNativeHardnessSeed
  | noForwardPathFromHardnessSeed
  | wrongDirectionOnly
  | representationMismatch
  | missingCertifiedReduction
  | missingSemanticProof
  | missingDirectTM
  | candidateWrongEndpoint
  | candidateWrongDirection
  | candidateNonstandardAxiom
  | candidateDependencyStale
  | authoringBudgetExhausted
  | requiredModelUnavailable
  | finalNPHardResolutionFailed
  | independentReplayFailed
  deriving BEq, Repr

namespace NPHardFailureCodeV1

/-- Stable external spellings used by the request/result and benchmark ABIs. -/
def label : NPHardFailureCodeV1 → String
  | .aggregateNotImported => "aggregate_not_imported"
  | .malformedNPHardRequest => "malformed_np_hard_request"
  | .inputNotPresentedProblem => "input_not_presented_problem"
  | .inputOpenOrPolymorphic => "input_open_or_polymorphic"
  | .noNativeHardnessSeed => "no_native_hardness_seed"
  | .noForwardPathFromHardnessSeed => "no_forward_path_from_hardness_seed"
  | .wrongDirectionOnly => "wrong_direction_only"
  | .representationMismatch => "representation_mismatch"
  | .missingCertifiedReduction => "missing_certified_reduction"
  | .missingSemanticProof => "missing_semantic_proof"
  | .missingDirectTM => "missing_direct_tm"
  | .candidateWrongEndpoint => "candidate_wrong_endpoint"
  | .candidateWrongDirection => "candidate_wrong_direction"
  | .candidateNonstandardAxiom => "candidate_nonstandard_axiom"
  | .candidateDependencyStale => "candidate_dependency_stale"
  | .authoringBudgetExhausted => "authoring_budget_exhausted"
  | .requiredModelUnavailable => "required_model_unavailable"
  | .finalNPHardResolutionFailed => "final_np_hard_resolution_failed"
  | .independentReplayFailed => "independent_replay_failed"

end NPHardFailureCodeV1

/--
Typed V1 failure payload.  Expression and declaration handles are diagnostic
only; no failure payload can be converted into a certificate.
-/
structure NPHardFailureV1 where
  code : NPHardFailureCodeV1
  requestId : String
  registryFingerprint : String
  request? : Option Expr := none
  problem? : Option Expr := none
  relatedEndpoint? : Option Expr := none
  declarationHandles : List Name := []
  stableGapId? : Option String := none
  explanation : String := ""
  deriving Repr

/-- The two admitted sources of exact V1 NP-hardness evidence. -/
inductive NPHardEvidenceKindV1 where
  | registeredHardness
  | transportedHardness
  deriving BEq, Repr

namespace NPHardEvidenceKindV1

def label : NPHardEvidenceKindV1 → String
  | .registeredHardness => "registered_hardness"
  | .transportedHardness => "transported_hardness"

end NPHardEvidenceKindV1

/-- Observational provenance returned beside the exact request-indexed term. -/
structure ResolvedNPHardRequestV1 where
  result : Expr
  evidenceKind : NPHardEvidenceKindV1
  hubDeclaration? : Option Name := none
  hardnessDeclaration? : Option Name := none
  completenessDeclaration? : Option Name := none
  path? : Option Protocol.ClosedResolver.ResolvedPath := none
  atomicRouteProvenance : List Protocol.ClosedResolver.AtomicProvenance := []
  registryFingerprint : String

private def controlledDefEq (first second : Expr) : MetaM Bool := do
  isDefEq (← whnf first) (← whnf second)

private def projection (name : Name) (structureTerm : Expr) : MetaM Expr :=
  mkAppM name #[structureTerm]

private def requestId (request : Expr) : String :=
  s!"lean:{request.hash}"

/--
Session-local deterministic fingerprint of the exact validated declarations.
The external runner will additionally bind this value to toolchain and source
hashes; the resolver retains it solely as observational provenance.
-/
def registryFingerprint (environment : Environment) : String :=
  let rows := (Registry.exportValidated environment).map fun entry =>
    s!"{entry.candidate}:{entry.elaboratedType.hash}"
  s!"lean:{(String.intercalate "|" rows).hash}"

private def failure (environment : Environment) (request : Expr)
    (code : NPHardFailureCodeV1) (explanation : String)
    (problem? : Option Expr := none) (relatedEndpoint? : Option Expr := none)
    (declarationHandles : List Name := []) : NPHardFailureV1 where
  code := code
  requestId := requestId request
  registryFingerprint := registryFingerprint environment
  request? := some request
  problem? := problem?
  relatedEndpoint? := relatedEndpoint?
  declarationHandles := declarationHandles
  explanation := explanation

private structure HardnessSeed where
  declaration : Name
  endpoint : Expr
  hardnessTerm : Expr
  completenessDeclaration? : Option Name := none

private def revalidatedHardnessSeeds (environment : Environment) : MetaM (List HardnessSeed) := do
  let mut seeds := []
  for entry in Registry.exportValidated environment do
    match entry.capability with
    | .nativeTMNPHard endpoint =>
        let hardness := Lean.mkConst entry.candidate
        match Registry.classifyElaboratedType (← inferType hardness) with
        | some (.nativeTMNPHard checkedEndpoint) =>
            if ← controlledDefEq checkedEndpoint endpoint then
              seeds := seeds ++ [{
                declaration := entry.candidate
                endpoint
                hardnessTerm := hardness
              }]
        | _ => pure ()
    | .nativeTMNPComplete endpoint =>
        let completeness := Lean.mkConst entry.candidate
        match Registry.classifyElaboratedType (← inferType completeness) with
        | some (.nativeTMNPComplete checkedEndpoint) =>
            if ← controlledDefEq checkedEndpoint endpoint then
              let hardness ← mkAppM
                ``ComplexityReduction.Certificate.NativeTMNPComplete.nativeHardness
                #[completeness]
              match Registry.classifyElaboratedType (← inferType hardness) with
              | some (.nativeTMNPHard projectedEndpoint) =>
                  if ← controlledDefEq projectedEndpoint endpoint then
                    seeds := seeds ++ [{
                      declaration := entry.candidate
                      endpoint
                      hardnessTerm := hardness
                      completenessDeclaration? := some entry.candidate
                    }]
              | _ => pure ()
        | _ => pure ()
    | _ => pure ()
  return seeds

private def canonicalProblemDeclaration? (environment : Environment) (endpoint : Expr) :
    MetaM (Option Name) := do
  for entry in Registry.exportValidated environment do
    match entry.capability with
    | .presentedProblem =>
        if ← controlledDefEq (Lean.mkConst entry.candidate) endpoint then
          return some entry.candidate
    | _ => pure ()
  return none

private structure ForwardCandidate where
  seed : HardnessSeed
  path : Protocol.ClosedResolver.ResolvedPath

private def ForwardCandidate.finalCompositionCount (candidate : ForwardCandidate) : Nat :=
  candidate.path.atomicProvenance.countP fun provenance =>
    provenance.role? == some .finalComposition

private def ForwardCandidate.uniqueDependencyCount (candidate : ForwardCandidate) : Nat :=
  (candidate.path.atomicProvenance.map fun provenance => provenance.declaration).dedup.length

private def ForwardCandidate.routeDeclarationKey (candidate : ForwardCandidate) : String :=
  String.intercalate "\n" <|
    candidate.path.atomicProvenance.map fun provenance => provenance.declaration.toString

/-- The exact deterministic ordering frozen in section 5.2 of the active plan. -/
private def ForwardCandidate.lt (left right : ForwardCandidate) : Bool :=
  if left.path.atoms.length < right.path.atoms.length then true
  else if right.path.atoms.length < left.path.atoms.length then false
  else if left.finalCompositionCount < right.finalCompositionCount then true
  else if right.finalCompositionCount < left.finalCompositionCount then false
  else if left.uniqueDependencyCount < right.uniqueDependencyCount then true
  else if right.uniqueDependencyCount < left.uniqueDependencyCount then false
  else if left.seed.declaration.toString < right.seed.declaration.toString then true
  else if right.seed.declaration.toString < left.seed.declaration.toString then false
  else decide (left.routeDeclarationKey < right.routeDeclarationKey)

private def insertForwardCandidate (candidate : ForwardCandidate) :
    List ForwardCandidate → List ForwardCandidate
  | [] => [candidate]
  | first :: rest =>
      if candidate.lt first then candidate :: first :: rest
      else first :: insertForwardCandidate candidate rest

private def resultHasRequestType (request result : Expr) : MetaM Bool := do
  let actual ← inferType result
  let expected ← mkAppM ``ComplexityReduction.Protocol.TypedNPHardResultV1 #[request]
  controlledDefEq actual expected

private def exactRegisteredHardness? (seeds : List HardnessSeed) (problem : Expr) :
    MetaM (Option HardnessSeed) := do
  for seed in seeds do
    if seed.completenessDeclaration?.isNone && (← controlledDefEq seed.endpoint problem) then
      return some seed
  return none

private def forwardCandidates (environment : Environment) (problem : Expr)
    (seeds : List HardnessSeed) : MetaM (List ForwardCandidate) := do
  let mut candidates := []
  for seed in seeds do
    match ← Protocol.ClosedResolver.resolvePathLengthFirst environment seed.endpoint problem with
    | .ok path =>
        candidates := insertForwardCandidate { seed, path } candidates
    | .error _ => pure ()
  return candidates

private def reverseOnlySeed? (environment : Environment) (problem : Expr)
    (seeds : List HardnessSeed) : MetaM (Option HardnessSeed) := do
  for seed in seeds do
    match ← Protocol.ClosedResolver.resolvePathLengthFirst environment problem seed.endpoint with
    | .ok _ => return some seed
    | .error _ => pure ()
  return none

/--
Resolve one exact V1 request.  Only the `result` field carries authority; all
other fields are observations of the same Lean-side selection.
-/
def resolveNPHardRequestV1 (environment : Environment) (request : Expr) :
    MetaM (Except NPHardFailureV1 ResolvedNPHardRequestV1) := do
  if !Protocol.ClosedResolver.hasProductionAggregate environment then
    return .error <| failure environment request .aggregateNotImported
      "ComplexityReduction.Registry.Aggregate is not imported"
  let requestType ← whnf (← inferType request)
  unless requestType.consumeMData.isConstOf
      ``ComplexityReduction.Protocol.TypedNPHardRequestV1 do
    return .error <| failure environment request .malformedNPHardRequest
      "request does not have exact type Protocol.TypedNPHardRequestV1"
  if request.hasFVar || request.hasMVar || request.hasLooseBVars || request.hasLevelParam then
    return .error <| failure environment request .inputOpenOrPolymorphic
      "request contains an open variable, metavariable, or universe parameter"
  let problem ← whnf (← projection
    ``ComplexityReduction.Protocol.TypedNPHardRequestV1.problem request)
  if problem.hasFVar || problem.hasMVar || problem.hasLooseBVars || problem.hasLevelParam then
    return .error <| failure environment request .inputOpenOrPolymorphic
      "projected input problem is open or polymorphic" (some problem)
  let problemType ← whnf (← inferType problem)
  unless problemType.consumeMData.isConstOf
      ``ComplexityReduction.Encoding.PresentedProblem do
    return .error <| failure environment request .inputNotPresentedProblem
      "request.problem is not an exact PresentedProblem" (some problem)
  let seeds ← revalidatedHardnessSeeds environment
  if seeds.isEmpty then
    return .error <| failure environment request .noNativeHardnessSeed
      "the validated registry exports neither native hardness nor native completeness"
      (some problem)
  if let some seed ← exactRegisteredHardness? seeds problem then
    let result ← mkAppM
      ``ComplexityReduction.Protocol.TypedNPHardResultV1.fromRegistered
      #[request, seed.hardnessTerm]
    let result ← instantiateMVars result
    unless ← resultHasRequestType request result do
      return .error <| failure environment request .finalNPHardResolutionFailed
        "registered hardness produced a result at the wrong request index"
        (some problem) (some seed.endpoint) [seed.declaration]
    return .ok {
      result
      evidenceKind := .registeredHardness
      hubDeclaration? := ← canonicalProblemDeclaration? environment seed.endpoint
      hardnessDeclaration? := some seed.declaration
      registryFingerprint := registryFingerprint environment
    }
  let candidates ← forwardCandidates environment problem seeds
  match candidates.head? with
  | some candidate =>
      let result ← mkAppM
        ``ComplexityReduction.Protocol.TypedNPHardResultV1.fromPath
        #[request, candidate.seed.hardnessTerm, candidate.path.path]
      let result ← instantiateMVars result
      unless ← resultHasRequestType request result do
        return .error <| failure environment request .finalNPHardResolutionFailed
          "transported hardness produced a result at the wrong request index"
          (some problem) (some candidate.seed.endpoint) [candidate.seed.declaration]
      return .ok {
        result
        evidenceKind := .transportedHardness
        hubDeclaration? := ← canonicalProblemDeclaration? environment candidate.seed.endpoint
        hardnessDeclaration? :=
          if candidate.seed.completenessDeclaration?.isNone then
            some candidate.seed.declaration
          else none
        completenessDeclaration? := candidate.seed.completenessDeclaration?
        path? := some candidate.path
        atomicRouteProvenance := candidate.path.atomicProvenance
        registryFingerprint := registryFingerprint environment
      }
  | none =>
      match ← reverseOnlySeed? environment problem seeds with
      | some reverseSeed =>
          return .error <| failure environment request .wrongDirectionOnly
            "a request.problem → hardness-seed path exists, but no hardness-seed → request.problem path exists"
            (some problem) (some reverseSeed.endpoint) [reverseSeed.declaration]
      | none =>
          return .error <| failure environment request .noForwardPathFromHardnessSeed
            "no validated forward path reaches request.problem from any native hardness seed"
            (some problem) none (seeds.map (fun seed => seed.declaration))

/-- Compatibility projection for term elaboration. -/
def resolveNPHardRequestV1Term (environment : Environment) (request : Expr) :
    MetaM (Except NPHardFailureV1 Expr) := do
  match ← resolveNPHardRequestV1 environment request with
  | .ok resolved => return .ok resolved.result
  | .error resolverFailure => return .error resolverFailure

syntax (name := byNPHardResolver) "by_np_hard_resolver" : term

@[term_elab byNPHardResolver]
def elabByNPHardResolver : TermElab := fun stx expectedType? => do
  let some expectedType := expectedType?
    | throwErrorAt stx "by_np_hard_resolver requires an expected TypedNPHardResultV1 type"
  let expectedType ← instantiateMVars expectedType
  let normalized := (← whnf expectedType).consumeMData
  unless normalized.getAppFn.consumeMData.isConstOf
      ``ComplexityReduction.Protocol.TypedNPHardResultV1 do
    throwErrorAt stx "expected type is not Protocol.TypedNPHardResultV1"
  let #[request] := normalized.getAppArgs
    | throwErrorAt stx "malformed TypedNPHardResultV1 expected type"
  match ← resolveNPHardRequestV1Term (← getEnv) request with
  | .ok result => ensureHasType expectedType? result
  | .error resolverFailure =>
      throwErrorAt stx m!"NP-hardness request could not be closed: {repr resolverFailure}"

end ComplexityReduction.Agent.Hardness.NPHardResolver
