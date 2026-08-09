/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Registry.Graph
import ComplexityReduction.Protocol.Result
import Lean.Elab.Term
import Lean.Meta.Basic

/-!
Closed/exact path and request resolution.

This is deliberately a Lean-session service rather than a second term-level
registry.  It consumes only declaration-local candidates which have already
passed `Registry.validateAttributedDeclaration`, reconnects endpoints only by
controlled `whnf` plus kernel definitional equality, and produces an
elaborated `CertifiedPath` term.  In particular it has no string-to-term,
metadata, descriptor, bare-cost, or whole-route-authoring input.

`Registry.Aggregate` remains an explicit consumer import.  The public
surface exports this resolver without importing that aggregate, so an absent
aggregate is reported as an import-configuration failure rather than a
durable missing-route blocker.
-/

namespace ComplexityReduction
namespace Protocol
namespace ClosedResolver

open Lean Meta Encoding Certificate

/-- The production aggregate is an explicit environment prerequisite for closed path search. -/
def productionAggregateModule : Name :=
  Name.str (Name.str (Name.str .anonymous "ComplexityReduction") "Registry") "Aggregate"

/-- Check only the imported-module environment; this is not a registry capability query. -/
def hasProductionAggregate (environment : Environment) : Bool :=
  environment.allImportedModuleNames.contains productionAggregateModule

/-- Failures retain exact elaborated endpoints and keep configuration distinct from missing paths. -/
inductive Failure where
  | aggregateNotImported
  | malformedRequest (request : Expr)
  | unsupportedRequest (request : Expr)
  | sourceObjectiveMismatch (source objectiveSource : Expr)
  | noRegistryPath (source target : Expr)
  | missingNativeMembership (target : Expr)
  | missingNativeCompleteness (target : Expr)
  deriving Repr

/-- A session-resolved path retains its source, target, revalidated atomic terms, and path term. -/
structure AtomicProvenance where
  declaration : Name
  role? : Option ReductionComponentRole
  deriving Repr

structure ResolvedPath where
  source : Expr
  target : Expr
  atoms : List Expr
  atomicProvenance : List AtomicProvenance
  path : Expr

/-- The five semantically distinct exact-resolution outcomes exposed to observational probes. -/
inductive EvidenceKind where
  | reduction
  | reductionToKnownNP
  | nativeMembership
  | registeredCompleteness
  | transportedCompleteness
  deriving BEq, Repr

namespace EvidenceKind

/-- Stable external spelling; this is observational metadata and grants no capability. -/
def label : EvidenceKind → String
  | .reduction => "reduction"
  | .reductionToKnownNP => "reduction_with_membership"
  | .nativeMembership => "native_membership"
  | .registeredCompleteness => "registered_completeness"
  | .transportedCompleteness => "transported_completeness"

end EvidenceKind

/--
The observational catalog view used to restrict closed path search.

`full` preserves the production resolver's historical behavior. `flatAPI`
admits only unannotated direct reductions and exact final-composition facades.
`irComponents` excludes final facades and therefore requires a route assembled
from reusable component declarations.  The mode can remove validated edges;
it can never manufacture a capability.
-/
inductive RouteCatalogMode where
  | full
  | flatAPI
  | irComponents
  deriving BEq, Repr

namespace RouteCatalogMode

/-- Stable external spelling used only by benchmark and probe metadata. -/
def label : RouteCatalogMode → String
  | .full => "full"
  | .flatAPI => "flat_api"
  | .irComponents => "ir_components"

end RouteCatalogMode

/--
One closed request result together with exact declaration/path provenance.

Only `result` carries authority.  The remaining fields are projections of the
same Lean-side resolution and are exposed so the probe does not need to
reimplement membership/completeness selection in Python.
-/
structure ResolvedExactRequest where
  result : Expr
  evidenceKind : EvidenceKind
  path? : Option ResolvedPath := none
  membershipDeclaration? : Option Name := none
  completenessDeclaration? : Option Name := none
  hub? : Option Expr := none

private def controlledDefEq (first second : Expr) : MetaM Bool := do
  let first ← whnf first
  let second ← whnf second
  isDefEq first second

private def endpointSeen (endpoints : List Expr) (endpoint : Expr) : MetaM Bool := do
  endpoints.anyM fun previous => controlledDefEq previous endpoint

private def edgeVisibleInCatalog {environment : Environment}
    (mode : RouteCatalogMode) (edge : Registry.ValidatedCertificateEdge environment) : Bool :=
  match mode with
  | .full => true
  | .flatAPI =>
      match edge.componentRole? with
      | none => true
      | some .finalComposition => true
      | some _ => false
  | .irComponents => edge.componentRole? != some .finalComposition

private def reductionEdges (environment : Environment) (mode : RouteCatalogMode) :
    List (Registry.ValidatedCertificateEdge environment) :=
  (Registry.validatedCertificateEdges environment).filter fun edge =>
    match edge with
    | .reduction .. => edgeVisibleInCatalog mode edge
    | .equiv .. | .presentationChange .. => false

/--
Recheck one selected edge through the closed attributed-declaration validator.

The graph observation is never trusted by itself: the declaration remains in
the current environment, has to retain a candidate tag, and has to classify
again as a reduction at definitionally equal endpoints before its term enters
a constructed path.
-/
private def revalidatedReductionTerm? {environment : Environment}
    (edge : Registry.ValidatedCertificateEdge environment) : MetaM (Option Expr) := do
  let candidate := edge.observation.entry.candidate
  match Registry.validateAttributedDeclaration environment candidate with
  | some entry =>
      match entry.capability with
      | .certifiedReduction source target =>
          unless ← controlledDefEq source edge.source do
            return none
          unless ← controlledDefEq target edge.target do
            return none
          let certificate := mkConst candidate
          let certificateType ← whnf (← inferType certificate)
          match Registry.classifyElaboratedType certificateType with
          | some (.certifiedReduction checkedSource checkedTarget) =>
              unless ← controlledDefEq checkedSource edge.source do
                return none
              unless ← controlledDefEq checkedTarget edge.target do
                return none
              return some certificate
          | _ => return none
      | _ => return none
  | none => return none

private structure SearchNode (environment : Environment) where
  current : Expr
  reversedPath : List (Registry.ValidatedCertificateEdge environment)
  finalCompositionEdges : Nat

private def SearchNode.declarationKey {environment : Environment}
    (node : SearchNode environment) : String :=
  String.intercalate "\n" <| node.reversedPath.reverse.map fun edge =>
    edge.observation.entry.candidate.toString

/--
Order complete paths by final-composition penalty, then length, then declaration names.

All validated edges remain in the frontier.  A final-composition edge is therefore available when
an endpoint needs it, while a component-only path wins even when it contains more atoms.
-/
private def SearchNode.lt {environment : Environment}
    (left right : SearchNode environment) : Bool :=
  if left.finalCompositionEdges < right.finalCompositionEdges then true
  else if right.finalCompositionEdges < left.finalCompositionEdges then false
  else if left.reversedPath.length < right.reversedPath.length then true
  else if right.reversedPath.length < left.reversedPath.length then false
  else decide (left.declarationKey < right.declarationKey)

private def insertSearchNode {environment : Environment} (node : SearchNode environment) :
    List (SearchNode environment) → List (SearchNode environment)
  | [] => [node]
  | first :: rest =>
      if node.lt first then node :: first :: rest
      else first :: insertSearchNode node rest

private def SearchNode.uniqueDependencyCount {environment : Environment}
    (node : SearchNode environment) : Nat :=
  (node.reversedPath.map fun edge => edge.observation.entry.candidate).dedup.length

/--
The path order frozen by the V1 NP-hardness protocol: atom count first,
followed by final-composition count, unique dependency count, and declaration
sequence.  This is deliberately separate from `SearchNode.lt`, so existing
closed-request resolution retains its historical component-first preference.
-/
private def SearchNode.lengthFirstLt {environment : Environment}
    (left right : SearchNode environment) : Bool :=
  if left.reversedPath.length < right.reversedPath.length then true
  else if right.reversedPath.length < left.reversedPath.length then false
  else if left.finalCompositionEdges < right.finalCompositionEdges then true
  else if right.finalCompositionEdges < left.finalCompositionEdges then false
  else if left.uniqueDependencyCount < right.uniqueDependencyCount then true
  else if right.uniqueDependencyCount < left.uniqueDependencyCount then false
  else decide (left.declarationKey < right.declarationKey)

private def insertLengthFirstSearchNode {environment : Environment}
    (node : SearchNode environment) :
    List (SearchNode environment) → List (SearchNode environment)
  | [] => [node]
  | first :: rest =>
      if node.lengthFirstLt first then node :: first :: rest
      else first :: insertLengthFirstSearchNode node rest

private partial def bestFirst {environment : Environment}
    (target : Expr) (edges : List (Registry.ValidatedCertificateEdge environment))
    (frontier : List (SearchNode environment)) (settled : List Expr) :
    MetaM (Option (List (Registry.ValidatedCertificateEdge environment))) := do
  match frontier with
  | [] => return none
  | node :: remaining =>
      if ← endpointSeen settled node.current then
        return ← bestFirst target edges remaining settled
      if ← controlledDefEq node.current target then
        return some node.reversedPath.reverse
      let outgoing ← edges.filterM fun edge => controlledDefEq edge.source node.current
      let mut nextFrontier := remaining
      for edge in outgoing do
        unless ← endpointSeen (node.current :: settled) edge.target do
          let penalty := if edge.componentRole? == some .finalComposition then 1 else 0
          let next : SearchNode environment := {
            current := edge.target
            reversedPath := edge :: node.reversedPath
            finalCompositionEdges := node.finalCompositionEdges + penalty
          }
          nextFrontier := insertSearchNode next nextFrontier
      bestFirst target edges nextFrontier (node.current :: settled)

private partial def bestFirstLengthFirst {environment : Environment}
    (target : Expr) (edges : List (Registry.ValidatedCertificateEdge environment))
    (frontier : List (SearchNode environment)) (settled : List Expr) :
    MetaM (Option (List (Registry.ValidatedCertificateEdge environment))) := do
  match frontier with
  | [] => return none
  | node :: remaining =>
      if ← endpointSeen settled node.current then
        return ← bestFirstLengthFirst target edges remaining settled
      if ← controlledDefEq node.current target then
        return some node.reversedPath.reverse
      let outgoing ← edges.filterM fun edge => controlledDefEq edge.source node.current
      let mut nextFrontier := remaining
      for edge in outgoing do
        unless ← endpointSeen (node.current :: settled) edge.target do
          let penalty := if edge.componentRole? == some .finalComposition then 1 else 0
          let next : SearchNode environment := {
            current := edge.target
            reversedPath := edge :: node.reversedPath
            finalCompositionEdges := node.finalCompositionEdges + penalty
          }
          nextFrontier := insertLengthFirstSearchNode next nextFrontier
      bestFirstLengthFirst target edges nextFrontier (node.current :: settled)

private def buildPath (source : Expr) (atoms : List Expr) : MetaM Expr := do
  match atoms with
  | [] =>
      mkAppM ``ComplexityReduction.Certificate.CertifiedPath.refl #[source]
  | first :: rest =>
      let mut path ← mkAppM ``ComplexityReduction.Certificate.CertifiedPath.step #[first]
      for atom in rest do
        path ← mkAppM ``ComplexityReduction.Certificate.CertifiedPath.cons #[path, atom]
      instantiateMVars path

private def pathEndpoints? (path : Expr) : MetaM (Option (Expr × Expr)) := do
  let pathType ← whnf (← inferType path)
  let pathType := pathType.consumeMData
  if pathType.getAppFn.consumeMData.isConstOf
      ``ComplexityReduction.Certificate.CertifiedPath then
    match pathType.getAppArgs with
    | #[source, target] => return some (source, target)
    | _ => return none
  else
    return none

/--
Find a deterministic shortest closed reduction path in one explicitly selected
catalog view.  Filtering is applied only after canonical type-directed edge
validation and can therefore turn a full-graph success into `noRegistryPath`,
but cannot turn an invalid declaration into a certificate.
-/
def resolvePathWithCatalog (environment : Environment) (source target : Expr)
    (catalogMode : RouteCatalogMode) : MetaM (Except Failure ResolvedPath) := do
  if !hasProductionAggregate environment then
    return .error .aggregateNotImported
  if ← controlledDefEq source target then
    let path ← buildPath source []
    return .ok { source, target, atoms := [], atomicProvenance := [], path }
  let edges := reductionEdges environment catalogMode
  let initial : SearchNode environment := {
    current := source
    reversedPath := []
    finalCompositionEdges := 0
  }
  let some selected ← bestFirst target edges [initial] []
    | return .error (.noRegistryPath source target)
  let mut atoms := []
  let mut atomicProvenance := []
  for edge in selected do
    let some atom ← revalidatedReductionTerm? edge
      | return .error (.noRegistryPath source target)
    atoms := atoms ++ [atom]
    atomicProvenance := atomicProvenance ++
      [{ declaration := edge.observation.entry.candidate, role? := edge.componentRole? }]
  let path ← buildPath source atoms
  match ← pathEndpoints? path with
  | some (actualSource, actualTarget) =>
      unless ← controlledDefEq actualSource source do
        return .error (.noRegistryPath source target)
      unless ← controlledDefEq actualTarget target do
        return .error (.noRegistryPath source target)
      return .ok { source, target, atoms, atomicProvenance, path }
  | none => return .error (.noRegistryPath source target)

/--
Find a deterministic shortest closed reduction path in the complete production
catalog.  This compatibility entry point retains the pre-catalog behavior.
-/
def resolvePath (environment : Environment) (source target : Expr) :
    MetaM (Except Failure ResolvedPath) :=
  resolvePathWithCatalog environment source target .full

/--
Resolve a production-catalog path using the V1 NP-hardness route order:
shortest atom sequence, then least final-composition use, then least unique
dependencies, then declaration order.  The returned atoms are revalidated in
exactly the same way as `resolvePath`.
-/
def resolvePathLengthFirst (environment : Environment) (source target : Expr) :
    MetaM (Except Failure ResolvedPath) := do
  if !hasProductionAggregate environment then
    return .error .aggregateNotImported
  if ← controlledDefEq source target then
    let path ← buildPath source []
    return .ok { source, target, atoms := [], atomicProvenance := [], path }
  let edges := reductionEdges environment .full
  let initial : SearchNode environment := {
    current := source
    reversedPath := []
    finalCompositionEdges := 0
  }
  let some selected ← bestFirstLengthFirst target edges [initial] []
    | return .error (.noRegistryPath source target)
  let mut atoms := []
  let mut atomicProvenance := []
  for edge in selected do
    let some atom ← revalidatedReductionTerm? edge
      | return .error (.noRegistryPath source target)
    atoms := atoms ++ [atom]
    atomicProvenance := atomicProvenance ++
      [{ declaration := edge.observation.entry.candidate, role? := edge.componentRole? }]
  let path ← buildPath source atoms
  match ← pathEndpoints? path with
  | some (actualSource, actualTarget) =>
      unless ← controlledDefEq actualSource source do
        return .error (.noRegistryPath source target)
      unless ← controlledDefEq actualTarget target do
        return .error (.noRegistryPath source target)
      return .ok { source, target, atoms, atomicProvenance, path }
  | none => return .error (.noRegistryPath source target)

private def projection (name : Name) (structureTerm : Expr) : MetaM Expr :=
  mkAppM name #[structureTerm]

private def exactUserPolicy? (policy : Expr) : MetaM Bool := do
  let presentation ← whnf (← projection
    ``ComplexityReduction.Protocol.AutoReductionTrustPolicy.presentation policy)
  return presentation.consumeMData.isConstOf
    ``ComplexityReduction.Protocol.PresentationPolicy.exactUser

private structure ResolvedNativeMembership where
  declaration : Name
  endpoint : Expr
  term : Expr

private structure ResolvedNativeCompleteness where
  declaration : Name
  endpoint : Expr
  term : Expr

private def targetNativeMembership? (environment : Environment) (target : Expr) :
    MetaM (Option ResolvedNativeMembership) := do
  for entry in Registry.exportValidated environment do
    match entry.capability with
    | .nativeTMInNP endpoint =>
        if ← controlledDefEq endpoint target then
          let membership := mkConst entry.candidate
          let membershipType ← inferType membership
          match Registry.classifyElaboratedType membershipType with
          | some (.nativeTMInNP checkedEndpoint) =>
              if ← controlledDefEq checkedEndpoint target then
                return some { declaration := entry.candidate, endpoint, term := membership }
          | _ => pure ()
    | _ => pure ()
  return none

private def targetNativeCompleteness? (environment : Environment) (target : Expr) :
    MetaM (Option ResolvedNativeCompleteness) := do
  for entry in Registry.exportValidated environment do
    match entry.capability with
    | .nativeTMNPComplete endpoint =>
        if ← controlledDefEq endpoint target then
          let completeness := mkConst entry.candidate
          match Registry.classifyElaboratedType (← inferType completeness) with
          | some (.nativeTMNPComplete checkedEndpoint) =>
              if ← controlledDefEq checkedEndpoint target then
                return some { declaration := entry.candidate, endpoint, term := completeness }
          | _ => pure ()
    | _ => pure ()
  return none

private structure CompletenessTransportCandidate where
  completeness : ResolvedNativeCompleteness
  path : ResolvedPath

private def CompletenessTransportCandidate.declarationKey
    (candidate : CompletenessTransportCandidate) : String :=
  String.intercalate "\n" <|
    candidate.path.atomicProvenance.map (fun provenance => provenance.declaration.toString) ++
      [candidate.completeness.declaration.toString]

private def CompletenessTransportCandidate.lt
    (left right : CompletenessTransportCandidate) : Bool :=
  let leftPenalty := left.path.atomicProvenance.countP fun provenance =>
    provenance.role? == some .finalComposition
  let rightPenalty := right.path.atomicProvenance.countP fun provenance =>
    provenance.role? == some .finalComposition
  if leftPenalty < rightPenalty then true
  else if rightPenalty < leftPenalty then false
  else if left.path.atoms.length < right.path.atoms.length then true
  else if right.path.atoms.length < left.path.atoms.length then false
  else decide (left.declarationKey < right.declarationKey)

private def insertCompletenessTransportCandidate
    (candidate : CompletenessTransportCandidate) :
    List CompletenessTransportCandidate → List CompletenessTransportCandidate
  | [] => [candidate]
  | first :: rest =>
      if candidate.lt first then candidate :: first :: rest
      else first :: insertCompletenessTransportCandidate candidate rest

/--
Find the least registered native-complete hub with a closed forward path to
the target.  Every completeness declaration and every selected path atom is
revalidated by the same canonical classifier used by final resolution.
-/
private def completenessTransportCandidate? (environment : Environment) (target : Expr) :
    MetaM (Option CompletenessTransportCandidate) := do
  let mut candidates := []
  for entry in Registry.exportValidated environment do
    match entry.capability with
    | .nativeTMNPComplete endpoint =>
        let completeness := mkConst entry.candidate
        match Registry.classifyElaboratedType (← inferType completeness) with
        | some (.nativeTMNPComplete checkedEndpoint) =>
            unless ← controlledDefEq checkedEndpoint endpoint do
              continue
            match ← resolvePath environment endpoint target with
            | .ok path =>
                candidates := insertCompletenessTransportCandidate
                  { completeness := {
                      declaration := entry.candidate
                      endpoint
                      term := completeness }
                    path }
                  candidates
            | .error _ => pure ()
        | _ => pure ()
    | _ => pure ()
  return candidates.head?

private def resultHasRequestType (request result : Expr) : MetaM Bool := do
  let actual ← inferType result
  let expected ← mkAppM ``ComplexityReduction.Protocol.TypedAutoReductionResult #[request]
  controlledDefEq actual expected

/--
Resolve the closed/exact request lane and retain observational provenance from
the very same Lean-side decision that constructs the typed result.
-/
def resolveExactRequestDetailed (environment : Environment) (request : Expr) :
    MetaM (Except Failure ResolvedExactRequest) := do
  if !hasProductionAggregate environment then
    return .error .aggregateNotImported
  let requestType ← whnf (← inferType request)
  unless requestType.consumeMData.isConstOf
      ``ComplexityReduction.Protocol.TypedAutoReductionRequest do
    return .error (.malformedRequest request)
  let source ← whnf (← projection
    ``ComplexityReduction.Protocol.TypedAutoReductionRequest.source request)
  let policy ← projection
    ``ComplexityReduction.Protocol.TypedAutoReductionRequest.policy request
  unless ← exactUserPolicy? policy do
    return .error (.unsupportedRequest request)
  let exactSource := source.consumeMData
  unless exactSource.getAppFn.consumeMData.isConstOf
      ``ComplexityReduction.Protocol.AutoReductionSource.fromPresented do
    return .error (.unsupportedRequest request)
  let #[sourceProblem] := exactSource.getAppArgs
    | return .error (.malformedRequest request)
  let objective ← whnf (← projection
    ``ComplexityReduction.Protocol.TypedAutoReductionRequest.objective request)
  let objective := objective.consumeMData
  let objectiveHead := objective.getAppFn.consumeMData
  let objectiveArgs := objective.getAppArgs
  if objectiveHead.isConstOf
      ``ComplexityReduction.Protocol.AutoReductionRequest.proveInNP then
    let #[membershipProblem] := objectiveArgs
      | return .error (.malformedRequest request)
    unless ← controlledDefEq sourceProblem membershipProblem do
      return .error (.sourceObjectiveMismatch sourceProblem membershipProblem)
    let some membership ← targetNativeMembership? environment membershipProblem
      | return .error (.missingNativeMembership membershipProblem)
    let sourceMatches ← mkAppM ``Eq.refl #[sourceProblem]
    let result ← mkAppM
      ``ComplexityReduction.Protocol.TypedAutoReductionResult.proveInNP
      #[policy, sourceMatches, membership.term]
    let result ← instantiateMVars result
    if ← resultHasRequestType request result then
      return .ok {
        result
        evidenceKind := .nativeMembership
        membershipDeclaration? := some membership.declaration }
    else
      return .error (.malformedRequest request)
  if objectiveHead.isConstOf
      ``ComplexityReduction.Protocol.AutoReductionRequest.proveNPComplete then
    let #[completeProblem] := objectiveArgs
      | return .error (.malformedRequest request)
    unless ← controlledDefEq sourceProblem completeProblem do
      return .error (.sourceObjectiveMismatch sourceProblem completeProblem)
    let sourceMatches ← mkAppM ``Eq.refl #[sourceProblem]
    match ← targetNativeCompleteness? environment completeProblem with
    | some completeness =>
        let result ← mkAppM
          ``ComplexityReduction.Protocol.TypedAutoReductionResult.proveNPComplete
          #[policy, sourceMatches, completeness.term]
        let result ← instantiateMVars result
        if ← resultHasRequestType request result then
          return .ok {
            result
            evidenceKind := .registeredCompleteness
            completenessDeclaration? := some completeness.declaration
            hub? := some completeness.endpoint }
        else
          return .error (.malformedRequest request)
    | none =>
        let some membership ← targetNativeMembership? environment completeProblem
          | return .error (.missingNativeMembership completeProblem)
        let some candidate ← completenessTransportCandidate? environment completeProblem
          | return .error (.missingNativeCompleteness completeProblem)
        let complete ← mkAppM
          ``ComplexityReduction.Certificate.CompletenessTransport.alongPath
          #[candidate.completeness.term, candidate.path.path, membership.term]
        let result ← mkAppM
          ``ComplexityReduction.Protocol.TypedAutoReductionResult.proveNPComplete
          #[policy, sourceMatches, complete]
        let result ← instantiateMVars result
        if ← resultHasRequestType request result then
          return .ok {
            result
            evidenceKind := .transportedCompleteness
            path? := some candidate.path
            membershipDeclaration? := some membership.declaration
            completenessDeclaration? := some candidate.completeness.declaration
            hub? := some candidate.completeness.endpoint }
        else
          return .error (.malformedRequest request)
  let (objectiveSource, target, knownNP) ←
    if objectiveHead.isConstOf ``ComplexityReduction.Protocol.AutoReductionRequest.reduceTo then
      match objectiveArgs with
      | #[objectiveSource, target] => pure (objectiveSource, target, false)
      | _ => return .error (.malformedRequest request)
    else if objectiveHead.isConstOf
        ``ComplexityReduction.Protocol.AutoReductionRequest.reduceToKnownNP then
      match objectiveArgs with
      | #[objectiveSource, target] => pure (objectiveSource, target, true)
      | _ => return .error (.malformedRequest request)
    else
      return .error (.unsupportedRequest request)
  unless ← controlledDefEq sourceProblem objectiveSource do
    return .error (.sourceObjectiveMismatch sourceProblem objectiveSource)
  let path ← resolvePath environment sourceProblem target
  match path with
  | .error failure => return .error failure
  | .ok path =>
      let sourceMatches ← mkAppM ``Eq.refl #[sourceProblem]
      let membership? ←
        if knownNP then targetNativeMembership? environment target else pure none
      if knownNP && membership?.isNone then
        return .error (.missingNativeMembership target)
      let result ← match membership? with
        | some membership =>
            mkAppM
              ``ComplexityReduction.Protocol.TypedAutoReductionResult.reduceToKnownNPPath
              #[policy, sourceMatches, path.path, membership.term]
        | none =>
            mkAppM ``ComplexityReduction.Protocol.TypedAutoReductionResult.reduceToPath
              #[policy, sourceMatches, path.path]
      let result ← instantiateMVars result
      if ← resultHasRequestType request result then
        return .ok {
          result
          evidenceKind := if knownNP then .reductionToKnownNP else .reduction
          path? := some path
          membershipDeclaration? := membership?.map (fun membership => membership.declaration) }
      else
        return .error (.malformedRequest request)

/-- Compatibility projection used by the final term elaborator. -/
def resolveExactRequest (environment : Environment) (request : Expr) : MetaM (Except Failure Expr) := do
  match ← resolveExactRequestDetailed environment request with
  | .ok resolved => return .ok resolved.result
  | .error failure => return .error failure

end ClosedResolver
end Protocol
end ComplexityReduction
