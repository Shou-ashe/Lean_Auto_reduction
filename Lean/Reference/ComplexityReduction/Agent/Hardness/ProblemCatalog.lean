/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Registry.HardnessAggregate
import ComplexityReduction.Registry.Graph
import Lean.Elab.Command
import Lean.Util.FoldConsts

/-!
Read-only export of public, closed `PresentedProblem` declarations.

The catalog is an observational search index.  It carries no proof authority:
the final artifact must still elaborate at the original user input declaration.
-/

namespace ComplexityReduction.Agent.Hardness.ProblemCatalog

open Lean Elab Command Meta
open Encoding Certificate Registry

private def schemaVersion := "hardness_problem_catalog_v2"
private def connectionSchemaVersion := "hardness_connection_catalog_v1"
private def marker := "HARDNESS_AGENT"
private def maximumRenderedChars := 2048
private def maximumReferencedConstants := 32

private def oneLine (value : String) : String :=
  ((((value.replace "\n" " ").replace "\r" " ").replace "\t" " ").take
    maximumRenderedChars).toString

private def renderExpr (expression : Expr) : MetaM String := do
  let rendered ←
    withOptions (fun options => options.setBool `pp.fullNames true) (ppExpr expression)
  return oneLine rendered.pretty

private def renderWhnf (expression : Expr) : MetaM String := do
  renderExpr (← whnf expression)

private def controlledDefEq (first second : Expr) : MetaM Bool := do
  isDefEq (← whnf first) (← whnf second)

private def endpointNodeId (endpoint : Expr) : MetaM String := do
  let normalized ← whnf endpoint
  return s!"lean-whnf:{normalized.hash}"

private def declarationKind : ConstantInfo → String
  | .axiomInfo .. => "axiom"
  | .defnInfo .. => "definition"
  | .thmInfo .. => "theorem"
  | .opaqueInfo .. => "opaque"
  | .quotInfo .. => "quotient"
  | .inductInfo .. => "inductive"
  | .ctorInfo .. => "constructor"
  | .recInfo .. => "recursor"

private def nameComponents : Name → List String
  | .anonymous => []
  | .str parent value => nameComponents parent ++ [value]
  | .num parent value => nameComponents parent ++ [toString value]

private def forbiddenComponents : List String :=
  ["Oracles", "Oracle", "Gold", "GoldProofs", "Expected", "HiddenTargets", "Legacy"]

private def allowedPublicName (name : Name) : Bool :=
  !isPrivateName name && !(nameComponents name).any forbiddenComponents.contains

private def referencedConstants (information : ConstantInfo) : String :=
  let names :=
    (Std.TreeSet.toList information.getUsedConstantsAsSet).take maximumReferencedConstants
  String.intercalate "," <| names.map Name.toString

private def isRegisteredProblem {environment : Environment}
    (entries : List (ValidatedEntry environment)) (declaration : Name) : Bool :=
  entries.any fun entry =>
    entry.candidate == declaration &&
      match entry.capability with
      | .presentedProblem => true
      | _ => false

private def emitWithSchema (schema nonce kind : String) (fields : List String := []) :
    MetaM Unit :=
  logInfo m!"{marker}\t{schema}\t{nonce}\t{kind}\t{String.intercalate "\t" fields}"

private def emit (nonce kind : String) (fields : List String := []) : MetaM Unit :=
  emitWithSchema schemaVersion nonce kind fields

private def emitConnection (nonce kind : String) (fields : List String := []) : MetaM Unit :=
  emitWithSchema connectionSchemaVersion nonce kind fields

private def emitProblem {environment : Environment} (nonce fingerprint : String)
    (entries : List (ValidatedEntry environment)) (declaration : Name)
    (information : ConstantInfo) : MetaM Unit := do
  let term := mkConst declaration
  let semantic ← mkAppM ``PresentedProblem.semantic #[term]
  let domain ← mkAppM ``PresentedProblem.Instance #[term]
  let accepts ← mkAppM ``PresentedProblem.accepts #[term]
  let representation ← mkAppM ``PresentedProblem.representation #[term]
  let normalizedRepresentation ← whnf representation
  let encoderBoundIdentity ←
    mkAppM ``LawfulEncodedType.encoderBoundIdentity #[normalizedRepresentation]
  emit nonce "problem" [
    declaration.toString,
    declarationKind information,
    ← renderWhnf term,
    ← endpointNodeId term,
    ← renderWhnf semantic,
    ← renderWhnf representation,
    ← renderWhnf encoderBoundIdentity,
    referencedConstants information,
    toString (isRegisteredProblem entries declaration),
    fingerprint,
    ← renderWhnf accepts,
    ← endpointNodeId accepts,
    ← renderWhnf domain,
    ← endpointNodeId domain,
    ← endpointNodeId representation,
    ← endpointNodeId encoderBoundIdentity]

private def emitProjectedConnection (nonce fingerprint capabilityKind relation direction
    termKind : String) (certificate projection : Name) (role : String)
    (term : Expr) : MetaM Unit := do
  let termType ← whnf (← inferType term)
  let executableTerm :=
    if termKind == "fixed_projection" then
      s!"{projection} {certificate}"
    else
      certificate.toString
  match classifyElaboratedType termType with
  | some (.certifiedReduction source target) =>
      emitConnection nonce "connection" [
        certificate.toString,
        capabilityKind,
        relation,
        direction,
        termKind,
        projection.toString,
        executableTerm,
        s!"lean:{source.hash}",
        s!"lean:{target.hash}",
        ← endpointNodeId source,
        ← endpointNodeId target,
        ← renderWhnf source,
        ← renderWhnf target,
        role,
        fingerprint]
  | _ =>
      throwError "fixed connection projection did not elaborate to CertifiedReduction: {term}"

private def emitConnections (environment : Environment) (nonce fingerprint : String) :
    MetaM Unit := do
  for edge in validatedCertificateEdges environment do
    let certificate := edge.observation.entry.candidate
    if allowedPublicName certificate then
      let role := edge.componentRole?.map toString |>.getD "unannotated"
      let certificateTerm := mkConst certificate
      match edge with
      | .reduction .. =>
          emitProjectedConnection nonce fingerprint "certified_reduction"
            "existing_reduction" "forward" "certificate" certificate certificate role
            certificateTerm
      | .equiv .. =>
          let forward ← mkAppM ``CertifiedEquiv.forwardReduction #[certificateTerm]
          emitProjectedConnection nonce fingerprint "certified_equiv"
            "certified_equiv_forward" "forward" "fixed_projection" certificate
            ``CertifiedEquiv.forwardReduction role forward
          let backward ← mkAppM ``CertifiedEquiv.backwardReduction #[certificateTerm]
          emitProjectedConnection nonce fingerprint "certified_equiv"
            "certified_equiv_backward" "backward" "fixed_projection" certificate
            ``CertifiedEquiv.backwardReduction role backward
      | .presentationChange .. =>
          let forward ← mkAppM ``CertifiedPresentationChange.forwardReduction #[certificateTerm]
          emitProjectedConnection nonce fingerprint "certified_presentation_change"
            "presentation_change_forward" "forward" "fixed_projection" certificate
            ``CertifiedPresentationChange.forwardReduction role forward
          let backward ← mkAppM ``CertifiedPresentationChange.backwardReduction #[certificateTerm]
          emitProjectedConnection nonce fingerprint "certified_presentation_change"
            "presentation_change_backward" "backward" "fixed_projection" certificate
            ``CertifiedPresentationChange.backwardReduction role backward

private def run (environment : Environment) (nonce : String)
    (registeredOnly : Bool := false) : MetaM Unit := do
  let entries := exportValidated environment
  let fingerprint := Registry.registryFingerprint entries
  emit nonce "registry" [fingerprint]
  emitConnection nonce "registry" [fingerprint]
  for (declaration, information) in environment.constants.toList do
    if allowedPublicName declaration && information.levelParams.isEmpty &&
        !information.type.hasMVar then
      if ← controlledDefEq information.type (mkConst ``PresentedProblem) then
        if !registeredOnly || isRegisteredProblem entries declaration then
          emitProblem nonce fingerprint entries declaration information
  emitConnections environment nonce fingerprint

syntax (name := hardnessExportProblemCatalog) "#hardness_export_problem_catalog " str : command

elab_rules : command
  | `(#hardness_export_problem_catalog $nonce:str) => do
      let environment ← getEnv
      Command.liftTermElabM <| run environment nonce.getString

syntax (name := hardnessExportRegisteredProblemCatalog)
  "#hardness_export_registered_problem_catalog " str : command

elab_rules : command
  | `(#hardness_export_registered_problem_catalog $nonce:str) => do
      let environment ← getEnv
      Command.liftTermElabM <| run environment nonce.getString true

end ComplexityReduction.Agent.Hardness.ProblemCatalog
