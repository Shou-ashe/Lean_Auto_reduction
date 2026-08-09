/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.InputGate
import ComplexityReduction.Registry.HardnessAggregate
import Lean.Elab.Command
import Lean.Util.FoldConsts

/-!
Read-only, nonce-bound observations of one Lean input declaration.

The output is diagnostic data for the external agent.  It grants no proof
authority: endpoint compatibility is still checked by Lean when the final
artifact is elaborated.
-/

namespace ComplexityReduction.Agent.Hardness.InputInspection

open Lean Elab Command Meta
open Encoding Registry

private def schemaVersion := "hardness_input_observation_v2"
private def marker := "HARDNESS_AGENT"
private def maximumRenderedChars := 2048
private def maximumReferencedConstants := 32

private def controlledDefEq (first second : Expr) : MetaM Bool := do
  isDefEq (← whnf first) (← whnf second)

private def oneLine (value : String) : String :=
  ((((value.replace "\n" " ").replace "\r" " ").replace "\t" " ").take
    maximumRenderedChars).toString

private def renderExpr (expression : Expr) : MetaM String := do
  let rendered ←
    withOptions (fun options => options.setBool `pp.fullNames true) (ppExpr expression)
  return oneLine rendered.pretty

private def renderWhnf (expression : Expr) : MetaM String := do
  renderExpr (← whnf expression)

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

private def requiresArguments : Expr → Bool
  | .forallE .. => true
  | _ => false

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

private def emit (nonce kind : String) (fields : List String := []) : MetaM Unit :=
  logInfo m!"{marker}\t{schemaVersion}\t{nonce}\t{kind}\t{String.intercalate "\t" fields}"

private def emitPredicateMatches (environment : Environment) (nonce fingerprint : String)
    (predicate : InputGate.PredicateHandle) : MetaM Unit := do
  for (candidate, information) in environment.constants.toList do
    if allowedPublicName candidate && information.levelParams.isEmpty &&
        !information.type.hasMVar then
      match ← InputGate.presented environment candidate with
      | .error _ => pure ()
      | .ok problem =>
          let compatibility ← InputGate.predicateCompatibility predicate problem
          if compatibility.domainDefEq && compatibility.acceptsDefEq then
            let domain ← mkAppM ``PresentedProblem.Instance #[problem.term]
            let accepts ← mkAppM ``PresentedProblem.accepts #[problem.term]
            let representation ← mkAppM ``PresentedProblem.representation #[problem.term]
            let normalizedRepresentation ← whnf representation
            let encoderBoundIdentity ←
              mkAppM ``LawfulEncodedType.encoderBoundIdentity #[normalizedRepresentation]
            emit nonce "predicate_match" [
              candidate.toString,
              ← endpointNodeId problem.term,
              ← endpointNodeId accepts,
              ← endpointNodeId domain,
              ← endpointNodeId representation,
              ← endpointNodeId encoderBoundIdentity,
              fingerprint]

private def run (environment : Environment) (nonce : String) (declaration : Name) :
    MetaM Unit := do
  let information ←
    match environment.find? declaration with
    | some information => pure information
    | none => throwError "hardness input observation failed: unknown declaration {declaration}"
  let elaboratedType := information.type
  let normalizedType ← whnf elaboratedType
  let hasMetavariables := elaboratedType.hasMVar
  let hasRequiredArguments := requiresArguments normalizedType
  let presentedHandle? ←
    match ← InputGate.presented environment declaration with
    | .ok handle => pure (some handle)
    | .error _ => pure none
  let predicateHandle? ←
    match ← InputGate.predicate environment declaration with
    | .ok handle => pure (some handle)
    | .error _ => pure none
  let presentedProblemCompatible := presentedHandle?.isSome
  let predicateCompatible := predicateHandle?.isSome
  let closedProposition ←
    if normalizedType == .sort .zero then
      pure true
    else
      isProp elaboratedType
  let closed :=
    information.levelParams.isEmpty && !hasMetavariables &&
      (presentedProblemCompatible || predicateCompatible || !hasRequiredArguments)
  let inputKind :=
    if presentedProblemCompatible then
      "presented_problem"
    else if predicateCompatible then
      "predicate"
    else if closedProposition then
      "closed_prop"
    else if !closed then
      "open_or_polymorphic"
    else
      "unsupported"
  let supported := presentedProblemCompatible || predicateCompatible
  let (failureCode, explanation) :=
    if supported then
      ("", "")
    else if closedProposition then
      ("closed_prop_has_no_problem_encoding",
        "the input is a closed Lean proposition and does not provide an instance type and lawful problem encoding")
    else if !closed then
      ("input_requires_parameters",
        "the input declaration still requires value or universe parameters; provide a fully instantiated problem declaration")
    else
      ("unsupported_input_type",
        "the input type is not definitionally equal to PresentedProblem and is not a supported decision predicate")
  let problemNodeId ←
    match presentedHandle? with
    | some handle => endpointNodeId handle.term
    | none => pure ""
  let (semanticSummary, representationSummary) ←
    match presentedHandle? with
    | some handle =>
        let semantic ← mkAppM ``PresentedProblem.semantic #[handle.term]
        let representation ← mkAppM ``PresentedProblem.representation #[handle.term]
        pure (← renderWhnf semantic, ← renderWhnf representation)
    | none => pure ("", "")
  let predicateDomainSummary ←
    match predicateHandle? with
    | some handle => renderWhnf handle.domain
    | none => pure ""
  let predicateSummary ←
    match predicateHandle? with
    | some handle => renderWhnf handle.term
    | none => pure ""
  let acceptsSummary ←
    match presentedHandle? with
    | some handle => renderWhnf (← mkAppM ``PresentedProblem.accepts #[handle.term])
    | none => pure ""
  let entries := exportValidated environment
  let fingerprint := Registry.registryFingerprint entries
  let predicateDomainNodeId ←
    match predicateHandle? with
    | some handle => endpointNodeId handle.domain
    | none => pure ""
  let predicateNodeId ←
    match predicateHandle? with
    | some handle => endpointNodeId handle.term
    | none => pure ""
  emit nonce "input" [
    declaration.toString,
    declarationKind information,
    toString supported,
    inputKind,
    ← renderExpr elaboratedType,
    ← renderExpr normalizedType,
    toString closed,
    String.intercalate "," <| information.levelParams.map Name.toString,
    toString hasMetavariables,
    toString presentedProblemCompatible,
    predicateDomainSummary,
    problemNodeId,
    referencedConstants information,
    semanticSummary,
    representationSummary,
    predicateSummary,
    acceptsSummary,
    fingerprint,
    failureCode,
    oneLine explanation,
    predicateDomainNodeId,
    predicateNodeId]
  match predicateHandle? with
  | some handle => emitPredicateMatches environment nonce fingerprint handle
  | none => pure ()

syntax (name := hardnessInspectInput) "#hardness_inspect_input " str ident : command

elab_rules : command
  | `(#hardness_inspect_input $nonce:str $input:ident) => do
      let declaration ← resolveGlobalConstNoOverload input
      let environment ← getEnv
      Command.liftTermElabM <| run environment nonce.getString declaration

end ComplexityReduction.Agent.Hardness.InputInspection
