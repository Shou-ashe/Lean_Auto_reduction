/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.InputGate
import ComplexityReduction.Registry.HardnessAggregate
import Lean.Elab.Command

/-!
Lean-authoritative normalization observations for the NP-hard production
entrypoint.  The command classifies one closed declaration and exports every
public `PresentedProblem` in the supplied import closure.  For a bare
`LawfulEncodedType`, candidate rows record exact definitional equality with
the candidate representation.

The external resolver may select only from these nonce-bound rows.  Its final
normalization certificate is compiled independently, so this catalog remains
observational rather than proof authority.
-/

namespace ComplexityReduction.Agent.Hardness.InputNormalization

open Lean Elab Command Meta
open Encoding Registry

private def schemaVersion := "hardness_np_hard_input_normalization_observation_v1"
private def marker := "HARDNESS_NP_HARD_INPUT"

private def nameComponents : Name → List String
  | .anonymous => []
  | .str parent value => nameComponents parent ++ [value]
  | .num parent value => nameComponents parent ++ [toString value]

private def forbiddenComponents : List String :=
  ["Oracles", "Oracle", "Gold", "GoldProofs", "Expected", "HiddenTargets", "Legacy"]

private def allowedPublicName (name : Name) : Bool :=
  !isPrivateName name && !(nameComponents name).any forbiddenComponents.contains

private def endpointNodeId (endpoint : Expr) : MetaM String := do
  let normalized ← whnf endpoint
  return s!"lean-whnf:{normalized.hash}"

private def controlledDefEq (first second : Expr) : MetaM Bool := do
  isDefEq (← whnf first) (← whnf second)

private def declarationModule? (environment : Environment) (declaration : Name) :
    Option Name := do
  let moduleIndex ← environment.getModuleIdxFor? declaration
  environment.header.moduleNames[moduleIndex]?

private def declarationsInAllowedModules (environment : Environment)
    (allowedModules : List String) : List (Name × ConstantInfo) := Id.run do
  let mut declarations := []
  for (moduleName, moduleData) in
      environment.header.moduleNames.toList.zip environment.header.moduleData.toList do
    if allowedModules.contains moduleName.toString then
      for declaration in moduleData.constNames.toList.zip moduleData.constants.toList do
        declarations := declaration :: declarations
  return declarations

private def emit (nonce kind : String) (fields : List String := []) : MetaM Unit :=
  logInfo m!"{marker}\t{schemaVersion}\t{nonce}\t{kind}\t{String.intercalate "\t" fields}"

private def run (environment : Environment) (nonce : String) (declaration : Name)
    (allowedModules : List String) : MetaM Unit := do
  unless allowedPublicName declaration do
    throwError "hardness input normalization rejected a non-public declaration"
  let information ←
    match environment.find? declaration with
    | some information => pure information
    | none => throwError "hardness input normalization failed: unknown declaration {declaration}"
  unless information.levelParams.isEmpty && !information.type.hasMVar do
    throwError "hardness input normalization requires a closed monomorphic declaration"
  let some inputModule := declarationModule? environment declaration
    | throwError "hardness input normalization cannot identify declaration ownership"
  unless allowedModules.contains inputModule.toString do
    throwError "hardness input normalization declaration escaped the import closure"
  let inputTerm := mkConst declaration
  let presented? ← controlledDefEq information.type (mkConst ``PresentedProblem)
  let encoding? ← controlledDefEq information.type (mkConst ``LawfulEncodedType)
  let inputKind := if presented? then "presented_problem" else if encoding? then "encoding" else "unsupported"
  let inputNode ← endpointNodeId inputTerm
  let entries := exportValidated environment
  let fingerprint := Registry.registryFingerprint entries
  emit nonce "input" [
    declaration.toString,
    inputKind,
    inputModule.toString,
    inputNode,
    fingerprint]
  let mut problemCount := 0
  let mut matchCount := 0
  let mut matchingProblems : List (Name × Expr) := []
  for (candidate, candidateInformation) in
      declarationsInAllowedModules environment allowedModules do
    if allowedPublicName candidate && candidateInformation.levelParams.isEmpty &&
        !candidateInformation.type.hasMVar &&
        candidateInformation.type.consumeMData.isConstOf ``PresentedProblem then
      match ← InputGate.presented environment candidate with
      | .error _ => pure ()
      | .ok problem =>
          let some candidateModule := declarationModule? environment candidate
            | continue
          let representation ← mkAppM ``PresentedProblem.representation #[problem.term]
          let representationMatches ←
            if encoding? then controlledDefEq inputTerm representation else pure false
          let problemMatchesInput ←
            if presented? then controlledDefEq inputTerm problem.term else pure false
          problemCount := problemCount + 1
          if representationMatches then
            matchCount := matchCount + 1
            matchingProblems := (candidate, problem.term) :: matchingProblems
          emit nonce "problem" [
            candidate.toString,
            candidateModule.toString,
            ← endpointNodeId problem.term,
            ← endpointNodeId representation,
            toString representationMatches,
            toString problemMatchesInput,
            fingerprint]
  for (firstName, firstTerm) in matchingProblems do
    for (secondName, secondTerm) in matchingProblems do
      if firstName.toString < secondName.toString &&
          (← controlledDefEq firstTerm secondTerm) then
        emit nonce "problem_defeq" [firstName.toString, secondName.toString, fingerprint]
  emit nonce "complete" [toString problemCount, toString matchCount, fingerprint]

syntax (name := hardnessNormalizeNPHardInput)
  "#hardness_normalize_np_hard_input " str ident str : command

elab_rules : command
  | `(#hardness_normalize_np_hard_input $nonce:str $input:ident $modules:str) => do
      let declaration ← resolveGlobalConstNoOverload input
      let environment ← getEnv
      let allowedModules :=
        modules.getString.splitOn "," |>.map String.trim |>.filter (fun value => !value.isEmpty)
      Command.liftTermElabM <| run environment nonce.getString declaration allowedModules

end ComplexityReduction.Agent.Hardness.InputNormalization
