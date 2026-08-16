/- Copyright (c) 2026. -/

import ComplexityReduction.Agent.GenerativeReduction.TheoremIndex
import Lean.Elab.Command
import Lean.Util.FoldConsts

/-!
Bounded, typed construction-basis discovery for capability generation.

Unlike the theorem index, this probe does not require a declaration to close
the exact target.  It exports the target head, definitions, constructors, and
nearby declarations that reference project constants occurring in the target.
The records are observational context only; generated source still has to pass
independent Lean elaboration and the normal dependency audits.
-/

namespace ComplexityReduction.Agent.GenerativeReduction.ConstructionBasis

open Lean Elab Command Meta Term

private def schemaVersion := "general_reduction_construction_basis_v1"
private def marker := "GENERAL_REDUCTION_CONSTRUCTION_BASIS"
private def maximumRenderedChars := 8192
private def maximumDefinitionChars := 12000
private def maximumEntries := 64

private def oneLineWithLimit (limit : Nat) (value : String) : String :=
  ((((value.replace "\n" " ").replace "\r" " ").replace "\t" " ").take
    limit).toString

private def oneLine (value : String) : String :=
  oneLineWithLimit maximumRenderedChars value

private def renderExpr (expression : Expr) (limit := maximumRenderedChars) : MetaM String := do
  let rendered ← withOptions (fun options => options.setBool `pp.fullNames true)
    (ppExpr (← instantiateMVars expression))
  return oneLineWithLimit limit rendered.pretty

private def emit (nonce kind : String) (fields : List String := []) : MetaM Unit :=
  logInfo m!"{marker}\t{schemaVersion}\t{nonce}\t{kind}\t{String.intercalate "\t" fields}"

private def nameComponents : Name → List String
  | .anonymous => []
  | .str parent value => nameComponents parent ++ [value]
  | .num parent value => nameComponents parent ++ [toString value]

private def forbiddenComponents : List String :=
  ["Oracles", "Oracle", "Gold", "GoldProofs", "Expected", "HiddenTargets", "Legacy"]

private def allowedPublicName (name : Name) : Bool :=
  let rendered := name.toString
  !isPrivateName name &&
    !(nameComponents name).any forbiddenComponents.contains &&
    !rendered.contains "._proof_" &&
    !rendered.endsWith "._flat_ctor" &&
    !rendered.endsWith ".noConfusion" &&
    !rendered.endsWith ".noConfusionType" &&
    !rendered.endsWith ".rec" &&
    !rendered.endsWith ".recOn" &&
    !rendered.endsWith ".casesOn" &&
    !rendered.contains "._sizeOf_"

private def projectConstant (name : Name) : Bool :=
  match nameComponents name with
  | "ComplexityReduction" :: _ => true
  | "Benchmark" :: _ => true
  | _ => false

private def declarationModule? (environment : Environment) (declaration : Name) :
    Option Name := do
  let moduleIndex ← environment.getModuleIdxFor? declaration
  environment.header.moduleNames[moduleIndex]?

private def declarationKind : ConstantInfo → String
  | .axiomInfo .. => "axiom"
  | .defnInfo .. => "definition"
  | .thmInfo .. => "theorem"
  | .opaqueInfo .. => "opaque"
  | .quotInfo .. => "quotient"
  | .inductInfo .. => "inductive"
  | .ctorInfo .. => "constructor"
  | .recInfo .. => "recursor"

private def conclusionHead? (type : Expr) : MetaM (Option Name) := do
  forallTelescope type fun _ conclusion =>
    pure conclusion.consumeMData.getAppFn.constName?

private def renderedValue (information : ConstantInfo) : MetaM String := do
  match information.value? (allowOpaque := true) with
  | some value => renderExpr value maximumDefinitionChars
  | none => pure ""

private def overlapCount (left right : NameSet) : Nat := Id.run do
  let mut count := 0
  for name in left do
    if right.contains name then
      count := count + 1
  return count

private structure BasisEntry where
  declaration : Name
  moduleName : Name
  information : ConstantInfo
  role : String
  distance : Nat
  overlap : Nat

private def roleFor (goalConstants : NameSet) (declaration : Name)
    (information : ConstantInfo) : String :=
  if goalConstants.contains declaration then
    "goal-constant"
  else
    match information with
    | .ctorInfo .. => "constructor"
    | .defnInfo .. | .opaqueInfo .. | .inductInfo .. | .recInfo .. => "definition"
    | .thmInfo .. => "lemma"
    | _ => "primitive"

private def priority (entry : BasisEntry) : Nat :=
  if entry.role == "goal-constant" then 0
  else if entry.role == "constructor" then 1
  else if entry.role == "lemma" then 2
  else if entry.role == "definition" then 3
  else 4

private def run (environment : Environment) (nonce : String) (target : Expr) : MetaM Unit := do
  let projectGoalConstants := target.getUsedConstantsAsSet.filter projectConstant
  let some head ← conclusionHead? target
    | throwError "construction-basis target has no constant conclusion head"
  let headInformation ← getConstInfo head
  let headModule := (declarationModule? environment head).getD Name.anonymous
  emit nonce "head" [
    head.toString,
    headModule.toString,
    declarationKind headInformation,
    ← renderExpr headInformation.type,
    ← renderedValue headInformation]

  let mut entries := #[]
  for (declaration, information) in environment.constants.toList do
    unless allowedPublicName declaration do
      continue
    let some moduleName := declarationModule? environment declaration | continue
    let overlap := overlapCount information.getUsedConstantsAsSet projectGoalConstants
    unless projectGoalConstants.contains declaration || overlap > 0 do
      continue
    let role := roleFor projectGoalConstants declaration information
    entries := entries.push {
      declaration,
      moduleName,
      information,
      role,
      distance := if projectGoalConstants.contains declaration then 0 else 1,
      overlap }
  let sorted := entries.qsort fun first second =>
    if priority first == priority second then
      if first.overlap == second.overlap then
        first.declaration.toString < second.declaration.toString
      else
        first.overlap > second.overlap
    else
      priority first < priority second
  for entry in sorted[:maximumEntries] do
    let definition ←
      if entry.role ∈ ["goal-constant", "definition"] then
        renderedValue entry.information
      else
        pure ""
    emit nonce "entry" [
      entry.declaration.toString,
      entry.moduleName.toString,
      declarationKind entry.information,
      entry.role,
      toString entry.distance,
      toString entry.overlap,
      ← renderExpr entry.information.type,
      definition]

private def runNamed (environment : Environment) (nonce names : String) : MetaM Unit := do
  for rawName in names.splitOn "," do
    let declaration := rawName.trimAscii.toString.toName
    if declaration.isAnonymous then
      continue
    let some information := environment.find? declaration
      | emit nonce "missing" [declaration.toString]
        continue
    unless allowedPublicName declaration do
      emit nonce "missing" [declaration.toString]
      continue
    let some moduleName := declarationModule? environment declaration
      | emit nonce "missing" [declaration.toString]
        continue
    emit nonce "named" [
      declaration.toString,
      moduleName.toString,
      declarationKind information,
      roleFor {} declaration information,
      "0",
      "0",
      ← renderExpr information.type,
      ← renderedValue information]

syntax (name := generativeReductionProbeConstructionBasis)
  "#generative_reduction_probe_construction_basis " str term : command

syntax (name := generativeReductionProbeNamedDeclarations)
  "#generative_reduction_probe_named_declarations " str str : command

elab_rules : command
  | `(#generative_reduction_probe_construction_basis $nonce:str $target:term) => do
      let environment ← getEnv
      Command.liftTermElabM do
        let target ← Term.elabTerm target none
        Term.synthesizeSyntheticMVarsNoPostponing
        run environment nonce.getString (← instantiateMVars target)
  | `(#generative_reduction_probe_named_declarations $nonce:str $names:str) => do
      let environment ← getEnv
      Command.liftTermElabM do
        runNamed environment nonce.getString names.getString

end ComplexityReduction.Agent.GenerativeReduction.ConstructionBasis
