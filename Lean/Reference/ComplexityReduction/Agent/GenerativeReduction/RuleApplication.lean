/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.GenerativeReduction.TheoremIndex
import Lean.Elab.Command

/-! Exact, universe-polymorphic application of one imported declaration. -/

namespace ComplexityReduction.Agent.GenerativeReduction.RuleApplication

open Lean Elab Tactic Meta Command Term

private def instantiationMarker := "GENERAL_REDUCTION_RULE_INSTANTIATION"
private def instantiationSchema := "general_reduction_rule_instantiation_v1"
private def maximumRenderedChars := 8192

private def oneLine (value : String) : String :=
  ((((value.replace "\n" " ").replace "\r" " ").replace "\t" " ").take
    maximumRenderedChars).toString

private def renderExpr (expression : Expr) : MetaM String := do
  let rendered ← withOptions (fun options =>
      options
        |>.setBool `pp.fullNames true
        |>.setBool `pp.explicit true
        |>.setBool `pp.universes true
        |>.setBool `pp.coercions true
        |>.setBool `pp.proofs true
        |>.setBool `pp.notation false)
    (ppExpr (← instantiateMVars expression))
  return oneLine rendered.pretty

private def premiseKind (type : Expr) : MetaM String := do
  if (← isClass? type).isSome then
    return "typeclass"
  if ← isProp type then
    return "proposition"
  return "data"

private def indexOfMVar (needle : MVarId) : List MVarId → Nat → Option Nat
  | [], _ => none
  | current :: remaining, ordinal =>
      if current == needle then some ordinal
      else indexOfMVar needle remaining (ordinal + 1)

private def parseAssignments (value : String) : Except String (List (Nat × Name)) := do
  let value := value.trimAscii.toString
  if value.isEmpty then
    return []
  let mut result := []
  for raw in value.splitOn "," do
    let fields := raw.splitOn "="
    unless fields.length == 2 do
      throw s!"invalid rule-instantiation assignment {raw}"
    let ordinalText := fields[0]!.trimAscii.toString
    let declarationText := fields[1]!.trimAscii.toString
    let some ordinal := ordinalText.toNat?
      | throw s!"invalid rule-instantiation ordinal {ordinalText}"
    if declarationText.isEmpty then
      throw "empty rule-instantiation declaration"
    result := result ++ [(ordinal, declarationText.toName)]
  return result

private def assignmentName? (assignments : List (Nat × Name)) (ordinal : Nat) : Option Name :=
  (assignments.find? fun assignment => assignment.1 == ordinal).map (·.2)

private def runInstantiation (nonce : String) (declaration : Name) (target : Expr)
    (assignments : List (Nat × Name)) : MetaM Unit := do
  let environment ← getEnv
  let some _ := environment.find? declaration
    | throwError "unknown generative rule declaration {declaration}"
  if isPrivateName declaration then
    throwError "the generative rule declaration is private"
  let theoremTerm ← mkConstWithFreshMVarLevels declaration
  let targetMVar ← mkFreshExprMVar target
  let generatedGoals ← targetMVar.mvarId!.apply theoremTerm
  let mut pending := #[]
  for generatedGoal in generatedGoals do
    unless ← generatedGoal.isAssigned do
      pending := pending.push generatedGoal
  for (ordinal, boundDeclaration) in assignments do
    let some mvarId := pending[ordinal]?
      | throwError "rule-instantiation assignment ordinal {ordinal} is out of range"
    let some _ := environment.find? boundDeclaration
      | throwError "unknown bound declaration {boundDeclaration}"
    let boundTerm ← mkConstWithFreshMVarLevels boundDeclaration
    unless ← isDefEq (mkMVar mvarId) boundTerm do
      let expectedType ← inferType (mkMVar mvarId)
      let actualType ← inferType boundTerm
      throwError "bound declaration {boundDeclaration} has type {actualType}, expected {expectedType}"
  let renderedTarget ← renderExpr target
  logInfo m!"{instantiationMarker}\t{instantiationSchema}\t{nonce}\tframe\t{declaration}\t{renderedTarget}\t{pending.size}"
  for h : ordinal in [:pending.size] do
    let mvarId := pending[ordinal]
    let type ← instantiateMVars (← inferType (mkMVar mvarId))
    let typeMVars ← getMVars type
    let dependencies := typeMVars.toList.filterMap fun dependency =>
      indexOfMVar dependency pending.toList 0
    let dependencyText := String.intercalate "," (dependencies.map toString)
    let assigned ← mvarId.isAssigned
    let ready ← dependencies.allM fun dependency => pending[dependency]!.isAssigned
    let status := if assigned then "bound" else if ready then "ready" else "dormant"
    let boundDeclaration := (assignmentName? assignments ordinal).map Name.toString |>.getD ""
    logInfo m!"{instantiationMarker}\t{instantiationSchema}\t{nonce}\tslot\t{ordinal}\t{← premiseKind type}\t{dependencyText}\t{status}\t{← renderExpr type}\t{boundDeclaration}\t{type.hash}"

private def applyRule (goal : MVarId) (declaration : Name) : MetaM (List MVarId) :=
  goal.withContext do
    let environment ← getEnv
    let some _ := environment.find? declaration
      | throwError "unknown generative rule declaration {declaration}"
    if isPrivateName declaration then
      throwError "the generative rule declaration is private"
    let theoremTerm ← mkConstWithFreshMVarLevels declaration
    let goals ← goal.apply theoremTerm
    let mut pending := []
    for subgoal in goals do
      unless ← subgoal.isAssigned do
        pending := pending ++ [subgoal]
    return pending

syntax (name := applyGenerativeRule) "apply_generative_rule " ident : tactic

elab_rules : tactic
  | `(tactic| apply_generative_rule $theoremName:ident) => do
      let declaration ← resolveGlobalConstNoOverload theoremName
      let goal ← getMainGoal
      let goals ← applyRule goal declaration
      replaceMainGoal goals

syntax (name := applyGenerativeRuleExact)
  "apply_generative_rule_exact " ident " [" term,* "]" : tactic

elab_rules : tactic
  | `(tactic| apply_generative_rule_exact $theoremName:ident [$proofs,*]) => do
      let declaration ← resolveGlobalConstNoOverload theoremName
      let goal ← getMainGoal
      let goals ← applyRule goal declaration
      let proofTerms := proofs.getElems
      unless proofTerms.size == goals.length do
        throwError "generative rule produced {goals.length} slots, but received {proofTerms.size} exact terms"
      for proofTerm in proofTerms, subgoal in goals do
        subgoal.withContext do
          let expectedType ← subgoal.getType
          let value ← Lean.Elab.Tactic.elabTermEnsuringType proofTerm expectedType
          if ← subgoal.isAssigned then
            unless ← isDefEq (mkMVar subgoal) value do
              throwError "exact term is inconsistent with an already instantiated generative-rule slot"
          else
            unless ← subgoal.checkedAssign value do
              throwError "failed to assign an exact generative-rule slot"
      let mut remaining := []
      for subgoal in goals do
        unless ← subgoal.isAssigned do
          remaining := remaining ++ [subgoal]
      replaceMainGoal remaining

syntax (name := generativeReductionProbeRuleInstantiation)
  "#generative_reduction_probe_rule " str ident "(" term ")" str : command

elab_rules : command
  | `(#generative_reduction_probe_rule $nonce:str $theoremName:ident ($target:term) $assignments:str) => do
      let declaration ← resolveGlobalConstNoOverload theoremName
      Command.liftTermElabM do
        let target ← Term.elabTerm target none
        Term.synthesizeSyntheticMVarsNoPostponing
        let assignments ← match parseAssignments assignments.getString with
          | .ok value => pure value
          | .error message => throwError message
        runInstantiation nonce.getString declaration (← instantiateMVars target) assignments

end ComplexityReduction.Agent.GenerativeReduction.RuleApplication
