/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.GenerativeReduction.TheoremIndex

/-! Exact, universe-polymorphic application of one imported declaration. -/

namespace ComplexityReduction.Agent.GenerativeReduction.RuleApplication

open Lean Elab Tactic Meta

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

end ComplexityReduction.Agent.GenerativeReduction.RuleApplication
