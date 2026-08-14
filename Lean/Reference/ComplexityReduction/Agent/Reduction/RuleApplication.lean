/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Reduction.TheoremIndex

/-!
Lean-side application of indexed NP-hard theorem schemas.

The theorem name is supplied by the search controller, but admission is
entirely type driven: the conclusion must unify with the requested exact
`NativeTMNPHard` goal, and the tactic must close every premise.  A failed or
hallucinated declaration therefore cannot create a proof.
-/

namespace ComplexityReduction
namespace Agent
namespace Reduction
namespace RuleApplication

open Lean Elab Tactic Meta
open Encoding Certificate

private def isNativeHardnessGoal (goal : MVarId) : MetaM Bool := do
  let target ← goal.getType
  return target.consumeMData.getAppFn.isConstOf ``NativeTMNPHard

private def applyTheorem (goal : MVarId) (declaration : Name) : MetaM (List MVarId) :=
  goal.withContext do
    unless ← isNativeHardnessGoal goal do
      throwError "reduction theorem application only supports NativeTMNPHard goals"
    let environment ← getEnv
    let some information := environment.find? declaration
      | throwError "unknown theorem declaration {declaration}"
    if isPrivateName declaration || !information.levelParams.isEmpty then
      throwError "the theorem declaration is private or universe-polymorphic"
    let theoremTerm ← mkConstWithFreshMVarLevels declaration
    let (_, _, conclusion) ← forallMetaTelescope (← inferType theoremTerm)
    let target ← goal.getType
    unless ← isDefEq (← whnf conclusion) (← whnf target) do
      throwError "the theorem conclusion does not unify with the exact NP-hard goal"
    let goals ← goal.apply theoremTerm
    let mut pending := []
    for subgoal in goals do
      unless ← subgoal.isAssigned do
        pending := pending ++ [subgoal]
    return pending

syntax (name := applyReductionTheorem) "apply_reduction_theorem " ident : tactic

elab_rules : tactic
  | `(tactic| apply_reduction_theorem $theoremName:ident) => do
      let declaration ← resolveGlobalConstNoOverload theoremName
      let goal ← getMainGoal
      let goals ← applyTheorem goal declaration
      replaceMainGoal goals

end RuleApplication
end Reduction
end Agent
end ComplexityReduction
