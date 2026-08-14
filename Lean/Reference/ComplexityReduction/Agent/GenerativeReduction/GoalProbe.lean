/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.InputGate
import Lean.Elab.Command

/-! Read-only normalization of the exact general NP-hard root goal. -/

namespace ComplexityReduction.Agent.GenerativeReduction.GoalProbe

open Lean Elab Command Meta
open ComplexityReduction Encoding Certificate

private def marker := "GENERAL_REDUCTION_GOAL"
private def schemaVersion := "general_reduction_goal_probe_v1"

private def oneLine (value : String) : String :=
  (((value.replace "\n" " ").replace "\r" " ").replace "\t" " ")

private def run (environment : Environment) (nonce : String) (problemName : Name) : MetaM Unit := do
  let problem ← match ← ComplexityReduction.Agent.Hardness.InputGate.presented environment problemName with
    | .ok handle => pure handle
    | .error failure => throwError "general NP-hard goal input rejected: {repr failure}"
  let target ← mkAppM ``NativeTMNPHard #[problem.term]
  let rendered ← withOptions (fun options => options.setBool `pp.fullNames true) (ppExpr target)
  logInfo m!"{marker}\t{schemaVersion}\t{nonce}\t{problem.declaration}\t{oneLine rendered.pretty}\t{target.hash}"

syntax (name := generativeReductionProbeGoal)
  "#generative_reduction_probe_goal " str ident : command

elab_rules : command
  | `(#generative_reduction_probe_goal $nonce:str $problem:ident) => do
      let problemName ← resolveGlobalConstNoOverload problem
      let environment ← getEnv
      Command.liftTermElabM <| run environment nonce.getString problemName

end ComplexityReduction.Agent.GenerativeReduction.GoalProbe
