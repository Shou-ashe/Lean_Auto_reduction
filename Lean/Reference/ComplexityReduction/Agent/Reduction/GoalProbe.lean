/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Agent.Hardness.InputGate
import Lean.Elab.Command

/-! Read-only normalization of the exact NP-hard root goal. -/

namespace ComplexityReduction
namespace Agent
namespace Reduction
namespace GoalProbe

open Lean Elab Command Meta
open Encoding Certificate

private def marker := "REDUCTION_GOAL"
private def schemaVersion := "reduction_goal_probe_v1"

private def oneLine (value : String) : String :=
  (((value.replace "\n" " ").replace "\r" " ").replace "\t" " ")

private def run (environment : Environment) (nonce : String) (problemName : Name) : MetaM Unit := do
  let problem ← match ← Hardness.InputGate.presented environment problemName with
    | .ok handle => pure handle
    | .error failure => throwError "NP-hard goal input rejected: {repr failure}"
  let target ← mkAppM ``NativeTMNPHard #[problem.term]
  let rendered ← ppExpr target
  logInfo m!"{marker}\t{schemaVersion}\t{nonce}\t{problem.declaration}\t{oneLine rendered.pretty}\t{target.hash}"

syntax (name := reductionProbeNPHardGoal) "#reduction_probe_np_hard_goal " str ident : command

elab_rules : command
  | `(#reduction_probe_np_hard_goal $nonce:str $problem:ident) => do
      let problemName ← resolveGlobalConstNoOverload problem
      let environment ← getEnv
      Command.liftTermElabM <| run environment nonce.getString problemName

end GoalProbe
end Reduction
end Agent
end ComplexityReduction
