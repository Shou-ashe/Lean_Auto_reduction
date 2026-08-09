/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Protocol.ClosedResolver
import Lean.Elab.Command

/-! Regression for the fail-closed aggregate prerequisite. -/

namespace ComplexityReduction.Agent.Hardness.Regression

open Lean Elab Command

run_cmd do
  if Protocol.ClosedResolver.hasProductionAggregate (← getEnv) then
    throwError "aggregate-missing regression unexpectedly imported the production aggregate"

end ComplexityReduction.Agent.Hardness.Regression
