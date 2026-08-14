/- Copyright (c) 2026. -/

import ComplexityReduction.Agent.GenerativeReduction.RuleApplication

/-! Small deterministic tactics used only as Lean-checked closure attempts. -/

namespace ComplexityReduction.Agent.GenerativeReduction.ExactClosureProbe

macro "generative_exact_closure" : tactic =>
  `(tactic| first | assumption | rfl | infer_instance | decide)

end ComplexityReduction.Agent.GenerativeReduction.ExactClosureProbe
