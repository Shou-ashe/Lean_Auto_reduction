/- Copyright (c) 2026. -/

import ComplexityReduction.Agent.GenerativeReduction.CapabilityProbe
import Mathlib.Tactic

namespace ComplexityReduction.Agent.GenerativeReduction.PremiseAutomation

macro "generative_bounded_automation" : tactic =>
  `(tactic| first | assumption | rfl | infer_instance | simp | aesop | omega | decide)

end ComplexityReduction.Agent.GenerativeReduction.PremiseAutomation
