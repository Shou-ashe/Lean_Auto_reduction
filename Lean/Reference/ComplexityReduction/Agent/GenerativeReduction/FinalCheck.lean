/- Copyright (c) 2026. -/

import ComplexityReduction.Agent.GenerativeReduction.ProofReconstruction
import ComplexityReduction.Agent.GenerativeReduction.RouteAudit
import ComplexityReduction.AxiomGate

/-! Stable final imports for independent artifact reconstruction. -/

namespace ComplexityReduction.Agent.GenerativeReduction.FinalCheck

open ComplexityReduction Encoding Certificate

theorem exactEndpoint {problem : PresentedProblem}
    (proof : NativeTMNPHard problem) : NativeTMNPHard problem := proof

end ComplexityReduction.Agent.GenerativeReduction.FinalCheck
