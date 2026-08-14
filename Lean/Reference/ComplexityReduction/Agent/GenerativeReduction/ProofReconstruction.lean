/- Copyright (c) 2026. -/

import ComplexityReduction.Agent.GenerativeReduction.GeneratedCandidateCheck

namespace ComplexityReduction.Agent.GenerativeReduction.ProofReconstruction

open ComplexityReduction Encoding Certificate

theorem exactEndpoint {problem : PresentedProblem}
    (proof : NativeTMNPHard problem) : NativeTMNPHard problem := proof

end ComplexityReduction.Agent.GenerativeReduction.ProofReconstruction
