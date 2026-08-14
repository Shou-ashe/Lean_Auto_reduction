/- Copyright (c) 2026. -/

import ComplexityReduction.Agent.GenerativeReduction.RuleKernel

namespace ComplexityReduction.Agent.GenerativeReduction.PathMeeting

open ComplexityReduction Encoding Certificate

def meet {source middle target : PresentedProblem}
    (forward : CertifiedPath source middle) (backwardNeed : CertifiedPath middle target) :
    CertifiedPath source target :=
  forward.append backwardNeed

end ComplexityReduction.Agent.GenerativeReduction.PathMeeting
