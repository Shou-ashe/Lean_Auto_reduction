/- Copyright (c) 2026. -/

import ComplexityReduction.Agent.GenerativeReduction.PathMeeting
import ComplexityReduction.AxiomGate

namespace ComplexityReduction.Agent.GenerativeReduction.GeneratedCandidateCheck

open ComplexityReduction Encoding Certificate

def exactReduction {source target : PresentedProblem}
    (candidate : CertifiedReduction source target) : CertifiedReduction source target :=
  candidate

end ComplexityReduction.Agent.GenerativeReduction.GeneratedCandidateCheck
