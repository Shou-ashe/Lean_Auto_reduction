import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B08: positive EXACT-1-IN-4-SAT. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case08PositiveExactlyOne4
open ComplexityReduction ComplexityReduction.CSP ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
noncomputable section

def gamma : Gamma := singletonGamma (StandardRelations.exactlyRel 4 1)
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case08PositiveExactlyOne4
