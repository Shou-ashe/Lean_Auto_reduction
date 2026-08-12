import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B15: positive EXACT-1-IN-6-SAT. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case15PositiveExactlyOne6
open ComplexityReduction ComplexityReduction.CSP ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
noncomputable section

def gamma : Gamma := singletonGamma (StandardRelations.exactlyRel 6 1)
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case15PositiveExactlyOne6
