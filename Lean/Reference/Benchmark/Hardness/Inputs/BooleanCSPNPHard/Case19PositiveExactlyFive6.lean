import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B19: positive EXACT-5-IN-6-SAT. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case19PositiveExactlyFive6
open ComplexityReduction ComplexityReduction.CSP ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
noncomputable section

def gamma : Gamma := singletonGamma (StandardRelations.exactlyRel 6 5)
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case19PositiveExactlyFive6
