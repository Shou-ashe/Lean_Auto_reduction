import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B14: positive EXACT-4-IN-5-SAT. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case14PositiveExactlyFour5
open ComplexityReduction ComplexityReduction.CSP ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
noncomputable section

def gamma : Gamma := singletonGamma (StandardRelations.exactlyRel 5 4)
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case14PositiveExactlyFour5
