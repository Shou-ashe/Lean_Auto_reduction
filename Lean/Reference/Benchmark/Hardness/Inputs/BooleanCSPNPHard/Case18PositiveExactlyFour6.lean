import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B18: positive EXACT-4-IN-6-SAT. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case18PositiveExactlyFour6
open ComplexityReduction ComplexityReduction.CSP ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
noncomputable section

def gamma : Gamma := singletonGamma (StandardRelations.exactlyRel 6 4)
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case18PositiveExactlyFour6
