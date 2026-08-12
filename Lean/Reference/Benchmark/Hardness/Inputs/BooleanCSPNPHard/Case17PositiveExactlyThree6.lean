import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B17: positive EXACT-3-IN-6-SAT. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case17PositiveExactlyThree6
open ComplexityReduction ComplexityReduction.CSP ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
noncomputable section

def gamma : Gamma := singletonGamma (StandardRelations.exactlyRel 6 3)
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case17PositiveExactlyThree6
