import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B10: positive EXACT-3-IN-4-SAT. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case10PositiveExactlyThree4
open ComplexityReduction ComplexityReduction.CSP ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
noncomputable section

def gamma : Gamma := singletonGamma (StandardRelations.exactlyRel 4 3)
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case10PositiveExactlyThree4
