import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B11: positive EXACT-1-IN-5-SAT. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case11PositiveExactlyOne5
open ComplexityReduction ComplexityReduction.CSP ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
noncomputable section

def gamma : Gamma := singletonGamma (StandardRelations.exactlyRel 5 1)
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case11PositiveExactlyOne5
