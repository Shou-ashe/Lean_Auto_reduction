import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B12: positive EXACT-2-IN-5-SAT. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case12PositiveExactlyTwo5
open ComplexityReduction ComplexityReduction.CSP ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
noncomputable section

def gamma : Gamma := singletonGamma (StandardRelations.exactlyRel 5 2)
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case12PositiveExactlyTwo5
