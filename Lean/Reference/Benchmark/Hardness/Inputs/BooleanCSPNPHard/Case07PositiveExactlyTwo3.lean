import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B07: positive EXACT-2-IN-3-SAT. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case07PositiveExactlyTwo3
open ComplexityReduction ComplexityReduction.CSP ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
noncomputable section

def gamma : Gamma := singletonGamma (StandardRelations.exactlyRel 3 2)
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case07PositiveExactlyTwo3
