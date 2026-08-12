import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B16: positive EXACT-2-IN-6-SAT. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case16PositiveExactlyTwo6
open ComplexityReduction ComplexityReduction.CSP ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
noncomputable section

def gamma : Gamma := singletonGamma (StandardRelations.exactlyRel 6 2)
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case16PositiveExactlyTwo6
