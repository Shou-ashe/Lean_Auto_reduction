import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B09: positive EXACT-2-IN-4-SAT. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case09PositiveExactlyTwo4
open ComplexityReduction ComplexityReduction.CSP ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
noncomputable section

def gamma : Gamma := singletonGamma (StandardRelations.exactlyRel 4 2)
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case09PositiveExactlyTwo4
