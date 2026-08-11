import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B13: positive EXACT-3-IN-5-SAT. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case13PositiveExactlyThree5
open ComplexityReduction ComplexityReduction.CSP ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
noncomputable section

def gamma : Gamma := singletonGamma (StandardRelations.exactlyRel 5 3)
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case13PositiveExactlyThree5
