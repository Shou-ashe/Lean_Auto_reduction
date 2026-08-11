import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B02: positive NAE-4-SAT as `CSP({NAE₄})`. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case02PositiveNAE4
open ComplexityReduction ComplexityReduction.CSP ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
noncomputable section

def gamma : Gamma := singletonGamma (StandardRelations.notAllEqualRel 4)
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case02PositiveNAE4
