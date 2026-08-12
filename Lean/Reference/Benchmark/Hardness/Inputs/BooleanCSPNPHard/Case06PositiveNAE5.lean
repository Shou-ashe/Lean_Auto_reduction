import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B06: positive NAE-5-SAT as `CSP({NAE₅})`. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case06PositiveNAE5
open ComplexityReduction ComplexityReduction.CSP ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
noncomputable section

def gamma : Gamma := singletonGamma (StandardRelations.notAllEqualRel 5)
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case06PositiveNAE5
