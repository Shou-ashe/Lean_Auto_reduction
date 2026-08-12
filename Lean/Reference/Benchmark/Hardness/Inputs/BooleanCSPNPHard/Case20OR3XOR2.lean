import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B20: the Schaefer-hard mixed language `{OR₃, XOR₂}`. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case20OR3XOR2
open ComplexityReduction ComplexityReduction.CSP ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common
noncomputable section

def gamma : Gamma := pairGamma
  (StandardRelations.ternaryClauseRel false false false)
  StandardRelations.xorRel
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case20OR3XOR2
