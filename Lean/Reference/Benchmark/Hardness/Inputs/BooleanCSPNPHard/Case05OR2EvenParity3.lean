import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B05: the Schaefer-hard mixed language `{OR₂, EVEN-PARITY₃}`. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case05OR2EvenParity3

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

noncomputable section

def gamma : Gamma := pairGamma
  (StandardRelations.binaryClauseRel false false)
  StandardRelations.evenParity3Rel

def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case05OR2EvenParity3
