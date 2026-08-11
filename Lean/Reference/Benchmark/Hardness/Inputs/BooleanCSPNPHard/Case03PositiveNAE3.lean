import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B03: positive NAE-3-SAT as the one-relation Boolean CSP `CSP({NAE₃})`. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

noncomputable section

/-- The finite language whose sole relation rejects exactly `000` and `111`. -/
def gamma : Gamma := singletonGamma StandardRelations.notAllEqual3Rel

def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case03PositiveNAE3
