import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B04: positive 1-IN-3-SAT as `CSP({EXACTLY-ONE₃})`. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case04PositiveExactlyOne3

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

noncomputable section

/-- The finite language accepting exactly `001`, `010`, and `100`. -/
def gamma : Gamma := singletonGamma StandardRelations.exactlyOne3Rel

def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case04PositiveExactlyOne3
