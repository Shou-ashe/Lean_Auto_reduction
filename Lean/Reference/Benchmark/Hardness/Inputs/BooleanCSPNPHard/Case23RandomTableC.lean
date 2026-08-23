import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B23: fixed-seed random Boolean-CSP truth-table language C. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case23RandomTableC

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

noncomputable section

def relation : BoolRel := truthTableRel 4 0x6890

def gamma : Gamma := singletonGamma relation
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case23RandomTableC

