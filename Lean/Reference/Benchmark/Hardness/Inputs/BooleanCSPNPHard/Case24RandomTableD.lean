import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B24: fixed-seed random Boolean-CSP truth-table language D. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case24RandomTableD

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

noncomputable section

def relation : BoolRel := truthTableRel 5 0x6C2A2F22

def gamma : Gamma := singletonGamma relation
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case24RandomTableD

