import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B22: fixed-seed random Boolean-CSP truth-table language B. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case22RandomTableB

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

noncomputable section

def relation : BoolRel := truthTableRel 5 0x5AE4ED46

def gamma : Gamma := singletonGamma relation
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case22RandomTableB

