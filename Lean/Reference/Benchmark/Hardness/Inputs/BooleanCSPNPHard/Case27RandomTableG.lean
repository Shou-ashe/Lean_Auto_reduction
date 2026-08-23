import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B27: fixed-seed random Boolean-CSP truth-table language G. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case27RandomTableG

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

noncomputable section

def relationA : BoolRel := truthTableRel 3 0x71
def relationB : BoolRel := truthTableRel 4 0x8CF8

def gamma : Gamma := pairGamma relationA relationB
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case27RandomTableG

