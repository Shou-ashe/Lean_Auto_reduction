import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B30: fixed-seed random Boolean-CSP truth-table language J. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case30RandomTableJ

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

noncomputable section

def relationA : BoolRel := truthTableRel 5 0x64ADBF05
def relationB : BoolRel := truthTableRel 3 0xCA

def gamma : Gamma := pairGamma relationA relationB
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case30RandomTableJ

