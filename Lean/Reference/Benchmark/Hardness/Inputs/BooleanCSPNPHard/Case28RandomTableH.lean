import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B28: fixed-seed random Boolean-CSP truth-table language H. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case28RandomTableH

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

noncomputable section

def relationA : BoolRel := truthTableRel 4 0x6AC7
def relationB : BoolRel := truthTableRel 4 0x96E2

def gamma : Gamma := pairGamma relationA relationB
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case28RandomTableH

