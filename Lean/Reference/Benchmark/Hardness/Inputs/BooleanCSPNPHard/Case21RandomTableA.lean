import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B21: fixed-seed random Boolean-CSP truth-table language A. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case21RandomTableA

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

noncomputable section

def relation : BoolRel := truthTableRel 4 0x14E4

def gamma : Gamma := singletonGamma relation
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case21RandomTableA

