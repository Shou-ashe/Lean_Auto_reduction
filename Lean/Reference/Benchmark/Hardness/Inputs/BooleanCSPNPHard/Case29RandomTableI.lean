import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B29: fixed-seed random Boolean-CSP truth-table language I. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case29RandomTableI

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

noncomputable section

def relationA : BoolRel := truthTableRel 4 0x0C39
def relationB : BoolRel := truthTableRel 5 0x8DF51404

def gamma : Gamma := pairGamma relationA relationB
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case29RandomTableI

