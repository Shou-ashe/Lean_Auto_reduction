import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-! Q-B25: fixed-seed random Boolean-CSP truth-table language E. -/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case25RandomTableE

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

noncomputable section

def relation : BoolRel := truthTableRel 4 0x69C6

def gamma : Gamma := singletonGamma relation
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.Case25RandomTableE

