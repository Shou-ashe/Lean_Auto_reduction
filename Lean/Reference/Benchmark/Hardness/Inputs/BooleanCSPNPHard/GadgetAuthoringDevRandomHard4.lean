import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-!
Non-scoring gadget-authoring development fixture: one fixed random hard-side
four-ary relation.  This module contains no reduction, theorem, route, or
oracle metadata.
-/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.GadgetAuthoringDevRandomHard4

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

noncomputable section

def relation : BoolRel := truthTableRel 4 0x135E

def gamma : Gamma := singletonGamma relation
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.GadgetAuthoringDevRandomHard4
