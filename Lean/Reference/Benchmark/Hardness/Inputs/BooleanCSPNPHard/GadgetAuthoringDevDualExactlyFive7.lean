import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-!
Non-scoring gadget-authoring development fixture: the Boolean dual of
EXACT-2-IN-7, represented as positive EXACT-5-IN-7.  This module contains no
reduction, theorem, route, or oracle metadata.
-/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.GadgetAuthoringDevDualExactlyFive7

open ComplexityReduction ComplexityReduction.CSP ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

noncomputable section

def gamma : Gamma := singletonGamma (StandardRelations.exactlyRel 7 5)
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.GadgetAuthoringDevDualExactlyFive7
