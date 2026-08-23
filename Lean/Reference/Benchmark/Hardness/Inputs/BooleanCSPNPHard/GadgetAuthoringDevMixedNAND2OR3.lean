import Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

/-!
Non-scoring gadget-authoring development fixture: the mixed-arity language
`{NAND₂, OR₃}`.  This module contains no reduction, theorem, route, or oracle
metadata.
-/

namespace Benchmark.Hardness.Inputs.BooleanCSPNPHard.GadgetAuthoringDevMixedNAND2OR3

open ComplexityReduction
open ComplexityReduction.CSP
open ComplexityReduction.Domain.BooleanCSP
open Benchmark.Hardness.Inputs.BooleanCSPNPHard.Common

noncomputable section

def nand2 : BoolRel := truthTableRel 2 0x7
def or3 : BoolRel := truthTableRel 3 0xFE

def gamma : Gamma := pairGamma nand2 or3
def problem : Encoding.PresentedProblem := cspOf gamma

end
end Benchmark.Hardness.Inputs.BooleanCSPNPHard.GadgetAuthoringDevMixedNAND2OR3
