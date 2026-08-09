import Benchmark.Hardness.Inputs.HCCrossModule.Entry

/-!
H-D held-out production input: the user supplies only a bare lawful encoding.
The unique matching `PresentedProblem`, its cross-module adapters, and its
typed proof gaps all live in imported modules and are not named by the
normalization or authoring planners.
-/

namespace Benchmark.Hardness.Inputs.HDCrossModuleEncoding

open ComplexityReduction
open ComplexityReduction.Encoding

def heldOutEncoding : LawfulEncodedType :=
  Benchmark.Hardness.Inputs.HCCrossModule.Problem.heldOutTarget.representation

end Benchmark.Hardness.Inputs.HDCrossModuleEncoding
