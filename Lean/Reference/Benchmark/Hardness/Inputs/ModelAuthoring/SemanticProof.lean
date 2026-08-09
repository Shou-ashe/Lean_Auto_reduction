import Benchmark.Hardness.Inputs.ModelAuthoring.SemanticProofCore
import ComplexityReduction.Agent.Hardness.Gap

/-!
Public Phase-7 model-authoring problem.

The executable and its exact direct-TM witness are public, but there is no
semantic proof, primitive, program, reduction, or registered route.  The gold
proof lives under `Benchmark.Hardness.Oracles` and is not imported here.
-/

namespace Benchmark.Hardness.Inputs.ModelAuthoring.SemanticProof

open Benchmark.Hardness.Inputs.ModelAuthoring.SemanticProofCore

@[complexity_reduction_ir_typed_gap]
def gap : ComplexityReduction.Agent.Hardness.Gap.DeclaredComponentGap
    .semanticProof .sharedGadget source target :=
  .exact

end Benchmark.Hardness.Inputs.ModelAuthoring.SemanticProof
