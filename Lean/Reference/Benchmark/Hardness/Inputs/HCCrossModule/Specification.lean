import Benchmark.Hardness.Inputs.HCCrossModule.Problem
import ComplexityReduction.Agent.Hardness.Gap

namespace Benchmark.Hardness.Inputs.HCCrossModule.Specification

open ComplexityReduction
open Benchmark.Hardness.Inputs.HCCrossModule.Problem

def mappingInvariant (input : hardnessHub.Instance)
    (output : heldOutTarget.Instance) : Prop :=
  output.1 = false ∧ output.2.1 = false ∧ output.2.2 = input

@[complexity_reduction_ir_typed_gap]
def programGap : Agent.Hardness.Gap.DeclaredComponentGap
    .executableRelationContract .egress hardnessHub heldOutTarget :=
  .exact

@[complexity_reduction_ir_typed_gap]
def semanticGap : Agent.Hardness.Gap.DeclaredComponentGap
    .semanticProof .egress hardnessHub heldOutTarget :=
  .exact

end Benchmark.Hardness.Inputs.HCCrossModule.Specification
