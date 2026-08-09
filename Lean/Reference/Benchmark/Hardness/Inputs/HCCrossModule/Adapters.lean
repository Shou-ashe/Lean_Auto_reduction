import Benchmark.Hardness.Inputs.HCCrossModule.Problem

namespace Benchmark.Hardness.Inputs.HCCrossModule.Adapters

open ComplexityReduction.Encoding
open ComplexityReduction.Program
open Benchmark.Hardness.Inputs.HCCrossModule.Problem

def firstAdapter : PolyProg hardnessHub.representation intermediate.representation :=
  .pair (.const hardnessHub.representation StandardInstances.bool false)
    (.id hardnessHub.representation)

def secondAdapter : PolyProg intermediate.representation heldOutTarget.representation :=
  .pair (.const intermediate.representation StandardInstances.bool false)
    (.id intermediate.representation)

end Benchmark.Hardness.Inputs.HCCrossModule.Adapters
