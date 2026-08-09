import ComplexityReduction.Agent.Hardness.Runtime
import Benchmark.Hardness.Inputs.Smoke.ThreeSATRefl

namespace Benchmark.Hardness.Regression.Refl

def policy : ComplexityReduction.Protocol.AutoReductionTrustPolicy :=
  { presentation := .exactUser, requireNativeNP := true }

def request : ComplexityReduction.Protocol.TypedAutoReductionRequest where
  source := .fromPresented Benchmark.Hardness.Inputs.Smoke.ThreeSATRefl.source
  policy := policy
  objective := .reduceToKnownNP
    Benchmark.Hardness.Inputs.Smoke.ThreeSATRefl.source
    Benchmark.Hardness.Inputs.Smoke.ThreeSATRefl.source

@[complexity_reduction_ir_typed_final_result]
noncomputable def result : ComplexityReduction.Protocol.TypedAutoReductionResult request :=
  by_hardness_resolver

end Benchmark.Hardness.Regression.Refl

assert_standard_axioms Benchmark.Hardness.Regression.Refl.result
