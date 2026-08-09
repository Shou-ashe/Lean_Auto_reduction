import ComplexityReduction.Agent.Hardness.Runtime
import Benchmark.Hardness.Inputs.Routes.GraphColoringRoute

namespace Benchmark.Hardness.Regression.RouteFallback

def policy : ComplexityReduction.Protocol.AutoReductionTrustPolicy :=
  { presentation := .exactUser, requireNativeNP := true }

def request : ComplexityReduction.Protocol.TypedAutoReductionRequest where
  source := .fromPresented Benchmark.Hardness.Inputs.Routes.GraphColoringRoute.source
  policy := policy
  objective := .reduceTo
    Benchmark.Hardness.Inputs.Routes.GraphColoringRoute.source
    ComplexityReduction.Presentation.CliqueCover.structuredProblem

@[complexity_reduction_ir_typed_final_result]
noncomputable def result : ComplexityReduction.Protocol.TypedAutoReductionResult request :=
  by_hardness_resolver

end Benchmark.Hardness.Regression.RouteFallback

assert_standard_axioms Benchmark.Hardness.Regression.RouteFallback.result
