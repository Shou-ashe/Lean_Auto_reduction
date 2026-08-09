import ComplexityReduction.Agent.Hardness.InputInspection
import Benchmark.Hardness.Inputs.InputGrounding.Observation

namespace Benchmark.Hardness.InputGroundingRegression

open Benchmark.Hardness.Inputs.InputGrounding.Observation

example : direct = problemAlias :=
  rfl

example : direct = wrapped :=
  rfl

#hardness_inspect_input "regression-direct"
  Benchmark.Hardness.Inputs.InputGrounding.Observation.direct

#hardness_inspect_input "regression-alias"
  Benchmark.Hardness.Inputs.InputGrounding.Observation.problemAlias

#hardness_inspect_input "regression-wrapped"
  Benchmark.Hardness.Inputs.InputGrounding.Observation.wrapped

#hardness_inspect_input "regression-prop"
  Benchmark.Hardness.Inputs.InputGrounding.Observation.ordinaryProp

#hardness_inspect_input "regression-predicate"
  Benchmark.Hardness.Inputs.InputGrounding.Observation.predicate

#hardness_inspect_input "regression-open"
  Benchmark.Hardness.Inputs.InputGrounding.Observation.openProblem

#hardness_inspect_input "regression-polymorphic"
  Benchmark.Hardness.Inputs.InputGrounding.Observation.polymorphicProblem

#hardness_inspect_input "regression-disconnected"
  Benchmark.Hardness.Inputs.InputGrounding.Observation.disconnectedProblem

#hardness_inspect_input "regression-reverse-only"
  Benchmark.Hardness.Inputs.InputGrounding.Observation.reverseOnlySource

end Benchmark.Hardness.InputGroundingRegression
