import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Encoding.StandardInstances

namespace Benchmark.Hardness.Inputs.Gaps.MissingNativeMembership

private def semantic : ComplexityReduction.DecisionProblem where
  Instance := Bool
  isYes := fun value => value = true

@[complexity_reduction_ir_typed_problem]
def problem : ComplexityReduction.Encoding.PresentedProblem where
  semantic := semantic
  representation := ComplexityReduction.Encoding.StandardInstances.bool
  carrier_eq := rfl

abbrev source : ComplexityReduction.Encoding.PresentedProblem :=
  problem

end Benchmark.Hardness.Inputs.Gaps.MissingNativeMembership
