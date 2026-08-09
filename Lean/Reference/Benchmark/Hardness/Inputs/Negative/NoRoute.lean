import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Encoding.StandardInstances

namespace Benchmark.Hardness.Inputs.Negative.NoRoute

private def sourceSemantic : ComplexityReduction.DecisionProblem where
  Instance := Bool
  isYes := fun value => value = true

private def targetSemantic : ComplexityReduction.DecisionProblem where
  Instance := Bool
  isYes := fun value => value = false

def source : ComplexityReduction.Encoding.PresentedProblem where
  semantic := sourceSemantic
  representation := ComplexityReduction.Encoding.StandardInstances.bool
  carrier_eq := rfl

@[complexity_reduction_ir_typed_problem]
def target : ComplexityReduction.Encoding.PresentedProblem where
  semantic := targetSemantic
  representation := ComplexityReduction.Encoding.StandardInstances.bool
  carrier_eq := rfl

end Benchmark.Hardness.Inputs.Negative.NoRoute
