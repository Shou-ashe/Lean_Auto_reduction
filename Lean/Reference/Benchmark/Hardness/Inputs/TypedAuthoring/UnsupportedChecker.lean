import ComplexityReduction.Agent.Hardness.Gap
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.StandardInstances

namespace Benchmark.Hardness.Inputs.TypedAuthoring.UnsupportedChecker

private def semantic : ComplexityReduction.DecisionProblem where
  Instance := Bool
  isYes := fun _ => True

@[complexity_reduction_ir_typed_problem]
def problem : ComplexityReduction.Encoding.PresentedProblem where
  semantic := semantic
  representation := ComplexityReduction.Encoding.StandardInstances.bool
  carrier_eq := rfl

abbrev source : ComplexityReduction.Encoding.PresentedProblem := problem

@[complexity_reduction_ir_typed_gap]
def gap : ComplexityReduction.Agent.Hardness.Gap.DeclaredComponentGap
    .checkerCombinatorUnsupported .finalComposition problem problem :=
  .exact

/-! No verifier, checker, TM, or native-membership template is admitted here. -/

end Benchmark.Hardness.Inputs.TypedAuthoring.UnsupportedChecker
