import ComplexityReduction.Agent.Hardness.Gap
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.PresentedProblem
import ComplexityReduction.Encoding.StandardInstances

namespace Benchmark.Hardness.Inputs.Gaps.MissingPrimitive

private def sourceSemantic : ComplexityReduction.DecisionProblem where
  Instance := Bool
  isYes := fun value => value = true

private def targetSemantic : ComplexityReduction.DecisionProblem where
  Instance := Bool
  isYes := fun _ => True

def source : ComplexityReduction.Encoding.PresentedProblem where
  semantic := sourceSemantic
  representation := ComplexityReduction.Encoding.StandardInstances.bool
  carrier_eq := rfl

@[complexity_reduction_ir_typed_problem]
def target : ComplexityReduction.Encoding.PresentedProblem where
  semantic := targetSemantic
  representation := ComplexityReduction.Encoding.StandardInstances.bool
  carrier_eq := rfl

/-!
The exact reason and component endpoints are Lean type indices.  This
declaration is diagnostic only and cannot construct a primitive or reduction.
-/
@[complexity_reduction_ir_typed_gap]
def gap : ComplexityReduction.Agent.Hardness.Gap.DeclaredComponentGap
    .primitive .sharedGadget source target :=
  .exact

end Benchmark.Hardness.Inputs.Gaps.MissingPrimitive
