import ComplexityReduction.Agent.Hardness.Gap
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.StandardInstances

namespace Benchmark.Hardness.Inputs.Authoring.MissingDirectTM

private def sourceSemantic : ComplexityReduction.DecisionProblem where
  Instance := Bool
  isYes := fun value => value = value

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

def executable : Bool → Bool := Bool.not

@[complexity_reduction_ir_typed_gap]
def gap : ComplexityReduction.Agent.Hardness.Gap.DeclaredComponentGap
    .directTM .sharedGadget source target :=
  .exact

/-!
Deliberately no direct-TM or program-reduction template is provided.  A bare
executable is observational source code only and must leave the exact
`.directTM` blocker intact.
-/

end Benchmark.Hardness.Inputs.Authoring.MissingDirectTM
