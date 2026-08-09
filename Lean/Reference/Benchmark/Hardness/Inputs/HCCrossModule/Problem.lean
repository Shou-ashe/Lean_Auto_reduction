import ComplexityReduction.Encoding.StandardInstances
import ComplexityReduction.Problems.Karp21.GraphAtoms

/-!
An H-C held-out target whose planning capabilities intentionally live in
separate imported modules.  The declaration is public but is not registered as
a reduction, hardness seed, or benchmark planner constant.
-/

namespace Benchmark.Hardness.Inputs.HCCrossModule.Problem

open ComplexityReduction
open ComplexityReduction.Encoding

abbrev hardnessHub : PresentedProblem :=
  ComplexityReduction.Problems.Karp21.GraphAtoms.cliqueStructuredProblem

def intermediateSemantic : ComplexityReduction.DecisionProblem where
  Instance := Bool × hardnessHub.Instance
  isYes := fun input => hardnessHub.accepts input.2

def intermediate : PresentedProblem where
  semantic := intermediateSemantic
  representation := StandardInstances.prod StandardInstances.bool hardnessHub.representation
  carrier_eq := rfl

def targetSemantic : ComplexityReduction.DecisionProblem where
  Instance := Bool × intermediate.Instance
  isYes := fun input => intermediate.accepts input.2

@[complexity_reduction_ir_typed_problem]
def heldOutTarget : PresentedProblem where
  semantic := targetSemantic
  representation := StandardInstances.prod StandardInstances.bool intermediate.representation
  carrier_eq := rfl

end Benchmark.Hardness.Inputs.HCCrossModule.Problem
