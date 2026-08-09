import ComplexityReduction.Agent.Hardness.Gap
import ComplexityReduction.Encoding.StandardInstances
import ComplexityReduction.Presentation.SetSystem

/-!
Set-system NP-hard authoring input.

Two endpoint-compatible public adapters are supplied, but their composition and
the program-indexed semantic certificate are intentionally not registered.
-/

namespace Benchmark.Hardness.Inputs.NPHardGeneralization.SetSystemProgramComposition

open ComplexityReduction
open ComplexityReduction.Certificate
open ComplexityReduction.Encoding
open ComplexityReduction.Program

abbrev hub : PresentedProblem :=
  ComplexityReduction.Presentation.SetSystem.exactCoverStructuredProblem

def intermediateSemantic : ComplexityReduction.DecisionProblem where
  Instance := Bool × hub.Instance
  isYes := fun input => hub.accepts input.2

def intermediate : PresentedProblem where
  semantic := intermediateSemantic
  representation := StandardInstances.prod StandardInstances.bool hub.representation
  carrier_eq := rfl

def composedSemantic : ComplexityReduction.DecisionProblem where
  Instance := Bool × intermediate.Instance
  isYes := fun input => intermediate.accepts input.2

@[complexity_reduction_ir_typed_problem]
def source : PresentedProblem where
  semantic := composedSemantic
  representation := StandardInstances.prod StandardInstances.bool intermediate.representation
  carrier_eq := rfl

def firstAdapter : PolyProg hub.representation intermediate.representation :=
  .pair (.const hub.representation StandardInstances.bool false) (.id hub.representation)

def secondAdapter : PolyProg intermediate.representation source.representation :=
  .pair (.const intermediate.representation StandardInstances.bool false)
    (.id intermediate.representation)

@[complexity_reduction_ir_typed_gap]
def programGap : ComplexityReduction.Agent.Hardness.Gap.DeclaredComponentGap
    .executableRelationContract .egress hub source :=
  .exact

@[complexity_reduction_ir_typed_gap]
def semanticGap : ComplexityReduction.Agent.Hardness.Gap.DeclaredComponentGap
    .semanticProof .egress hub source :=
  .exact

end Benchmark.Hardness.Inputs.NPHardGeneralization.SetSystemProgramComposition
