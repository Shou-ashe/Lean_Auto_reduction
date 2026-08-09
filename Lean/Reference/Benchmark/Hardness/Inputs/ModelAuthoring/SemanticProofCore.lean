import ComplexityReduction.Agent.Hardness.ModelAuthoring
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.StandardInstances

/-! Lightweight public mathematical context for the Phase-7 semantic-proof task. -/

namespace Benchmark.Hardness.Inputs.ModelAuthoring.SemanticProofCore

def sourceSemantic : ComplexityReduction.DecisionProblem where
  Instance := Bool
  isYes := fun value => value = value

def targetSemantic : ComplexityReduction.DecisionProblem where
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

def executable : source.Instance → target.Instance := Bool.not

def executableDirectTM :
    ComplexityReduction.Agent.Hardness.Authoring.ExecutableDirectTMEvidence
      source target executable :=
  ComplexityReduction.TMPolyTimeMap.bool_not

@[complexity_reduction_ir_hardness_program_model_template]
def template :
    ComplexityReduction.Agent.Hardness.Authoring.ProgramIndexedModelTemplate
      .sharedGadget source target executable executableDirectTM :=
  ⟨True.intro⟩

end Benchmark.Hardness.Inputs.ModelAuthoring.SemanticProofCore
