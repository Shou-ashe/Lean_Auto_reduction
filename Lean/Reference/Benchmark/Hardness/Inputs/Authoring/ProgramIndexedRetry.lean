import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.Agent.Hardness.Gap
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.StandardInstances

namespace Benchmark.Hardness.Inputs.Authoring.ProgramIndexedRetry

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

@[complexity_reduction_ir_typed_gap]
def gap : ComplexityReduction.Agent.Hardness.Gap.DeclaredComponentGap
    .semanticProof .sharedGadget source target :=
  .exact

def executable : source.Instance → target.Instance := Bool.not

def executableDirectTM :
    ComplexityReduction.Agent.Hardness.Authoring.ExecutableDirectTMEvidence
      source target executable :=
  ComplexityReduction.TMPolyTimeMap.bool_not

/-!
Keep the retry fixture self-contained: `native_decide` supplies a deliberately
non-standard proof dependency without importing an unrelated benchmark route.
The first generated semantic checkpoint must therefore fail its dependency gate.
-/
opaque retainedBackendFact : True := by native_decide

def aPoisonedCorrect :
    ComplexityReduction.Agent.Hardness.Authoring.ExecutableSemanticProof
      source target executable := by
  intro input
  change input = input ↔ True
  exact ⟨fun _ => retainedBackendFact, fun _ => rfl⟩

/-! The first marker selects a semantic declaration outside the standard proof basis. -/
@[complexity_reduction_ir_hardness_program_reduction_template]
def aPoisonedTemplate :
    ComplexityReduction.Agent.Hardness.Authoring.ProgramIndexedReductionTemplate
      .sharedGadget source target executable executableDirectTM aPoisonedCorrect :=
  ⟨True.intro⟩

def zCleanCorrect :
    ComplexityReduction.Agent.Hardness.Authoring.ExecutableSemanticProof
      source target executable := by
  intro input
  change input = input ↔ True
  simp

/-! The retry must overwrite all stage-local outputs and accept only this clean observation. -/
@[complexity_reduction_ir_hardness_program_reduction_template]
def zCleanTemplate :
    ComplexityReduction.Agent.Hardness.Authoring.ProgramIndexedReductionTemplate
      .sharedGadget source target executable executableDirectTM zCleanCorrect :=
  ⟨True.intro⟩

end Benchmark.Hardness.Inputs.Authoring.ProgramIndexedRetry
