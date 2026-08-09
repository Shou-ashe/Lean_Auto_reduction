import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.Agent.Hardness.Gap
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.StandardInstances

namespace Benchmark.Hardness.Inputs.Authoring.ProgramIndexedReduction

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

/-!
The marker is observational input to the Phase-5 authoring lane.  Its three
components are independent global declarations, so each generated checkpoint
has its own transitive proof basis.  No primitive, program, program-indexed
checkpoint, or route is registered by this module.  The new executable is
Boolean negation rather than an identity/refl shortcut.
-/
def executable : source.Instance → target.Instance := Bool.not

def executableDirectTM :
    ComplexityReduction.Agent.Hardness.Authoring.ExecutableDirectTMEvidence
      source target executable :=
  ComplexityReduction.TMPolyTimeMap.bool_not

def executableCorrect :
    ComplexityReduction.Agent.Hardness.Authoring.ExecutableSemanticProof
      source target executable := by
  intro input
  change input = input ↔ True
  simp

@[complexity_reduction_ir_hardness_program_reduction_template]
def template :
    ComplexityReduction.Agent.Hardness.Authoring.ProgramIndexedReductionTemplate
      .sharedGadget source target executable executableDirectTM executableCorrect :=
  ⟨True.intro⟩

end Benchmark.Hardness.Inputs.Authoring.ProgramIndexedReduction
