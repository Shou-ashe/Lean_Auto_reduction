import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.Agent.Hardness.Gap
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.StandardInstances

namespace Benchmark.Hardness.Inputs.Authoring.PrimitiveAdmission

private def sourceSemantic : ComplexityReduction.DecisionProblem where
  Instance := Bool
  isYes := fun value => value = false

private def targetSemantic : ComplexityReduction.DecisionProblem where
  Instance := Bool
  isYes := fun value => false = value

def source : ComplexityReduction.Encoding.PresentedProblem where
  semantic := sourceSemantic
  representation := ComplexityReduction.Encoding.StandardInstances.bool
  carrier_eq := rfl

@[complexity_reduction_ir_typed_problem]
def target : ComplexityReduction.Encoding.PresentedProblem where
  semantic := targetSemantic
  representation := ComplexityReduction.Encoding.StandardInstances.bool
  carrier_eq := rfl

/-- The executable exists before primitive admission. -/
def executable : Bool → Bool := fun value => value

/-- Existing direct-TM evidence for that exact executable. -/
def executableTM : ComplexityReduction.TMPolyTimeMap
    ComplexityReduction.EncodedType.bool ComplexityReduction.EncodedType.bool executable := by
  simpa [executable] using
    ComplexityReduction.TMPolyTimeMap.id ComplexityReduction.EncodedType.bool

@[complexity_reduction_ir_typed_gap]
def gap : ComplexityReduction.Agent.Hardness.Gap.DeclaredComponentGap
    .primitive .sharedGadget source target :=
  .exact

/-!
The template exposes an already implemented executable plus its dependent
direct-TM witness.  It is discovery-only and cannot enter the registry until
the job-local primitive and route bundle passes canonical validation.
-/
@[complexity_reduction_ir_hardness_primitive_admission_template]
def template :
    ComplexityReduction.Agent.Hardness.Authoring.PrimitiveAdmissionTemplate
      .sharedGadget source target where
  run := executable
  tmPolyTime := executableTM
  correct := by
    intro input
    change input = false ↔ false = executable input
    simp only [executable]
    exact eq_comm

end Benchmark.Hardness.Inputs.Authoring.PrimitiveAdmission
