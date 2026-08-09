import ComplexityReduction.Agent.Hardness.Authoring
import ComplexityReduction.Agent.Hardness.Gap
import ComplexityReduction.Annotations.Attributes
import ComplexityReduction.Encoding.StandardInstances

namespace Benchmark.Hardness.Inputs.Authoring.LawfulPresentation

private def sourceSemantic : ComplexityReduction.DecisionProblem where
  Instance := Bool
  isYes := fun value => value = true

private def targetSemantic : ComplexityReduction.DecisionProblem where
  Instance := Bool
  isYes := fun value => true = value

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
    .lawfulPresentation .ingress source target :=
  .exact

/-!
This is observational authoring data, not a registry capability.  Its origin
is the closed Boolean structural origin and its executable is encoder
coherent at the exact source/target presentations.
-/
@[complexity_reduction_ir_hardness_lawful_presentation_template]
def template :
    ComplexityReduction.Agent.Hardness.Authoring.LawfulPresentationTemplate
      .ingress source target where
  origin := .bool
  run := id
  alphabetEquiv := Equiv.refl _
  encodeCoherence := by
    intro input
    change ComplexityReduction.EncodedType.bool.encode input =
      (ComplexityReduction.EncodedType.bool.encode input).map (Equiv.refl _)
    simp
  correct := by
    intro input
    change input = true ↔ true = input
    exact eq_comm

end Benchmark.Hardness.Inputs.Authoring.LawfulPresentation
