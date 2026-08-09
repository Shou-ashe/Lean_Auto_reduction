import ComplexityReduction.Routes.GraphToRoleGraph.Unified

namespace Benchmark.Hardness.Inputs.InputGrounding.Observation

abbrev direct : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.GraphToRoleGraph.originalSourceProblem

abbrev problemAlias : ComplexityReduction.Encoding.PresentedProblem :=
  direct

noncomputable def wrapped : ComplexityReduction.Encoding.PresentedProblem :=
  direct

def ordinaryProp : Prop :=
  True

def predicate (value : Nat) : Prop :=
  value = 0

def openProblem
    (problem : ComplexityReduction.Encoding.PresentedProblem) :
    ComplexityReduction.Encoding.PresentedProblem :=
  problem

universe u

def polymorphicProblem
    {α : Type u} (_value : α)
    (problem : ComplexityReduction.Encoding.PresentedProblem) :
    ComplexityReduction.Encoding.PresentedProblem :=
  problem

noncomputable def disconnectedProblem : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Encoding.PresentedProblem.ofProblemAt
    direct.representation ⟨fun _ => False⟩

abbrev reverseOnlySource : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.GraphToRoleGraph.roleGraphTargetProblem

abbrev reverseOnlyTarget : ComplexityReduction.Encoding.PresentedProblem :=
  direct

end Benchmark.Hardness.Inputs.InputGrounding.Observation
