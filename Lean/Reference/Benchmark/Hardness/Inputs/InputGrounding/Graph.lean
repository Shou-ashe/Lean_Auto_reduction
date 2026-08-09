import ComplexityReduction.Routes.GraphToRoleGraph.Unified

namespace Benchmark.Hardness.Inputs.InputGrounding.Graph

abbrev direct : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.GraphToRoleGraph.originalSourceProblem

abbrev problemAlias : ComplexityReduction.Encoding.PresentedProblem :=
  direct

noncomputable def wrapped : ComplexityReduction.Encoding.PresentedProblem :=
  direct

abbrev target : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.GraphToRoleGraph.roleGraphTargetProblem

end Benchmark.Hardness.Inputs.InputGrounding.Graph
