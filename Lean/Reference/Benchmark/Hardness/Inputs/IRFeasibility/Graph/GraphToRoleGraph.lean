import ComplexityReduction.Routes.GraphToRoleGraph.Unified

namespace Benchmark.Hardness.Inputs.IRFeasibility.Graph.GraphToRoleGraph

/-- Concrete structured-graph wrapper used by both sides of the matched study. -/
abbrev source : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.GraphToRoleGraph.originalSourceProblem

/-- The exact RoleGraphIR endpoint, registered only so the fixed-target input gate can name it. -/
@[complexity_reduction_ir_typed_problem]
abbrev target : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.GraphToRoleGraph.roleGraphTargetProblem

end Benchmark.Hardness.Inputs.IRFeasibility.Graph.GraphToRoleGraph
