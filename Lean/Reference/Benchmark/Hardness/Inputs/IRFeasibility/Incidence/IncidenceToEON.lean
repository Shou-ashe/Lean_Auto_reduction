import ComplexityReduction.Routes.IncidenceToRoleGraph.Unified

namespace Benchmark.Hardness.Inputs.IRFeasibility.Incidence.IncidenceToEON

/-- Existing structured Exact-Cover/set-system source. -/
abbrev originalSource : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.IncidenceToRoleGraph.originalSourceProblem

/-- Existing Boolean-tagged Exact-Cover source with its own certified ingress. -/
abbrev modifiedSource : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.IncidenceToRoleGraph.modifiedSourceProblem

/-- Existential Exactly-One-Neighbor endpoint reached by the shared incidence gadget. -/
@[complexity_reduction_ir_typed_problem]
abbrev target : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.IncidenceToRoleGraph.existentialFinalTargetProblem

end Benchmark.Hardness.Inputs.IRFeasibility.Incidence.IncidenceToEON
