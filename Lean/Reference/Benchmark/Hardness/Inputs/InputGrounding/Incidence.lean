import ComplexityReduction.Routes.IncidenceToRoleGraph.Unified

namespace Benchmark.Hardness.Inputs.InputGrounding.Incidence

abbrev exactCoverDirect : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.IncidenceToRoleGraph.originalSourceProblem

abbrev exactCoverAlias : ComplexityReduction.Encoding.PresentedProblem :=
  exactCoverDirect

noncomputable def exactCoverWrapped : ComplexityReduction.Encoding.PresentedProblem :=
  exactCoverDirect

abbrev modifiedExactCoverDirect : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.IncidenceToRoleGraph.modifiedSourceProblem

abbrev modifiedExactCoverAlias : ComplexityReduction.Encoding.PresentedProblem :=
  modifiedExactCoverDirect

noncomputable def modifiedExactCoverWrapped : ComplexityReduction.Encoding.PresentedProblem :=
  modifiedExactCoverDirect

abbrev target : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.IncidenceToRoleGraph.existentialFinalTargetProblem

end Benchmark.Hardness.Inputs.InputGrounding.Incidence
