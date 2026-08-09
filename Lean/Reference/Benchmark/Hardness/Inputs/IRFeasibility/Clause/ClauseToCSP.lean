import ComplexityReduction.Routes.ClauseToCSP.IngressAdapters

namespace Benchmark.Hardness.Inputs.IRFeasibility.Clause.ClauseToCSP

/-- Public structured-CNF source backed by the existing Clause-to-CSP route. -/
abbrev structuredCNFSource : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.ClauseToCSP.originalClauseCNFProblem

/-- Direct 2CNF source whose existing ingress normalizes into the shared clause hub. -/
abbrev twoCNFSource : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.ClauseToCSP.IngressAdapters.twoCNFSourceProblem

/-- Bundled structured 3SAT source, definitionally already at the shared clause hub. -/
abbrev threeSATSource : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.ClauseToCSP.IngressAdapters.threeSATSourceProblem

/-- Exact existing CSP endpoint shared by all three matched source forms. -/
@[complexity_reduction_ir_typed_problem]
noncomputable abbrev target : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.ClauseToCSP.IngressAdapters.cspTargetProblem

end Benchmark.Hardness.Inputs.IRFeasibility.Clause.ClauseToCSP
