import ComplexityReduction.Routes.ClauseToCSP.IngressAdapters

namespace Benchmark.Hardness.Inputs.InputGrounding.Clause

abbrev structuredCNFDirect : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.ClauseToCSP.originalClauseCNFProblem

abbrev structuredCNFAlias : ComplexityReduction.Encoding.PresentedProblem :=
  structuredCNFDirect

noncomputable def structuredCNFWrapped : ComplexityReduction.Encoding.PresentedProblem :=
  structuredCNFDirect

abbrev twoCNFDirect : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.ClauseToCSP.IngressAdapters.twoCNFSourceProblem

abbrev twoCNFAlias : ComplexityReduction.Encoding.PresentedProblem :=
  twoCNFDirect

noncomputable def twoCNFWrapped : ComplexityReduction.Encoding.PresentedProblem :=
  twoCNFDirect

abbrev threeSATDirect : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.ClauseToCSP.IngressAdapters.threeSATSourceProblem

abbrev threeSATAlias : ComplexityReduction.Encoding.PresentedProblem :=
  threeSATDirect

noncomputable def threeSATWrapped : ComplexityReduction.Encoding.PresentedProblem :=
  threeSATDirect

noncomputable def target : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.ClauseToCSP.IngressAdapters.cspTargetProblem

end Benchmark.Hardness.Inputs.InputGrounding.Clause
