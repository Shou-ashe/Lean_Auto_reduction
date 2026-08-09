import ComplexityReduction.Problems.Karp21.CliqueNativeVerifier
import ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters

namespace Benchmark.Hardness.Inputs.Routes.ThreeSATExplicitSuffix

/-- Canonical structured 3SAT, with a fixed, distinct native-NP Clique target. -/
abbrev source : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem

abbrev target : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Problems.Karp21.GraphAtoms.cliqueStructuredProblem

end Benchmark.Hardness.Inputs.Routes.ThreeSATExplicitSuffix
