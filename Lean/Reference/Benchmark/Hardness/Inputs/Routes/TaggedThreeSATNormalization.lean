import ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters

namespace Benchmark.Hardness.Inputs.Routes.TaggedThreeSATNormalization

/-- A Boolean-tagged presentation whose registered ingress erases the ignored tag. -/
abbrev source : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Routes.ThreeSATToClique.IngressAdapters.taggedThreeSATProblem

abbrev target : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem

end Benchmark.Hardness.Inputs.Routes.TaggedThreeSATNormalization
