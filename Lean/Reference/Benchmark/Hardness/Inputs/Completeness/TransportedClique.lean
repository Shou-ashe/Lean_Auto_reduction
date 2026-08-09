import ComplexityReduction.Problems.Karp21.GraphMembership

namespace Benchmark.Hardness.Inputs.Completeness.TransportedClique

/-- Native-NP target reachable by a registered forward path from canonical 3SAT. -/
abbrev source : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Problems.Karp21.GraphAtoms.cliqueStructuredProblem

end Benchmark.Hardness.Inputs.Completeness.TransportedClique
