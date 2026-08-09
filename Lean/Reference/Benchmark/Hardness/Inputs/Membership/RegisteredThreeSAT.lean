import ComplexityReduction.Problems.Karp21.ThreeSATNativeVerifier

namespace Benchmark.Hardness.Inputs.Membership.RegisteredThreeSAT

/-- Exact endpoint with an already registered V2-native membership declaration. -/
abbrev source : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem

end Benchmark.Hardness.Inputs.Membership.RegisteredThreeSAT
