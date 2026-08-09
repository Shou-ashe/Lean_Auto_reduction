import ComplexityReduction.Problems.Karp21.KnapsackNativeVerifier
import ComplexityReduction.Problems.Karp21.ThreeSATNativeVerifier

namespace Benchmark.Hardness.Inputs.Negative.WrongMembership

abbrev source : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Presentation.Knapsack.structuredProblem

/-- Deliberately proves membership at the wrong exact endpoint. -/
theorem wrongMembership : ComplexityReduction.Certificate.NativeTMInNP
    ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem :=
  ComplexityReduction.Problems.Karp21.ThreeSATNativeVerifier.threeSATStructuredNativeTMInNP

end Benchmark.Hardness.Inputs.Negative.WrongMembership
