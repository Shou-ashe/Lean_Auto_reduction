import ComplexityReduction.Problems.Karp21.KnapsackNativeVerifier
import ComplexityReduction.Problems.Karp21.CliqueNativeVerifier

namespace Benchmark.Hardness.Inputs.CookLevin.KnapsackNativeNP

/-- An exact native-NP source reserved for the Phase 2 checked Cook--Levin lane. -/
abbrev source : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Presentation.Knapsack.structuredProblem

theorem membership : ComplexityReduction.Certificate.NativeTMInNP source :=
  ComplexityReduction.Problems.Karp21.KnapsackNativeVerifier.structured_nativeTMInNP

end Benchmark.Hardness.Inputs.CookLevin.KnapsackNativeNP
