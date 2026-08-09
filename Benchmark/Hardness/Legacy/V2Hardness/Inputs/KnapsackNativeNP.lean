import ComplexityReduction_IR.V2.Problems.Karp21.KnapsackNativeVerifier

/-!
An NP input supplied in the agent's intended ABI: one exact `PresentedProblem`
and one V2-native membership theorem.  The agent must synthesize the checked
Cook--Levin root before selecting a library target.
-/

namespace Benchmark.V2Hardness.KnapsackNativeNP

abbrev source : ComplexityReduction_IR.V2.Encoding.PresentedProblem :=
  ComplexityReduction_IR.V2.Presentation.Knapsack.structuredProblem

theorem membership : ComplexityReduction_IR.V2.Certificate.NativeTMInNP source :=
  ComplexityReduction_IR.V2.Problems.Karp21.KnapsackNativeVerifier.structured_nativeTMInNP

end Benchmark.V2Hardness.KnapsackNativeNP
