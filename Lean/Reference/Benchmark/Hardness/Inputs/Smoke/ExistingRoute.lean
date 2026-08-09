import ComplexityReduction.Problems.Karp21.SATTractable

namespace Benchmark.Hardness.Inputs.Smoke.ExistingRoute

/-- Direct 2CNF reaches native structured 3SAT through registered component edges. -/
abbrev source : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Problems.Karp21.SATTractable.twoCNFStructuredProblem

end Benchmark.Hardness.Inputs.Smoke.ExistingRoute
