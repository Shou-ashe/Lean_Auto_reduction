import ComplexityReduction_IR.V2.Problems.Karp21.Satisfiability

/-! Canonical V2 source used by the trusted hardness-route smoke benchmark. -/

namespace Benchmark.V2Hardness.ThreeSAT

abbrev source : ComplexityReduction_IR.V2.Encoding.PresentedProblem :=
  ComplexityReduction_IR.V2.Problems.Karp21.Satisfiability.threeSATStructuredProblem

end Benchmark.V2Hardness.ThreeSAT
