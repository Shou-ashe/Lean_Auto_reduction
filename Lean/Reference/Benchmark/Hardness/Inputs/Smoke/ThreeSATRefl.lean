import ComplexityReduction.Problems.Karp21.Satisfiability

namespace Benchmark.Hardness.Inputs.Smoke.ThreeSATRefl

/-- The source is definitionally the canonical native structured-3SAT target. -/
abbrev source : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Problems.Karp21.Satisfiability.threeSATStructuredProblem

end Benchmark.Hardness.Inputs.Smoke.ThreeSATRefl
