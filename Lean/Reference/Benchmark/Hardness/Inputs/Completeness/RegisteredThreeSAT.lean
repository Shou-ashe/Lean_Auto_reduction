import ComplexityReduction.Certificate.NativeCookLevin

namespace Benchmark.Hardness.Inputs.Completeness.RegisteredThreeSAT

/-- Exact canonical complete endpoint; no transport path is needed. -/
abbrev source : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Certificate.NativeCookLevin.canonicalThreeSAT

end Benchmark.Hardness.Inputs.Completeness.RegisteredThreeSAT
