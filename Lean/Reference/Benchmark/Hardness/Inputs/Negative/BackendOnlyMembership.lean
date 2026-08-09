import ComplexityReduction.Problems.Karp21.ChromaticMembership

namespace Benchmark.Hardness.Inputs.Negative.BackendOnlyMembership

abbrev source : ComplexityReduction.Encoding.PresentedProblem :=
  ComplexityReduction.Presentation.ChromaticNumber.structuredProblem

/-- Backend evidence is intentionally not an exact `NativeTMInNP source`. -/
theorem backendOnlyMembership : ComplexityReduction.TMInNP source.toEncodedDecisionProblem :=
  ComplexityReduction.Problems.Karp21.ChromaticMembership.chromaticNumberStructured_backendTMInNP_export

end Benchmark.Hardness.Inputs.Negative.BackendOnlyMembership
