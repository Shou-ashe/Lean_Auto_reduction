import ComplexityReduction.Karp21.PackagedCatalog

namespace BenchmarkHiddenSample

noncomputable section

abbrev sampleProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.directedHamiltonianCircuitStructuredDecisionProblem

abbrev sampleClaim : Prop :=
  ComplexityReduction.SAT.TMInNPWithCheckedSuffixDecoder sampleProblem ∧
    ComplexityReduction.TMInNP sampleProblem

#check sampleProblem
#check sampleClaim

end

end BenchmarkHiddenSample
