import ComplexityReduction.Karp21

namespace BenchmarkHiddenSample

noncomputable section

abbrev sampleProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.exactCoverDecisionProblem

abbrev sampleClaim : Prop :=
  ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel sampleProblem

#check sampleProblem
#check sampleClaim

end

end BenchmarkHiddenSample
