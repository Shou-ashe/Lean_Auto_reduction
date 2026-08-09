import ComplexityReduction.CSP.Examples.ThreeSATLikeInNP

namespace BenchmarkHiddenSample

noncomputable section

abbrev sampleProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.CSP.Examples.threeSATLikeDecisionProblem

abbrev sampleClaim : Prop :=
  ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel sampleProblem

#check sampleProblem
#check sampleClaim

end

end BenchmarkHiddenSample
