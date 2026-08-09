import ComplexityReduction.SAT.ThreeSATInNP

namespace BenchmarkHiddenSample

noncomputable section

abbrev sampleProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.SAT.threeSATDecisionProblem

abbrev sampleClaim : Prop :=
  ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel sampleProblem

#check sampleProblem
#check sampleClaim

end

end BenchmarkHiddenSample
