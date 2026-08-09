import ComplexityReduction.CSP.Examples.NAE3SAT

namespace BenchmarkHiddenSample

noncomputable section

abbrev sampleProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.CSP.Examples.notAllEqual3DecisionProblem

abbrev sampleClaim : Prop :=
  ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel sampleProblem

#check sampleProblem
#check sampleClaim

end

end BenchmarkHiddenSample
