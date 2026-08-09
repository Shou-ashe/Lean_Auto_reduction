import ComplexityReduction.Schaefer

namespace BenchmarkHiddenSample

noncomputable section

abbrev sampleCspLanguage : ComplexityReduction.CSP.BoolLanguage :=
  ComplexityReduction.CSP.Examples.threeSATLikeLanguage

abbrev sampleProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Schaefer.satSDecisionProblem sampleCspLanguage

abbrev sampleSchaeferHardCertificateClaim : Type 1 :=
  ComplexityReduction.Schaefer.Hardness.HardRelationCertificate sampleCspLanguage

abbrev sampleSchaeferCompletenessClaim : Prop :=
  ComplexityReduction.NPCompleteEnc
    ComplexityReduction.CostedPolyTimeModel
    sampleProblem

abbrev sampleClaim : Prop :=
  ∃ hardCertificate : sampleSchaeferHardCertificateClaim,
    sampleSchaeferCompletenessClaim

#check sampleCspLanguage
#check sampleProblem
#check sampleSchaeferHardCertificateClaim
#check sampleSchaeferCompletenessClaim
#check sampleClaim

end

end BenchmarkHiddenSample
