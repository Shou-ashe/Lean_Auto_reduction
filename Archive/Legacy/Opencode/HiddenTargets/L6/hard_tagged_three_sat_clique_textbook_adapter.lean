import ComplexityReduction.Karp21

namespace BenchmarkHiddenSample

noncomputable section

abbrev sampleSourceBase : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.SAT.threeSATDecisionProblem

abbrev sampleProblem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.EncodedType.prod
      ComplexityReduction.EncodedType.bool
      sampleSourceBase.Instance
    isYes := fun p => sampleSourceBase.isYes p.2 }

abbrev sampleTextbookTarget : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.cliqueDecisionProblem

abbrev sampleTextbookReductionClaim : Type :=
  ComplexityReduction.KarpReductionM
    ComplexityReduction.CostedPolyTimeModel
    sampleProblem
    sampleTextbookTarget

abbrev sampleTextbookRouteClaim : Prop :=
  ComplexityReduction.PolyReducibleM
    ComplexityReduction.CostedPolyTimeModel
    sampleProblem
    sampleTextbookTarget

abbrev sampleTextbookTargetMembershipClaim : Prop :=
  ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel sampleTextbookTarget

abbrev sampleClaim : Prop :=
  ∃ textbookTarget : ComplexityReduction.EncodedDecisionProblem,
    textbookTarget = sampleTextbookTarget ∧
      ∃ textbookReductionCertificate :
        ComplexityReduction.KarpReductionM ComplexityReduction.CostedPolyTimeModel sampleProblem textbookTarget,
        ∃ textbookRouteCertificate :
          ComplexityReduction.PolyReducibleM ComplexityReduction.CostedPolyTimeModel sampleProblem textbookTarget,
          ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel textbookTarget ∧
            ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel sampleProblem

#check sampleProblem
#check sampleTextbookTarget
#check sampleTextbookReductionClaim
#check sampleTextbookRouteClaim
#check sampleTextbookTargetMembershipClaim
#check sampleClaim

end

end BenchmarkHiddenSample
