import ComplexityReduction.Karp21

namespace BenchmarkHiddenSample

noncomputable section

abbrev sampleNormalizedProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.exactCoverDecisionProblem

abbrev sampleProblem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.EncodedType.prod
      ComplexityReduction.EncodedType.bool
      (ComplexityReduction.EncodedType.prod
        ComplexityReduction.EncodedType.bool
        sampleNormalizedProblem.Instance)
    isYes := fun p => sampleNormalizedProblem.isYes p.2.2 }

abbrev sampleNormalizedRouteTarget : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.steinerTreeDecisionProblem

abbrev sampleEncodingBridgeClaim : Type :=
  ComplexityReduction.ProblemEquivM
    ComplexityReduction.CostedPolyTimeModel
    sampleProblem
    sampleNormalizedProblem

abbrev sampleNormalizedReductionClaim : Type :=
  ComplexityReduction.KarpReductionM
    ComplexityReduction.CostedPolyTimeModel
    sampleNormalizedProblem
    sampleNormalizedRouteTarget

abbrev sampleLiftedReductionClaim : Prop :=
  ComplexityReduction.PolyReducibleM
    ComplexityReduction.CostedPolyTimeModel
    sampleProblem
    sampleNormalizedRouteTarget

abbrev sampleNormalizedRouteTargetMembershipClaim : Prop :=
  ComplexityReduction.InNPEnc
    ComplexityReduction.CostedPolyTimeModel
    sampleNormalizedRouteTarget

abbrev sampleClaim : Prop :=
  ∃ normalizedProblem : ComplexityReduction.EncodedDecisionProblem,
    normalizedProblem = sampleNormalizedProblem ∧
      ∃ encodingBridgeCertificate :
        ComplexityReduction.ProblemEquivM ComplexityReduction.CostedPolyTimeModel sampleProblem normalizedProblem,
        ∃ normalizedRouteTarget : ComplexityReduction.EncodedDecisionProblem,
          normalizedRouteTarget = sampleNormalizedRouteTarget ∧
            ∃ normalizedReductionCertificate :
              ComplexityReduction.KarpReductionM ComplexityReduction.CostedPolyTimeModel normalizedProblem normalizedRouteTarget,
              ∃ liftedReductionCertificate :
                ComplexityReduction.PolyReducibleM ComplexityReduction.CostedPolyTimeModel sampleProblem normalizedRouteTarget,
                ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel normalizedRouteTarget ∧
                  ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel sampleProblem

#check sampleProblem
#check sampleNormalizedProblem
#check sampleEncodingBridgeClaim
#check sampleNormalizedRouteTarget
#check sampleNormalizedReductionClaim
#check sampleLiftedReductionClaim
#check sampleNormalizedRouteTargetMembershipClaim
#check sampleClaim

end

end BenchmarkHiddenSample
