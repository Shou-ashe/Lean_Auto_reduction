import ComplexityReduction.Karp21

namespace BenchmarkHiddenSample

noncomputable section

abbrev sampleProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.setCoveringDecisionProblem

abbrev sampleRouteTarget1 : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.exactCoverDecisionProblem

abbrev sampleRouteTarget2 : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.steinerTreeDecisionProblem

abbrev sampleReductionStep1Claim : Type :=
  ComplexityReduction.KarpReductionM
    ComplexityReduction.CostedPolyTimeModel
    sampleProblem
    sampleRouteTarget1

abbrev sampleReductionStep2Claim : Type :=
  ComplexityReduction.KarpReductionM
    ComplexityReduction.CostedPolyTimeModel
    sampleRouteTarget1
    sampleRouteTarget2

abbrev sampleComposedReductionClaim : Prop :=
  ComplexityReduction.PolyReducibleM
    ComplexityReduction.CostedPolyTimeModel
    sampleProblem
    sampleRouteTarget2

abbrev sampleRouteTarget2MembershipClaim : Prop :=
  ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel sampleRouteTarget2

abbrev sampleClaim : Prop :=
  ∃ routeTarget1 : ComplexityReduction.EncodedDecisionProblem,
    routeTarget1 = sampleRouteTarget1 ∧
      ∃ routeTarget2 : ComplexityReduction.EncodedDecisionProblem,
        routeTarget2 = sampleRouteTarget2 ∧
          ∃ reductionStep1 :
            ComplexityReduction.KarpReductionM ComplexityReduction.CostedPolyTimeModel sampleProblem routeTarget1,
            ∃ reductionStep2 :
              ComplexityReduction.KarpReductionM ComplexityReduction.CostedPolyTimeModel routeTarget1 routeTarget2,
              ∃ composedReduction :
                ComplexityReduction.PolyReducibleM ComplexityReduction.CostedPolyTimeModel sampleProblem routeTarget2,
                ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel routeTarget2 ∧
                  ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel sampleProblem

#check sampleProblem
#check sampleRouteTarget1
#check sampleRouteTarget2
#check sampleReductionStep1Claim
#check sampleReductionStep2Claim
#check sampleComposedReductionClaim
#check sampleRouteTarget2MembershipClaim
#check sampleClaim

end

end BenchmarkHiddenSample
