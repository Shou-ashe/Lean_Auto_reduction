import ComplexityReduction.Karp21

namespace BenchmarkHiddenSample

noncomputable section

abbrev sampleProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.knapsackKarpDecisionProblem

abbrev sampleRouteTarget : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.partitionDecisionProblem

abbrev sampleReductionClaim : Type :=
  ComplexityReduction.KarpReductionM
    ComplexityReduction.CostedPolyTimeModel
    sampleProblem
    sampleRouteTarget

abbrev sampleRouteMembershipClaim : Prop :=
  ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel sampleRouteTarget

abbrev sampleClaim : Prop :=
  ∃ routeTarget : ComplexityReduction.EncodedDecisionProblem,
    routeTarget = sampleRouteTarget ∧
      ∃ reductionCertificate :
        ComplexityReduction.KarpReductionM ComplexityReduction.CostedPolyTimeModel sampleProblem routeTarget,
        ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel routeTarget ∧
          ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel sampleProblem

#check sampleProblem
#check sampleRouteTarget
#check sampleReductionClaim
#check sampleRouteMembershipClaim
#check sampleClaim

end

end BenchmarkHiddenSample
