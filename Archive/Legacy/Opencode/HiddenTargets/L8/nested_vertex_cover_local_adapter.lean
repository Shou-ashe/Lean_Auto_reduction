import ComplexityReduction.Karp21

namespace BenchmarkHiddenSample

noncomputable section

abbrev sampleLocalAdapterTarget : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.vertexCoverDecisionProblem

abbrev sampleProblem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.EncodedType.prod
      (ComplexityReduction.EncodedType.prod
        sampleLocalAdapterTarget.Instance
        ComplexityReduction.EncodedType.bool)
      ComplexityReduction.EncodedType.bool
    isYes := fun p => sampleLocalAdapterTarget.isYes p.1.1 }

abbrev sampleLocalAdapterClaim : Prop :=
  ∀ x : sampleProblem.Instance.Carrier,
    sampleProblem.isYes x ↔ sampleLocalAdapterTarget.isYes x.1.1

abbrev sampleLocalAdapterReductionClaim : Type :=
  ComplexityReduction.KarpReductionM
    ComplexityReduction.CostedPolyTimeModel
    sampleProblem
    sampleLocalAdapterTarget

abbrev sampleLocalAdapterRouteClaim : Prop :=
  ComplexityReduction.PolyReducibleM
    ComplexityReduction.CostedPolyTimeModel
    sampleProblem
    sampleLocalAdapterTarget

abbrev sampleLocalAdapterTargetMembershipClaim : Prop :=
  ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel sampleLocalAdapterTarget

abbrev sampleClaim : Prop :=
  ComplexityReduction.InNPEnc ComplexityReduction.CostedPolyTimeModel sampleProblem

#check sampleProblem
#check sampleLocalAdapterTarget
#check sampleLocalAdapterClaim
#check sampleLocalAdapterReductionClaim
#check sampleLocalAdapterRouteClaim
#check sampleLocalAdapterTargetMembershipClaim
#check sampleClaim

end

end BenchmarkHiddenSample
