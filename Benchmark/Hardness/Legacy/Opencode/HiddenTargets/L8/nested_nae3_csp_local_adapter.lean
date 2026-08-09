import ComplexityReduction.CSP.Examples.NAE3SAT

namespace BenchmarkHiddenSample

noncomputable section

abbrev sampleLocalAdapterTarget : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.CSP.Examples.notAllEqual3DecisionProblem

abbrev sampleProblem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.EncodedType.prod
      (ComplexityReduction.EncodedType.prod
        ComplexityReduction.EncodedType.bool
        sampleLocalAdapterTarget.Instance)
      ComplexityReduction.EncodedType.bool
    isYes := fun p => sampleLocalAdapterTarget.isYes p.1.2 }

abbrev sampleLocalAdapterClaim : Prop :=
  ∀ x : sampleProblem.Instance.Carrier,
    sampleProblem.isYes x ↔ sampleLocalAdapterTarget.isYes x.1.2

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
