import ComplexityReduction.Karp21

namespace BenchmarkHiddenSample

noncomputable section

abbrev sampleProblem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.Combinatorics.Graph.vertexCoverEncodedType
    isYes := fun I => False ∨ ComplexityReduction.Combinatorics.Graph.VertexCover I }

abbrev sampleReferenceProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.vertexCoverDecisionProblem

abbrev sampleInterfaceEquivalenceClaim : Type :=
  ComplexityReduction.ProblemEquivM
    ComplexityReduction.CostedPolyTimeModel
    sampleProblem
    sampleReferenceProblem

abbrev sampleInterfaceReductionClaim : Type :=
  ComplexityReduction.KarpReductionM
    ComplexityReduction.CostedPolyTimeModel
    sampleProblem
    sampleReferenceProblem

abbrev sampleReferenceMembershipClaim : Prop :=
  ComplexityReduction.InNPEnc
    ComplexityReduction.CostedPolyTimeModel
    sampleReferenceProblem

abbrev sampleClaim : Prop :=
  ∃ e : ComplexityReduction.ProblemEquivM
      ComplexityReduction.CostedPolyTimeModel sampleProblem sampleReferenceProblem,
    ∃ h : ComplexityReduction.PolyReducibleM
        ComplexityReduction.CostedPolyTimeModel sampleProblem sampleReferenceProblem,
      h = ComplexityReduction.ProblemEquivM.toReducible e ∧
        sampleReferenceMembershipClaim ∧
          ComplexityReduction.InNPEnc
            ComplexityReduction.CostedPolyTimeModel sampleProblem

#check sampleProblem
#check sampleReferenceProblem
#check sampleInterfaceEquivalenceClaim
#check sampleInterfaceReductionClaim
#check sampleReferenceMembershipClaim
#check sampleClaim

end

end BenchmarkHiddenSample
