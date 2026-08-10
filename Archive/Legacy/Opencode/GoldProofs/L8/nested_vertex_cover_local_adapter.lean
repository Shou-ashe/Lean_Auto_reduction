import ComplexityReduction

noncomputable section

abbrev localAdapterTarget : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.vertexCoverDecisionProblem

abbrev problem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.EncodedType.prod
      (ComplexityReduction.EncodedType.prod
        localAdapterTarget.Instance
        ComplexityReduction.EncodedType.bool)
      ComplexityReduction.EncodedType.bool
    isYes := fun p => localAdapterTarget.isYes p.1.1 }

namespace BenchmarkGoldProof

def localAdapterProof :
    ∀ x : problem.Instance.Carrier, problem.isYes x ↔ localAdapterTarget.isYes x.1.1 := by
  intro x
  exact Iff.rfl

def outerFst :
    ComplexityReduction.PolyTimeMap
      ComplexityReduction.CostedPolyTimeModel
      problem.Instance
      (ComplexityReduction.EncodedType.prod
        localAdapterTarget.Instance
        ComplexityReduction.EncodedType.bool) :=
  ComplexityReduction.PolyTimeMap.fst
    ComplexityReduction.CostedPolyTimeModel
    (ComplexityReduction.EncodedType.prod
      localAdapterTarget.Instance
      ComplexityReduction.EncodedType.bool)
    ComplexityReduction.EncodedType.bool

def innerFst :
    ComplexityReduction.PolyTimeMap
      ComplexityReduction.CostedPolyTimeModel
      (ComplexityReduction.EncodedType.prod
        localAdapterTarget.Instance
        ComplexityReduction.EncodedType.bool)
      localAdapterTarget.Instance :=
  ComplexityReduction.PolyTimeMap.fst
    ComplexityReduction.CostedPolyTimeModel
    localAdapterTarget.Instance
    ComplexityReduction.EncodedType.bool

def localAdapterMap :
    ComplexityReduction.PolyTimeMap
      ComplexityReduction.CostedPolyTimeModel
      problem.Instance
      localAdapterTarget.Instance :=
  ComplexityReduction.PolyTimeMap.comp innerFst outerFst

def localAdapterReduction :
    ComplexityReduction.KarpReductionM
      ComplexityReduction.CostedPolyTimeModel
      problem
      localAdapterTarget where
  f := localAdapterMap
  correct := localAdapterProof

def localAdapterRoute :
    ComplexityReduction.PolyReducibleM
      ComplexityReduction.CostedPolyTimeModel
      problem
      localAdapterTarget :=
  ⟨localAdapterReduction⟩

def localAdapterTargetInNP :
    ComplexityReduction.InNPEnc
      ComplexityReduction.CostedPolyTimeModel
      localAdapterTarget :=
  ComplexityReduction.Karp21.VertexCover.vertexCoverInNP

def sourceInNP :
    ComplexityReduction.InNPEnc
      ComplexityReduction.CostedPolyTimeModel
      problem :=
  ComplexityReduction.InNPEnc.of_reduction localAdapterRoute localAdapterTargetInNP

theorem goldCertificate :
    (∀ x : problem.Instance.Carrier,
        problem.isYes x ↔ localAdapterTarget.isYes x.1.1) ∧
      ∃ _localAdapterReduction :
        ComplexityReduction.KarpReductionM
          ComplexityReduction.CostedPolyTimeModel
          problem
          localAdapterTarget,
        ComplexityReduction.PolyReducibleM
          ComplexityReduction.CostedPolyTimeModel
          problem
          localAdapterTarget ∧
        ComplexityReduction.InNPEnc
          ComplexityReduction.CostedPolyTimeModel
          localAdapterTarget ∧
        ComplexityReduction.InNPEnc
          ComplexityReduction.CostedPolyTimeModel
          problem := by
  refine ⟨localAdapterProof, ?_⟩
  exact ⟨localAdapterReduction, localAdapterRoute, localAdapterTargetInNP, sourceInNP⟩

end BenchmarkGoldProof
