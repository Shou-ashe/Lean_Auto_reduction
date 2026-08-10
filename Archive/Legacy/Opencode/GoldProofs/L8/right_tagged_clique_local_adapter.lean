import ComplexityReduction

noncomputable section

abbrev localAdapterTarget : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.cliqueDecisionProblem

abbrev problem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.EncodedType.prod
      ComplexityReduction.EncodedType.bool
      localAdapterTarget.Instance
    isYes := fun p => localAdapterTarget.isYes p.2 }

namespace BenchmarkGoldProof

def localAdapterProof :
    ∀ x : problem.Instance.Carrier, problem.isYes x ↔ localAdapterTarget.isYes x.2 := by
  intro x
  exact Iff.rfl

def localAdapterMap :
    ComplexityReduction.PolyTimeMap
      ComplexityReduction.CostedPolyTimeModel
      problem.Instance
      localAdapterTarget.Instance :=
  ComplexityReduction.PolyTimeMap.snd
    ComplexityReduction.CostedPolyTimeModel
    ComplexityReduction.EncodedType.bool
    localAdapterTarget.Instance

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
  ComplexityReduction.Karp21.Clique.cliqueInNP

def sourceInNP :
    ComplexityReduction.InNPEnc
      ComplexityReduction.CostedPolyTimeModel
      problem :=
  ComplexityReduction.InNPEnc.of_reduction localAdapterRoute localAdapterTargetInNP

theorem goldCertificate :
    (∀ x : problem.Instance.Carrier,
        problem.isYes x ↔ localAdapterTarget.isYes x.2) ∧
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
