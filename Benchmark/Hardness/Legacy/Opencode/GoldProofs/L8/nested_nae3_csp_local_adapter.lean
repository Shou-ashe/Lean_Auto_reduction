import ComplexityReduction

noncomputable section

abbrev localAdapterTarget : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.CSP.Examples.notAllEqual3DecisionProblem

abbrev problem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.EncodedType.prod
      (ComplexityReduction.EncodedType.prod
        ComplexityReduction.EncodedType.bool
        localAdapterTarget.Instance)
      ComplexityReduction.EncodedType.bool
    isYes := fun p => localAdapterTarget.isYes p.1.2 }

namespace BenchmarkGoldProof

def localAdapterProof :
    ∀ x : problem.Instance.Carrier, problem.isYes x ↔ localAdapterTarget.isYes x.1.2 := by
  intro x
  exact Iff.rfl

def outerFst :
    ComplexityReduction.PolyTimeMap
      ComplexityReduction.CostedPolyTimeModel
      problem.Instance
      (ComplexityReduction.EncodedType.prod
        ComplexityReduction.EncodedType.bool
        localAdapterTarget.Instance) :=
  ComplexityReduction.PolyTimeMap.fst
    ComplexityReduction.CostedPolyTimeModel
    (ComplexityReduction.EncodedType.prod
      ComplexityReduction.EncodedType.bool
      localAdapterTarget.Instance)
    ComplexityReduction.EncodedType.bool

def innerSnd :
    ComplexityReduction.PolyTimeMap
      ComplexityReduction.CostedPolyTimeModel
      (ComplexityReduction.EncodedType.prod
        ComplexityReduction.EncodedType.bool
        localAdapterTarget.Instance)
      localAdapterTarget.Instance :=
  ComplexityReduction.PolyTimeMap.snd
    ComplexityReduction.CostedPolyTimeModel
    ComplexityReduction.EncodedType.bool
    localAdapterTarget.Instance

def localAdapterMap :
    ComplexityReduction.PolyTimeMap
      ComplexityReduction.CostedPolyTimeModel
      problem.Instance
      localAdapterTarget.Instance :=
  ComplexityReduction.PolyTimeMap.comp innerSnd outerFst

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
  ComplexityReduction.CSP.Hardness.NAE3SAT.nae3NPComplete.1

def sourceInNP :
    ComplexityReduction.InNPEnc
      ComplexityReduction.CostedPolyTimeModel
      problem :=
  ComplexityReduction.InNPEnc.of_reduction localAdapterRoute localAdapterTargetInNP

theorem goldCertificate :
    (∀ x : problem.Instance.Carrier,
        problem.isYes x ↔ localAdapterTarget.isYes x.1.2) ∧
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
