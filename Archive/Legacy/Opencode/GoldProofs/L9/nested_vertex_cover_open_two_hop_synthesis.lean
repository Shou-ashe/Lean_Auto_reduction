import ComplexityReduction

noncomputable section

abbrev sourceProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.vertexCoverDecisionProblem

abbrev problem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.EncodedType.prod
      (ComplexityReduction.EncodedType.prod
        sourceProblem.Instance
        ComplexityReduction.EncodedType.bool)
      ComplexityReduction.EncodedType.bool
    isYes := fun p => sourceProblem.isYes p.1.1 }

namespace BenchmarkGoldProof

open ComplexityReduction

abbrev normalizedProblem : EncodedDecisionProblem :=
  sourceProblem

abbrev routeTarget1 : EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.setCoveringDecisionProblem

abbrev routeTarget2 : EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.hittingSetDecisionProblem

def sourceProjection :
    PolyTimeMap CostedPolyTimeModel problem.Instance sourceProblem.Instance :=
  PolyTimeMap.comp
    (PolyTimeMap.fst
      CostedPolyTimeModel
      sourceProblem.Instance
      EncodedType.bool)
    (PolyTimeMap.fst
      CostedPolyTimeModel
      (EncodedType.prod sourceProblem.Instance EncodedType.bool)
      EncodedType.bool)

def sourceWithInnerFlag :
    PolyTimeMap
      CostedPolyTimeModel
      sourceProblem.Instance
      (EncodedType.prod sourceProblem.Instance EncodedType.bool) :=
  PolyTimeMap.prod_mk
    (PolyTimeMap.id CostedPolyTimeModel sourceProblem.Instance)
    (PolyTimeMap.const
      CostedPolyTimeModel
      sourceProblem.Instance
      EncodedType.bool
      false)

def sourceInjection :
    PolyTimeMap CostedPolyTimeModel sourceProblem.Instance problem.Instance :=
  PolyTimeMap.prod_mk
    sourceWithInnerFlag
    (PolyTimeMap.const
      CostedPolyTimeModel
      sourceProblem.Instance
      EncodedType.bool
      true)

def encodingBridgeCertificate :
    ProblemEquivM CostedPolyTimeModel problem normalizedProblem where
  toMap := sourceProjection
  invMap := sourceInjection
  to_correct := fun _ => Iff.rfl
  inv_correct := fun _ => Iff.rfl

def reductionStep1 :
    KarpReductionM CostedPolyTimeModel normalizedProblem routeTarget1 := by
  simpa [normalizedProblem, routeTarget1] using
    ComplexityReduction.Karp21.SetCovering.vertexCoverToSetCoveringKarpReduction

def reductionStep2 :
    KarpReductionM CostedPolyTimeModel routeTarget1 routeTarget2 := by
  simpa [routeTarget1, routeTarget2] using
    ComplexityReduction.Karp21.HittingSet.setCoveringToHittingSetKarpReduction

def normalizedRoute :
    PolyReducibleM CostedPolyTimeModel normalizedProblem routeTarget2 :=
  PolyReducibleM.trans ⟨reductionStep1⟩ ⟨reductionStep2⟩

def composedReduction :
    PolyReducibleM CostedPolyTimeModel problem routeTarget2 :=
  ProblemEquivM.transportSource encodingBridgeCertificate normalizedRoute

def routeTarget2InNP :
    InNPEnc CostedPolyTimeModel routeTarget2 := by
  simpa [routeTarget2] using ComplexityReduction.Karp21.HittingSet.hittingSetInNP

def sourceInNP :
    InNPEnc CostedPolyTimeModel problem :=
  InNPEnc.of_reduction composedReduction routeTarget2InNP

theorem goldCertificate :
    ∃ normalizedProblem : EncodedDecisionProblem,
      ∃ routeTarget1 : EncodedDecisionProblem,
        ∃ routeTarget2 : EncodedDecisionProblem,
          ∃ _encodingBridgeCertificate :
            ProblemEquivM CostedPolyTimeModel problem normalizedProblem,
            ∃ _reductionStep1 :
              KarpReductionM CostedPolyTimeModel normalizedProblem routeTarget1,
              ∃ _reductionStep2 :
                KarpReductionM CostedPolyTimeModel routeTarget1 routeTarget2,
                PolyReducibleM CostedPolyTimeModel problem routeTarget2 ∧
                InNPEnc CostedPolyTimeModel routeTarget2 ∧
                InNPEnc CostedPolyTimeModel problem := by
  refine
    ⟨ normalizedProblem
    , routeTarget1
    , routeTarget2
    , encodingBridgeCertificate
    , reductionStep1
    , reductionStep2
    , ?_ ⟩
  exact ⟨composedReduction, routeTarget2InNP, sourceInNP⟩

end BenchmarkGoldProof
