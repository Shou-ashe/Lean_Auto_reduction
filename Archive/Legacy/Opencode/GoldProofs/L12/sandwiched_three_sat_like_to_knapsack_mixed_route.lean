import ComplexityReduction

noncomputable section

abbrev sourceProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.CSP.Examples.threeSATLikeDecisionProblem

abbrev targetProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.knapsackKarpDecisionProblem

abbrev problem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.EncodedType.prod
      (ComplexityReduction.EncodedType.prod
        ComplexityReduction.EncodedType.bool
        sourceProblem.Instance)
      (ComplexityReduction.EncodedType.prod
        ComplexityReduction.EncodedType.bool
        ComplexityReduction.EncodedType.bool)
    isYes := fun p => sourceProblem.isYes p.1.2 }

namespace BenchmarkGoldProof

open ComplexityReduction

abbrev normalizedProblem : EncodedDecisionProblem :=
  sourceProblem

abbrev routeTarget2 : EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.zeroOneIntegerProgrammingDecisionProblem

def sourceProjection :
    PolyTimeMap CostedPolyTimeModel problem.Instance sourceProblem.Instance :=
  PolyTimeMap.comp
    (PolyTimeMap.snd CostedPolyTimeModel EncodedType.bool sourceProblem.Instance)
    (PolyTimeMap.fst
      CostedPolyTimeModel
      (EncodedType.prod EncodedType.bool sourceProblem.Instance)
      (EncodedType.prod EncodedType.bool EncodedType.bool))

def sourceWithLeftFlag :
    PolyTimeMap
      CostedPolyTimeModel
      sourceProblem.Instance
      (EncodedType.prod EncodedType.bool sourceProblem.Instance) :=
  PolyTimeMap.prod_mk
    (PolyTimeMap.const
      CostedPolyTimeModel
      sourceProblem.Instance
      EncodedType.bool
      false)
    (PolyTimeMap.id CostedPolyTimeModel sourceProblem.Instance)

def rightFlags :
    PolyTimeMap
      CostedPolyTimeModel
      sourceProblem.Instance
      (EncodedType.prod EncodedType.bool EncodedType.bool) :=
  PolyTimeMap.prod_mk
    (PolyTimeMap.const
      CostedPolyTimeModel
      sourceProblem.Instance
      EncodedType.bool
      true)
    (PolyTimeMap.const
      CostedPolyTimeModel
      sourceProblem.Instance
      EncodedType.bool
      false)

def sourceInjection :
    PolyTimeMap CostedPolyTimeModel sourceProblem.Instance problem.Instance :=
  PolyTimeMap.prod_mk sourceWithLeftFlag rightFlags

def encodingBridgeCertificate :
    ProblemEquivM CostedPolyTimeModel problem normalizedProblem where
  toMap := sourceProjection
  invMap := sourceInjection
  to_correct := fun _ => Iff.rfl
  inv_correct := fun _ => Iff.rfl

def sourceToSatGadget :
    KarpReductionM CostedPolyTimeModel normalizedProblem SAT.threeSATDecisionProblem := by
  simpa [normalizedProblem] using
    ComplexityReduction.CSP.Examples.threeSATLikeToThreeSATKarpReduction

def satToIntermediateRoute :
    KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem routeTarget2 := by
  simpa [routeTarget2] using
    ComplexityReduction.Karp21.ZeroOneIP.threeSATToZeroOneIP_textbookKarpReduction

def intermediateToFinalRoute :
    KarpReductionM CostedPolyTimeModel routeTarget2 targetProblem := by
  simpa [routeTarget2, targetProblem] using
    ComplexityReduction.Karp21.Knapsack.zeroOneIPToKnapsack_textbookKarpReduction

def normalizedRoute :
    PolyReducibleM CostedPolyTimeModel normalizedProblem targetProblem :=
  PolyReducibleM.trans
    (PolyReducibleM.trans
      (⟨sourceToSatGadget⟩ :
        PolyReducibleM CostedPolyTimeModel normalizedProblem SAT.threeSATDecisionProblem)
      (⟨satToIntermediateRoute⟩ :
        PolyReducibleM CostedPolyTimeModel SAT.threeSATDecisionProblem routeTarget2))
    (⟨intermediateToFinalRoute⟩ :
      PolyReducibleM CostedPolyTimeModel routeTarget2 targetProblem)

def composedReduction :
    PolyReducibleM CostedPolyTimeModel problem targetProblem :=
  ProblemEquivM.transportSource encodingBridgeCertificate normalizedRoute

def targetInNP :
    InNPEnc CostedPolyTimeModel targetProblem := by
  simpa [targetProblem] using ComplexityReduction.Karp21.Knapsack.knapsackInNP

def sourceInNP :
    InNPEnc CostedPolyTimeModel problem :=
  InNPEnc.of_reduction composedReduction targetInNP

theorem goldCertificate :
    ∃ normalizedProblem : EncodedDecisionProblem,
      ∃ routeTarget2 : EncodedDecisionProblem,
        ∃ _encodingBridgeCertificate :
          ProblemEquivM CostedPolyTimeModel problem normalizedProblem,
          ∃ _sourceToSatGadget :
            KarpReductionM CostedPolyTimeModel normalizedProblem SAT.threeSATDecisionProblem,
            ∃ _satToIntermediateRoute :
              KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem routeTarget2,
              ∃ _intermediateToFinalRoute :
                KarpReductionM CostedPolyTimeModel routeTarget2 targetProblem,
                PolyReducibleM CostedPolyTimeModel problem targetProblem ∧
                InNPEnc CostedPolyTimeModel targetProblem ∧
                InNPEnc CostedPolyTimeModel problem := by
  refine
    ⟨ normalizedProblem
    , routeTarget2
    , encodingBridgeCertificate
    , sourceToSatGadget
    , satToIntermediateRoute
    , intermediateToFinalRoute
    , ?_ ⟩
  exact ⟨composedReduction, targetInNP, sourceInNP⟩

end BenchmarkGoldProof
