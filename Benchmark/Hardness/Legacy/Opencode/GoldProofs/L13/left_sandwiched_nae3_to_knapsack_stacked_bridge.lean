import ComplexityReduction

noncomputable section

abbrev sourceProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.CSP.Examples.notAllEqual3DecisionProblem

abbrev targetProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.knapsackKarpDecisionProblem

abbrev problem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.EncodedType.prod
      (ComplexityReduction.EncodedType.prod
        ComplexityReduction.EncodedType.bool
        (ComplexityReduction.EncodedType.prod
          sourceProblem.Instance
          ComplexityReduction.EncodedType.bool))
      ComplexityReduction.EncodedType.bool
    isYes := fun p => sourceProblem.isYes p.1.2.1 }

namespace BenchmarkGoldProof

open ComplexityReduction

abbrev bridgeProblem : EncodedDecisionProblem :=
  { Instance := EncodedType.prod sourceProblem.Instance EncodedType.bool
    isYes := fun p => sourceProblem.isYes p.1 }

abbrev normalizedProblem : EncodedDecisionProblem :=
  sourceProblem

abbrev routeTarget2 : EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.zeroOneIntegerProgrammingDecisionProblem

def outerProjection :
    PolyTimeMap CostedPolyTimeModel problem.Instance bridgeProblem.Instance :=
  PolyTimeMap.comp
    (PolyTimeMap.snd CostedPolyTimeModel EncodedType.bool bridgeProblem.Instance)
    (PolyTimeMap.fst
      CostedPolyTimeModel
      (EncodedType.prod EncodedType.bool bridgeProblem.Instance)
      EncodedType.bool)

def bridgeWithLeftFlag :
    PolyTimeMap
      CostedPolyTimeModel
      bridgeProblem.Instance
      (EncodedType.prod EncodedType.bool bridgeProblem.Instance) :=
  PolyTimeMap.prod_mk
    (PolyTimeMap.const CostedPolyTimeModel bridgeProblem.Instance EncodedType.bool false)
    (PolyTimeMap.id CostedPolyTimeModel bridgeProblem.Instance)

def outerInjection :
    PolyTimeMap CostedPolyTimeModel bridgeProblem.Instance problem.Instance :=
  PolyTimeMap.prod_mk
    bridgeWithLeftFlag
    (PolyTimeMap.const CostedPolyTimeModel bridgeProblem.Instance EncodedType.bool true)

def outerBridge :
    ProblemEquivM CostedPolyTimeModel problem bridgeProblem where
  toMap := outerProjection
  invMap := outerInjection
  to_correct := fun _ => Iff.rfl
  inv_correct := fun _ => Iff.rfl

def innerBridge :
    ProblemEquivM CostedPolyTimeModel bridgeProblem normalizedProblem where
  toMap := PolyTimeMap.fst CostedPolyTimeModel sourceProblem.Instance EncodedType.bool
  invMap :=
    PolyTimeMap.prod_mk
      (PolyTimeMap.id CostedPolyTimeModel sourceProblem.Instance)
      (PolyTimeMap.const CostedPolyTimeModel sourceProblem.Instance EncodedType.bool false)
  to_correct := fun _ => Iff.rfl
  inv_correct := fun _ => Iff.rfl

def stackedBridge :
    ProblemEquivM CostedPolyTimeModel problem normalizedProblem :=
  ProblemEquivM.trans outerBridge innerBridge

def sourceToSatGadget :
    KarpReductionM CostedPolyTimeModel normalizedProblem SAT.threeSATDecisionProblem := by
  simpa [normalizedProblem] using
    ComplexityReduction.CSP.Examples.notAllEqual3ToThreeSATKarpReduction

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
  ProblemEquivM.transportSource stackedBridge normalizedRoute

def targetInNP :
    InNPEnc CostedPolyTimeModel targetProblem := by
  simpa [targetProblem] using ComplexityReduction.Karp21.Knapsack.knapsackInNP

def sourceInNP :
    InNPEnc CostedPolyTimeModel problem :=
  InNPEnc.of_reduction composedReduction targetInNP

theorem goldCertificate :
    ∃ bridgeProblem : EncodedDecisionProblem,
      ∃ normalizedProblem : EncodedDecisionProblem,
        ∃ routeTarget2 : EncodedDecisionProblem,
          ∃ _outerBridgeCertificate :
            ProblemEquivM CostedPolyTimeModel problem bridgeProblem,
            ∃ _innerBridgeCertificate :
              ProblemEquivM CostedPolyTimeModel bridgeProblem normalizedProblem,
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
    ⟨ bridgeProblem
    , normalizedProblem
    , routeTarget2
    , outerBridge
    , innerBridge
    , sourceToSatGadget
    , satToIntermediateRoute
    , intermediateToFinalRoute
    , ?_ ⟩
  exact ⟨composedReduction, targetInNP, sourceInNP⟩

end BenchmarkGoldProof
