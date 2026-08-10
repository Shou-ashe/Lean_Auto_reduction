import ComplexityReduction

noncomputable section

abbrev sourceProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.CSP.Examples.dualHorn3DecisionProblem

abbrev graphTargetProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.cliqueCoverDecisionProblem

abbrev numericTargetProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.knapsackKarpDecisionProblem

abbrev problem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.EncodedType.prod
      ComplexityReduction.EncodedType.bool
      (ComplexityReduction.EncodedType.prod
        sourceProblem.Instance
        ComplexityReduction.EncodedType.bool)
    isYes := fun p => sourceProblem.isYes p.2.1 }

namespace BenchmarkGoldProof

open ComplexityReduction

abbrev normalizedProblem : EncodedDecisionProblem :=
  sourceProblem

abbrev graphRouteTarget : EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.chromaticNumberDecisionProblem

abbrev numericRouteTarget : EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.zeroOneIntegerProgrammingDecisionProblem

def sourceProjection :
    PolyTimeMap CostedPolyTimeModel problem.Instance sourceProblem.Instance :=
  PolyTimeMap.comp
    (PolyTimeMap.fst CostedPolyTimeModel sourceProblem.Instance EncodedType.bool)
    (PolyTimeMap.snd
      CostedPolyTimeModel
      EncodedType.bool
      (EncodedType.prod sourceProblem.Instance EncodedType.bool))

def sourceWithRightFlag :
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
      true)

def sourceInjection :
    PolyTimeMap CostedPolyTimeModel sourceProblem.Instance problem.Instance :=
  PolyTimeMap.prod_mk
    (PolyTimeMap.const
      CostedPolyTimeModel
      sourceProblem.Instance
      EncodedType.bool
      false)
    sourceWithRightFlag

def encodingBridgeCertificate :
    ProblemEquivM CostedPolyTimeModel problem normalizedProblem where
  toMap := sourceProjection
  invMap := sourceInjection
  to_correct := fun _ => Iff.rfl
  inv_correct := fun _ => Iff.rfl

def sourceToSatGadget :
    KarpReductionM CostedPolyTimeModel normalizedProblem SAT.threeSATDecisionProblem := by
  simpa [normalizedProblem] using
    ComplexityReduction.CSP.Examples.dualHorn3ToThreeSATKarpReduction

def satToGraphRoute :
    KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem graphRouteTarget := by
  simpa [graphRouteTarget] using
    ComplexityReduction.Karp21.ChromaticNumber.threeSATToChromaticNumber_textbookKarpReduction

def graphToFinalRoute :
    KarpReductionM CostedPolyTimeModel graphRouteTarget graphTargetProblem := by
  simpa [graphRouteTarget, graphTargetProblem] using
    ComplexityReduction.Karp21.CliqueCover.chromaticNumberToCliqueCover_textbookKarpReduction

def satToNumericRoute :
    KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem numericRouteTarget := by
  simpa [numericRouteTarget] using
    ComplexityReduction.Karp21.ZeroOneIP.threeSATToZeroOneIP_textbookKarpReduction

def numericToFinalRoute :
    KarpReductionM CostedPolyTimeModel numericRouteTarget numericTargetProblem := by
  simpa [numericRouteTarget, numericTargetProblem] using
    ComplexityReduction.Karp21.Knapsack.zeroOneIPToKnapsack_textbookKarpReduction

def graphNormalizedRoute :
    PolyReducibleM CostedPolyTimeModel normalizedProblem graphTargetProblem :=
  PolyReducibleM.trans
    (PolyReducibleM.trans
      (⟨sourceToSatGadget⟩ :
        PolyReducibleM CostedPolyTimeModel normalizedProblem SAT.threeSATDecisionProblem)
      (⟨satToGraphRoute⟩ :
        PolyReducibleM CostedPolyTimeModel SAT.threeSATDecisionProblem graphRouteTarget))
    (⟨graphToFinalRoute⟩ :
      PolyReducibleM CostedPolyTimeModel graphRouteTarget graphTargetProblem)

def numericNormalizedRoute :
    PolyReducibleM CostedPolyTimeModel normalizedProblem numericTargetProblem :=
  PolyReducibleM.trans
    (PolyReducibleM.trans
      (⟨sourceToSatGadget⟩ :
        PolyReducibleM CostedPolyTimeModel normalizedProblem SAT.threeSATDecisionProblem)
      (⟨satToNumericRoute⟩ :
        PolyReducibleM CostedPolyTimeModel SAT.threeSATDecisionProblem numericRouteTarget))
    (⟨numericToFinalRoute⟩ :
      PolyReducibleM CostedPolyTimeModel numericRouteTarget numericTargetProblem)

def graphReduction :
    PolyReducibleM CostedPolyTimeModel problem graphTargetProblem :=
  ProblemEquivM.transportSource encodingBridgeCertificate graphNormalizedRoute

def numericReduction :
    PolyReducibleM CostedPolyTimeModel problem numericTargetProblem :=
  ProblemEquivM.transportSource encodingBridgeCertificate numericNormalizedRoute

def graphTargetInNP :
    InNPEnc CostedPolyTimeModel graphTargetProblem := by
  simpa [graphTargetProblem] using ComplexityReduction.Karp21.CliqueCover.cliqueCoverInNP

def numericTargetInNP :
    InNPEnc CostedPolyTimeModel numericTargetProblem := by
  simpa [numericTargetProblem] using ComplexityReduction.Karp21.Knapsack.knapsackInNP

def sourceInNP :
    InNPEnc CostedPolyTimeModel problem :=
  InNPEnc.of_reduction graphReduction graphTargetInNP

theorem goldCertificate :
    ∃ normalizedProblem : EncodedDecisionProblem,
      ∃ graphRouteTarget : EncodedDecisionProblem,
        ∃ numericRouteTarget : EncodedDecisionProblem,
          ∃ _encodingBridgeCertificate :
            ProblemEquivM CostedPolyTimeModel problem normalizedProblem,
            ∃ _sourceToSatGadget :
              KarpReductionM CostedPolyTimeModel normalizedProblem SAT.threeSATDecisionProblem,
              ∃ _satToGraphRoute :
                KarpReductionM CostedPolyTimeModel
                  SAT.threeSATDecisionProblem
                  graphRouteTarget,
                ∃ _graphToFinalRoute :
                  KarpReductionM CostedPolyTimeModel graphRouteTarget graphTargetProblem,
                  ∃ _satToNumericRoute :
                    KarpReductionM CostedPolyTimeModel
                      SAT.threeSATDecisionProblem
                      numericRouteTarget,
                    ∃ _numericToFinalRoute :
                      KarpReductionM CostedPolyTimeModel
                        numericRouteTarget
                        numericTargetProblem,
                      PolyReducibleM CostedPolyTimeModel problem graphTargetProblem ∧
                      PolyReducibleM CostedPolyTimeModel problem numericTargetProblem ∧
                      InNPEnc CostedPolyTimeModel graphTargetProblem ∧
                      InNPEnc CostedPolyTimeModel numericTargetProblem ∧
                      InNPEnc CostedPolyTimeModel problem := by
  refine
    ⟨ normalizedProblem
    , graphRouteTarget
    , numericRouteTarget
    , encodingBridgeCertificate
    , sourceToSatGadget
    , satToGraphRoute
    , graphToFinalRoute
    , satToNumericRoute
    , numericToFinalRoute
    , ?_ ⟩
  exact ⟨graphReduction, numericReduction, graphTargetInNP, numericTargetInNP, sourceInNP⟩

end BenchmarkGoldProof
