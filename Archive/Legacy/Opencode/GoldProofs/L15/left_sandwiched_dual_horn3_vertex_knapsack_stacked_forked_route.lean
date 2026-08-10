import ComplexityReduction

noncomputable section

abbrev sourceProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.CSP.Examples.dualHorn3DecisionProblem

abbrev graphTargetProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.vertexCoverDecisionProblem

abbrev numericTargetProblem : ComplexityReduction.EncodedDecisionProblem :=
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

abbrev graphRouteTarget : EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.cliqueDecisionProblem

abbrev numericRouteTarget : EncodedDecisionProblem :=
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
    ComplexityReduction.CSP.Examples.dualHorn3ToThreeSATKarpReduction

def satToGraphRoute :
    KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem graphRouteTarget := by
  simpa [graphRouteTarget] using
    ComplexityReduction.Karp21.Clique.threeSATToClique_textbookKarpReduction

def graphToFinalRoute :
    KarpReductionM CostedPolyTimeModel graphRouteTarget graphTargetProblem := by
  simpa [graphRouteTarget, graphTargetProblem] using
    ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverKarpReduction

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
  ProblemEquivM.transportSource stackedBridge graphNormalizedRoute

def numericReduction :
    PolyReducibleM CostedPolyTimeModel problem numericTargetProblem :=
  ProblemEquivM.transportSource stackedBridge numericNormalizedRoute

def graphTargetInNP :
    InNPEnc CostedPolyTimeModel graphTargetProblem := by
  simpa [graphTargetProblem] using ComplexityReduction.Karp21.VertexCover.vertexCoverInNP

def numericTargetInNP :
    InNPEnc CostedPolyTimeModel numericTargetProblem := by
  simpa [numericTargetProblem] using ComplexityReduction.Karp21.Knapsack.knapsackInNP

def sourceInNP :
    InNPEnc CostedPolyTimeModel problem :=
  InNPEnc.of_reduction graphReduction graphTargetInNP

theorem goldCertificate :
    ∃ bridgeProblem : EncodedDecisionProblem,
      ∃ normalizedProblem : EncodedDecisionProblem,
        ∃ graphRouteTarget : EncodedDecisionProblem,
          ∃ numericRouteTarget : EncodedDecisionProblem,
            ∃ _outerBridgeCertificate :
              ProblemEquivM CostedPolyTimeModel problem bridgeProblem,
              ∃ _innerBridgeCertificate :
                ProblemEquivM CostedPolyTimeModel bridgeProblem normalizedProblem,
                ∃ _sourceToSatGadget :
                  KarpReductionM CostedPolyTimeModel
                    normalizedProblem
                    SAT.threeSATDecisionProblem,
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
    ⟨ bridgeProblem
    , normalizedProblem
    , graphRouteTarget
    , numericRouteTarget
    , outerBridge
    , innerBridge
    , sourceToSatGadget
    , satToGraphRoute
    , graphToFinalRoute
    , satToNumericRoute
    , numericToFinalRoute
    , ?_ ⟩
  exact ⟨graphReduction, numericReduction, graphTargetInNP, numericTargetInNP, sourceInNP⟩

end BenchmarkGoldProof
