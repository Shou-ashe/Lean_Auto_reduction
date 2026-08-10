import ComplexityReduction

noncomputable section

abbrev sourceProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.CSP.Examples.notAllEqual3DecisionProblem

abbrev targetProblem : ComplexityReduction.EncodedDecisionProblem :=
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

abbrev routeTarget2 : EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.cliqueDecisionProblem

def sourceProjection :
    PolyTimeMap CostedPolyTimeModel problem.Instance sourceProblem.Instance :=
  PolyTimeMap.comp
    (PolyTimeMap.fst CostedPolyTimeModel sourceProblem.Instance EncodedType.bool)
    (PolyTimeMap.fst
      CostedPolyTimeModel
      (EncodedType.prod sourceProblem.Instance EncodedType.bool)
      EncodedType.bool)

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
    sourceWithRightFlag
    (PolyTimeMap.const
      CostedPolyTimeModel
      sourceProblem.Instance
      EncodedType.bool
      false)

def encodingBridgeCertificate :
    ProblemEquivM CostedPolyTimeModel problem normalizedProblem where
  toMap := sourceProjection
  invMap := sourceInjection
  to_correct := fun _ => Iff.rfl
  inv_correct := fun _ => Iff.rfl

def sourceToSatGadget :
    KarpReductionM CostedPolyTimeModel normalizedProblem SAT.threeSATDecisionProblem := by
  simpa [normalizedProblem] using
    ComplexityReduction.CSP.Examples.notAllEqual3ToThreeSATKarpReduction

def satToIntermediateRoute :
    KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem routeTarget2 := by
  simpa [routeTarget2] using
    ComplexityReduction.Karp21.Clique.threeSATToClique_textbookKarpReduction

def intermediateToFinalRoute :
    KarpReductionM CostedPolyTimeModel routeTarget2 targetProblem := by
  simpa [routeTarget2, targetProblem] using
    ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverKarpReduction

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
  simpa [targetProblem] using ComplexityReduction.Karp21.VertexCover.vertexCoverInNP

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
