import ComplexityReduction

noncomputable section

abbrev sourceProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.CSP.Examples.oneInThreeDecisionProblem

abbrev targetProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.vertexCoverDecisionProblem

abbrev problem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.EncodedType.prod
      ComplexityReduction.EncodedType.bool
      sourceProblem.Instance
    isYes := fun p => sourceProblem.isYes p.2 }

namespace BenchmarkGoldProof

open ComplexityReduction

abbrev normalizedProblem : EncodedDecisionProblem :=
  sourceProblem

abbrev routeTarget2 : EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.cliqueDecisionProblem

def encodingBridgeCertificate :
    ProblemEquivM CostedPolyTimeModel problem normalizedProblem where
  toMap :=
    PolyTimeMap.snd
      CostedPolyTimeModel
      EncodedType.bool
      sourceProblem.Instance
  invMap :=
    PolyTimeMap.prod_mk
      (PolyTimeMap.const
        CostedPolyTimeModel
        sourceProblem.Instance
        EncodedType.bool
        false)
      (PolyTimeMap.id CostedPolyTimeModel sourceProblem.Instance)
  to_correct := fun _ => Iff.rfl
  inv_correct := fun _ => Iff.rfl

def sourceToSatGadget :
    KarpReductionM CostedPolyTimeModel normalizedProblem SAT.threeSATDecisionProblem := by
  simpa [normalizedProblem] using
    ComplexityReduction.CSP.Examples.oneInThreeToThreeSATKarpReduction

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
