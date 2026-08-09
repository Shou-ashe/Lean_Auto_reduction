import ComplexityReduction

noncomputable section

abbrev sourceProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.SAT.threeSATDecisionProblem

abbrev problem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.EncodedType.prod
      ComplexityReduction.EncodedType.bool
      sourceProblem.Instance
    isYes := fun p => sourceProblem.isYes p.2 }

namespace BenchmarkGoldProof

open ComplexityReduction

abbrev normalizedProblem : EncodedDecisionProblem :=
  sourceProblem

abbrev routeTarget1 : EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.cliqueDecisionProblem

abbrev routeTarget2 : EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.vertexCoverDecisionProblem

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

def reductionStep1 :
    KarpReductionM CostedPolyTimeModel normalizedProblem routeTarget1 := by
  simpa [normalizedProblem, routeTarget1] using
    ComplexityReduction.Karp21.Clique.threeSATToClique_textbookKarpReduction

def reductionStep2 :
    KarpReductionM CostedPolyTimeModel routeTarget1 routeTarget2 := by
  simpa [routeTarget1, routeTarget2] using
    ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverKarpReduction

def normalizedRoute :
    PolyReducibleM CostedPolyTimeModel normalizedProblem routeTarget2 :=
  PolyReducibleM.trans ⟨reductionStep1⟩ ⟨reductionStep2⟩

def composedReduction :
    PolyReducibleM CostedPolyTimeModel problem routeTarget2 :=
  ProblemEquivM.transportSource encodingBridgeCertificate normalizedRoute

def routeTarget2InNP :
    InNPEnc CostedPolyTimeModel routeTarget2 := by
  simpa [routeTarget2] using ComplexityReduction.Karp21.VertexCover.vertexCoverInNP

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
  exact
    ⟨composedReduction, routeTarget2InNP, sourceInNP⟩

end BenchmarkGoldProof
