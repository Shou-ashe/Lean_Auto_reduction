import ComplexityReduction

noncomputable section

abbrev sourceProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Karp21.satisfiabilityDecisionProblem

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
  ComplexityReduction.SAT.threeSATDecisionProblem

abbrev routeTarget2 : EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.Graph.cliqueDecisionProblem

abbrev routeTarget3 : EncodedDecisionProblem :=
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
    ComplexityReduction.Karp21.cnfSATToThreeSATKarpReduction

def reductionStep2 :
    KarpReductionM CostedPolyTimeModel routeTarget1 routeTarget2 := by
  simpa [routeTarget1, routeTarget2] using
    ComplexityReduction.Karp21.Clique.threeSATToClique_textbookKarpReduction

def reductionStep3 :
    KarpReductionM CostedPolyTimeModel routeTarget2 routeTarget3 := by
  simpa [routeTarget2, routeTarget3] using
    ComplexityReduction.Karp21.VertexCover.cliqueToVertexCoverKarpReduction

def normalizedRoute :
    PolyReducibleM CostedPolyTimeModel normalizedProblem routeTarget3 :=
  PolyReducibleM.trans (PolyReducibleM.trans ⟨reductionStep1⟩ ⟨reductionStep2⟩)
    ⟨reductionStep3⟩

def composedReduction :
    PolyReducibleM CostedPolyTimeModel problem routeTarget3 :=
  ProblemEquivM.transportSource encodingBridgeCertificate normalizedRoute

def routeTarget3InNP :
    InNPEnc CostedPolyTimeModel routeTarget3 := by
  simpa [routeTarget3] using ComplexityReduction.Karp21.VertexCover.vertexCoverInNP

def sourceInNP :
    InNPEnc CostedPolyTimeModel problem :=
  InNPEnc.of_reduction composedReduction routeTarget3InNP

theorem goldCertificate :
    ∃ normalizedProblem : EncodedDecisionProblem,
      ∃ routeTarget1 : EncodedDecisionProblem,
        ∃ routeTarget2 : EncodedDecisionProblem,
          ∃ routeTarget3 : EncodedDecisionProblem,
            ∃ _encodingBridgeCertificate :
              ProblemEquivM CostedPolyTimeModel problem normalizedProblem,
              ∃ _reductionStep1 :
                KarpReductionM CostedPolyTimeModel normalizedProblem routeTarget1,
                ∃ _reductionStep2 :
                  KarpReductionM CostedPolyTimeModel routeTarget1 routeTarget2,
                  ∃ _reductionStep3 :
                    KarpReductionM CostedPolyTimeModel routeTarget2 routeTarget3,
                    PolyReducibleM CostedPolyTimeModel problem routeTarget3 ∧
                    InNPEnc CostedPolyTimeModel routeTarget3 ∧
                    InNPEnc CostedPolyTimeModel problem := by
  refine
    ⟨ normalizedProblem
    , routeTarget1
    , routeTarget2
    , routeTarget3
    , encodingBridgeCertificate
    , reductionStep1
    , reductionStep2
    , reductionStep3
    , ?_ ⟩
  exact ⟨composedReduction, routeTarget3InNP, sourceInNP⟩

end BenchmarkGoldProof
