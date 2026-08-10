import ComplexityReduction

noncomputable section

abbrev sourceProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.setCoveringDecisionProblem

abbrev problem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.EncodedType.prod
      sourceProblem.Instance
      ComplexityReduction.EncodedType.bool
    isYes := fun p => sourceProblem.isYes p.1 }

namespace BenchmarkGoldProof

open ComplexityReduction

abbrev normalizedProblem : EncodedDecisionProblem :=
  sourceProblem

abbrev routeTarget1 : EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.exactCoverDecisionProblem

abbrev routeTarget2 : EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.knapsackKarpDecisionProblem

abbrev routeTarget3 : EncodedDecisionProblem :=
  ComplexityReduction.Combinatorics.jobSequencingDecisionProblem

def encodingBridgeCertificate :
    ProblemEquivM CostedPolyTimeModel problem normalizedProblem where
  toMap :=
    PolyTimeMap.fst
      CostedPolyTimeModel
      sourceProblem.Instance
      EncodedType.bool
  invMap :=
    PolyTimeMap.prod_mk
      (PolyTimeMap.id CostedPolyTimeModel sourceProblem.Instance)
      (PolyTimeMap.const
        CostedPolyTimeModel
        sourceProblem.Instance
        EncodedType.bool
        false)
  to_correct := fun _ => Iff.rfl
  inv_correct := fun _ => Iff.rfl

def reductionStep1 :
    KarpReductionM CostedPolyTimeModel normalizedProblem routeTarget1 := by
  simpa [normalizedProblem, routeTarget1] using
    ComplexityReduction.Karp21.ExactCover.setCoveringToExactCoverKarpReduction

def reductionStep2 :
    KarpReductionM CostedPolyTimeModel routeTarget1 routeTarget2 := by
  simpa [routeTarget1, routeTarget2] using
    ComplexityReduction.Karp21.Knapsack.exactCoverToKnapsack_baseDigitKarpReduction

def reductionStep3 :
    KarpReductionM CostedPolyTimeModel routeTarget2 routeTarget3 := by
  simpa [routeTarget2, routeTarget3] using
    ComplexityReduction.Karp21.JobSequencing.knapsackToJobSequencing_textbookKarpReduction

def normalizedRoute :
    PolyReducibleM CostedPolyTimeModel normalizedProblem routeTarget3 :=
  PolyReducibleM.trans (PolyReducibleM.trans ⟨reductionStep1⟩ ⟨reductionStep2⟩)
    ⟨reductionStep3⟩

def composedReduction :
    PolyReducibleM CostedPolyTimeModel problem routeTarget3 :=
  ProblemEquivM.transportSource encodingBridgeCertificate normalizedRoute

def routeTarget3InNP :
    InNPEnc CostedPolyTimeModel routeTarget3 := by
  simpa [routeTarget3] using ComplexityReduction.Karp21.JobSequencing.jobSequencingInNP

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
