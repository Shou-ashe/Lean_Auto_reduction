import ComplexityReduction
import LeanAutoReduction

noncomputable section

abbrev sourceProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.CSP.Examples.notAllEqual3DecisionProblem

abbrev targetProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.CSP.Examples.oneInThreeDecisionProblem

abbrev problem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.EncodedType.prod
      sourceProblem.Instance
      ComplexityReduction.EncodedType.bool
    isYes := fun p => sourceProblem.isYes p.1 }

namespace BenchmarkGoldProof

open ComplexityReduction

abbrev normalizedProblem : EncodedDecisionProblem :=
  sourceProblem

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

def sourceToPivotGadget :
    KarpReductionM
      CostedPolyTimeModel
      normalizedProblem
      SAT.threeSATDecisionProblem := by
  simpa [normalizedProblem] using
    ComplexityReduction.CSP.Examples.notAllEqual3ToThreeSATKarpReduction

def pivotToTargetGadget :
    KarpReductionM
      CostedPolyTimeModel
      SAT.threeSATDecisionProblem
      targetProblem := by
  simpa [targetProblem] using
    ComplexityReduction.CSP.Hardness.OneInThree.threeSATToOneInThreeKarpReduction

def composedGadgetRoute :
    PolyReducibleM CostedPolyTimeModel problem targetProblem :=
  LeanAutoReduction.Reduction.polyReducibleOfBridgeAndTwoKarpReductions
    encodingBridgeCertificate
    sourceToPivotGadget
    pivotToTargetGadget

def targetInNP :
    InNPEnc CostedPolyTimeModel targetProblem := by
  simpa [targetProblem] using
    ComplexityReduction.CSP.Hardness.OneInThree.oneInThreeInNP_of_threeSATInNP
      ComplexityReduction.SAT.threeSAT_inNP

def sourceInNP :
    InNPEnc CostedPolyTimeModel problem :=
  InNPEnc.of_reduction composedGadgetRoute targetInNP

theorem goldCertificate :
    ∃ normalizedProblem : EncodedDecisionProblem,
      ∃ _encodingBridgeCertificate :
        ProblemEquivM CostedPolyTimeModel problem normalizedProblem,
        ∃ _sourceToPivotGadget :
          KarpReductionM CostedPolyTimeModel normalizedProblem SAT.threeSATDecisionProblem,
          ∃ _pivotToTargetGadget :
            KarpReductionM CostedPolyTimeModel SAT.threeSATDecisionProblem targetProblem,
            PolyReducibleM CostedPolyTimeModel problem targetProblem ∧
            InNPEnc CostedPolyTimeModel targetProblem ∧
            InNPEnc CostedPolyTimeModel problem := by
  exact
    ⟨ normalizedProblem
    , encodingBridgeCertificate
    , sourceToPivotGadget
    , pivotToTargetGadget
    , composedGadgetRoute
    , targetInNP
    , sourceInNP ⟩

end BenchmarkGoldProof
