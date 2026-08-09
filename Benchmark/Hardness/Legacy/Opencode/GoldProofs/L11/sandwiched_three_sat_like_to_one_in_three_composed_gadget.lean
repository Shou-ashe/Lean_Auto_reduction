import ComplexityReduction
import LeanAutoReduction

noncomputable section

abbrev sourceProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.CSP.Examples.threeSATLikeDecisionProblem

abbrev targetProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.CSP.Examples.oneInThreeDecisionProblem

abbrev problem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.EncodedType.prod
      (ComplexityReduction.EncodedType.prod
        ComplexityReduction.EncodedType.bool
        sourceProblem.Instance)
      ComplexityReduction.EncodedType.bool
    isYes := fun p => sourceProblem.isYes p.1.2 }

namespace BenchmarkGoldProof

open ComplexityReduction

abbrev normalizedProblem : EncodedDecisionProblem :=
  sourceProblem

def encodingBridgeCertificate :
    ProblemEquivM CostedPolyTimeModel problem normalizedProblem :=
  let forwardMap : PolyTimeMap CostedPolyTimeModel problem.Instance sourceProblem.Instance :=
    PolyTimeMap.comp
      (PolyTimeMap.snd CostedPolyTimeModel EncodedType.bool sourceProblem.Instance)
      (PolyTimeMap.fst
        CostedPolyTimeModel
        (EncodedType.prod EncodedType.bool sourceProblem.Instance)
        EncodedType.bool)
  let backwardMap : PolyTimeMap CostedPolyTimeModel sourceProblem.Instance problem.Instance :=
    PolyTimeMap.prod_mk
      (PolyTimeMap.prod_mk
        (PolyTimeMap.const
          CostedPolyTimeModel
          sourceProblem.Instance
          EncodedType.bool
          false)
        (PolyTimeMap.id CostedPolyTimeModel sourceProblem.Instance))
      (PolyTimeMap.const
        CostedPolyTimeModel
        sourceProblem.Instance
        EncodedType.bool
        false)
  { toMap := forwardMap
    invMap := backwardMap
    to_correct := by
      intro x
      have h : forwardMap.toFun x = x.1.2 := by rfl
      rw [h]
    inv_correct := by
      intro x
      dsimp [problem, normalizedProblem]
      have h : (backwardMap.toFun x).1.2 = x := by rfl
      rw [h] }

def sourceToPivotGadget :
    KarpReductionM
      CostedPolyTimeModel
      normalizedProblem
      SAT.threeSATDecisionProblem := by
  simpa [normalizedProblem] using
    ComplexityReduction.CSP.Examples.threeSATLikeToThreeSATKarpReduction

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
