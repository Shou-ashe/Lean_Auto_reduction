import ComplexityReduction
import LeanAutoReduction

noncomputable section

abbrev sourceProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.CSP.Examples.oneInThreeDecisionProblem

abbrev targetProblem : ComplexityReduction.EncodedDecisionProblem :=
  ComplexityReduction.CSP.Examples.notAllEqual3DecisionProblem

abbrev problem : ComplexityReduction.EncodedDecisionProblem :=
  { Instance := ComplexityReduction.EncodedType.prod
      ComplexityReduction.EncodedType.bool
      sourceProblem.Instance
    isYes := fun p => sourceProblem.isYes p.2 }

namespace BenchmarkGoldProof

open ComplexityReduction

abbrev normalizedProblem : EncodedDecisionProblem :=
  sourceProblem

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

def sourceToPivotGadget :
    KarpReductionM
      CostedPolyTimeModel
      normalizedProblem
      SAT.threeSATDecisionProblem := by
  simpa [normalizedProblem] using
    ComplexityReduction.CSP.Examples.oneInThreeToThreeSATKarpReduction

def pivotToTargetGadget :
    KarpReductionM
      CostedPolyTimeModel
      SAT.threeSATDecisionProblem
      targetProblem := by
  simpa [targetProblem] using
    ComplexityReduction.CSP.Hardness.NAE3SAT.threeSATToNAE3KarpReduction

def composedGadgetRoute :
    PolyReducibleM CostedPolyTimeModel problem targetProblem :=
  LeanAutoReduction.Reduction.polyReducibleOfBridgeAndTwoKarpReductions
    encodingBridgeCertificate
    sourceToPivotGadget
    pivotToTargetGadget

def targetInNP :
    InNPEnc CostedPolyTimeModel targetProblem := by
  simpa [targetProblem] using
    ComplexityReduction.CSP.Hardness.NAE3SAT.nae3InNP_of_threeSATInNP
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
