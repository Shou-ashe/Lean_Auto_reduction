import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.Slots
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover.StructuredTM.SetCoveringCNF.Coverage

namespace ComplexityReduction
namespace Karp21
namespace ExactCover

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-!
Direct TM-backed final assembly for the compact Set-Covering-to-CNF route.
-/

def setCoveringCNFExecutable (I : SetCoveringInput) : SAT.CNF :=
  setCoveringSlotClausesExecutable I ++ setCoveringCoverageClausesExecutable I

theorem setCoveringCNFExecutable_eq (I : SetCoveringInput) :
    setCoveringCNFExecutable I = setCoveringCNF I := by
  simp [setCoveringCNFExecutable, setCoveringCNF, setCoveringSlotClausesExecutable_eq,
    setCoveringCoverageClausesExecutable_eq]

theorem setCoveringCNFExecutable_tm_polytime :
    TMPolyTimeMap
      setCoveringStructuredEncodedType
      cnfStructuredEncodedType
      setCoveringCNFExecutable := by
  let X := setCoveringStructuredEncodedType
  have hSlots :
      TMPolyTimeMap X cnfStructuredEncodedType setCoveringSlotClausesExecutable := by
    simpa [X] using setCoveringSlotClausesExecutable_tm_polytime
  have hCoverage :
      TMPolyTimeMap X cnfStructuredEncodedType setCoveringCoverageClausesExecutable := by
    simpa [X] using setCoveringCoverageClausesExecutable_tm_polytime
  have hAppendInput :
      TMPolyTimeMap X (EncodedType.prod cnfStructuredEncodedType cnfStructuredEncodedType)
        (fun I : X.Carrier =>
          (setCoveringSlotClausesExecutable I, setCoveringCoverageClausesExecutable I)) :=
    TMPolyTimeMap.prod_mk hSlots hCoverage
  have hAppend :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_append clauseStructuredEncodedType) hAppendInput
  simpa [Function.comp, setCoveringCNFExecutable, cnfStructuredEncodedType, X] using hAppend

theorem setCoveringCNFExecutable_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : SetCoveringInput => setCoveringStructuredEncodedType.inputSize I)
      (fun φ : SAT.CNF => cnfStructuredEncodedType.inputSize φ)
      setCoveringCNFExecutable := by
  refine PolynomialSizeBound.intro_with 8 100000000 100000000 ?_
  intro I
  rw [setCoveringCNFExecutable_eq]
  exact setCoveringCNF_structured_inputSize_le_source_poly I

noncomputable def setCoveringCNFTMBackedMap :
    TMBackedCostedMap
      setCoveringStructuredEncodedType
      cnfStructuredEncodedType
      setCoveringCNFExecutable where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      setCoveringCNFExecutable_polynomialSizeBound
  tm_polytime := setCoveringCNFExecutable_tm_polytime

theorem setCoveringCNFExecutable_correct (I : SetCoveringInput) :
    setCoveringStructuredDecisionProblem.isYes I ↔
      satisfiabilityStructuredDecisionProblem.isYes (setCoveringCNFExecutable I) := by
  rw [setCoveringCNFExecutable_eq]
  simpa [setCoveringStructuredDecisionProblem, satisfiabilityStructuredDecisionProblem]
    using setCoveringCNF_correct I

noncomputable def setCoveringToSatisfiabilityStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      setCoveringStructuredDecisionProblem
      satisfiabilityStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    setCoveringCNFTMBackedMap
    (by
      intro I
      exact setCoveringCNFExecutable_correct I)

/--
Public structured Set-Covering-to-CNF-SAT reduction, projected from the direct
TM-backed CNF assembly.
-/
noncomputable def setCoveringToSatisfiabilityStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      setCoveringStructuredDecisionProblem satisfiabilityStructuredDecisionProblem :=
  setCoveringToSatisfiabilityStructuredTMBackedKarpReduction.toCostedKarpReduction

/-- Direct TM-facing structured Set-Covering-to-CNF-SAT reduction. -/
noncomputable def setCoveringToSatisfiabilityStructuredTMKarpReduction :
    TMKarpReduction
      setCoveringStructuredDecisionProblem satisfiabilityStructuredDecisionProblem :=
  setCoveringToSatisfiabilityStructuredTMBackedKarpReduction.toTMKarpReduction

end ExactCover
end Karp21
end ComplexityReduction
