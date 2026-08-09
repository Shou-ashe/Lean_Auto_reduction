import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.CNFSplit.Part3

namespace ComplexityReduction
namespace Karp21
open ComplexityReduction
open Turing.TM2.Stmt

noncomputable def cnfSplitFromStructuredBoundToThreeCNFTMBackedMap :
    TMBackedCostedMap
      cnfStructuredEncodedType
      threeCNFStructuredEncodedType
      cnfSplitFromStructuredBoundToThreeCNF where
  costed := CostedMap.of_encodedPolynomialSizeBound
    cnfSplitFromStructuredBound_polynomialSizeBound
  tm_polytime := by
    rcases cnfSplitRunnerFold_clauses_tm_polytime with ⟨hCNF⟩
    refine ⟨?_⟩
    exact
      { tm := hCNF.tm
        inputAlphabet := hCNF.inputAlphabet
        outputAlphabet := hCNF.outputAlphabet
        time := hCNF.time
        outputsFun := by
          intro φ
          have hEnc :
              threeCNFStructuredEncodedType.encode (cnfSplitFromStructuredBoundToThreeCNF φ) =
                cnfStructuredEncodedType.encode ((cnfSplitRunnerFold φ).2) := by
            rw [cnfSplitRunnerFold_clauses_eq]
            rfl
          simpa [hEnc] using hCNF.outputsFun φ }

theorem cnfSATToThreeSATStructured_tm_polytime :
    TMPolyTimeMap
      cnfStructuredEncodedType
      threeCNFStructuredEncodedType
      cnfSplitFromStructuredBoundToThreeCNF :=
  cnfSplitFromStructuredBoundToThreeCNFTMBackedMap.tm_polytime

noncomputable def cnfSATToThreeSATStructuredTMBackedMap :
    TMBackedCostedMap
      cnfStructuredEncodedType
      threeCNFStructuredEncodedType
      cnfSplitFromStructuredBoundToThreeCNF :=
  cnfSplitFromStructuredBoundToThreeCNFTMBackedMap

noncomputable def cnfSATToThreeSATStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      satisfiabilityStructuredDecisionProblem threeSATStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    cnfSplitFromStructuredBoundToThreeCNFTMBackedMap
    (by
      intro φ
      exact (cnfSplitFromStructuredBound_satisfiable_iff φ).symm)

end Karp21
end ComplexityReduction
