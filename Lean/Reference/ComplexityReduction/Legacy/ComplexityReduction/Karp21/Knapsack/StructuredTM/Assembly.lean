import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryArithmetic
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryCompareTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.RowNegativeShift
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.SlackItemVectors

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

/-!
Final direct TM-backed assembly for the compact binary
`0-1 IP -> Knapsack` route.
-/

theorem compactMap_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      knapsackBinaryStructuredEncodedType
      compactMap :=
  compactMap_tm_polytime_of_binary_arithmetic_witnesses
    rowNegativeShift_tm_polytime
    binaryNatSuccLeBool_tm_polytime
    compactItemCodes_tm_polytime
    compactTargetCode_tm_polytime

noncomputable def compactMapTMBackedMap :
    TMBackedCostedMap
      integerProgrammingBinaryStructuredEncodedType
      knapsackBinaryStructuredEncodedType
      compactMap :=
  compactMapTMBackedMap_of_binary_arithmetic_witnesses
    rowNegativeShift_tm_polytime
    binaryNatSuccLeBool_tm_polytime
    compactItemCodes_tm_polytime
    compactTargetCode_tm_polytime

noncomputable def zeroOneIPToKnapsackBinaryStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      zeroOneIntegerProgrammingBinaryStructuredDecisionProblem
      knapsackBinaryStructuredDecisionProblem :=
  zeroOneIPToKnapsackBinaryStructuredTMBackedKarpReduction_of_binary_arithmetic_witnesses
    rowNegativeShift_tm_polytime
    binaryNatSuccLeBool_tm_polytime
    compactItemCodes_tm_polytime
    compactTargetCode_tm_polytime

noncomputable def zeroOneIPToKnapsackBinaryStructuredTMKarpReduction :
    TMKarpReduction
      zeroOneIntegerProgrammingBinaryStructuredDecisionProblem
      knapsackBinaryStructuredDecisionProblem :=
  zeroOneIPToKnapsackBinaryStructuredTMBackedKarpReduction.toTMKarpReduction

end Knapsack
end Karp21
end ComplexityReduction
