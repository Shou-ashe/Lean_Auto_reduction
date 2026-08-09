import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.ItemDigits

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

/-!
Assembly of the full compact item digit-vector list.

The variable truth-item vectors are now direct.  The remaining open component is
the slack-vector generator; this file isolates that dependency and immediately
propagates it to the numeric code witnesses.
-/

theorem compactItemDigitVectors_tm_polytime_of_slack_vectors
    (hSlack :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        (EncodedType.list (EncodedType.list EncodedType.binaryNat))
        compactSlackItemDigitVectors) :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list (EncodedType.list EncodedType.binaryNat))
      compactItemDigitVectors := by
  let X := integerProgrammingBinaryStructuredEncodedType
  let L := EncodedType.list (EncodedType.list EncodedType.binaryNat)
  have hVariable : TMPolyTimeMap X L compactVariableItemDigitVectors := by
    simpa [X, L] using compactVariableItemDigitVectors_tm_polytime
  have hPair :
      TMPolyTimeMap X (EncodedType.prod L L)
        (fun I : IntegerProgrammingInput =>
          (compactVariableItemDigitVectors I, compactSlackItemDigitVectors I)) :=
    TMPolyTimeMap.prod_mk hVariable hSlack
  have hAppend := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append (EncodedType.list EncodedType.binaryNat)) hPair
  simpa [Function.comp, compactItemDigitVectors, X, L] using hAppend

theorem compactBase_tm_polytime_of_slack_vectors
    (hSlack :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        (EncodedType.list (EncodedType.list EncodedType.binaryNat))
        compactSlackItemDigitVectors) :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      EncodedType.binaryNat
      compactBase :=
  compactBase_tm_polytime_of_item_digit_vectors
    (compactItemDigitVectors_tm_polytime_of_slack_vectors hSlack)

theorem compactItemCodes_tm_polytime_of_slack_vectors
    (hSlack :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        (EncodedType.list (EncodedType.list EncodedType.binaryNat))
        compactSlackItemDigitVectors) :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list EncodedType.binaryNat)
      compactItemCodes :=
  compactItemCodes_tm_polytime_of_item_digit_vectors
    (compactItemDigitVectors_tm_polytime_of_slack_vectors hSlack)

theorem compactTargetCode_tm_polytime_of_slack_vectors
    (hSlack :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        (EncodedType.list (EncodedType.list EncodedType.binaryNat))
        compactSlackItemDigitVectors) :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      EncodedType.binaryNat
      compactTargetCode :=
  compactTargetCode_tm_polytime_of_item_digit_vectors
    (compactItemDigitVectors_tm_polytime_of_slack_vectors hSlack)

end Knapsack
end Karp21
end ComplexityReduction
