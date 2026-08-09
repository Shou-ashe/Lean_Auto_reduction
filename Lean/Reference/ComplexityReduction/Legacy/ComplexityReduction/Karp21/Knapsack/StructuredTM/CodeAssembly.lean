import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.CodeGeneration

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

/-!
Assembly witnesses for the compact Knapsack numeric codes.

The only remaining input to this layer is a direct witness for the full compact
item digit-vector list.  Once that list is available, the no-carry base, item
codes, and target code are all obtained from already checked binary arithmetic
and `Nat.ofDigits` runners.
-/

theorem compactBase_tm_polytime_of_item_digit_vectors
    (hVectors :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        (EncodedType.list (EncodedType.list EncodedType.binaryNat))
        compactItemDigitVectors) :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      EncodedType.binaryNat
      compactBase := by
  let X := integerProgrammingBinaryStructuredEncodedType
  have hTargetDigits :
      TMPolyTimeMap X (EncodedType.list EncodedType.binaryNat) compactTargetDigits := by
    simpa [X] using compactTargetDigits_tm_polytime
  have hTargetSum :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun I : IntegerProgrammingInput => (compactTargetDigits I).sum) := by
    have hComp := TMPolyTimeMap.comp binaryNatListSum_tm_polytime_sum hTargetDigits
    simpa [Function.comp, X] using hComp
  have hMass :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun I : IntegerProgrammingInput => compactDigitVectorsMass (compactItemDigitVectors I)) := by
    have hComp := TMPolyTimeMap.comp compactDigitVectorsMass_tm_polytime hVectors
    simpa [Function.comp, X] using hComp
  have hPair₁ :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun I : IntegerProgrammingInput =>
          ((compactTargetDigits I).sum,
            compactDigitVectorsMass (compactItemDigitVectors I))) :=
    TMPolyTimeMap.prod_mk hTargetSum hMass
  have hSumMass :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun I : IntegerProgrammingInput =>
          (compactTargetDigits I).sum +
            compactDigitVectorsMass (compactItemDigitVectors I)) := by
    have hComp := TMPolyTimeMap.comp binaryNatAdd_tm_polytime hPair₁
    simpa [Function.comp, X] using hComp
  have hTwoRaw : TMPolyTimeMap X EncodedType.binaryNat (fun _ : X.Carrier => (2 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (2 : Nat)
  have hTwo : TMPolyTimeMap X EncodedType.binaryNat
      (fun _ : IntegerProgrammingInput => (2 : Nat)) := by
    simpa [X] using hTwoRaw
  have hPair₂ :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun I : IntegerProgrammingInput =>
          ((compactTargetDigits I).sum +
              compactDigitVectorsMass (compactItemDigitVectors I),
            (2 : Nat))) :=
    TMPolyTimeMap.prod_mk hSumMass hTwo
  have hBase :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun I : IntegerProgrammingInput =>
          (compactTargetDigits I).sum +
            compactDigitVectorsMass (compactItemDigitVectors I) + 2) := by
    have hComp := TMPolyTimeMap.comp binaryNatAdd_tm_polytime hPair₂
    simpa [Function.comp, X, Nat.add_assoc] using hComp
  simpa [compactBase, X] using hBase

theorem compactItemCodes_tm_polytime_of_item_digit_vectors
    (hVectors :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        (EncodedType.list (EncodedType.list EncodedType.binaryNat))
        compactItemDigitVectors) :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      (EncodedType.list EncodedType.binaryNat)
      compactItemCodes := by
  let X := integerProgrammingBinaryStructuredEncodedType
  have hBase : TMPolyTimeMap X EncodedType.binaryNat compactBase :=
    compactBase_tm_polytime_of_item_digit_vectors hVectors
  have hPair :
      TMPolyTimeMap X sharedBaseDigitPairsInputEncodedType
        (fun I : IntegerProgrammingInput => (compactBase I, compactItemDigitVectors I)) :=
    TMPolyTimeMap.prod_mk hBase hVectors
  have hCodes := TMPolyTimeMap.comp sharedBaseDigitCodes_tm_polytime hPair
  convert hCodes using 1
  funext I
  rw [Function.comp_apply, sharedBaseDigitCodes_eq]
  rfl

theorem compactTargetCode_tm_polytime_of_item_digit_vectors
    (hVectors :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        (EncodedType.list (EncodedType.list EncodedType.binaryNat))
        compactItemDigitVectors) :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      EncodedType.binaryNat
      compactTargetCode := by
  let X := integerProgrammingBinaryStructuredEncodedType
  have hBase : TMPolyTimeMap X EncodedType.binaryNat compactBase :=
    compactBase_tm_polytime_of_item_digit_vectors hVectors
  have hDigits :
      TMPolyTimeMap X (EncodedType.list EncodedType.binaryNat) compactTargetDigits := by
    simpa [X] using compactTargetDigits_tm_polytime
  have hPair :
      TMPolyTimeMap X binaryNatOfDigitsInputEncodedType
        (fun I : IntegerProgrammingInput => (compactBase I, compactTargetDigits I)) :=
    TMPolyTimeMap.prod_mk hBase hDigits
  have hCode := TMPolyTimeMap.comp binaryNatOfDigits_tm_polytime hPair
  convert hCode using 1

end Knapsack
end Karp21
end ComplexityReduction
