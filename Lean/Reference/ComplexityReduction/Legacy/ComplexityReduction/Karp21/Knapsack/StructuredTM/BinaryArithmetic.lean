import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.Front

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

/-!
Binary-arithmetic front layer for the compact 0-1-IP-to-Knapsack route.

This file keeps the proven symbol-level parts separate from the still-missing
binary comparison primitive.  The direct `binaryInt` sign and payload projections
are enough to reduce `intNatAddNonnegativeBool` to a single binary natural
comparison witness.
-/

def binaryIntSignBool : Int → Bool
  | Int.ofNat _ => false
  | Int.negSucc _ => true

def binaryIntPayload : Int → Nat
  | Int.ofNat n => n
  | Int.negSucc n => n

def binaryIntSignKeep : EncodedType.binaryInt.Symbol → Option EncodedType.bool.Symbol
  | Sum.inl b => some b
  | Sum.inr _ => none

def binaryIntPayloadKeep : EncodedType.binaryInt.Symbol → Option EncodedType.binaryNat.Symbol
  | Sum.inl _ => none
  | Sum.inr b => some b

theorem binaryIntSignBool_encode_filterMap (z : Int) :
    EncodedType.bool.encode (binaryIntSignBool z) =
      (EncodedType.binaryInt.encode z).filterMap binaryIntSignKeep := by
  cases z <;> simp [EncodedType.binaryInt, EncodedType.bool, binaryIntSignBool,
    binaryIntSignKeep]

theorem binaryIntPayload_encode_filterMap (z : Int) :
    EncodedType.binaryNat.encode (binaryIntPayload z) =
      (EncodedType.binaryInt.encode z).filterMap binaryIntPayloadKeep := by
  cases z <;> simp [EncodedType.binaryInt, binaryIntPayload, binaryIntPayloadKeep]

theorem binaryIntSignBool_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryInt
      EncodedType.bool
      binaryIntSignBool :=
  (TMBackedCostedMap.symbolFilterMap
    EncodedType.binaryInt
    EncodedType.bool
    binaryIntSignBool
    binaryIntSignKeep
    binaryIntSignBool_encode_filterMap).tm_polytime

theorem binaryIntPayload_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryInt
      EncodedType.binaryNat
      binaryIntPayload :=
  (TMBackedCostedMap.symbolFilterMap
    EncodedType.binaryInt
    EncodedType.binaryNat
    binaryIntPayload
    binaryIntPayloadKeep
    binaryIntPayload_encode_filterMap).tm_polytime

def binaryNatSuccLeBool (p : Nat × Nat) : Bool :=
  decide (p.1.succ ≤ p.2)

theorem intNatAddNonnegativeBool_eq_sign_dispatch (p : Int × Nat) :
    intNatAddNonnegativeBool p =
      match binaryIntSignBool p.1 with
      | true => binaryNatSuccLeBool (binaryIntPayload p.1, p.2)
      | false => true := by
  rcases p with ⟨z, n⟩
  cases z with
  | ofNat m =>
      have hNonnegative : 0 ≤ (m : Int) + (n : Int) :=
        Int.add_nonneg (Int.natCast_nonneg m) (Int.natCast_nonneg n)
      simp [intNatAddNonnegativeBool, binaryIntSignBool, hNonnegative]
  | negSucc m =>
      by_cases hLe : m.succ ≤ n
      · have hNonnegative : 0 ≤ Int.negSucc m + (n : Int) := by omega
        simp [intNatAddNonnegativeBool, binaryIntSignBool, binaryIntPayload,
          binaryNatSuccLeBool, hLe, hNonnegative]
      · have hNegative : ¬ 0 ≤ Int.negSucc m + (n : Int) := by omega
        simp [intNatAddNonnegativeBool, binaryIntSignBool, binaryIntPayload,
          binaryNatSuccLeBool, hLe, hNegative]

theorem intNatAddNonnegativeBool_tm_polytime_of_binaryNatSuccLe_witness
    (hSuccLe :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        EncodedType.bool
        binaryNatSuccLeBool) :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryInt EncodedType.binaryNat)
      EncodedType.bool
      intNatAddNonnegativeBool := by
  let X := EncodedType.prod EncodedType.binaryInt EncodedType.binaryNat
  let N := EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat
  have hInt :
      TMPolyTimeMap X EncodedType.binaryInt (fun p : Int × Nat => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.binaryInt EncodedType.binaryNat
  have hShift :
      TMPolyTimeMap X EncodedType.binaryNat (fun p : Int × Nat => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.binaryInt EncodedType.binaryNat
  have hSign :
      TMPolyTimeMap X EncodedType.bool (fun p : Int × Nat => binaryIntSignBool p.1) := by
    have hComp := TMPolyTimeMap.comp binaryIntSignBool_tm_polytime hInt
    simpa [Function.comp, X] using hComp
  have hPayload :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun p : Int × Nat => binaryIntPayload p.1) := by
    have hComp := TMPolyTimeMap.comp binaryIntPayload_tm_polytime hInt
    simpa [Function.comp, X] using hComp
  have hNatPair :
      TMPolyTimeMap X N (fun p : Int × Nat => (binaryIntPayload p.1, p.2)) :=
    TMPolyTimeMap.prod_mk hPayload hShift
  have hBranchInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool N)
        (fun p : Int × Nat => (binaryIntSignBool p.1, (binaryIntPayload p.1, p.2))) :=
    TMPolyTimeMap.prod_mk hSign hNatPair
  have hFalse :
      TMPolyTimeMap N EncodedType.bool (fun _ : Nat × Nat => true) :=
    TMPolyTimeMap.const N EncodedType.bool true
  have hDispatch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool N)
        EncodedType.bool
        (fun p : Bool × (Nat × Nat) =>
          match p.1 with
          | true => binaryNatSuccLeBool p.2
          | false => true) :=
    Clique.boolProduct_dispatch_tm_polytime N EncodedType.bool
      (fFalse := fun _ : Nat × Nat => true)
      (fTrue := binaryNatSuccLeBool)
      hFalse hSuccLe
  have hOut := TMPolyTimeMap.comp hDispatch hBranchInput
  convert hOut using 1
  funext p
  exact intNatAddNonnegativeBool_eq_sign_dispatch p

theorem compactMap_tm_polytime_of_binary_arithmetic_witnesses
    (hRowShift :
      TMPolyTimeMap
        intRowBinaryStructuredEncodedType
        EncodedType.binaryNat
        rowNegativeShift)
    (hSuccLe :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        EncodedType.bool
        binaryNatSuccLeBool)
    (hCodes :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        (EncodedType.list EncodedType.binaryNat)
        compactItemCodes)
    (hTarget :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        EncodedType.binaryNat
        compactTargetCode) :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      knapsackBinaryStructuredEncodedType
      compactMap :=
  compactMap_tm_polytime_of_arithmetic_witnesses hRowShift
    (intNatAddNonnegativeBool_tm_polytime_of_binaryNatSuccLe_witness hSuccLe)
    hCodes hTarget

noncomputable def compactMapTMBackedMap_of_binary_arithmetic_witnesses
    (hRowShift :
      TMPolyTimeMap
        intRowBinaryStructuredEncodedType
        EncodedType.binaryNat
        rowNegativeShift)
    (hSuccLe :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        EncodedType.bool
        binaryNatSuccLeBool)
    (hCodes :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        (EncodedType.list EncodedType.binaryNat)
        compactItemCodes)
    (hTarget :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        EncodedType.binaryNat
        compactTargetCode) :
    TMBackedCostedMap
      integerProgrammingBinaryStructuredEncodedType
      knapsackBinaryStructuredEncodedType
      compactMap :=
  compactMapTMBackedMap_of_arithmetic_witnesses hRowShift
    (intNatAddNonnegativeBool_tm_polytime_of_binaryNatSuccLe_witness hSuccLe)
    hCodes hTarget

noncomputable def zeroOneIPToKnapsackBinaryStructuredTMBackedKarpReduction_of_binary_arithmetic_witnesses
    (hRowShift :
      TMPolyTimeMap
        intRowBinaryStructuredEncodedType
        EncodedType.binaryNat
        rowNegativeShift)
    (hSuccLe :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        EncodedType.bool
        binaryNatSuccLeBool)
    (hCodes :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        (EncodedType.list EncodedType.binaryNat)
        compactItemCodes)
    (hTarget :
      TMPolyTimeMap
        integerProgrammingBinaryStructuredEncodedType
        EncodedType.binaryNat
        compactTargetCode) :
    TMBackedCostedReduction
      zeroOneIntegerProgrammingBinaryStructuredDecisionProblem
      knapsackBinaryStructuredDecisionProblem :=
  zeroOneIPToKnapsackBinaryStructuredTMBackedKarpReduction_of_arithmetic_witnesses
    hRowShift
    (intNatAddNonnegativeBool_tm_polytime_of_binaryNatSuccLe_witness hSuccLe)
    hCodes hTarget

end Knapsack
end Karp21
end ComplexityReduction
