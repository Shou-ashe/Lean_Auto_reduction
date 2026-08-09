import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryCompare

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

/-!
Bit-level specification lemmas for direct binary natural addition.

The project binary natural encoding stores little-endian bits and omits high
zeroes.  These pure lemmas identify the bitwise adder with `Nat` addition; the
TM implementation lives in `BinaryAddTM`.
-/

def binaryNatAddStep (carry leftBit rightBit : Bool) : Bool × Bool :=
  let total := boolBitValue carry + boolBitValue leftBit + boolBitValue rightBit
  (decide (total % 2 = 1), decide (2 ≤ total))

def binaryNatAddRawAux :
    List Bool → List Bool → Bool → List Bool
  | [], [], carry =>
      if carry then [true] else []
  | leftBit :: left, [], carry =>
      let next := binaryNatAddStep carry leftBit false
      next.1 :: binaryNatAddRawAux left [] next.2
  | [], rightBit :: right, carry =>
      let next := binaryNatAddStep carry false rightBit
      next.1 :: binaryNatAddRawAux [] right next.2
  | leftBit :: left, rightBit :: right, carry =>
      let next := binaryNatAddStep carry leftBit rightBit
      next.1 :: binaryNatAddRawAux left right next.2

def binaryNatAddRaw (left right : List Bool) : List Bool :=
  binaryNatAddRawAux left right false

def binaryTrimRev : List Bool → List Bool
  | [] => []
  | false :: rest => binaryTrimRev rest
  | true :: rest => (true :: rest).reverse

def binaryNatAddBits (left right : List Bool) : List Bool :=
  binaryTrimRev (binaryNatAddRaw left right).reverse

def boolBitsCanonical (bs : List Bool) : Prop :=
  bs = [] ∨ ∃ pref, bs = pref ++ [true]

theorem binaryNatAddStep_spec
    (leftValue rightValue : Nat) (carry leftBit rightBit : Bool) :
    let next := binaryNatAddStep carry leftBit rightBit
    boolBitValue next.1 + 2 * (leftValue + rightValue + boolBitValue next.2) =
      boolBitValue leftBit + boolBitValue rightBit + boolBitValue carry +
        2 * (leftValue + rightValue) := by
  cases carry <;> cases leftBit <;> cases rightBit <;>
    simp [binaryNatAddStep, boolBitValue] <;> omega

theorem binaryNatAddRawAux_value :
    ∀ (left right : List Bool) (carry : Bool),
      boolBitsValue (binaryNatAddRawAux left right carry) =
        boolBitsValue left + boolBitsValue right + boolBitValue carry
  | [], [], carry => by
      cases carry <;> simp [binaryNatAddRawAux, boolBitsValue, boolBitValue,
        Nat.ofDigits_cons]
  | leftBit :: left, [], carry => by
      rw [binaryNatAddRawAux]
      set next := binaryNatAddStep carry leftBit false
      have hTail := binaryNatAddRawAux_value left [] next.2
      have hStep := binaryNatAddStep_spec (boolBitsValue left) (boolBitsValue []) carry
        leftBit false
      cases carry <;> cases leftBit <;>
        simp [binaryNatAddStep, boolBitValue, boolBitsValue, Nat.ofDigits_cons, next]
          at hTail hStep ⊢ <;>
        omega
  | [], rightBit :: right, carry => by
      rw [binaryNatAddRawAux]
      set next := binaryNatAddStep carry false rightBit
      have hTail := binaryNatAddRawAux_value [] right next.2
      have hStep := binaryNatAddStep_spec (boolBitsValue []) (boolBitsValue right) carry
        false rightBit
      cases carry <;> cases rightBit <;>
        simp [binaryNatAddStep, boolBitValue, boolBitsValue, Nat.ofDigits_cons, next]
          at hTail hStep ⊢ <;>
        omega
  | leftBit :: left, rightBit :: right, carry => by
      rw [binaryNatAddRawAux]
      set next := binaryNatAddStep carry leftBit rightBit
      have hTail := binaryNatAddRawAux_value left right next.2
      have hStep := binaryNatAddStep_spec (boolBitsValue left) (boolBitsValue right) carry
        leftBit rightBit
      cases carry <;> cases leftBit <;> cases rightBit <;>
        simp [binaryNatAddStep, boolBitValue, boolBitsValue, Nat.ofDigits_cons, next]
          at hTail hStep ⊢ <;>
        omega

theorem binaryNatAddRaw_value (left right : List Bool) :
    boolBitsValue (binaryNatAddRaw left right) =
      boolBitsValue left + boolBitsValue right := by
  simpa [binaryNatAddRaw, boolBitValue] using binaryNatAddRawAux_value left right false

theorem boolBitsValue_append_false (bs : List Bool) :
    boolBitsValue (bs ++ [false]) = boolBitsValue bs := by
  unfold boolBitsValue
  rw [List.map_append]
  simp [boolBitValue, Nat.ofDigits_append_zero]

theorem binaryTrimRev_value (rev : List Bool) :
    boolBitsValue (binaryTrimRev rev) = boolBitsValue rev.reverse := by
  induction rev with
  | nil =>
      simp [binaryTrimRev, boolBitsValue]
  | cons bit rest ih =>
      cases bit
      · simp [binaryTrimRev, ih, boolBitsValue_append_false]
      · simp [binaryTrimRev]

theorem binaryTrimRev_canonical (rev : List Bool) :
    boolBitsCanonical (binaryTrimRev rev) := by
  induction rev with
  | nil =>
      simp [binaryTrimRev, boolBitsCanonical]
  | cons bit rest ih =>
      cases bit
      · simpa [binaryTrimRev] using ih
      · right
        exact ⟨rest.reverse, by simp [binaryTrimRev]⟩

theorem binaryNat_encode_eq_of_canonical
    (bs : List Bool) (hCanon : boolBitsCanonical bs) :
    EncodedType.binaryNat.encode (boolBitsValue bs) = bs := by
  rcases hCanon with rfl | ⟨pref, rfl⟩
  · simp [EncodedType.binaryNat, boolBitsValue, Nat.digits_zero]
  · unfold EncodedType.binaryNat boolBitsValue
    have hDigits :
        Nat.digits 2 (Nat.ofDigits 2 ((pref ++ [true]).map boolBitValue)) =
          (pref ++ [true]).map boolBitValue := by
      refine Nat.digits_ofDigits 2 (by decide) _ ?_ ?_
      · intro d hd
        rcases List.mem_map.mp hd with ⟨b, _hb, rfl⟩
        cases b <;> simp [boolBitValue]
      · intro hne
        simp [boolBitValue]
    change
      (Nat.digits 2 (Nat.ofDigits 2 ((pref ++ [true]).map boolBitValue))).map
          (fun d => decide (d = 1)) =
        pref ++ [true]
    rw [hDigits]
    have hMap : ∀ bs : List Bool,
        (bs.map boolBitValue).map (fun d => decide (d = 1)) = bs := by
      intro bs
      induction bs with
      | nil =>
          simp
      | cons bit bs ih =>
          cases bit <;> simp [boolBitValue, ih]
    simpa using hMap (pref ++ [true])

theorem binaryNatAddBits_encode_eq (p : Nat × Nat) :
    binaryNatAddBits
        (EncodedType.binaryNat.encode p.1)
        (EncodedType.binaryNat.encode p.2) =
      EncodedType.binaryNat.encode (p.1 + p.2) := by
  rcases p with ⟨m, n⟩
  have hValue :
      boolBitsValue
          (binaryNatAddBits (EncodedType.binaryNat.encode m)
            (EncodedType.binaryNat.encode n)) =
        m + n := by
    rw [binaryNatAddBits, binaryTrimRev_value, List.reverse_reverse,
      binaryNatAddRaw_value, boolBitsValue_binaryNat_encode,
      boolBitsValue_binaryNat_encode]
  have hCanon :
      boolBitsCanonical
        (binaryNatAddBits (EncodedType.binaryNat.encode m)
          (EncodedType.binaryNat.encode n)) := by
    exact binaryTrimRev_canonical (binaryNatAddRaw
      (EncodedType.binaryNat.encode m) (EncodedType.binaryNat.encode n)).reverse
  have hEncode :=
    binaryNat_encode_eq_of_canonical
      (binaryNatAddBits (EncodedType.binaryNat.encode m)
        (EncodedType.binaryNat.encode n))
      hCanon
  rw [hValue] at hEncode
  exact hEncode.symm

end Knapsack
end Karp21
end ComplexityReduction
