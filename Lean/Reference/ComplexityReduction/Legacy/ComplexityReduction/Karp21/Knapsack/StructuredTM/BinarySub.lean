import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryAdd

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

/-!
Bit-level specification for binary natural subtraction.

The TM witness will use the same little-endian scan discipline as the binary
adder: emit raw low-to-high bits into a reverse stack, then trim high zeroes.
If the final borrow is set, the truncated natural subtraction is zero.
-/

def binaryNatSubStep (borrow leftBit rightBit : Bool) : Bool × Bool :=
  let left := boolBitValue leftBit
  let right := boolBitValue rightBit + boolBitValue borrow
  (decide ((left + 2 - right) % 2 = 1), decide (left < right))

def binaryNatSubRawAux :
    List Bool → List Bool → Bool → Bool × List Bool
  | [], [], borrow =>
      (borrow, [])
  | leftBit :: left, [], borrow =>
      let next := binaryNatSubStep borrow leftBit false
      let tail := binaryNatSubRawAux left [] next.2
      (tail.1, next.1 :: tail.2)
  | [], rightBit :: right, borrow =>
      let next := binaryNatSubStep borrow false rightBit
      let tail := binaryNatSubRawAux [] right next.2
      (tail.1, next.1 :: tail.2)
  | leftBit :: left, rightBit :: right, borrow =>
      let next := binaryNatSubStep borrow leftBit rightBit
      let tail := binaryNatSubRawAux left right next.2
      (tail.1, next.1 :: tail.2)

def binaryNatSubRaw (left right : List Bool) : Bool × List Bool :=
  binaryNatSubRawAux left right false

def binaryNatSubBits (left right : List Bool) : List Bool :=
  let raw := binaryNatSubRaw left right
  if raw.1 then [] else binaryTrimRev raw.2.reverse

theorem binaryNatSubStep_spec (borrow leftBit rightBit : Bool) :
    let next := binaryNatSubStep borrow leftBit rightBit
    boolBitValue next.1 + boolBitValue rightBit + boolBitValue borrow =
      boolBitValue leftBit + 2 * boolBitValue next.2 := by
  cases borrow <;> cases leftBit <;> cases rightBit <;>
    simp [binaryNatSubStep, boolBitValue]

theorem binaryNatSubRawAux_length :
    ∀ (left right : List Bool) (borrow : Bool),
      (binaryNatSubRawAux left right borrow).2.length = max left.length right.length
  | [], [], borrow => by
      simp [binaryNatSubRawAux]
  | leftBit :: left, [], borrow => by
      rw [binaryNatSubRawAux]
      set next := binaryNatSubStep borrow leftBit false
      set tail := binaryNatSubRawAux left [] next.2
      simp [tail, binaryNatSubRawAux_length left [] next.2]
  | [], rightBit :: right, borrow => by
      rw [binaryNatSubRawAux]
      set next := binaryNatSubStep borrow false rightBit
      set tail := binaryNatSubRawAux [] right next.2
      simp [tail, binaryNatSubRawAux_length [] right next.2]
  | leftBit :: left, rightBit :: right, borrow => by
      rw [binaryNatSubRawAux]
      set next := binaryNatSubStep borrow leftBit rightBit
      set tail := binaryNatSubRawAux left right next.2
      simp [tail, binaryNatSubRawAux_length left right next.2]

theorem boolBitsValue_lt_two_pow_length (bs : List Bool) :
    boolBitsValue bs < 2 ^ bs.length := by
  unfold boolBitsValue
  have hDigits : ∀ digit ∈ bs.map boolBitValue, digit < 2 := by
    intro digit hdigit
    rcases List.mem_map.mp hdigit with ⟨b, _hb, rfl⟩
    cases b <;> simp [boolBitValue]
  simpa using Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2) hDigits

theorem binaryNatSubRawAux_value :
    ∀ (left right : List Bool) (borrow : Bool),
      let raw := binaryNatSubRawAux left right borrow
      boolBitsValue raw.2 + boolBitsValue right + boolBitValue borrow =
        boolBitsValue left +
          2 ^ max left.length right.length * boolBitValue raw.1
  | [], [], borrow => by
      cases borrow <;> simp [binaryNatSubRawAux, boolBitsValue, boolBitValue]
  | leftBit :: left, [], borrow => by
      rw [binaryNatSubRawAux]
      set next := binaryNatSubStep borrow leftBit false
      rcases hTailPair : binaryNatSubRawAux left [] next.2 with ⟨final, bits⟩
      have hTail := binaryNatSubRawAux_value left [] next.2
      rw [hTailPair] at hTail
      cases borrow <;> cases leftBit <;> cases final <;>
        simp [binaryNatSubStep, boolBitsValue, Nat.ofDigits_cons, boolBitValue,
          next, pow_succ] at hTail ⊢ <;>
        omega
  | [], rightBit :: right, borrow => by
      rw [binaryNatSubRawAux]
      set next := binaryNatSubStep borrow false rightBit
      rcases hTailPair : binaryNatSubRawAux [] right next.2 with ⟨final, bits⟩
      have hTail := binaryNatSubRawAux_value [] right next.2
      rw [hTailPair] at hTail
      cases borrow <;> cases rightBit <;> cases final <;>
        simp [binaryNatSubStep, boolBitsValue, Nat.ofDigits_cons, boolBitValue,
          next, pow_succ] at hTail ⊢ <;>
        omega
  | leftBit :: left, rightBit :: right, borrow => by
      rw [binaryNatSubRawAux]
      set next := binaryNatSubStep borrow leftBit rightBit
      rcases hTailPair : binaryNatSubRawAux left right next.2 with ⟨final, bits⟩
      have hTail := binaryNatSubRawAux_value left right next.2
      rw [hTailPair] at hTail
      cases borrow <;> cases leftBit <;> cases rightBit <;> cases final <;>
        simp [binaryNatSubStep, boolBitsValue, Nat.ofDigits_cons, boolBitValue,
          next, pow_succ] at hTail ⊢ <;>
        omega

theorem binaryNatSubRaw_value (left right : List Bool) :
    let raw := binaryNatSubRaw left right
    boolBitsValue raw.2 + boolBitsValue right =
      boolBitsValue left +
        2 ^ max left.length right.length * boolBitValue raw.1 := by
  simpa [binaryNatSubRaw, boolBitValue] using binaryNatSubRawAux_value left right false

theorem binaryNatSubRaw_no_borrow_value
    {left right : List Bool} (hBorrow : (binaryNatSubRaw left right).1 = false) :
    boolBitsValue (binaryNatSubRaw left right).2 =
      boolBitsValue left - boolBitsValue right := by
  have hValue := binaryNatSubRaw_value left right
  have hEq :
      boolBitsValue (binaryNatSubRaw left right).2 + boolBitsValue right =
        boolBitsValue left := by
    simpa [hBorrow, boolBitValue] using hValue
  rw [← hEq]
  exact (Nat.add_sub_cancel (boolBitsValue (binaryNatSubRaw left right).2)
    (boolBitsValue right)).symm

theorem binaryNatSubRaw_borrow_lt
    {left right : List Bool} (hBorrow : (binaryNatSubRaw left right).1 = true) :
    boolBitsValue left < boolBitsValue right := by
  have hValue := binaryNatSubRaw_value left right
  have hRawLt :
      boolBitsValue (binaryNatSubRaw left right).2 <
        2 ^ max left.length right.length := by
    have hLen :
        (binaryNatSubRaw left right).2.length = max left.length right.length := by
      simpa [binaryNatSubRaw] using binaryNatSubRawAux_length left right false
    have h := boolBitsValue_lt_two_pow_length (binaryNatSubRaw left right).2
    rw [hLen] at h
    exact h
  simp [hBorrow, boolBitValue] at hValue
  omega

theorem binaryNatSubBits_value (left right : List Bool) :
    boolBitsValue (binaryNatSubBits left right) =
      boolBitsValue left - boolBitsValue right := by
  unfold binaryNatSubBits
  by_cases hBorrow : (binaryNatSubRaw left right).1 = true
  · simp [hBorrow]
    exact
      (Nat.sub_eq_zero_of_le
        (Nat.le_of_lt (binaryNatSubRaw_borrow_lt hBorrow))).symm
  · have hBorrowFalse : (binaryNatSubRaw left right).1 = false := by
      cases h : (binaryNatSubRaw left right).1
      · rfl
      · exact False.elim (hBorrow h)
    simp [hBorrowFalse, binaryTrimRev_value, binaryNatSubRaw_no_borrow_value hBorrowFalse]

theorem binaryNatSubBits_canonical (left right : List Bool) :
    boolBitsCanonical (binaryNatSubBits left right) := by
  unfold binaryNatSubBits
  by_cases hBorrow : (binaryNatSubRaw left right).1 = true
  · simp [hBorrow, boolBitsCanonical]
  · have hBorrowFalse : (binaryNatSubRaw left right).1 = false := by
      cases h : (binaryNatSubRaw left right).1
      · rfl
      · exact False.elim (hBorrow h)
    simp [hBorrowFalse]
    exact binaryTrimRev_canonical (binaryNatSubRaw left right).2.reverse

theorem binaryNatSubBits_encode_eq (p : Nat × Nat) :
    binaryNatSubBits
        (EncodedType.binaryNat.encode p.1)
        (EncodedType.binaryNat.encode p.2) =
      EncodedType.binaryNat.encode (p.1 - p.2) := by
  rcases p with ⟨m, n⟩
  have hValue :
      boolBitsValue
          (binaryNatSubBits (EncodedType.binaryNat.encode m)
            (EncodedType.binaryNat.encode n)) =
        m - n := by
    rw [binaryNatSubBits_value, boolBitsValue_binaryNat_encode,
      boolBitsValue_binaryNat_encode]
  have hCanon :
      boolBitsCanonical
        (binaryNatSubBits (EncodedType.binaryNat.encode m)
          (EncodedType.binaryNat.encode n)) :=
    binaryNatSubBits_canonical (EncodedType.binaryNat.encode m)
      (EncodedType.binaryNat.encode n)
  have hEncode :=
    binaryNat_encode_eq_of_canonical
      (binaryNatSubBits (EncodedType.binaryNat.encode m)
        (EncodedType.binaryNat.encode n))
      hCanon
  rw [hValue] at hEncode
  exact hEncode.symm

end Knapsack
end Karp21
end ComplexityReduction
