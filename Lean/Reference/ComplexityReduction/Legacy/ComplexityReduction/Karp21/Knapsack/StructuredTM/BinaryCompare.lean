import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryArithmetic

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

/-!
Pure bit-level specification for the binary comparison primitive needed by the
compact Knapsack guard.

The direct TM machine still needs to be supplied separately.  This file proves
the small little-endian borrow algorithm that the machine should implement.
-/

def boolBitValue (b : Bool) : Nat :=
  if b then 1 else 0

def boolBitsValue (bs : List Bool) : Nat :=
  Nat.ofDigits 2 (bs.map boolBitValue)

theorem boolBitValue_le_one (b : Bool) : boolBitValue b ≤ 1 := by
  cases b <;> simp [boolBitValue]

def binarySuccLeStep (carry borrow leftBit rightBit : Bool) : Bool × Bool :=
  let left := boolBitValue leftBit
  let right := boolBitValue rightBit
  let carryNat := boolBitValue carry
  let borrowNat := boolBitValue borrow
  let subBit := (left + carryNat) % 2
  let nextCarry := decide (2 ≤ left + carryNat)
  let nextBorrow := decide (right < subBit + borrowNat)
  (nextCarry, nextBorrow)

def binaryNatSuccLeBitsAux :
    List Bool → List Bool → Bool → Bool → Bool
  | [], [], carry, borrow =>
      decide (boolBitValue carry + boolBitValue borrow ≤ 0)
  | leftBit :: left, [], carry, borrow =>
      let next := binarySuccLeStep carry borrow leftBit false
      binaryNatSuccLeBitsAux left [] next.1 next.2
  | [], rightBit :: right, carry, borrow =>
      let next := binarySuccLeStep carry borrow false rightBit
      binaryNatSuccLeBitsAux [] right next.1 next.2
  | leftBit :: left, rightBit :: right, carry, borrow =>
      let next := binarySuccLeStep carry borrow leftBit rightBit
      binaryNatSuccLeBitsAux left right next.1 next.2

def binaryNatSuccLeBits (left right : List Bool) : Bool :=
  binaryNatSuccLeBitsAux left right true false

theorem binarySuccLeStep_spec
    (leftValue rightValue : Nat) (carry borrow leftBit rightBit : Bool) :
    let next := binarySuccLeStep carry borrow leftBit rightBit
    (boolBitValue leftBit + boolBitValue carry + boolBitValue borrow +
        2 * leftValue ≤ boolBitValue rightBit + 2 * rightValue) ↔
      leftValue + boolBitValue next.1 + boolBitValue next.2 ≤ rightValue := by
  cases carry <;> cases borrow <;> cases leftBit <;> cases rightBit <;>
    simp [binarySuccLeStep, boolBitValue] <;> omega

theorem binaryNatSuccLeBitsAux_eq_decide :
    ∀ (left right : List Bool) (carry borrow : Bool),
      binaryNatSuccLeBitsAux left right carry borrow =
        decide
          (boolBitsValue left + boolBitValue carry + boolBitValue borrow ≤
            boolBitsValue right)
  | [], [], carry, borrow => by
      cases carry <;> cases borrow <;> simp [binaryNatSuccLeBitsAux, boolBitsValue,
        boolBitValue]
  | leftBit :: left, [], carry, borrow => by
      rw [binaryNatSuccLeBitsAux]
      set next := binarySuccLeStep carry borrow leftBit false
      rw [binaryNatSuccLeBitsAux_eq_decide]
      exact Bool.decide_congr (show
        (boolBitsValue left + boolBitValue next.1 + boolBitValue next.2 ≤
            boolBitsValue []) ↔
        (boolBitsValue (leftBit :: left) + boolBitValue carry + boolBitValue borrow ≤
            boolBitsValue []) by
        cases carry <;> cases borrow <;> cases leftBit <;>
          simp [boolBitsValue, Nat.ofDigits_cons, binarySuccLeStep, boolBitValue, next])
  | [], rightBit :: right, carry, borrow => by
      rw [binaryNatSuccLeBitsAux]
      set next := binarySuccLeStep carry borrow false rightBit
      rw [binaryNatSuccLeBitsAux_eq_decide]
      exact Bool.decide_congr (show
        (boolBitsValue [] + boolBitValue next.1 + boolBitValue next.2 ≤
            boolBitsValue right) ↔
          (boolBitsValue [] + boolBitValue carry + boolBitValue borrow ≤
            boolBitsValue (rightBit :: right)) by
        cases carry <;> cases borrow <;> cases rightBit <;>
          simp [boolBitsValue, Nat.ofDigits_cons, binarySuccLeStep, boolBitValue, next] <;>
          omega)
  | leftBit :: left, rightBit :: right, carry, borrow => by
      rw [binaryNatSuccLeBitsAux]
      set next := binarySuccLeStep carry borrow leftBit rightBit
      rw [binaryNatSuccLeBitsAux_eq_decide]
      exact Bool.decide_congr (show
        (boolBitsValue left + boolBitValue next.1 + boolBitValue next.2 ≤
            boolBitsValue right) ↔
          (boolBitsValue (leftBit :: left) + boolBitValue carry + boolBitValue borrow ≤
            boolBitsValue (rightBit :: right)) by
        cases carry <;> cases borrow <;> cases leftBit <;> cases rightBit <;>
          simp [boolBitsValue, Nat.ofDigits_cons, binarySuccLeStep, boolBitValue, next] <;>
          omega)

theorem boolBitsValue_binaryNat_encode (n : Nat) :
    boolBitsValue (EncodedType.binaryNat.encode n) = n := by
  unfold boolBitsValue
  rw [show (EncodedType.binaryNat.encode n).map boolBitValue = Nat.digits 2 n by
    simpa [boolBitValue] using EncodedType.binaryNat_decode_encode n]
  exact Nat.ofDigits_digits 2 n

theorem binaryNatSuccLeBits_encode_eq (p : Nat × Nat) :
    binaryNatSuccLeBits
        (EncodedType.binaryNat.encode p.1)
        (EncodedType.binaryNat.encode p.2) =
      binaryNatSuccLeBool p := by
  rcases p with ⟨m, n⟩
  rw [binaryNatSuccLeBits, binaryNatSuccLeBitsAux_eq_decide,
    boolBitsValue_binaryNat_encode m, boolBitsValue_binaryNat_encode n]
  simp [binaryNatSuccLeBool, boolBitValue, Nat.succ_eq_add_one]

end Knapsack
end Karp21
end ComplexityReduction
