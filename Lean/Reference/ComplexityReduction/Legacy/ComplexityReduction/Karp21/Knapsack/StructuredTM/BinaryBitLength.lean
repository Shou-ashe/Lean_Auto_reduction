import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryBitsList
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Satisfiability.Encoding

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

/-!
Unary bit-length witness for `binaryNat`.

This is a small fuel primitive for later binary multiplication folds: it counts
the raw bits of a binary natural after `binaryNatBitsList` has converted them to
the typed list encoding.
-/

def boolListLengthFoldStep (p : Nat × Bool) : Nat :=
  p.1.succ

def boolListLengthFold (bits : List Bool) : Nat :=
  bits.foldl (fun acc bit => boolListLengthFoldStep (acc, bit)) 0

theorem boolListLengthFold_eq_length_from (bits : List Bool) (acc : Nat) :
    bits.foldl (fun acc bit => boolListLengthFoldStep (acc, bit)) acc =
      acc + bits.length := by
  induction bits generalizing acc with
  | nil =>
      simp
  | cons bit bits ih =>
      change bits.foldl (fun acc bit => boolListLengthFoldStep (acc, bit))
          (boolListLengthFoldStep (acc, bit)) =
        acc + (bit :: bits).length
      rw [ih]
      simp [boolListLengthFoldStep, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm]

theorem boolListLengthFold_eq_length (bits : List Bool) :
    boolListLengthFold bits = bits.length := by
  unfold boolListLengthFold
  simpa using boolListLengthFold_eq_length_from bits 0

theorem boolListLengthFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.nat EncodedType.bool)
      EncodedType.nat
      boolListLengthFoldStep := by
  let X := EncodedType.prod EncodedType.nat EncodedType.bool
  have hAcc : TMPolyTimeMap X EncodedType.nat (fun p : Nat × Bool => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.nat EncodedType.bool
  have hSucc := TMPolyTimeMap.comp natSuccTMBackedMap.tm_polytime hAcc
  simpa [Function.comp, boolListLengthFoldStep, X] using hSucc

theorem boolListLengthFold_tm_polytime :
    TMPolyTimeMap
      (EncodedType.list EncodedType.bool)
      EncodedType.nat
      boolListLengthFold := by
  rcases boolListLengthFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      EncodedType.bool EncodedType.nat boolListLengthFoldStep (0 : Nat) hStep
      (Polynomial.C 1) (Polynomial.C 1) ?_ ?_
  · intro bits
    simp [EncodedType.inputSize, EncodedType.nat]
  · intro source acc bit _hbit
    simp [boolListLengthFoldStep, EncodedType.inputSize, EncodedType.nat]

def binaryNatBitLength (n : Nat) : Nat :=
  (EncodedType.binaryNat.encode n).length

theorem binaryNatBitLength_eq_bitsListLength (n : Nat) :
    boolListLengthFold (binaryNatBitsList n) = binaryNatBitLength n := by
  simpa [binaryNatBitLength, binaryNatBitsList] using
    boolListLengthFold_eq_length (binaryNatBitsList n)

theorem binaryNatBitLength_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryNat
      EncodedType.nat
      binaryNatBitLength := by
  have hComp := TMPolyTimeMap.comp boolListLengthFold_tm_polytime binaryNatBitsList_tm_polytime
  convert hComp using 1
  funext n
  exact (binaryNatBitLength_eq_bitsListLength n).symm

end Knapsack
end Karp21
end ComplexityReduction
