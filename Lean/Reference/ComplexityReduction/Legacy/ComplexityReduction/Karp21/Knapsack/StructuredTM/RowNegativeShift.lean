import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryAddTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.StructuredTM.BinaryCompareTM

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

/-!
Direct binary TM witness for `rowNegativeShift`.

This file keeps the compact Knapsack guard arithmetic on the binary encodings:
`intNegativePart` is obtained from the binary integer sign and payload, and the
row sum is a checked typed fold whose step uses the direct binary adder.
-/

theorem binaryNatAdd_inputSize_le (a b : Nat) :
    EncodedType.binaryNat.inputSize (a + b) ≤
      EncodedType.binaryNat.inputSize a + EncodedType.binaryNat.inputSize b + 1 := by
  let sa := EncodedType.binaryNat.inputSize a
  let sb := EncodedType.binaryNat.inputSize b
  have ha : a < 2 ^ sa := by
    simpa [sa] using binaryNat_lt_two_pow_inputSize a
  have hb : b < 2 ^ sb := by
    simpa [sb] using binaryNat_lt_two_pow_inputSize b
  have hA : 2 ^ sa ≤ 2 ^ (sa + sb) := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hB : 2 ^ sb ≤ 2 ^ (sa + sb) := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  have hsumLt : a + b < 2 ^ sa + 2 ^ sb :=
    Nat.add_lt_add ha hb
  have hsumPow : 2 ^ sa + 2 ^ sb ≤ 2 ^ (sa + sb + 1) := by
    calc
      2 ^ sa + 2 ^ sb ≤ 2 ^ (sa + sb) + 2 ^ (sa + sb) :=
        Nat.add_le_add hA hB
      _ = 2 ^ (sa + sb + 1) := by
        rw [pow_succ]
        ring
  exact binaryNat_inputSize_le_of_lt_two_pow (lt_of_lt_of_le hsumLt hsumPow)

theorem intNegativePart_binaryNat_inputSize_le (z : Int) :
    EncodedType.binaryNat.inputSize (intNegativePart z) ≤
      EncodedType.binaryInt.inputSize z + 1 := by
  have hle := intNegativePart_le_two_pow_binaryInt_inputSize z
  have hlt : intNegativePart z < 2 ^ (EncodedType.binaryInt.inputSize z + 1) := by
    have hpowPos : 0 < 2 ^ EncodedType.binaryInt.inputSize z :=
      pow_pos (by decide : 0 < 2) _
    rw [pow_succ]
    nlinarith
  exact binaryNat_inputSize_le_of_lt_two_pow hlt

theorem binaryNatSucc_tm_polytime :
    TMPolyTimeMap EncodedType.binaryNat EncodedType.binaryNat Nat.succ := by
  have hPair :
      TMPolyTimeMap
        EncodedType.binaryNat
        (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun n : Nat => (n, (1 : Nat))) :=
    TMPolyTimeMap.prod_id_const EncodedType.binaryNat EncodedType.binaryNat (1 : Nat)
  have hComp := TMPolyTimeMap.comp binaryNatAdd_tm_polytime hPair
  simpa [Function.comp, Nat.succ_eq_add_one] using hComp

theorem intNegativePart_eq_sign_dispatch (z : Int) :
    intNegativePart z =
      match binaryIntSignBool z with
      | false => 0
      | true => Nat.succ (binaryIntPayload z) := by
  cases z <;> simp [intNegativePart, binaryIntSignBool, binaryIntPayload]

theorem intNegativePart_tm_polytime :
    TMPolyTimeMap
      EncodedType.binaryInt
      EncodedType.binaryNat
      intNegativePart := by
  let N := EncodedType.binaryNat
  have hBranchInput :
      TMPolyTimeMap
        EncodedType.binaryInt
        (EncodedType.prod EncodedType.bool N)
        (fun z : Int => (binaryIntSignBool z, binaryIntPayload z)) :=
    TMPolyTimeMap.prod_mk binaryIntSignBool_tm_polytime binaryIntPayload_tm_polytime
  have hFalse :
      TMPolyTimeMap N N (fun _ : Nat => (0 : Nat)) :=
    TMPolyTimeMap.const N N (0 : Nat)
  have hDispatch :
      TMPolyTimeMap
        (EncodedType.prod EncodedType.bool N)
        N
        (fun p : Bool × Nat =>
          match p.1 with
          | true => Nat.succ p.2
          | false => (0 : Nat)) :=
    Clique.boolProduct_dispatch_tm_polytime N N
      (fFalse := fun _ : Nat => (0 : Nat))
      (fTrue := Nat.succ)
      hFalse binaryNatSucc_tm_polytime
  have hComp := TMPolyTimeMap.comp hDispatch hBranchInput
  have hEq :
      intNegativePart =
        ((fun p : Bool × Nat =>
            match p.1 with
            | true => Nat.succ p.2
            | false => (0 : Nat)) ∘
          fun z : Int => (binaryIntSignBool z, binaryIntPayload z)) := by
    funext z
    rw [intNegativePart_eq_sign_dispatch z]
    by_cases h : binaryIntSignBool z <;> simp [Function.comp, h]
  simpa [N, hEq] using hComp

def rowNegativeShiftStep (p : Nat × Int) : Nat :=
  p.1 + intNegativePart p.2

theorem rowNegativeShiftStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod EncodedType.binaryNat EncodedType.binaryInt)
      EncodedType.binaryNat
      rowNegativeShiftStep := by
  let X := EncodedType.prod EncodedType.binaryNat EncodedType.binaryInt
  have hAcc : TMPolyTimeMap X EncodedType.binaryNat (fun p : Nat × Int => p.1) := by
    simpa [X] using TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryInt
  have hCoeff : TMPolyTimeMap X EncodedType.binaryInt (fun p : Nat × Int => p.2) := by
    simpa [X] using TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryInt
  have hNeg :
      TMPolyTimeMap X EncodedType.binaryNat (fun p : Nat × Int => intNegativePart p.2) := by
    have hComp := TMPolyTimeMap.comp intNegativePart_tm_polytime hCoeff
    simpa [Function.comp, X] using hComp
  have hPair :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : Nat × Int => (p.1, intNegativePart p.2)) :=
    TMPolyTimeMap.prod_mk hAcc hNeg
  have hOut := TMPolyTimeMap.comp binaryNatAdd_tm_polytime hPair
  simpa [Function.comp, rowNegativeShiftStep, X] using hOut

theorem rowNegativeShift_foldl_aux (row : List Int) (acc : Nat) :
    row.foldl (fun acc z => rowNegativeShiftStep (acc, z)) acc =
      acc + rowNegativeShift row := by
  induction row generalizing acc with
  | nil =>
      simp [rowNegativeShift]
  | cons z zs ih =>
      change List.foldl (fun acc z => rowNegativeShiftStep (acc, z))
          (rowNegativeShiftStep (acc, z)) zs =
        acc + (intNegativePart z + rowNegativeShift zs)
      rw [ih (rowNegativeShiftStep (acc, z))]
      simp [rowNegativeShiftStep]
      omega

theorem rowNegativeShift_eq_foldl (row : List Int) :
    rowNegativeShift row =
      row.foldl (fun acc z => rowNegativeShiftStep (acc, z)) 0 := by
  simpa using (rowNegativeShift_foldl_aux row 0).symm

theorem rowNegativeShiftStep_growth
    (source : List Int) (acc : Nat) (z : Int)
    (hz :
      EncodedType.binaryInt.inputSize z ≤
        intRowBinaryStructuredEncodedType.inputSize source) :
    EncodedType.binaryNat.inputSize (rowNegativeShiftStep (acc, z)) ≤
      EncodedType.binaryNat.inputSize acc +
        ((Polynomial.X + Polynomial.C 2).eval
          (intRowBinaryStructuredEncodedType.inputSize source)) := by
  have hAdd := binaryNatAdd_inputSize_le acc (intNegativePart z)
  have hNeg := intNegativePart_binaryNat_inputSize_le z
  simp [rowNegativeShiftStep, Polynomial.eval_add, Polynomial.eval_X] at ⊢
  omega

theorem rowNegativeShift_tm_polytime :
    TMPolyTimeMap
      intRowBinaryStructuredEncodedType
      EncodedType.binaryNat
      rowNegativeShift := by
  rcases rowNegativeShiftStep_tm_polytime with ⟨hStep⟩
  have hFold :
      TMPolyTimeMap
        intRowBinaryStructuredEncodedType
        EncodedType.binaryNat
        (fun row : List Int =>
          row.foldl (fun acc z => rowNegativeShiftStep (acc, z)) (0 : Nat)) := by
    refine
      TMPolyTimeMap.list_foldl_typed_growth_bounded
        EncodedType.binaryInt EncodedType.binaryNat
        rowNegativeShiftStep (0 : Nat) hStep
        (Polynomial.C 1) (Polynomial.X + Polynomial.C 2) ?_ ?_
    · intro row
      change EncodedType.binaryNat.inputSize (0 : Nat) ≤ (Polynomial.C 1).eval
        (intRowBinaryStructuredEncodedType.inputSize row)
      simp [EncodedType.inputSize, EncodedType.binaryNat]
    · intro source acc z hz
      exact rowNegativeShiftStep_growth source acc z hz
  convert hFold using 1
  funext row
  exact rowNegativeShift_eq_foldl row

theorem compactConstraintBoundNonnegativeBool_tm_polytime :
    TMPolyTimeMap
      constraintBinaryStructuredEncodedType
      EncodedType.bool
      compactConstraintBoundNonnegativeBool :=
  compactConstraintBoundNonnegativeBool_tm_polytime_of_arithmetic_witnesses
    rowNegativeShift_tm_polytime intNatAddNonnegativeBool_tm_polytime

theorem compactConstraintBoundsNonnegativeBool_tm_polytime :
    TMPolyTimeMap
      integerProgrammingBinaryStructuredEncodedType
      EncodedType.bool
      compactConstraintBoundsNonnegativeBool :=
  compactConstraintBoundsNonnegativeBool_tm_polytime_of_arithmetic_witnesses
    rowNegativeShift_tm_polytime intNatAddNonnegativeBool_tm_polytime

end Knapsack
end Karp21
end ComplexityReduction
