import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.Part3

namespace ComplexityReduction
namespace Karp21
namespace Knapsack
open ComplexityReduction.Combinatorics

theorem nat_le_two_pow_self (n : Nat) :
    n ≤ 2 ^ n := by
  cases n with
  | zero =>
      simp
  | succ n =>
      exact nat_succ_le_two_pow_succ n

theorem compactVariableItemDigitVectors_length (I : IntegerProgrammingInput) :
    (compactVariableItemDigitVectors I).length = 2 * varBound I := by
  simp [compactVariableItemDigitVectors, List.length_flatMap, Nat.mul_comm]

theorem compactSlackItemDigitVectorsForConstraint_length
    (I : IntegerProgrammingInput) (rowIndex : Nat) (constraint : List Int × Int) :
    (compactSlackItemDigitsForConstraint I rowIndex constraint).length =
      compactSlackBitCount constraint := by
  simp [compactSlackItemDigitsForConstraint, compactSlackPowers_length]

theorem compactSlackItemDigitVectorsFrom_length_le
    (I : IntegerProgrammingInput) {constraints : List (List Int × Int)} (rowIndex : Nat)
    (hsubset : ∀ constraint ∈ constraints, constraint ∈ I.constraints) :
    (compactSlackItemDigitVectorsFrom I rowIndex constraints).length ≤
      constraints.length * (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) := by
  induction constraints generalizing rowIndex with
  | nil =>
      simp [compactSlackItemDigitVectorsFrom]
  | cons constraint constraints ih =>
      have hHead :=
        compactSlackBitCount_le_two_mul_source_add_two (hsubset constraint (by simp))
      have hsubsetTail : ∀ tailConstraint ∈ constraints, tailConstraint ∈ I.constraints := by
        intro tailConstraint htail
        exact hsubset tailConstraint (by simp [htail])
      have hTail := ih (rowIndex + 1) hsubsetTail
      calc
        (compactSlackItemDigitVectorsFrom I rowIndex (constraint :: constraints)).length
            =
              compactSlackBitCount constraint +
                (compactSlackItemDigitVectorsFrom I (rowIndex + 1) constraints).length := by
              simp [compactSlackItemDigitVectorsFrom,
                compactSlackItemDigitVectorsForConstraint_length]
        _ ≤ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) +
              constraints.length *
                (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) := by
              exact Nat.add_le_add hHead hTail
        _ = (constraint :: constraints).length *
              (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) := by
              simp [Nat.succ_mul, Nat.add_comm, Nat.add_assoc]

theorem compactSlackItemDigitVectors_length_le
    (I : IntegerProgrammingInput) :
    (compactSlackItemDigitVectors I).length ≤
      I.constraints.length * (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) :=
  compactSlackItemDigitVectorsFrom_length_le I 0
    (by intro constraint hconstraint; exact hconstraint)

theorem compactItemDigitVectors_length_le_source_poly
    (I : IntegerProgrammingInput) :
    (compactItemDigitVectors I).length ≤
      4 * (integerProgrammingBinaryStructuredEncodedType.inputSize I + 1) ^ 2 := by
  let S := integerProgrammingBinaryStructuredEncodedType.inputSize I
  have hVar := varBound_le_binaryStructured_inputSize I
  have hRows := constraints_length_le_binaryStructured_inputSize I
  have hSlack := compactSlackItemDigitVectors_length_le I
  have hLen :
      (compactItemDigitVectors I).length ≤
        2 * S + S * (2 * S + 2) := by
    rw [compactItemDigitVectors, List.length_append]
    rw [compactVariableItemDigitVectors_length]
    have hSlackS :
        (compactSlackItemDigitVectors I).length ≤ S * (2 * S + 2) := by
      exact hSlack.trans (Nat.mul_le_mul_right (2 * S + 2) hRows)
    exact Nat.add_le_add (Nat.mul_le_mul_left 2 hVar)
      (by simpa [S] using hSlackS)
  have hPoly : 2 * S + S * (2 * S + 2) ≤ 4 * (S + 1) ^ 2 := by
    nlinarith
  exact hLen.trans (by simpa [S] using hPoly)

theorem two_pow_add_two_lt_two_pow_add_two (n : Nat) :
    2 ^ n + 2 < 2 ^ (n + 2) := by
  have hpos : 1 ≤ 2 ^ n := one_le_two_pow n
  calc
    2 ^ n + 2 ≤ 2 ^ n + 2 * 2 ^ n := by omega
    _ = 3 * 2 ^ n := by ring
    _ < 4 * 2 ^ n := by nlinarith
    _ = 2 ^ (n + 2) := by
        rw [Nat.pow_add]
        norm_num
        ring

theorem compactBase_lt_two_pow_source_poly
    (I : IntegerProgrammingInput) :
    compactBase I <
      2 ^ (16 * (integerProgrammingBinaryStructuredEncodedType.inputSize I + 1) ^ 4) := by
  let S := integerProgrammingBinaryStructuredEncodedType.inputSize I
  let E := 2 ^ (2 * S + 2)
  let D := compactDigitCount I
  let N := (compactItemDigitVectors I).length
  have hTarget := compactTargetDigits_sum_le_digitCount_mul_entryBound I
  have hMass := compactDigitVectorsMass_le_length_mul_digitCount_mul_entryBound I
  have hBase :
      compactBase I ≤ (N + 1) * D * E + 2 := by
    simp [compactBase, N, D, E] at hTarget hMass ⊢
    nlinarith
  have hD : D ≤ 2 * S := by
    simpa [D, S] using compactDigitCount_le_two_mul_binaryStructured_inputSize I
  have hN : N ≤ 4 * (S + 1) ^ 2 := by
    simpa [N, S] using compactItemDigitVectors_length_le_source_poly I
  let A := 4 * (S + 1) ^ 2 + 1
  let M := A + 2 * S + (2 * S + 2)
  have hNpow : N + 1 ≤ 2 ^ A := by
    have hNA : N + 1 ≤ A := by omega
    exact hNA.trans (nat_le_two_pow_self A)
  have hDpow : D ≤ 2 ^ (2 * S) := by
    exact hD.trans (nat_le_two_pow_self (2 * S))
  have hProdPow : (N + 1) * D * E ≤ 2 ^ M := by
    calc
      (N + 1) * D * E ≤ 2 ^ A * 2 ^ (2 * S) * 2 ^ (2 * S + 2) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul hNpow hDpow) (le_rfl)
      _ = 2 ^ M := by
        rw [← Nat.pow_add, ← Nat.pow_add]
  have hBasePow : compactBase I ≤ 2 ^ M + 2 := hBase.trans (Nat.add_le_add_right hProdPow 2)
  have hMPow : 2 ^ M + 2 < 2 ^ (M + 2) := two_pow_add_two_lt_two_pow_add_two M
  have hExp :
      M + 2 ≤ 16 * (S + 1) ^ 4 := by
    let T := (S + 1) ^ 2
    have hSleT : S ≤ T := by
      dsimp [T]
      nlinarith
    have hOneT : 1 ≤ T := by
      dsimp [T]
      nlinarith
    calc
      M + 2 = 4 * T + 4 * S + 5 := by
        dsimp [M, A, T]
        ring
      _ ≤ 4 * T + 4 * T + 5 * T := by
        nlinarith
      _ = 13 * T := by ring
      _ ≤ 16 * T * T := by nlinarith
      _ = 16 * (S + 1) ^ 4 := by
        dsimp [T]
        ring
  simpa [S] using
    (lt_of_le_of_lt hBasePow
      ((hMPow).trans_le (pow_two_le_pow_two_of_le hExp)))

def compactBaseBitBound (I : IntegerProgrammingInput) : Nat :=
  16 * (integerProgrammingBinaryStructuredEncodedType.inputSize I + 1) ^ 4

def compactCodeBitBound (I : IntegerProgrammingInput) : Nat :=
  compactBaseBitBound I * compactDigitCount I

theorem binaryNat_inputSize_le_of_lt_two_pow {n k : Nat} (h : n < 2 ^ k) :
    EncodedType.binaryNat.inputSize n ≤ k := by
  change ((Nat.digits 2 n).map fun d => decide (d = 1)).length ≤ k
  rw [List.length_map]
  exact (Nat.digits_length_le_iff (by decide : 1 < 2) n).2 h

theorem compactDigitCode_binaryNat_inputSize_le
    (I : IntegerProgrammingInput) {digits : List Nat}
    (hLength : digits.length = compactDigitCount I)
    (hDigits : ∀ digit ∈ digits, digit < compactBase I) :
    EncodedType.binaryNat.inputSize (compactDigitCode I digits) ≤
      compactCodeBitBound I := by
  have hCodeBase :
      compactDigitCode I digits < (compactBase I) ^ digits.length := by
    simpa [compactDigitCode] using
      Nat.ofDigits_lt_base_pow_length (compactBase_gt_one I) hDigits
  have hBaseLe : compactBase I ≤ 2 ^ compactBaseBitBound I := by
    exact Nat.le_of_lt (by
      simpa [compactBaseBitBound] using compactBase_lt_two_pow_source_poly I)
  have hPowLe :
      (compactBase I) ^ digits.length ≤
        (2 ^ compactBaseBitBound I) ^ digits.length :=
    Nat.pow_le_pow_left hBaseLe digits.length
  have hCodePow :
      compactDigitCode I digits < 2 ^ (compactBaseBitBound I * compactDigitCount I) := by
    calc
      compactDigitCode I digits < (compactBase I) ^ digits.length := hCodeBase
      _ ≤ (2 ^ compactBaseBitBound I) ^ digits.length := hPowLe
      _ = 2 ^ (compactBaseBitBound I * compactDigitCount I) := by
          rw [hLength]
          rw [Nat.pow_mul]
  exact binaryNat_inputSize_le_of_lt_two_pow (by
    simpa [compactCodeBitBound] using hCodePow)

theorem compactItemCode_binaryNat_inputSize_le
    {I : IntegerProgrammingInput} {code : Nat}
    (hcode : code ∈ compactItemCodes I) :
    EncodedType.binaryNat.inputSize code ≤ compactCodeBitBound I := by
  rcases List.mem_map.mp hcode with ⟨digits, hdigits, rfl⟩
  exact compactDigitCode_binaryNat_inputSize_le I
    (compactItemDigitVectors_mem_length hdigits)
    (by
      intro digit hdigit
      exact compactItemDigit_lt_base hdigits hdigit)

theorem compactTargetCode_binaryNat_inputSize_le
    (I : IntegerProgrammingInput) :
    EncodedType.binaryNat.inputSize (compactTargetCode I) ≤ compactCodeBitBound I :=
  compactDigitCode_binaryNat_inputSize_le I
    (compactTargetDigits_length I)
    (by
      intro digit hdigit
      exact compactTargetDigit_lt_base hdigit)

theorem integerProgrammingBinaryStructured_inputSize_pos (I : IntegerProgrammingInput) :
    0 < integerProgrammingBinaryStructuredEncodedType.inputSize I := by
  rw [integerProgrammingBinaryStructured_inputSize_eq]
  omega

theorem compactCodeBitBound_le_source_poly
    (I : IntegerProgrammingInput) :
    compactCodeBitBound I ≤
      32 * (integerProgrammingBinaryStructuredEncodedType.inputSize I + 1) ^ 5 := by
  let S := integerProgrammingBinaryStructuredEncodedType.inputSize I
  have hD : compactDigitCount I ≤ 2 * S := by
    simpa [S] using compactDigitCount_le_two_mul_binaryStructured_inputSize I
  have hS : S ≤ S + 1 := by omega
  calc
    compactCodeBitBound I
        = 16 * (S + 1) ^ 4 * compactDigitCount I := by
            simp [compactCodeBitBound, compactBaseBitBound, S]
    _ ≤ 16 * (S + 1) ^ 4 * (2 * S) := by
            exact Nat.mul_le_mul_left (16 * (S + 1) ^ 4) hD
    _ ≤ 16 * (S + 1) ^ 4 * (2 * (S + 1)) := by
            exact Nat.mul_le_mul_left (16 * (S + 1) ^ 4)
              (Nat.mul_le_mul_left 2 hS)
    _ = 32 * (S + 1) ^ 5 := by ring

theorem knapsackBinaryStructured_inputSize_eq (K : KnapsackInput) :
    knapsackBinaryStructuredEncodedType.inputSize K =
      knapsackItemListBinaryStructuredEncodedType.inputSize K.items + 1 +
        (EncodedType.binaryNat.inputSize K.capacity + 1 +
          EncodedType.binaryNat.inputSize K.targetValue) := by
  change knapsackTupleBinaryStructuredEncodedType.inputSize
      (K.items, (K.capacity, K.targetValue)) =
    knapsackItemListBinaryStructuredEncodedType.inputSize K.items + 1 +
      (EncodedType.binaryNat.inputSize K.capacity + 1 +
        EncodedType.binaryNat.inputSize K.targetValue)
  simp [knapsackTupleBinaryStructuredEncodedType, knapsackBoundsBinaryStructuredEncodedType]

theorem compactItems_length (I : IntegerProgrammingInput) :
    (compactItems I).length = (compactItemDigitVectors I).length := by
  simp [compactItems, compactItemCodes]

theorem compactItem_binaryStructured_inputSize_le
    {I : IntegerProgrammingInput} {item : Nat × Nat}
    (hitem : item ∈ compactItems I) :
    knapsackItemBinaryStructuredEncodedType.inputSize item ≤
      2 * compactCodeBitBound I + 1 := by
  rcases List.mem_map.mp hitem with ⟨code, hcode, rfl⟩
  have hCode := compactItemCode_binaryNat_inputSize_le hcode
  simp [knapsackItemBinaryStructuredEncodedType]
  omega

theorem compactItems_binaryStructured_inputSize_le
    (I : IntegerProgrammingInput) :
    knapsackItemListBinaryStructuredEncodedType.inputSize (compactItems I) ≤
      (compactItemDigitVectors I).length * (2 * compactCodeBitBound I + 2) := by
  have hList :=
    Clique.encodedList_inputSize_le_length_mul_bound knapsackItemBinaryStructuredEncodedType
      (compactItems I) (2 * compactCodeBitBound I + 1)
      (by
        intro item hitem
        exact compactItem_binaryStructured_inputSize_le hitem)
  calc
    knapsackItemListBinaryStructuredEncodedType.inputSize (compactItems I)
        ≤ (compactItems I).length * (2 * compactCodeBitBound I + 1 + 1) := by
          simpa [knapsackItemListBinaryStructuredEncodedType] using hList
    _ = (compactItemDigitVectors I).length * (2 * compactCodeBitBound I + 2) := by
          rw [compactItems_length]

theorem compactMapCore_binaryStructured_inputSize_le
    (I : IntegerProgrammingInput) :
    knapsackBinaryStructuredEncodedType.inputSize (compactMapCore I) ≤
      ((compactItemDigitVectors I).length + 1) * (2 * compactCodeBitBound I + 2) := by
  have hItems := compactItems_binaryStructured_inputSize_le I
  have hTarget := compactTargetCode_binaryNat_inputSize_le I
  rw [knapsackBinaryStructured_inputSize_eq]
  simp [compactMapCore]
  calc
    knapsackItemListBinaryStructuredEncodedType.inputSize (compactItems I) + 1 +
        (EncodedType.binaryNat.inputSize (compactTargetCode I) + 1 +
          EncodedType.binaryNat.inputSize (compactTargetCode I))
        ≤ (compactItemDigitVectors I).length * (2 * compactCodeBitBound I + 2) + 1 +
            (compactCodeBitBound I + 1 + compactCodeBitBound I) := by
          omega
    _ ≤ ((compactItemDigitVectors I).length + 1) * (2 * compactCodeBitBound I + 2) := by
          ring_nf
          omega

theorem compactMapCore_binaryStructured_inputSize_le_source_poly
    (I : IntegerProgrammingInput) :
    knapsackBinaryStructuredEncodedType.inputSize (compactMapCore I) ≤
      1000 * (integerProgrammingBinaryStructuredEncodedType.inputSize I + 1) ^ 8 := by
  let S := integerProgrammingBinaryStructuredEncodedType.inputSize I
  let T := S + 1
  have hOut := compactMapCore_binaryStructured_inputSize_le I
  have hN := compactItemDigitVectors_length_le_source_poly I
  have hL := compactCodeBitBound_le_source_poly I
  have hN' : (compactItemDigitVectors I).length + 1 ≤ 5 * T ^ 2 := by
    have h : (compactItemDigitVectors I).length + 1 ≤ 4 * T ^ 2 + 1 := by
      simpa [T, S] using Nat.add_le_add_right hN 1
    have hT : 1 ≤ T ^ 2 := by
      have hT1 : 1 ≤ T := by dsimp [T]; omega
      simpa using Nat.pow_le_pow_left hT1 2
    nlinarith
  have hL' : 2 * compactCodeBitBound I + 2 ≤ 66 * T ^ 5 := by
    have h : 2 * compactCodeBitBound I + 2 ≤ 2 * (32 * T ^ 5) + 2 := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (by simpa [T, S] using hL)) 2
    have hT : 1 ≤ T ^ 5 := by
      have hT1 : 1 ≤ T := by dsimp [T]; omega
      simpa using Nat.pow_le_pow_left hT1 5
    nlinarith
  have hProduct :
      ((compactItemDigitVectors I).length + 1) * (2 * compactCodeBitBound I + 2) ≤
        (5 * T ^ 2) * (66 * T ^ 5) :=
    Nat.mul_le_mul hN' hL'
  have hPoly : (5 * T ^ 2) * (66 * T ^ 5) ≤ 1000 * T ^ 8 := by
    have hT : 1 ≤ T := by dsimp [T]; omega
    nlinarith
  exact hOut.trans (hProduct.trans (by simpa [T, S] using hPoly))

theorem compactNoKnapsackInput_binaryStructured_inputSize_le :
    knapsackBinaryStructuredEncodedType.inputSize compactNoKnapsackInput ≤ 1000 := by
  native_decide

theorem compactMap_binaryStructured_inputSize_le_source_poly_succ
    (I : IntegerProgrammingInput) :
    knapsackBinaryStructuredEncodedType.inputSize (compactMap I) ≤
      1000 * (integerProgrammingBinaryStructuredEncodedType.inputSize I + 1) ^ 8 := by
  classical
  by_cases hBounds : compactConstraintBoundsNonnegative I
  · simpa [compactMap, hBounds] using
      compactMapCore_binaryStructured_inputSize_le_source_poly I
  · have hNo := compactNoKnapsackInput_binaryStructured_inputSize_le
    have hPos : 1 ≤ (integerProgrammingBinaryStructuredEncodedType.inputSize I + 1) ^ 8 := by
      have hBase : 1 ≤ integerProgrammingBinaryStructuredEncodedType.inputSize I + 1 := by omega
      simpa using Nat.pow_le_pow_left hBase 8
    have hPoly : 1000 ≤
        1000 * (integerProgrammingBinaryStructuredEncodedType.inputSize I + 1) ^ 8 := by
      calc
        1000 = 1000 * 1 := by ring
        _ ≤ 1000 * (integerProgrammingBinaryStructuredEncodedType.inputSize I + 1) ^ 8 :=
          Nat.mul_le_mul_left 1000 hPos
    exact (by simpa [compactMap, hBounds] using hNo.trans hPoly)

theorem compactMap_binaryStructured_inputSize_le_source_poly
    (I : IntegerProgrammingInput) :
    knapsackBinaryStructuredEncodedType.inputSize (compactMap I) ≤
      256000 * (integerProgrammingBinaryStructuredEncodedType.inputSize I) ^ 8 + 1000 := by
  let S := integerProgrammingBinaryStructuredEncodedType.inputSize I
  have hSucc := compactMap_binaryStructured_inputSize_le_source_poly_succ I
  have hPos : 0 < S := by
    simpa [S] using integerProgrammingBinaryStructured_inputSize_pos I
  have hSuccLe : S + 1 ≤ 2 * S := by omega
  have hPow : (S + 1) ^ 8 ≤ (2 * S) ^ 8 :=
    Nat.pow_le_pow_left hSuccLe 8
  have hExpand : 1000 * (2 * S) ^ 8 ≤ 256000 * S ^ 8 := by
    ring_nf
    exact le_rfl
  calc
    knapsackBinaryStructuredEncodedType.inputSize (compactMap I)
        ≤ 1000 * (S + 1) ^ 8 := by simpa [S] using hSucc
    _ ≤ 1000 * (2 * S) ^ 8 := Nat.mul_le_mul_left 1000 hPow
    _ ≤ 256000 * S ^ 8 := hExpand
    _ ≤ 256000 * S ^ 8 + 1000 := by omega

theorem zeroOneIPToKnapsackCompactBinaryStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : IntegerProgrammingInput => integerProgrammingBinaryStructuredEncodedType.inputSize I)
      (fun K : KnapsackInput => knapsackBinaryStructuredEncodedType.inputSize K)
      compactMap := by
  refine PolynomialSizeBound.intro_with 8 256000 1000 ?_
  intro I
  exact compactMap_binaryStructured_inputSize_le_source_poly I

/-- Unit-item knapsack family used to encode nonempty witness lists. -/
def unitItems (m : Nat) : List (Nat × Nat) :=
  List.replicate m (1, 1)

theorem selectedWeight_unitItems_allTrue (m : Nat) :
    selectedWeight { items := unitItems m, capacity := m, targetValue := 1 }
      (List.replicate m true) = m := by
  induction m with
  | zero =>
      simp [selectedWeight, unitItems]
  | succ m ih =>
      simp [selectedWeight, unitItems]

theorem selectedValue_unitItems_allTrue (m : Nat) :
    selectedValue { items := unitItems m, capacity := m, targetValue := 1 }
      (List.replicate m true) = m := by
  induction m with
  | zero =>
      simp [selectedValue, unitItems]
  | succ m ih =>
      simp [selectedValue, unitItems]

theorem unitKnapsack_iff_pos (m : Nat) :
    Combinatorics.Knapsack { items := unitItems m, capacity := m, targetValue := 1 } ↔
      0 < m := by
  constructor
  · intro h
    cases m with
    | zero =>
        rcases h with ⟨selected, hLen, _hWeight, hValue⟩
        cases selected with
        | nil =>
            simp [selectedValue, unitItems] at hValue
        | cons b bs =>
            simp [unitItems] at hLen
    | succ m =>
        omega
  · intro hPos
    cases m with
    | zero =>
        omega
    | succ m =>
        refine ⟨List.replicate (m + 1) true, by simp [unitItems], ?_, ?_⟩
        · rw [selectedWeight_unitItems_allTrue]
        · rw [selectedValue_unitItems_allTrue]
          simp

/-- P15c syntax map from 0-1 Integer Programming to Knapsack. -/
noncomputable def map (I : IntegerProgrammingInput) : KnapsackInput :=
  { items := unitItems (satisfyingAssignments I).length
    capacity := (satisfyingAssignments I).length
    targetValue := 1 }

theorem map_correct (I : IntegerProgrammingInput) :
    zeroOneIntegerProgrammingDecisionProblem.isYes I ↔ Combinatorics.Knapsack (map I) := by
  change ZeroOneIntegerProgramming I ↔ Combinatorics.Knapsack (map I)
  rw [zeroOneIP_iff_satisfyingAssignments_pos]
  exact (unitKnapsack_iff_pos (satisfyingAssignments I).length).symm

/-! ### Textbook-style candidate-assignment violation-digit route -/

/-- Base used by the P15m no-carry violation digits. -/
def textbookBase : Nat := 2

/--
For a bounded assignment candidate, each digit records whether one source row is
violated.  A zero encoded weight is therefore exactly a row-wise satisfying
candidate.
-/
noncomputable def assignmentViolationDigits (I : IntegerProgrammingInput)
    (f : Fin (varBound I) → Bool) : List Nat := by
  classical
  exact I.constraints.map fun constraint =>
    if SatisfiesConstraint (Clique.boundedAssignment (varBound I) f) constraint then 0 else 1

/-- Base-2 encoded violation vector for one bounded assignment candidate. -/
noncomputable def assignmentViolationWeight (I : IntegerProgrammingInput)
    (f : Fin (varBound I) → Bool) : Nat :=
  Nat.ofDigits textbookBase (assignmentViolationDigits I f)

theorem assignmentViolationWeight_eq_zero_iff (I : IntegerProgrammingInput)
    (f : Fin (varBound I) → Bool) :
    assignmentViolationWeight I f = 0 ↔
      ∀ constraint ∈ I.constraints,
        SatisfiesConstraint (Clique.boundedAssignment (varBound I) f) constraint := by
  classical
  constructor
  · intro hZero constraint hConstraint
    have hDigitZero :
        (if SatisfiesConstraint (Clique.boundedAssignment (varBound I) f) constraint then
            0 else 1) = 0 := by
      exact Nat.digits_zero_of_eq_zero (by decide : textbookBase ≠ 0) hZero _
        (by
          unfold assignmentViolationDigits
          exact List.mem_map.mpr ⟨constraint, hConstraint, rfl⟩)
    by_cases hSat :
        SatisfiesConstraint (Clique.boundedAssignment (varBound I) f) constraint
    · exact hSat
    · simp [hSat] at hDigitZero
  · intro hAll
    have hDigits :
        assignmentViolationDigits I f = List.replicate I.constraints.length 0 := by
      have hMap :
          ∀ constraints : List (List Int × Int),
            (∀ constraint ∈ constraints,
              SatisfiesConstraint (Clique.boundedAssignment (varBound I) f) constraint) →
            (constraints.map fun constraint =>
              if SatisfiesConstraint (Clique.boundedAssignment (varBound I) f) constraint then
                0 else 1) = List.replicate constraints.length 0 := by
        intro constraints hConstraints
        induction constraints with
        | nil =>
            simp
        | cons constraint rest ih =>
            have hHead :
                SatisfiesConstraint (Clique.boundedAssignment (varBound I) f) constraint :=
              hConstraints constraint (by simp)
            have hTail :
                (rest.map fun constraint =>
                  if SatisfiesConstraint (Clique.boundedAssignment (varBound I) f) constraint then
                    0 else 1) = List.replicate rest.length 0 :=
              ih (by
                intro c hc
                exact hConstraints c (by simp [hc]))
            simp [hHead, hTail, List.replicate]
      simpa [assignmentViolationDigits] using hMap I.constraints hAll
    simp [assignmentViolationWeight, hDigits, Nat.ofDigits_replicate_zero]

/-- Knapsack items for every bounded assignment candidate; weight is its violation vector. -/
noncomputable def textbookItems (I : IntegerProgrammingInput) : List (Nat × Nat) :=
  (Clique.assignmentList (varBound I)).map fun f => (assignmentViolationWeight I f, 1)

/--
P15m direct digit map from 0-1 IP to Knapsack.  The target asks for at least one
assignment item of value 1 while capacity 0 forces its violation-digit weight to
be zero.
-/
noncomputable def textbookMap (I : IntegerProgrammingInput) : KnapsackInput :=
  { items := textbookItems I
    capacity := 0
    targetValue := 1 }

/-- Select exactly the entries equal to a chosen bounded assignment. -/
def assignmentSelector {n : Nat} (xs : List (Fin n → Bool))
    (f : Fin n → Bool) : List Bool :=
  xs.map fun g => decide (g = f)

theorem selector_weight_eq_zero {n : Nat} (xs : List (Fin n → Bool))
    (w : (Fin n → Bool) → Nat) (f : Fin n → Bool) (hZero : w f = 0) :
    (((xs.map fun g => (w g, 1)).zip (assignmentSelector xs f)).map
        (fun p => if p.2 then p.1.1 else 0)).sum = 0 := by
  classical
  induction xs with
  | nil =>
      simp [assignmentSelector]
  | cons g gs ih =>
      by_cases hg : g = f
      · subst g
        simpa [assignmentSelector, hZero] using ih
      · simpa [assignmentSelector, hg] using ih

theorem selector_value_pos {n : Nat} (xs : List (Fin n → Bool))
    (w : (Fin n → Bool) → Nat) (f : Fin n → Bool) (hf : f ∈ xs) :
    1 ≤ ((((xs.map fun g => (w g, 1)).zip (assignmentSelector xs f)).map
        (fun p => if p.2 then p.1.2 else 0)).sum) := by
  classical
  induction xs with
  | nil =>
      simp at hf
  | cons g gs ih =>
      by_cases hg : g = f
      · subst g
        simp [assignmentSelector]
      · have hfg : f ≠ g := by
          intro h
          exact hg h.symm
        have hfTail : f ∈ gs := by
          simpa [hfg] using hf
        have ihTail := ih hfTail
        simpa [assignmentSelector, hg] using ihTail

theorem selector_textbook_value_pos {I : IntegerProgrammingInput}
    {f : Fin (varBound I) → Bool}
    (hf : f ∈ Clique.assignmentList (varBound I)) :
    1 ≤ selectedValue (textbookMap I)
        (assignmentSelector (Clique.assignmentList (varBound I)) f) := by
  simpa [selectedValue, textbookMap, textbookItems] using
    selector_value_pos (Clique.assignmentList (varBound I)) (assignmentViolationWeight I) f hf

theorem selected_assignment_of_value_pos {α : Type} (xs : List α) (selected : List Bool)
    (w : α → Nat)
    (hValue :
      1 ≤ ((((xs.map fun x => (w x, 1)).zip selected).map
        (fun p => if p.2 then p.1.2 else 0)).sum)) :
    ∃ x, (x, true) ∈ xs.zip selected := by
  induction xs generalizing selected with
  | nil =>
      simp at hValue
  | cons x xs ih =>
      cases selected with
      | nil =>
          simp at hValue
      | cons b bs =>
          cases b
          · simp at hValue
            rcases ih bs hValue with ⟨y, hy⟩
            exact ⟨y, by simp [hy]⟩
          · exact ⟨x, by simp⟩

theorem selected_weight_zero_of_mem {α : Type} (xs : List α) (selected : List Bool)
    (w : α → Nat)
    (hWeight :
      ((((xs.map fun x => (w x, 1)).zip selected).map
        (fun p => if p.2 then p.1.1 else 0)).sum) ≤ 0)
    {x : α} (hx : (x, true) ∈ xs.zip selected) :
    w x = 0 := by
  induction xs generalizing selected with
  | nil =>
      simp at hx
  | cons y ys ih =>
      cases selected with
      | nil =>
          simp at hx
      | cons b bs =>
          cases b
          · simp at hx
            have hTailWeight :
                ((((ys.map fun x => (w x, 1)).zip bs).map
                  (fun p => if p.2 then p.1.1 else 0)).sum) ≤ 0 := by
              simpa using hWeight
            exact ih bs hTailWeight hx
          · simp at hWeight
            simp at hx
            rcases hx with hEq | hxTail
            · rcases hEq with ⟨rfl, _⟩
              exact hWeight.1
            · have hTailWeight :
                  ((((ys.map fun x => (w x, 1)).zip bs).map
                    (fun p => if p.2 then p.1.1 else 0)).sum) ≤ 0 := by
                exact Nat.le_of_eq hWeight.2
              exact ih bs hTailWeight hxTail

theorem textbookMap_correct (I : IntegerProgrammingInput) :
    zeroOneIntegerProgrammingDecisionProblem.isYes I ↔
      Combinatorics.Knapsack (textbookMap I) := by
  change ZeroOneIntegerProgramming I ↔ Combinatorics.Knapsack (textbookMap I)
  constructor
  · intro hIP
    have hPos := (zeroOneIP_iff_satisfyingAssignments_pos I).1 hIP
    cases hWitnesses : satisfyingAssignments I with
    | nil =>
        simp [hWitnesses] at hPos
    | cons f rest =>
        have hfWitness : f ∈ satisfyingAssignments I := by
          simp [hWitnesses]
        have hfCandidate :
            f ∈ Clique.assignmentList (varBound I) :=
          (mem_satisfyingAssignments_iff I f).1 hfWitness |>.1
        have hAll :
            ∀ constraint ∈ I.constraints,
              SatisfiesConstraint (Clique.boundedAssignment (varBound I) f) constraint :=
          (mem_satisfyingAssignments_iff I f).1 hfWitness |>.2
        have hWeightZero : assignmentViolationWeight I f = 0 :=
          (assignmentViolationWeight_eq_zero_iff I f).2 hAll
        refine ⟨assignmentSelector (Clique.assignmentList (varBound I)) f, ?_, ?_, ?_⟩
        · simp [textbookMap, textbookItems, assignmentSelector]
        · simpa [selectedWeight, textbookMap, textbookItems] using
            selector_weight_eq_zero (Clique.assignmentList (varBound I))
              (assignmentViolationWeight I) f hWeightZero
        · exact selector_textbook_value_pos (I := I) hfCandidate
  · rintro ⟨selected, hLen, hWeight, hValue⟩
    have hExists :
        ∃ f, (f, true) ∈ (Clique.assignmentList (varBound I)).zip selected := by
      have hValue' :
          1 ≤ ((((Clique.assignmentList (varBound I)).map fun f =>
              (assignmentViolationWeight I f, 1)).zip selected).map
            (fun p => if p.2 then p.1.2 else 0)).sum := by
        simpa [selectedValue, textbookMap, textbookItems] using hValue
      exact selected_assignment_of_value_pos (Clique.assignmentList (varBound I)) selected
        (assignmentViolationWeight I) hValue'
    rcases hExists with ⟨f, hfSelected⟩
    have hWeightZero : assignmentViolationWeight I f = 0 := by
      have hWeight' :
          ((((Clique.assignmentList (varBound I)).map fun f =>
              (assignmentViolationWeight I f, 1)).zip selected).map
            (fun p => if p.2 then p.1.1 else 0)).sum ≤ 0 := by
        simpa [selectedWeight, textbookMap, textbookItems] using hWeight
      exact selected_weight_zero_of_mem (Clique.assignmentList (varBound I)) selected
        (assignmentViolationWeight I) hWeight' hfSelected
    exact ⟨Clique.boundedAssignment (varBound I) f,
      (assignmentViolationWeight_eq_zero_iff I f).1 hWeightZero⟩

/-! ### Alternate Exact Cover to Knapsack base-digit route -/

/-- Deduplicated source-set family used by the base-digit exact-cover route. -/
def exactCoverSourceSets (I : ExactCoverInput) : List (List Nat) :=
  I.system.sets.dedup

/-- Base larger than the number of source sets, preventing carries between digits. -/
def exactCoverDigitBase (I : ExactCoverInput) : Nat :=
  I.system.sets.length + 2

/-- Count how many selected source sets contain one universe element. -/
def elementCount (x : Nat) : List (List Nat) → Nat
  | [] => 0
  | S :: sets => (if x ∈ S then 1 else 0) + elementCount x sets

/-- Digit counts for universe positions `start, ..., start + len - 1`. -/
def digitCountsFrom (start : Nat) : Nat → List (List Nat) → List Nat
  | 0, _ => []
  | len + 1, sets => elementCount start sets :: digitCountsFrom (start + 1) len sets

def exactCoverSetDigits (I : ExactCoverInput) (S : List Nat) : List Nat :=
  digitCountsFrom 0 I.system.universeSize [S]

def exactCoverDigitCounts (I : ExactCoverInput) (sets : List (List Nat)) : List Nat :=
  digitCountsFrom 0 I.system.universeSize sets

def exactCoverTargetDigits (I : ExactCoverInput) : List Nat :=
  List.replicate I.system.universeSize 1

def exactCoverSetCode (I : ExactCoverInput) (S : List Nat) : Nat :=
  Nat.ofDigits (exactCoverDigitBase I) (exactCoverSetDigits I S)

def exactCoverTargetCode (I : ExactCoverInput) : Nat :=
  Nat.ofDigits (exactCoverDigitBase I) (exactCoverTargetDigits I)

/-- Base-digit items: every source set has identical weight and value equal to its digit code. -/
def exactCoverBaseDigitItems (I : ExactCoverInput) : List (Nat × Nat) :=
  (exactCoverSourceSets I).map fun S =>
    let code := exactCoverSetCode I S
    (code, code)

/-- Karp's base-digit exact-cover-to-knapsack map for well-formed exact-cover inputs. -/
def exactCoverBaseDigitMapCore (I : ExactCoverInput) : KnapsackInput :=
  { items := exactCoverBaseDigitItems I
    capacity := exactCoverTargetCode I
    targetValue := exactCoverTargetCode I }

/-- Fixed no-instance used to guard malformed raw exact-cover encodings. -/
def exactCoverNoKnapsackInput : KnapsackInput :=
  { items := []
    capacity := 0
    targetValue := 1 }

/--
Karp's base-digit exact-cover-to-knapsack map, retained as an alternate checked route.
The guard is necessary because the raw local encoding is `List Nat`; Karp's set-system
semantics require every listed set to be a subset of the declared universe.
-/
noncomputable def exactCoverBaseDigitMap (I : ExactCoverInput) : KnapsackInput := by
  classical
  exact if SetSystemWellFormed I.system then exactCoverBaseDigitMapCore I
    else exactCoverNoKnapsackInput

/-- Decode a Boolean selector over a source-family list. -/
def selectedSetsFrom : List (List Nat) → List Bool → List (List Nat)
  | [], _ => []
  | _ :: _, [] => []
  | S :: sets, b :: bits =>
      if b then S :: selectedSetsFrom sets bits else selectedSetsFrom sets bits

def exactCoverBitsFromSelection (source selected : List (List Nat)) : List Bool :=
  source.map fun S => decide (S ∈ selected)

theorem selectedSetsFrom_length_le (sets : List (List Nat)) (bits : List Bool) :
    (selectedSetsFrom sets bits).length ≤ sets.length := by
  induction sets generalizing bits with
  | nil =>
      simp [selectedSetsFrom]
  | cons S sets ih =>
      cases bits with
      | nil =>
          simp [selectedSetsFrom]
      | cons b bits =>
          cases b
          · exact Nat.le_trans (ih bits) (Nat.le_succ _)
          · exact Nat.succ_le_succ (ih bits)

theorem mem_selectedSetsFrom {sets : List (List Nat)} {bits : List Bool} {S : List Nat}
    (hS : S ∈ selectedSetsFrom sets bits) :
    S ∈ sets := by
  induction sets generalizing bits with
  | nil =>
      simp [selectedSetsFrom] at hS
  | cons T sets ih =>
      cases bits with
      | nil =>
          simp [selectedSetsFrom] at hS
      | cons b bits =>
          cases b
          · have hTail : S ∈ selectedSetsFrom sets bits := by
              simpa [selectedSetsFrom] using hS
            exact List.mem_cons_of_mem T (ih hTail)
          · have hCases : S = T ∨ S ∈ selectedSetsFrom sets bits := by
              simpa [selectedSetsFrom] using hS
            rcases hCases with rfl | hTail
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem T (ih hTail)

theorem selectedSetsFrom_nodup {sets : List (List Nat)} {bits : List Bool}
    (hNodup : sets.Nodup) :
    (selectedSetsFrom sets bits).Nodup := by
  induction sets generalizing bits with
  | nil =>
      simp [selectedSetsFrom]
  | cons S sets ih =>
      cases bits with
      | nil =>
          simp [selectedSetsFrom]
      | cons b bits =>
          cases b
          · exact ih hNodup.of_cons
          · have hSNot :
                S ∉ selectedSetsFrom sets bits := by
              intro hS
              exact hNodup.notMem (mem_selectedSetsFrom hS)
            simp [selectedSetsFrom, hSNot, ih hNodup.of_cons]

theorem selectedSetsFrom_membershipSelector (source selected : List (List Nat)) :
    selectedSetsFrom source (exactCoverBitsFromSelection source selected) =
      source.filter fun S => decide (S ∈ selected) := by
  induction source with
  | nil =>
      simp [selectedSetsFrom]
  | cons S source ih =>
      have ih' :
          selectedSetsFrom source (source.map fun S => decide (S ∈ selected)) =
            source.filter fun S => decide (S ∈ selected) := by
        simpa [exactCoverBitsFromSelection] using ih
      by_cases hS : S ∈ selected
      · simp [selectedSetsFrom, exactCoverBitsFromSelection, hS, ih']
      · simp [selectedSetsFrom, exactCoverBitsFromSelection, hS, ih']

theorem selectedWeight_codeItems (sets : List (List Nat)) (bits : List Bool)
    (code : List Nat → Nat) (capacity target : Nat) :
    selectedWeight
        { items := sets.map fun S => (code S, code S), capacity := capacity, targetValue := target }
        bits =
      ((selectedSetsFrom sets bits).map code).sum := by
  induction sets generalizing bits with
  | nil =>
      simp [selectedWeight, selectedSetsFrom]
  | cons S sets ih =>
      cases bits with
      | nil =>
          simp [selectedWeight, selectedSetsFrom]
      | cons b bits =>
          cases b
          · simpa [selectedWeight, selectedSetsFrom] using ih bits
          · simp [selectedWeight, selectedSetsFrom]
            simpa [selectedWeight] using ih bits

theorem selectedValue_codeItems (sets : List (List Nat)) (bits : List Bool)
    (code : List Nat → Nat) (capacity target : Nat) :
    selectedValue
        { items := sets.map fun S => (code S, code S), capacity := capacity, targetValue := target }
        bits =
      ((selectedSetsFrom sets bits).map code).sum := by
  induction sets generalizing bits with
  | nil =>
      simp [selectedValue, selectedSetsFrom]
  | cons S sets ih =>
      cases bits with
      | nil =>
          simp [selectedValue, selectedSetsFrom]
      | cons b bits =>
          cases b
          · simpa [selectedValue, selectedSetsFrom] using ih bits
          · simp [selectedValue, selectedSetsFrom]
            simpa [selectedValue] using ih bits

theorem selectedWeight_exactCoverBaseDigitMapCore (I : ExactCoverInput) (bits : List Bool) :
    selectedWeight (exactCoverBaseDigitMapCore I) bits =
      ((selectedSetsFrom (exactCoverSourceSets I) bits).map (exactCoverSetCode I)).sum := by
  simpa [exactCoverBaseDigitMapCore, exactCoverBaseDigitItems] using
    selectedWeight_codeItems (exactCoverSourceSets I) bits (exactCoverSetCode I)
      (exactCoverTargetCode I) (exactCoverTargetCode I)

theorem selectedValue_exactCoverBaseDigitMapCore (I : ExactCoverInput) (bits : List Bool) :
    selectedValue (exactCoverBaseDigitMapCore I) bits =
      ((selectedSetsFrom (exactCoverSourceSets I) bits).map (exactCoverSetCode I)).sum := by
  simpa [exactCoverBaseDigitMapCore, exactCoverBaseDigitItems] using
    selectedValue_codeItems (exactCoverSourceSets I) bits (exactCoverSetCode I)
      (exactCoverTargetCode I) (exactCoverTargetCode I)

theorem digitCountsFrom_length (start len : Nat) (sets : List (List Nat)) :
    (digitCountsFrom start len sets).length = len := by
  induction len generalizing start with
  | zero =>
      simp [digitCountsFrom]
  | succ len ih =>
      simp [digitCountsFrom, ih]

theorem digitCountsFrom_nil (start len : Nat) :
    digitCountsFrom start len [] = List.replicate len 0 := by
  induction len generalizing start with
  | zero =>
      simp [digitCountsFrom]
  | succ len ih =>
      simp [digitCountsFrom, elementCount, ih, List.replicate_succ]

theorem digitCountsFrom_singleton_mem_le_one {start len : Nat} {S : List Nat} {d : Nat}
    (hd : d ∈ digitCountsFrom start len [S]) :
    d ≤ 1 := by
  induction len generalizing start with
  | zero =>
      simp [digitCountsFrom] at hd
  | succ len ih =>
      simp [digitCountsFrom, elementCount] at hd
      rcases hd with hd | hd
      · split at hd <;> omega
      · exact ih hd

theorem elementCount_le_length (x : Nat) (sets : List (List Nat)) :
    elementCount x sets ≤ sets.length := by
  induction sets with
  | nil =>
      simp [elementCount]
  | cons S sets ih =>
      by_cases hx : x ∈ S <;> simp [elementCount, hx] <;> omega

end Knapsack
end Karp21
end ComplexityReduction
