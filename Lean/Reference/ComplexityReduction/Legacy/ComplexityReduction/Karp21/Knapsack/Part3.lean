import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.Part2

namespace ComplexityReduction
namespace Karp21
namespace Knapsack
open ComplexityReduction.Combinatorics

theorem compactDigitVectorsMass_selectedEntries_le
    (vectors : List (List Nat)) (selected : List Bool) :
    compactDigitVectorsMass (selectedEntries vectors selected) ≤
      compactDigitVectorsMass vectors := by
  induction vectors generalizing selected with
  | nil =>
      simp [selectedEntries, compactDigitVectorsMass]
  | cons digits vectors ih =>
      cases selected with
      | nil =>
          simp [selectedEntries, compactDigitVectorsMass]
      | cons bit selected =>
          cases bit
          · have hTail := ih selected
            have h :
                compactDigitVectorsMass (selectedEntries vectors selected) ≤
                  digits.sum + compactDigitVectorsMass vectors :=
              le_trans hTail (Nat.le_add_left _ _)
            simpa [selectedEntries, compactDigitVectorsMass] using h
          · have hTail := ih selected
            have h :
                digits.sum + compactDigitVectorsMass (selectedEntries vectors selected) ≤
                  digits.sum + compactDigitVectorsMass vectors :=
              Nat.add_le_add_left hTail digits.sum
            simpa [selectedEntries, compactDigitVectorsMass] using h

theorem selectedDigitwiseSum_digit_lt_base
    {I : IntegerProgrammingInput} {selected : List Bool} {digit : Nat}
    (hdigit : digit ∈
      digitwiseSum (compactDigitCount I)
        (selectedEntries (compactItemDigitVectors I) selected)) :
    digit < compactBase I := by
  have hDigitLe :
      digit ≤
        (digitwiseSum (compactDigitCount I)
          (selectedEntries (compactItemDigitVectors I) selected)).sum :=
    nat_mem_le_sum hdigit
  have hSumLe :
      (digitwiseSum (compactDigitCount I)
        (selectedEntries (compactItemDigitVectors I) selected)).sum ≤
        compactDigitVectorsMass
          (selectedEntries (compactItemDigitVectors I) selected) :=
    digitwiseSum_sum_le_mass (compactDigitCount I)
      (selectedEntries (compactItemDigitVectors I) selected)
  have hSelectedMassLe :
      compactDigitVectorsMass
          (selectedEntries (compactItemDigitVectors I) selected) ≤
        compactDigitVectorsMass (compactItemDigitVectors I) :=
    compactDigitVectorsMass_selectedEntries_le (compactItemDigitVectors I) selected
  simp [compactBase]
  omega

theorem selectedCompactCodeSum_eq_targetCode_to_digitwiseSum_eq
    (I : IntegerProgrammingInput) (selected : List Bool)
    (hSum : selectedNatSum (compactItemCodes I) selected = compactTargetCode I) :
    digitwiseSum (compactDigitCount I)
        (selectedEntries (compactItemDigitVectors I) selected) =
      compactTargetDigits I := by
  have hEncoded := selectedCompactCodeSum_eq_targetCode_to_ofDigits_eq I selected hSum
  have hLength :
      (digitwiseSum (compactDigitCount I)
        (selectedEntries (compactItemDigitVectors I) selected)).length =
        (compactTargetDigits I).length := by
    rw [digitwiseSum_length, compactTargetDigits_length]
    intro digits hdigits
    exact selectedCompactItemDigitVectors_mem_length hdigits
  exact Nat.ofDigits_inj_of_len_eq (compactBase_gt_one I) hLength
    (by
      intro digit hdigit
      exact selectedDigitwiseSum_digit_lt_base hdigit)
    (by
      intro digit hdigit
      exact compactTargetDigit_lt_base hdigit)
    hEncoded

theorem selectedVariableChoiceCount_eq_one_of_digitwiseEq
    (I : IntegerProgrammingInput) (selected : List Bool)
    (hDigits :
      digitwiseSum (compactDigitCount I)
          (selectedEntries (compactItemDigitVectors I) selected) =
        compactTargetDigits I)
    {i : Nat} (hi : i < varBound I) :
    selectedVariableChoiceCount I i selected = 1 := by
  rw [selectedVariableChoiceCount_eq_digitwiseSum_getD I selected hi]
  rw [hDigits]
  exact compactTargetDigits_getD_variableChoice I hi

theorem selectedConstraintDigit_eq_bound_of_digitwiseEq
    (I : IntegerProgrammingInput) (selected : List Bool)
    (hDigits :
      digitwiseSum (compactDigitCount I)
          (selectedEntries (compactItemDigitVectors I) selected) =
        compactTargetDigits I)
    (rowIndex : Nat) :
    (digitwiseSum (compactDigitCount I)
        (selectedEntries (compactItemDigitVectors I) selected)).getD
        (varBound I + rowIndex) 0 =
      compactConstraintBound (I.constraints.getD rowIndex ([], (0 : Int))) := by
  rw [hDigits]
  exact compactTargetDigits_getD_constraint I rowIndex

theorem selectedVariableChoiceCount_eq_one_of_selectedCodeSum
    (I : IntegerProgrammingInput) (selected : List Bool)
    (hSum : selectedNatSum (compactItemCodes I) selected = compactTargetCode I)
    {i : Nat} (hi : i < varBound I) :
    selectedVariableChoiceCount I i selected = 1 := by
  exact selectedVariableChoiceCount_eq_one_of_digitwiseEq I selected
    (selectedCompactCodeSum_eq_targetCode_to_digitwiseSum_eq I selected hSum) hi

theorem selectedConstraintDigit_eq_bound_of_selectedCodeSum
    (I : IntegerProgrammingInput) (selected : List Bool)
    (hSum : selectedNatSum (compactItemCodes I) selected = compactTargetCode I)
    (rowIndex : Nat) :
    (digitwiseSum (compactDigitCount I)
        (selectedEntries (compactItemDigitVectors I) selected)).getD
        (varBound I + rowIndex) 0 =
      compactConstraintBound (I.constraints.getD rowIndex ([], (0 : Int))) := by
  exact selectedConstraintDigit_eq_bound_of_digitwiseEq I selected
    (selectedCompactCodeSum_eq_targetCode_to_digitwiseSum_eq I selected hSum) rowIndex

theorem selectedVariableChoiceExists_of_selectedCodeSum
    (I : IntegerProgrammingInput) (selected : List Bool)
    (hSum : selectedNatSum (compactItemCodes I) selected = compactTargetCode I)
    {i : Nat} (hi : i < varBound I) :
    ∃ b : Bool,
      compactVariableItemDigits I i b ∈
        selectedEntries (compactItemDigitVectors I) selected := by
  exact selectedVariableChoiceExists_of_count_eq_one I selected hi
    (selectedVariableChoiceCount_eq_one_of_selectedCodeSum I selected hSum hi)

theorem selectedVariableChoice_mem_decoded_of_selectedCodeSum
    (I : IntegerProgrammingInput) (selected : List Bool)
    (hSum : selectedNatSum (compactItemCodes I) selected = compactTargetCode I)
    {i : Nat} (hi : i < varBound I) :
    compactVariableItemDigits I i (decodedCompactAssignment I selected i) ∈
      selectedEntries (compactItemDigitVectors I) selected := by
  by_cases hTrue :
      compactVariableItemDigits I i true ∈
        selectedEntries (compactItemDigitVectors I) selected
  · simp [decodedCompactAssignment, hTrue]
  · have hDecoded : decodedCompactAssignment I selected i = false := by
      simp [decodedCompactAssignment, hTrue]
    rw [hDecoded]
    rcases selectedVariableChoiceExists_of_selectedCodeSum I selected hSum hi with
      ⟨b, hb⟩
    cases b
    · exact hb
    · exact False.elim (hTrue hb)

theorem selectedDecodedVariableContribution_le_constraintDigit
    (I : IntegerProgrammingInput) (selected : List Bool)
    (hSum : selectedNatSum (compactItemCodes I) selected = compactTargetCode I)
    {rowIndex i : Nat} (hrow : rowIndex < I.constraints.length) (hi : i < varBound I) :
    compactCoeffContribution
        (compactCoeffAt (I.constraints.getD rowIndex ([], (0 : Int))).1 i)
        (decodedCompactAssignment I selected i) ≤
      (digitwiseSum (compactDigitCount I)
        (selectedEntries (compactItemDigitVectors I) selected)).getD
        (varBound I + rowIndex) 0 := by
  have hMem :=
    selectedVariableChoice_mem_decoded_of_selectedCodeSum I selected hSum hi
  have hidx : varBound I + rowIndex < compactDigitCount I := by
    simp [compactDigitCount]
    omega
  have hLe :=
    mem_getD_le_digitwiseSum_getD
      (vectors := selectedEntries (compactItemDigitVectors I) selected)
      (digits := compactVariableItemDigits I i (decodedCompactAssignment I selected i))
      hMem
      (by
        intro digits hdigits
        exact selectedCompactItemDigitVectors_mem_length hdigits)
      hidx
  rwa [compactVariableItemDigits_getD_constraint] at hLe

theorem sum_map_le_of_sublist {α : Type} (f : α → Nat) {xs ys : List α}
    (h : List.Sublist xs ys) :
    (xs.map f).sum ≤ (ys.map f).sum := by
  induction h with
  | slnil =>
      simp
  | cons _ _ ih =>
      exact ih.trans (Nat.le_add_left _ _)
  | cons₂ a _ ih =>
      simp [Nat.add_le_add_left ih (f a)]

theorem sum_map_le_of_subperm {α : Type} (f : α → Nat) {xs ys : List α}
    (h : List.Subperm xs ys) :
    (xs.map f).sum ≤ (ys.map f).sum := by
  rcases List.subperm_iff.mp h with ⟨zs, hPerm, hSublist⟩
  have hLe := sum_map_le_of_sublist f hSublist
  have hPermSum : (zs.map f).sum = (ys.map f).sum := by
    exact (hPerm.map f).sum_eq
  simpa [hPermSum] using hLe

def decodedCompactVariableItems (I : IntegerProgrammingInput) (selected : List Bool) :
    List (List Nat) :=
  (List.range (varBound I)).map fun i =>
    compactVariableItemDigits I i (decodedCompactAssignment I selected i)

theorem compactVariableItemDigits_index_eq_of_eq
    {I : IntegerProgrammingInput} {i j : Nat} {b c : Bool}
    (hi : i < varBound I) (hEq :
      compactVariableItemDigits I i b = compactVariableItemDigits I j c) :
    i = j := by
  have hGet := congrArg (fun digits : List Nat => digits.getD i 0) hEq
  change (compactVariableItemDigits I i b).getD i 0 =
    (compactVariableItemDigits I j c).getD i 0 at hGet
  rw [compactVariableItemDigits_getD_variableChoice (I := I) (i := i) (j := i) hi b] at hGet
  rw [compactVariableItemDigits_getD_variableChoice (I := I) (i := i) (j := j) hi c] at hGet
  by_contra hne
  simp [hne] at hGet

theorem decodedCompactVariableItems_nodup
    (I : IntegerProgrammingInput) (selected : List Bool) :
    (decodedCompactVariableItems I selected).Nodup := by
  unfold decodedCompactVariableItems
  apply List.Nodup.map_on
  · intro i hi j _hj hEq
    exact compactVariableItemDigits_index_eq_of_eq (I := I)
      (List.mem_range.mp hi) hEq
  · exact List.nodup_range

theorem decodedCompactVariableItems_subset_selectedEntries_of_selectedCodeSum
    (I : IntegerProgrammingInput) (selected : List Bool)
    (hSum : selectedNatSum (compactItemCodes I) selected = compactTargetCode I) :
    decodedCompactVariableItems I selected ⊆
      selectedEntries (compactItemDigitVectors I) selected := by
  intro digits hdigits
  rcases List.mem_map.mp hdigits with ⟨i, hi, rfl⟩
  exact selectedVariableChoice_mem_decoded_of_selectedCodeSum I selected hSum
    (List.mem_range.mp hi)

theorem decodedCompactVariableItems_subperm_selectedEntries_of_selectedCodeSum
    (I : IntegerProgrammingInput) (selected : List Bool)
    (hSum : selectedNatSum (compactItemCodes I) selected = compactTargetCode I) :
    List.Subperm (decodedCompactVariableItems I selected)
      (selectedEntries (compactItemDigitVectors I) selected) :=
  (decodedCompactVariableItems_nodup I selected).subperm
    (decodedCompactVariableItems_subset_selectedEntries_of_selectedCodeSum I selected hSum)

theorem decodedCompactVariableItems_constraintDigit_sum
    (I : IntegerProgrammingInput) (selected : List Bool)
    {rowIndex : Nat} (hrow : rowIndex < I.constraints.length) :
    ((decodedCompactVariableItems I selected).map fun digits =>
        digits.getD (varBound I + rowIndex) 0).sum =
      compactConstraintValue (decodedCompactAssignment I selected)
        (I.constraints.getD rowIndex ([], (0 : Int))).1 := by
  have hConstraintMem :
      I.constraints.getD rowIndex ([], (0 : Int)) ∈ I.constraints := by
    rw [List.getD_eq_getElem (l := I.constraints) (d := ([], (0 : Int)))
      (n := rowIndex) hrow]
    exact List.getElem_mem _
  have hLen :
      (I.constraints.getD rowIndex ([], (0 : Int))).1.length ≤ varBound I :=
    constraint_row_length_le_varBound_of_mem hConstraintMem
  rw [compactConstraintValue_eq_sum_range_of_length_le
    (decodedCompactAssignment I selected)
    (I.constraints.getD rowIndex ([], (0 : Int))).1 hLen]
  unfold decodedCompactVariableItems
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _hi
  exact compactVariableItemDigits_getD_constraint I rowIndex i
    (decodedCompactAssignment I selected i)

theorem decodedCompactAssignment_compactConstraintValue_le_of_selectedCodeSum
    (I : IntegerProgrammingInput) (selected : List Bool)
    (hSum : selectedNatSum (compactItemCodes I) selected = compactTargetCode I)
    {rowIndex : Nat} (hrow : rowIndex < I.constraints.length) :
    compactConstraintValue (decodedCompactAssignment I selected)
        (I.constraints.getD rowIndex ([], (0 : Int))).1 ≤
      compactConstraintBound (I.constraints.getD rowIndex ([], (0 : Int))) := by
  let digit := varBound I + rowIndex
  let rowWeight : List Nat → Nat := fun digits => digits.getD digit 0
  have hDecodedSum :=
    decodedCompactVariableItems_constraintDigit_sum I selected hrow
  have hSubperm :=
    decodedCompactVariableItems_subperm_selectedEntries_of_selectedCodeSum I selected hSum
  have hLeEntries :
      ((decodedCompactVariableItems I selected).map rowWeight).sum ≤
        ((selectedEntries (compactItemDigitVectors I) selected).map rowWeight).sum :=
    sum_map_le_of_subperm rowWeight hSubperm
  have hidx : digit < compactDigitCount I := by
    simp [digit, compactDigitCount]
    omega
  have hDigitwise :
      (digitwiseSum (compactDigitCount I)
          (selectedEntries (compactItemDigitVectors I) selected)).getD digit 0 =
        ((selectedEntries (compactItemDigitVectors I) selected).map rowWeight).sum := by
    simpa [rowWeight, digit] using
      digitwiseSum_getD_eq_sum_getD
        (vectors := selectedEntries (compactItemDigitVectors I) selected)
        (hLength := by
          intro digits hdigits
          exact selectedCompactItemDigitVectors_mem_length hdigits)
        hidx
  have hEntriesEq :
      ((selectedEntries (compactItemDigitVectors I) selected).map rowWeight).sum =
        compactConstraintBound (I.constraints.getD rowIndex ([], (0 : Int))) := by
    have hBound := selectedConstraintDigit_eq_bound_of_selectedCodeSum I selected hSum rowIndex
    rw [hDigitwise] at hBound
    exact hBound
  calc
    compactConstraintValue (decodedCompactAssignment I selected)
        (I.constraints.getD rowIndex ([], (0 : Int))).1
        = ((decodedCompactVariableItems I selected).map rowWeight).sum := by
          simpa [rowWeight, digit] using hDecodedSum.symm
    _ ≤ ((selectedEntries (compactItemDigitVectors I) selected).map rowWeight).sum := hLeEntries
    _ = compactConstraintBound (I.constraints.getD rowIndex ([], (0 : Int))) := hEntriesEq

theorem decodedCompactAssignment_compactConstraints_of_selectedCodeSum
    (I : IntegerProgrammingInput) (selected : List Bool)
    (hSum : selectedNatSum (compactItemCodes I) selected = compactTargetCode I) :
    ∀ constraint ∈ I.constraints,
      compactConstraintValue (decodedCompactAssignment I selected) constraint.1 ≤
        compactConstraintBound constraint := by
  intro constraint hConstraint
  let rowIndex := I.constraints.idxOf constraint
  have hrow : rowIndex < I.constraints.length := by
    simpa [rowIndex] using List.idxOf_lt_length_iff.mpr hConstraint
  have hget : I.constraints.getD rowIndex ([], (0 : Int)) = constraint := by
    rw [List.getD_eq_getElem (l := I.constraints) (d := ([], (0 : Int))) hrow]
    simp [rowIndex]
  have hLe :=
    decodedCompactAssignment_compactConstraintValue_le_of_selectedCodeSum
      I selected hSum hrow
  rw [hget] at hLe
  exact hLe

theorem zeroOneIP_of_compactMapCore_knapsack
    (I : IntegerProgrammingInput) (hBounds : compactConstraintBoundsNonnegative I)
    (hKnapsack : Combinatorics.Knapsack (compactMapCore I)) :
    ZeroOneIntegerProgramming I := by
  rcases (compactMapCore_knapsack_iff_selectedNatSum_eq I).1 hKnapsack with
    ⟨selected, _hLength, hSum⟩
  refine (zeroOneIP_iff_compactConstraints_of_bounds I hBounds).2 ?_
  exact ⟨decodedCompactAssignment I selected,
    decodedCompactAssignment_compactConstraints_of_selectedCodeSum I selected hSum⟩

theorem zeroOneIP_of_compactMap_knapsack
    (I : IntegerProgrammingInput) :
    Combinatorics.Knapsack (compactMap I) → ZeroOneIntegerProgramming I := by
  classical
  intro hKnapsack
  by_cases hBounds : compactConstraintBoundsNonnegative I
  · have hCore : Combinatorics.Knapsack (compactMapCore I) := by
      simpa [compactMap, hBounds] using hKnapsack
    exact zeroOneIP_of_compactMapCore_knapsack I hBounds hCore
  · have hNo : Combinatorics.Knapsack compactNoKnapsackInput := by
      simpa [compactMap, hBounds] using hKnapsack
    exact (compactNoKnapsackInput_not hNo).elim

theorem compactMap_correct (I : IntegerProgrammingInput) :
    zeroOneIntegerProgrammingDecisionProblem.isYes I ↔
      Combinatorics.Knapsack (compactMap I) := by
  change ZeroOneIntegerProgramming I ↔ Combinatorics.Knapsack (compactMap I)
  exact ⟨compactMap_knapsack_of_zeroOneIP I, zeroOneIP_of_compactMap_knapsack I⟩

/-! ### Binary-structured size bounds for the compact route -/

theorem encodedList_length_le_inputSize (X : EncodedType) (xs : List X.Carrier) :
    xs.length ≤ (EncodedType.list X).inputSize xs := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      calc
        (x :: xs).length = xs.length + 1 := by simp
        _ ≤ (EncodedType.list X).inputSize xs + 1 := by omega
        _ ≤ X.inputSize x + 1 + (EncodedType.list X).inputSize xs := by omega
        _ = (EncodedType.list X).inputSize (x :: xs) := by
          symm
          exact EncodedType.inputSize_list_cons X x xs

theorem encodedList_element_inputSize_le
    (X : EncodedType) {xs : List X.Carrier} {x : X.Carrier} (hx : x ∈ xs) :
    X.inputSize x ≤ (EncodedType.list X).inputSize xs := by
  induction hx with
  | head tail =>
      rw [EncodedType.inputSize_list_cons]
      omega
  | tail head _hmem ih =>
      rw [EncodedType.inputSize_list_cons]
      exact ih.trans (by omega)

theorem binaryNat_lt_two_pow_inputSize (n : Nat) :
    n < 2 ^ EncodedType.binaryNat.inputSize n := by
  change n < 2 ^ ((Nat.digits 2 n).map fun d => decide (d = 1)).length
  rw [List.length_map]
  exact (Nat.digits_length_le_iff (by decide : 1 < 2) n).1 le_rfl

theorem intPositivePart_le_two_pow_binaryInt_inputSize (z : Int) :
    intPositivePart z ≤ 2 ^ EncodedType.binaryInt.inputSize z := by
  cases z with
  | ofNat n =>
      have hlt := binaryNat_lt_two_pow_inputSize n
      have hpow :
          2 ^ EncodedType.binaryNat.inputSize n ≤
            2 ^ EncodedType.binaryInt.inputSize (Int.ofNat n) := by
        apply Nat.pow_le_pow_right (by decide : 0 < 2)
        simp [EncodedType.inputSize, EncodedType.binaryInt]
      exact (Nat.le_of_lt hlt).trans hpow
  | negSucc n =>
      simp [intPositivePart]

theorem intNegativePart_le_two_pow_binaryInt_inputSize (z : Int) :
    intNegativePart z ≤ 2 ^ EncodedType.binaryInt.inputSize z := by
  cases z with
  | ofNat n =>
      simp [intNegativePart]
  | negSucc n =>
      have hlt := binaryNat_lt_two_pow_inputSize n
      have hsucc : n + 1 ≤ 2 ^ EncodedType.binaryNat.inputSize n := by omega
      have hpow :
          2 ^ EncodedType.binaryNat.inputSize n ≤
            2 ^ EncodedType.binaryInt.inputSize (Int.negSucc n) := by
        apply Nat.pow_le_pow_right (by decide : 0 < 2)
        simp [EncodedType.inputSize, EncodedType.binaryInt]
      exact hsucc.trans hpow

theorem integerProgrammingBinaryStructured_inputSize_eq (I : IntegerProgrammingInput) :
    integerProgrammingBinaryStructuredEncodedType.inputSize I =
      EncodedType.binaryNat.inputSize I.numVariables + 1 +
        constraintListBinaryStructuredEncodedType.inputSize I.constraints := by
  change integerProgrammingTupleBinaryStructuredEncodedType.inputSize
      (I.numVariables, I.constraints) =
    EncodedType.binaryNat.inputSize I.numVariables + 1 +
      constraintListBinaryStructuredEncodedType.inputSize I.constraints
  simp [integerProgrammingTupleBinaryStructuredEncodedType]

theorem constraintListBinaryStructured_inputSize_le_source
    (I : IntegerProgrammingInput) :
    constraintListBinaryStructuredEncodedType.inputSize I.constraints ≤
      integerProgrammingBinaryStructuredEncodedType.inputSize I := by
  rw [integerProgrammingBinaryStructured_inputSize_eq]
  omega

theorem constraints_length_le_binaryStructured_inputSize (I : IntegerProgrammingInput) :
    I.constraints.length ≤ integerProgrammingBinaryStructuredEncodedType.inputSize I := by
  have hList := encodedList_length_le_inputSize constraintBinaryStructuredEncodedType I.constraints
  exact hList.trans (constraintListBinaryStructured_inputSize_le_source I)

theorem constraint_binaryStructured_inputSize_le_source
    {I : IntegerProgrammingInput} {constraint : List Int × Int}
    (hconstraint : constraint ∈ I.constraints) :
    constraintBinaryStructuredEncodedType.inputSize constraint ≤
      integerProgrammingBinaryStructuredEncodedType.inputSize I := by
  have hElement :=
    encodedList_element_inputSize_le constraintBinaryStructuredEncodedType hconstraint
  exact hElement.trans (constraintListBinaryStructured_inputSize_le_source I)

theorem constraint_row_binaryStructured_inputSize_le_constraint
    (constraint : List Int × Int) :
    intRowBinaryStructuredEncodedType.inputSize constraint.1 ≤
      constraintBinaryStructuredEncodedType.inputSize constraint := by
  cases constraint with
  | mk row bound =>
      simp [constraintBinaryStructuredEncodedType]
      omega

theorem constraint_bound_binaryInt_inputSize_le_constraint
    (constraint : List Int × Int) :
    EncodedType.binaryInt.inputSize constraint.2 ≤
      constraintBinaryStructuredEncodedType.inputSize constraint := by
  cases constraint with
  | mk row bound =>
      simp [constraintBinaryStructuredEncodedType]

theorem row_binaryStructured_inputSize_le_source
    {I : IntegerProgrammingInput} {constraint : List Int × Int}
    (hconstraint : constraint ∈ I.constraints) :
    intRowBinaryStructuredEncodedType.inputSize constraint.1 ≤
      integerProgrammingBinaryStructuredEncodedType.inputSize I :=
  (constraint_row_binaryStructured_inputSize_le_constraint constraint).trans
    (constraint_binaryStructured_inputSize_le_source hconstraint)

theorem constraint_bound_binaryInt_inputSize_le_source
    {I : IntegerProgrammingInput} {constraint : List Int × Int}
    (hconstraint : constraint ∈ I.constraints) :
    EncodedType.binaryInt.inputSize constraint.2 ≤
      integerProgrammingBinaryStructuredEncodedType.inputSize I :=
  (constraint_bound_binaryInt_inputSize_le_constraint constraint).trans
    (constraint_binaryStructured_inputSize_le_source hconstraint)

theorem row_length_le_binaryStructured_inputSize_of_mem
    {I : IntegerProgrammingInput} {constraint : List Int × Int}
    (hconstraint : constraint ∈ I.constraints) :
    constraint.1.length ≤ integerProgrammingBinaryStructuredEncodedType.inputSize I := by
  have hRowLength :=
    encodedList_length_le_inputSize EncodedType.binaryInt constraint.1
  exact hRowLength.trans (row_binaryStructured_inputSize_le_source hconstraint)

theorem coefficient_binaryInt_inputSize_le_source
    {I : IntegerProgrammingInput} {constraint : List Int × Int} {z : Int}
    (hconstraint : constraint ∈ I.constraints) (hz : z ∈ constraint.1) :
    EncodedType.binaryInt.inputSize z ≤
      integerProgrammingBinaryStructuredEncodedType.inputSize I := by
  have hCoeff := encodedList_element_inputSize_le EncodedType.binaryInt hz
  exact hCoeff.trans (row_binaryStructured_inputSize_le_source hconstraint)

theorem intPositivePart_le_two_pow_source_of_mem
    {I : IntegerProgrammingInput} {constraint : List Int × Int} {z : Int}
    (hconstraint : constraint ∈ I.constraints) (hz : z ∈ constraint.1) :
    intPositivePart z ≤ 2 ^ integerProgrammingBinaryStructuredEncodedType.inputSize I := by
  have hSize := coefficient_binaryInt_inputSize_le_source hconstraint hz
  exact (intPositivePart_le_two_pow_binaryInt_inputSize z).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) hSize)

theorem intNegativePart_le_two_pow_source_of_mem
    {I : IntegerProgrammingInput} {constraint : List Int × Int} {z : Int}
    (hconstraint : constraint ∈ I.constraints) (hz : z ∈ constraint.1) :
    intNegativePart z ≤ 2 ^ integerProgrammingBinaryStructuredEncodedType.inputSize I := by
  have hSize := coefficient_binaryInt_inputSize_le_source hconstraint hz
  exact (intNegativePart_le_two_pow_binaryInt_inputSize z).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) hSize)

theorem constraint_bound_positivePart_le_two_pow_source
    {I : IntegerProgrammingInput} {constraint : List Int × Int}
    (hconstraint : constraint ∈ I.constraints) :
    intPositivePart constraint.2 ≤
      2 ^ integerProgrammingBinaryStructuredEncodedType.inputSize I := by
  have hSize := constraint_bound_binaryInt_inputSize_le_source hconstraint
  exact (intPositivePart_le_two_pow_binaryInt_inputSize constraint.2).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) hSize)

theorem rowNegativeShift_le_length_mul_bound
    {row : List Int} {B : Nat}
    (hrow : ∀ z ∈ row, intNegativePart z ≤ B) :
    rowNegativeShift row ≤ row.length * B := by
  induction row with
  | nil =>
      simp [rowNegativeShift]
  | cons z zs ih =>
      have hz : intNegativePart z ≤ B := hrow z (by simp)
      have hzs : ∀ w ∈ zs, intNegativePart w ≤ B := by
        intro w hw
        exact hrow w (by simp [hw])
      have htail := ih hzs
      calc
        rowNegativeShift (z :: zs)
            = intNegativePart z + rowNegativeShift zs := rfl
        _ ≤ B + zs.length * B := Nat.add_le_add hz htail
        _ = (z :: zs).length * B := by
            simp [Nat.add_mul, Nat.add_comm]

theorem rowNegativeShift_le_source_mul_two_pow_source
    {I : IntegerProgrammingInput} {constraint : List Int × Int}
    (hconstraint : constraint ∈ I.constraints) :
    rowNegativeShift constraint.1 ≤
      integerProgrammingBinaryStructuredEncodedType.inputSize I *
        2 ^ integerProgrammingBinaryStructuredEncodedType.inputSize I := by
  have hrow :
      ∀ z ∈ constraint.1,
        intNegativePart z ≤ 2 ^ integerProgrammingBinaryStructuredEncodedType.inputSize I := by
    intro z hz
    exact intNegativePart_le_two_pow_source_of_mem hconstraint hz
  have hShift := rowNegativeShift_le_length_mul_bound hrow
  have hLength := row_length_le_binaryStructured_inputSize_of_mem hconstraint
  exact hShift.trans (Nat.mul_le_mul_right _ hLength)

theorem compactConstraintBound_le_posPart_add_shift (constraint : List Int × Int) :
    compactConstraintBound constraint ≤ intPositivePart constraint.2 + rowNegativeShift constraint.1 := by
  cases constraint with
  | mk row bound =>
      cases bound with
      | ofNat n =>
          simp [compactConstraintBound, intPositivePart]
      | negSucc n =>
          simp [compactConstraintBound, intPositivePart]
          omega

theorem compactConstraintBound_le_source_succ_mul_two_pow_source
    {I : IntegerProgrammingInput} {constraint : List Int × Int}
    (hconstraint : constraint ∈ I.constraints) :
    compactConstraintBound constraint ≤
      (integerProgrammingBinaryStructuredEncodedType.inputSize I + 1) *
        2 ^ integerProgrammingBinaryStructuredEncodedType.inputSize I := by
  have hPos := constraint_bound_positivePart_le_two_pow_source hconstraint
  have hShift := rowNegativeShift_le_source_mul_two_pow_source hconstraint
  have hBound := compactConstraintBound_le_posPart_add_shift constraint
  calc
    compactConstraintBound constraint
        ≤ intPositivePart constraint.2 + rowNegativeShift constraint.1 := hBound
    _ ≤ 2 ^ integerProgrammingBinaryStructuredEncodedType.inputSize I +
          integerProgrammingBinaryStructuredEncodedType.inputSize I *
            2 ^ integerProgrammingBinaryStructuredEncodedType.inputSize I := by
          omega
    _ = (integerProgrammingBinaryStructuredEncodedType.inputSize I + 1) *
          2 ^ integerProgrammingBinaryStructuredEncodedType.inputSize I := by
          rw [Nat.add_mul, one_mul, Nat.add_comm]

theorem nat_succ_le_two_pow_succ (n : Nat) :
    n + 1 ≤ 2 ^ (n + 1) := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      calc
        n + 2 ≤ 2 * (n + 1) := by omega
        _ ≤ 2 * 2 ^ (n + 1) := Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (n + 2) := by rw [Nat.pow_succ']; ring

theorem compactConstraintBound_lt_two_pow_two_mul_source_add_two
    {I : IntegerProgrammingInput} {constraint : List Int × Int}
    (hconstraint : constraint ∈ I.constraints) :
    compactConstraintBound constraint <
      2 ^ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) := by
  let S := integerProgrammingBinaryStructuredEncodedType.inputSize I
  have hBound :
      compactConstraintBound constraint ≤ (S + 1) * 2 ^ S := by
    simpa [S] using compactConstraintBound_le_source_succ_mul_two_pow_source hconstraint
  have hSucc : S + 1 ≤ 2 ^ (S + 1) := nat_succ_le_two_pow_succ S
  have hMul : (S + 1) * 2 ^ S ≤ 2 ^ (S + 1) * 2 ^ S :=
    Nat.mul_le_mul_right (2 ^ S) hSucc
  have hPowEq : 2 ^ (S + 1) * 2 ^ S = 2 ^ (2 * S + 1) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hLe : compactConstraintBound constraint ≤ 2 ^ (2 * S + 1) := by
    exact hBound.trans (hMul.trans (le_of_eq hPowEq))
  have hPowLt : 2 ^ (2 * S + 1) < 2 ^ (2 * S + 2) := by
    apply Nat.pow_lt_pow_right (by decide : 1 < 2)
    omega
  exact lt_of_le_of_lt hLe hPowLt

theorem compactSlackBitCount_le_two_mul_source_add_two
    {I : IntegerProgrammingInput} {constraint : List Int × Int}
    (hconstraint : constraint ∈ I.constraints) :
    compactSlackBitCount constraint ≤
      2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2 := by
  unfold compactSlackBitCount
  exact (Nat.digits_length_le_iff (by decide : 1 < 2)
    (compactConstraintBound constraint)).2
      (compactConstraintBound_lt_two_pow_two_mul_source_add_two hconstraint)

theorem constraintsVarBound_le_of_forall
    {constraints : List (List Int × Int)} {B : Nat}
    (hAll : ∀ constraint ∈ constraints, constraint.1.length ≤ B) :
    constraintsVarBound constraints ≤ B := by
  induction constraints with
  | nil =>
      simp [constraintsVarBound]
  | cons constraint constraints ih =>
      have hHead : constraint.1.length ≤ B := hAll constraint (by simp)
      have hTail : constraintsVarBound constraints ≤ B := by
        apply ih
        intro tailConstraint htail
        exact hAll tailConstraint (by simp [htail])
      change max (constraintVarBound constraint) (constraintsVarBound constraints) ≤ B
      exact max_le (by simpa [constraintVarBound] using hHead) hTail

theorem constraintsVarBound_le_binaryStructured_inputSize
    (I : IntegerProgrammingInput) :
    constraintsVarBound I.constraints ≤ integerProgrammingBinaryStructuredEncodedType.inputSize I := by
  apply constraintsVarBound_le_of_forall
  intro constraint hconstraint
  exact row_length_le_binaryStructured_inputSize_of_mem
    (I := I) (constraint := constraint) hconstraint

theorem varBound_le_binaryStructured_inputSize (I : IntegerProgrammingInput) :
    varBound I ≤ integerProgrammingBinaryStructuredEncodedType.inputSize I := by
  simpa [varBound] using constraintsVarBound_le_binaryStructured_inputSize I

theorem compactDigitCount_le_two_mul_binaryStructured_inputSize
    (I : IntegerProgrammingInput) :
    compactDigitCount I ≤ 2 * integerProgrammingBinaryStructuredEncodedType.inputSize I := by
  have hVar := varBound_le_binaryStructured_inputSize I
  have hRows := constraints_length_le_binaryStructured_inputSize I
  simp [compactDigitCount]
  omega

theorem pow_two_le_pow_two_of_le {a b : Nat} (h : a ≤ b) :
    2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide : 0 < 2) h

theorem one_le_two_pow (n : Nat) :
    1 ≤ 2 ^ n := by
  cases n with
  | zero =>
      simp
  | succ n =>
      exact Nat.succ_le_of_lt (Nat.pow_pos (by decide : 0 < 2))

theorem compactCoeffContribution_le_two_pow_source_of_getD
    {I : IntegerProgrammingInput} {constraint : List Int × Int}
    (hconstraint : constraint ∈ I.constraints) (i : Nat) (b : Bool) :
    compactCoeffContribution (compactCoeffAt constraint.1 i) b ≤
      2 ^ integerProgrammingBinaryStructuredEncodedType.inputSize I := by
  by_cases hi : i < constraint.1.length
  · have hgetMem : constraint.1.getD i 0 ∈ constraint.1 := by
      rw [List.getD_eq_getElem (l := constraint.1) (d := 0) (n := i) hi]
      exact List.getElem_mem _
    cases b
    · simp [compactCoeffContribution]
      exact intNegativePart_le_two_pow_source_of_mem hconstraint hgetMem
    · simp [compactCoeffContribution]
      exact intPositivePart_le_two_pow_source_of_mem hconstraint hgetMem
  · have hle : constraint.1.length ≤ i := Nat.le_of_not_gt hi
    rw [compactCoeffAt, List.getD_eq_default (l := constraint.1) (d := (0 : Int)) (n := i) hle]
    cases b <;> simp [compactCoeffContribution, intPositivePart, intNegativePart]

theorem compactCoeffContribution_le_entryBound_of_getD
    {I : IntegerProgrammingInput} {constraint : List Int × Int}
    (hconstraint : constraint ∈ I.constraints) (i : Nat) (b : Bool) :
    compactCoeffContribution (compactCoeffAt constraint.1 i) b ≤
      2 ^ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) := by
  have hSmall := compactCoeffContribution_le_two_pow_source_of_getD hconstraint i b
  exact hSmall.trans (pow_two_le_pow_two_of_le (by omega))

theorem compactVariableChoiceDigits_entry_le_one
    {I : IntegerProgrammingInput} {i digit : Nat}
    (hdigit : digit ∈ compactVariableChoiceDigits I i) :
    digit ≤ 1 := by
  rcases List.mem_map.mp hdigit with ⟨j, _hj, rfl⟩
  by_cases hji : j = i <;> simp [hji]

theorem compactVariableConstraintDigits_entry_le_entryBound
    {I : IntegerProgrammingInput} {i : Nat} {b : Bool} {digit : Nat}
    (hdigit : digit ∈ compactVariableConstraintDigits I i b) :
    digit ≤ 2 ^ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) := by
  rcases List.mem_map.mp hdigit with ⟨constraint, hconstraint, rfl⟩
  exact compactCoeffContribution_le_entryBound_of_getD hconstraint i b

theorem compactVariableItemDigits_entry_le_entryBound
    {I : IntegerProgrammingInput} {i : Nat} {b : Bool} {digit : Nat}
    (hdigit : digit ∈ compactVariableItemDigits I i b) :
    digit ≤ 2 ^ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) := by
  rw [compactVariableItemDigits] at hdigit
  rcases List.mem_append.mp hdigit with hChoice | hConstraint
  · exact (compactVariableChoiceDigits_entry_le_one hChoice).trans
      (one_le_two_pow _)
  · exact compactVariableConstraintDigits_entry_le_entryBound hConstraint

theorem compactBinaryPowers_entry_lt_two_pow_length
    {n power : Nat} (hpower : power ∈ compactBinaryPowers n) :
    power < 2 ^ n := by
  induction n generalizing power with
  | zero =>
      simp [compactBinaryPowers] at hpower
  | succ n ih =>
      rw [compactBinaryPowers] at hpower
      rcases List.mem_cons.mp hpower with rfl | hpower
      · exact Nat.one_lt_pow (by omega) (by decide : 1 < 2)
      · rcases List.mem_map.mp hpower with ⟨tailPower, htail, rfl⟩
        have htailLt := ih htail
        calc
          2 * tailPower < 2 * 2 ^ n := Nat.mul_lt_mul_of_pos_left htailLt (by decide)
          _ = 2 ^ (n + 1) := by rw [Nat.pow_succ']

theorem compactSlackPowers_entry_le_entryBound
    {I : IntegerProgrammingInput} {constraint : List Int × Int} {power : Nat}
    (hconstraint : constraint ∈ I.constraints) (hpower : power ∈ compactSlackPowers constraint) :
    power ≤ 2 ^ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) := by
  have hlt : power < 2 ^ compactSlackBitCount constraint := by
    simpa [compactSlackPowers] using compactBinaryPowers_entry_lt_two_pow_length hpower
  have hBits := compactSlackBitCount_le_two_mul_source_add_two hconstraint
  exact (Nat.le_of_lt hlt).trans (pow_two_le_pow_two_of_le hBits)

theorem compactSlackItemDigits_entry_le_entryBound
    {I : IntegerProgrammingInput} {rowIndex power digit : Nat}
    (hpower : power ≤ 2 ^ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2))
    (hdigit : digit ∈ compactSlackItemDigits I rowIndex power) :
    digit ≤ 2 ^ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) := by
  rw [compactSlackItemDigits] at hdigit
  rcases List.mem_append.mp hdigit with hPrefix | hTail
  · simp at hPrefix
    rcases hPrefix with ⟨_, rfl⟩
    simp
  · rcases List.mem_map.mp hTail with ⟨j, _hj, rfl⟩
    by_cases hEq : j = rowIndex
    · simpa [hEq] using hpower
    · simp [hEq]

theorem compactSlackItemDigitsForConstraint_entry_le_entryBound
    {I : IntegerProgrammingInput} {rowIndex : Nat} {constraint : List Int × Int} {digits : List Nat}
    (hconstraint : constraint ∈ I.constraints)
    (hdigits : digits ∈ compactSlackItemDigitsForConstraint I rowIndex constraint)
    {digit : Nat} (hdigit : digit ∈ digits) :
    digit ≤ 2 ^ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) := by
  rcases List.mem_map.mp hdigits with ⟨power, hpower, rfl⟩
  exact compactSlackItemDigits_entry_le_entryBound
    (compactSlackPowers_entry_le_entryBound hconstraint hpower) hdigit

theorem compactSlackItemDigitVectorsFrom_entry_le_entryBound
    {I : IntegerProgrammingInput} {constraints : List (List Int × Int)}
    {rowIndex : Nat} (hsubset : ∀ constraint ∈ constraints, constraint ∈ I.constraints)
    {digits : List Nat}
    (hdigits : digits ∈ compactSlackItemDigitVectorsFrom I rowIndex constraints)
    {digit : Nat} (hdigit : digit ∈ digits) :
    digit ≤ 2 ^ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) := by
  induction constraints generalizing rowIndex with
  | nil =>
      simp [compactSlackItemDigitVectorsFrom] at hdigits
  | cons constraint constraints ih =>
      simp [compactSlackItemDigitVectorsFrom] at hdigits
      rcases hdigits with hHere | hTail
      · exact compactSlackItemDigitsForConstraint_entry_le_entryBound
          (hsubset constraint (by simp)) hHere hdigit
      · have hsubsetTail : ∀ tailConstraint ∈ constraints, tailConstraint ∈ I.constraints := by
          intro tailConstraint htail
          exact hsubset tailConstraint (by simp [htail])
        exact ih hsubsetTail hTail

theorem compactItemDigitVectors_entry_le_entryBound
    {I : IntegerProgrammingInput} {digits : List Nat}
    (hdigits : digits ∈ compactItemDigitVectors I)
    {digit : Nat} (hdigit : digit ∈ digits) :
    digit ≤ 2 ^ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) := by
  rw [compactItemDigitVectors] at hdigits
  rcases List.mem_append.mp hdigits with hVariable | hSlack
  · rcases List.mem_flatMap.mp hVariable with ⟨i, _hi, hmem⟩
    simp at hmem
    rcases hmem with rfl | rfl
    · exact compactVariableItemDigits_entry_le_entryBound hdigit
    · exact compactVariableItemDigits_entry_le_entryBound hdigit
  · exact compactSlackItemDigitVectorsFrom_entry_le_entryBound
      (I := I) (constraints := I.constraints) (rowIndex := 0)
      (by intro constraint hconstraint; exact hconstraint) hSlack hdigit

theorem compactTargetDigits_entry_le_entryBound
    {I : IntegerProgrammingInput} {digit : Nat}
    (hdigit : digit ∈ compactTargetDigits I) :
    digit ≤ 2 ^ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) := by
  rw [compactTargetDigits] at hdigit
  rcases List.mem_append.mp hdigit with hPrefix | hTail
  · have hOne : digit = 1 := by
      simp at hPrefix
      exact hPrefix.2
    rw [hOne]
    exact one_le_two_pow _
  · rcases List.mem_map.mp hTail with ⟨constraint, hconstraint, rfl⟩
    exact (Nat.le_of_lt
      (compactConstraintBound_lt_two_pow_two_mul_source_add_two hconstraint))

theorem list_sum_le_length_mul_bound {xs : List Nat} {B : Nat}
    (hB : ∀ x ∈ xs, x ≤ B) :
    xs.sum ≤ xs.length * B := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : x ≤ B := hB x (by simp)
      have htail : ∀ y ∈ xs, y ≤ B := by
        intro y hy
        exact hB y (by simp [hy])
      have hih := ih htail
      calc
        (x :: xs).sum = x + xs.sum := by simp
        _ ≤ B + xs.length * B := Nat.add_le_add hx hih
        _ = (x :: xs).length * B := by
            simp [Nat.add_mul, Nat.add_comm]

theorem compactDigitVectorsMass_le_length_mul_digitCount_mul_entryBound
    (I : IntegerProgrammingInput) :
    compactDigitVectorsMass (compactItemDigitVectors I) ≤
      (compactItemDigitVectors I).length * compactDigitCount I *
        2 ^ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) := by
  unfold compactDigitVectorsMass
  have hEach :
      ∀ digits ∈ compactItemDigitVectors I,
        digits.sum ≤ compactDigitCount I *
          2 ^ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) := by
    intro digits hdigits
    have hLen := compactItemDigitVectors_mem_length hdigits
    have hSum :=
      list_sum_le_length_mul_bound
        (xs := digits)
        (B := 2 ^ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2))
        (by
          intro digit hdigit
          exact compactItemDigitVectors_entry_le_entryBound hdigits hdigit)
    simpa [hLen] using hSum
  have hMass :=
    list_sum_le_length_mul_bound
      (xs := (compactItemDigitVectors I).map List.sum)
      (B := compactDigitCount I *
        2 ^ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2))
      (by
        intro sum hsum
        rcases List.mem_map.mp hsum with ⟨digits, hdigits, rfl⟩
        exact hEach digits hdigits)
  simpa [List.length_map, Nat.mul_assoc] using hMass

theorem compactTargetDigits_sum_le_digitCount_mul_entryBound
    (I : IntegerProgrammingInput) :
    (compactTargetDigits I).sum ≤
      compactDigitCount I *
        2 ^ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2) := by
  have hSum :=
    list_sum_le_length_mul_bound
      (xs := compactTargetDigits I)
      (B := 2 ^ (2 * integerProgrammingBinaryStructuredEncodedType.inputSize I + 2))
      (by
        intro digit hdigit
        exact compactTargetDigits_entry_le_entryBound hdigit)
  simpa [compactTargetDigits_length] using hSum

end Knapsack
end Karp21
end ComplexityReduction
