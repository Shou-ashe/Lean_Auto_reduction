import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Knapsack.Part1

namespace ComplexityReduction
namespace Karp21
namespace Knapsack
open ComplexityReduction.Combinatorics

theorem digitwiseSum_length {length : Nat} {vectors : List (List Nat)}
    (hLength : ∀ digits ∈ vectors, digits.length = length) :
    (digitwiseSum length vectors).length = length := by
  induction vectors with
  | nil =>
      simp [digitwiseSum]
  | cons digits vectors ih =>
      have hHead : digits.length = length := hLength digits (by simp)
      have hTail : ∀ tailDigits ∈ vectors, tailDigits.length = length := by
        intro tailDigits htail
        exact hLength tailDigits (by simp [htail])
      simp [digitwiseSum, hHead, ih hTail]

theorem zipWith_add_getD
    (xs ys : List Nat) (idx : Nat)
    (hxs : idx < xs.length) (hys : idx < ys.length) :
    (xs.zipWith (· + ·) ys).getD idx 0 = xs.getD idx 0 + ys.getD idx 0 := by
  induction xs generalizing ys idx with
  | nil =>
      simp at hxs
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp at hys
      | cons y ys =>
          cases idx with
          | zero =>
              simp
          | succ idx =>
              simp at hxs hys ⊢
              exact ih ys idx hxs hys

theorem digitwiseSum_getD_eq_sum_getD
    {length idx : Nat} {vectors : List (List Nat)}
    (hLength : ∀ digits ∈ vectors, digits.length = length) (hidx : idx < length) :
    (digitwiseSum length vectors).getD idx 0 =
      ((vectors.map fun digits => digits.getD idx 0).sum) := by
  induction vectors with
  | nil =>
      simp [digitwiseSum]
  | cons digits vectors ih =>
      have hHead : digits.length = length := hLength digits (by simp)
      have hTail : ∀ tailDigits ∈ vectors, tailDigits.length = length := by
        intro tailDigits htail
        exact hLength tailDigits (by simp [htail])
      have hTailLength : (digitwiseSum length vectors).length = length :=
        digitwiseSum_length hTail
      have hHeadIdx : idx < digits.length := by
        simpa [hHead] using hidx
      have hTailIdx : idx < (digitwiseSum length vectors).length := by
        simpa [hTailLength] using hidx
      rw [digitwiseSum, zipWith_add_getD digits (digitwiseSum length vectors)
        idx hHeadIdx hTailIdx, ih hTail]
      simp

theorem mem_getD_le_digitwiseSum_getD
    {length idx : Nat} {vectors : List (List Nat)} {digits : List Nat}
    (hdigits : digits ∈ vectors)
    (hLength : ∀ vector ∈ vectors, vector.length = length) (hidx : idx < length) :
    digits.getD idx 0 ≤ (digitwiseSum length vectors).getD idx 0 := by
  induction vectors with
  | nil =>
      simp at hdigits
  | cons head tail ih =>
      have hHead : head.length = length := hLength head (by simp)
      have hTail : ∀ tailDigits ∈ tail, tailDigits.length = length := by
        intro tailDigits htail
        exact hLength tailDigits (by simp [htail])
      have hTailLength : (digitwiseSum length tail).length = length :=
        digitwiseSum_length hTail
      have hHeadIdx : idx < head.length := by
        simpa [hHead] using hidx
      have hTailIdx : idx < (digitwiseSum length tail).length := by
        simpa [hTailLength] using hidx
      rw [digitwiseSum, zipWith_add_getD head (digitwiseSum length tail)
        idx hHeadIdx hTailIdx]
      simp at hdigits
      rcases hdigits with rfl | hmem
      · exact Nat.le_add_right _ _
      · exact (ih hmem hTail).trans (Nat.le_add_left _ _)

theorem sum_digitCodes_eq_ofDigits_digitwiseSum
    (base length : Nat) (vectors : List (List Nat))
    (hLength : ∀ digits ∈ vectors, digits.length = length) :
    ((vectors.map fun digits => Nat.ofDigits base digits).sum) =
      Nat.ofDigits base (digitwiseSum length vectors) := by
  induction vectors with
  | nil =>
      simp [digitwiseSum, Nat.ofDigits_replicate_zero]
  | cons digits vectors ih =>
      have hHead : digits.length = length := hLength digits (by simp)
      have hTail : ∀ tailDigits ∈ vectors, tailDigits.length = length := by
        intro tailDigits htail
        exact hLength tailDigits (by simp [htail])
      have hTailLength : (digitwiseSum length vectors).length = length :=
        digitwiseSum_length hTail
      have hSameLength : digits.length = (digitwiseSum length vectors).length := by
        rw [hHead, hTailLength]
      rw [List.map_cons, List.sum_cons, ih hTail]
      rw [Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq hSameLength]
      rfl

theorem selectedEntries_mem {α : Type} {x : α} {xs : List α} {selected : List Bool}
    (hx : x ∈ selectedEntries xs selected) :
    x ∈ xs := by
  induction xs generalizing selected with
  | nil =>
      simp [selectedEntries] at hx
  | cons y ys ih =>
      cases selected with
      | nil =>
          simp [selectedEntries] at hx
      | cons bit selected =>
          cases bit
          · exact List.mem_cons_of_mem y (ih hx)
          · simp [selectedEntries] at hx
            rcases hx with rfl | hx
            · simp
            · exact List.mem_cons_of_mem y (ih hx)

theorem selectedEntries_append_append {α : Type}
    (xs ys : List α) (bits₁ bits₂ : List Bool)
    (hLength : bits₁.length = xs.length) :
    selectedEntries (xs ++ ys) (bits₁ ++ bits₂) =
      selectedEntries xs bits₁ ++ selectedEntries ys bits₂ := by
  induction xs generalizing bits₁ with
  | nil =>
      cases bits₁ with
      | nil =>
          simp [selectedEntries]
      | cons bit bits =>
          simp at hLength
  | cons x xs ih =>
      cases bits₁ with
      | nil =>
          simp at hLength
      | cons bit bits =>
          simp at hLength
          cases bit <;> simp [selectedEntries, ih bits hLength]

theorem selectedEntries_map {α β : Type} (xs : List α) (bits : List Bool) (f : α → β) :
    selectedEntries (xs.map f) bits = (selectedEntries xs bits).map f := by
  induction xs generalizing bits with
  | nil =>
      simp [selectedEntries]
  | cons x xs ih =>
      cases bits with
      | nil =>
          simp [selectedEntries]
      | cons bit bits =>
          cases bit <;> simp [selectedEntries, ih bits]

theorem selectedEntries_variableItemPairs
    (I : IntegerProgrammingInput) (a : BoolAssignment) (indices : List Nat) :
    selectedEntries
        (indices.flatMap fun i =>
          [compactVariableItemDigits I i true, compactVariableItemDigits I i false])
        (indices.flatMap fun i => [a i, !(a i)]) =
      indices.map fun i => compactVariableItemDigits I i (a i) := by
  induction indices with
  | nil =>
      simp [selectedEntries]
  | cons i indices ih =>
      cases h : a i <;> simp [selectedEntries, h, ih]

theorem selectedEntries_compactVariableItemSelection
    (I : IntegerProgrammingInput) (a : BoolAssignment) :
    selectedEntries (compactVariableItemDigitVectors I) (compactVariableItemSelection I a) =
      (List.range (varBound I)).map fun i => compactVariableItemDigits I i (a i) := by
  simpa [compactVariableItemDigitVectors, compactVariableItemSelection] using
    selectedEntries_variableItemPairs I a (List.range (varBound I))

theorem selectedVariableItemSelection_constraintDigit_sum
    (I : IntegerProgrammingInput) (a : BoolAssignment)
    {rowIndex : Nat} (hrow : rowIndex < I.constraints.length) :
    ((selectedEntries (compactVariableItemDigitVectors I)
        (compactVariableItemSelection I a)).map fun digits =>
          digits.getD (varBound I + rowIndex) 0).sum =
      compactConstraintValue a (I.constraints.getD rowIndex ([], (0 : Int))).1 := by
  have hConstraintMem :
      I.constraints.getD rowIndex ([], (0 : Int)) ∈ I.constraints := by
    rw [List.getD_eq_getElem (l := I.constraints) (d := ([], (0 : Int)))
      (n := rowIndex) hrow]
    exact List.getElem_mem _
  have hLen :
      (I.constraints.getD rowIndex ([], (0 : Int))).1.length ≤ varBound I :=
    constraint_row_length_le_varBound_of_mem hConstraintMem
  rw [selectedEntries_compactVariableItemSelection]
  rw [compactConstraintValue_eq_sum_range_of_length_le a
    (I.constraints.getD rowIndex ([], (0 : Int))).1 hLen]
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _hi
  exact compactVariableItemDigits_getD_constraint I rowIndex i (a i)

theorem compactVariableItemDigitVectors_mem_length
    {I : IntegerProgrammingInput} {digits : List Nat}
    (hdigits : digits ∈ compactVariableItemDigitVectors I) :
    digits.length = compactDigitCount I := by
  rcases List.mem_flatMap.mp hdigits with ⟨i, _hi, hmem⟩
  simp at hmem
  rcases hmem with rfl | rfl
  · exact compactVariableItemDigits_length I i true
  · exact compactVariableItemDigits_length I i false

theorem compactSlackItemDigitVectorsFrom_mem_length
    (I : IntegerProgrammingInput) (rowIndex : Nat) (constraints : List (List Int × Int))
    {digits : List Nat}
    (hdigits : digits ∈ compactSlackItemDigitVectorsFrom I rowIndex constraints) :
    digits.length = compactDigitCount I := by
  induction constraints generalizing rowIndex with
  | nil =>
      simp [compactSlackItemDigitVectorsFrom] at hdigits
  | cons constraint constraints ih =>
      rw [compactSlackItemDigitVectorsFrom] at hdigits
      rcases List.mem_append.mp hdigits with hHead | hTail
      · exact compactSlackItemDigitsForConstraint_mem_length hHead
      · exact ih (rowIndex + 1) hTail

theorem compactSlackSelectionsFrom_length
    (I : IntegerProgrammingInput) (constraints : List (List Int × Int))
    (a : BoolAssignment) (rowIndex : Nat) :
    (compactSlackSelectionsFrom I constraints a).length =
      (compactSlackItemDigitVectorsFrom I rowIndex constraints).length := by
  induction constraints generalizing rowIndex with
  | nil =>
      simp [compactSlackSelectionsFrom, compactSlackItemDigitVectorsFrom]
  | cons constraint constraints ih =>
      simp [compactSlackSelectionsFrom, compactSlackItemDigitVectorsFrom,
        compactSlackItemDigitsForConstraint, compactSlackSelection_length_of_le,
        compactSlackPowers_length, ih (rowIndex + 1)]

theorem compactSlackSelections_length (I : IntegerProgrammingInput) (a : BoolAssignment) :
    (compactSlackSelections I a).length = (compactSlackItemDigitVectors I).length := by
  exact compactSlackSelectionsFrom_length I I.constraints a 0

theorem compactSlackItemDigitVectors_mem_length
    {I : IntegerProgrammingInput} {digits : List Nat}
    (hdigits : digits ∈ compactSlackItemDigitVectors I) :
    digits.length = compactDigitCount I := by
  exact compactSlackItemDigitVectorsFrom_mem_length I 0 I.constraints hdigits

theorem compactSlackItemDigitsForConstraint_getD_variableChoice_zero
    {I : IntegerProgrammingInput} {rowIndex : Nat} {constraint : List Int × Int}
    {digits : List Nat}
    (hdigits : digits ∈ compactSlackItemDigitsForConstraint I rowIndex constraint)
    {i : Nat} (hi : i < varBound I) :
    digits.getD i 0 = 0 := by
  rcases List.mem_map.mp hdigits with ⟨power, _hpower, rfl⟩
  exact compactSlackItemDigits_getD_variableChoice I hi

theorem compactSlackItemDigitVectorsFrom_getD_variableChoice_zero
    (I : IntegerProgrammingInput) (rowIndex : Nat) (constraints : List (List Int × Int))
    {digits : List Nat}
    (hdigits : digits ∈ compactSlackItemDigitVectorsFrom I rowIndex constraints)
    {i : Nat} (hi : i < varBound I) :
    digits.getD i 0 = 0 := by
  induction constraints generalizing rowIndex with
  | nil =>
      simp [compactSlackItemDigitVectorsFrom] at hdigits
  | cons constraint constraints ih =>
      rw [compactSlackItemDigitVectorsFrom] at hdigits
      rcases List.mem_append.mp hdigits with hHead | hTail
      · exact compactSlackItemDigitsForConstraint_getD_variableChoice_zero hHead hi
      · exact ih (rowIndex + 1) hTail

theorem compactSlackItemDigitVectors_getD_variableChoice_zero
    {I : IntegerProgrammingInput} {digits : List Nat}
    (hdigits : digits ∈ compactSlackItemDigitVectors I)
    {i : Nat} (hi : i < varBound I) :
    digits.getD i 0 = 0 := by
  exact compactSlackItemDigitVectorsFrom_getD_variableChoice_zero I 0 I.constraints hdigits hi

theorem selectedSlackItemDigitsForConstraint_ownDigit_sum
    (I : IntegerProgrammingInput) {rowIndex : Nat} (constraint : List Int × Int)
    {slack : Nat} (hrow : rowIndex < I.constraints.length)
    (hSlack : slack ≤ compactConstraintBound constraint) :
    ((selectedEntries (compactSlackItemDigitsForConstraint I rowIndex constraint)
        (compactSlackSelection constraint slack)).map fun digits =>
          digits.getD (varBound I + rowIndex) 0).sum =
      slack := by
  have hSelection := compactSlackSelection_value_of_le constraint hSlack
  have hSelectedId :
      ((selectedEntries (compactSlackPowers constraint)
          (compactSlackSelection constraint slack)).map fun power => power).sum =
        slack := by
    have hMap :
        selectedNatSum (compactSlackPowers constraint) (compactSlackSelection constraint slack) =
          ((selectedEntries (compactSlackPowers constraint)
            (compactSlackSelection constraint slack)).map fun power => power).sum := by
      simpa using
        selectedNatSum_map (compactSlackPowers constraint)
          (compactSlackSelection constraint slack) (fun power => power)
    exact hMap.symm.trans hSelection
  rw [compactSlackItemDigitsForConstraint, selectedEntries_map, List.map_map]
  have hMapEq :
      List.map
          (((fun digits => digits.getD (varBound I + rowIndex) 0) ∘
            fun power => compactSlackItemDigits I rowIndex power))
          (selectedEntries (compactSlackPowers constraint)
            (compactSlackSelection constraint slack)) =
        (selectedEntries (compactSlackPowers constraint)
          (compactSlackSelection constraint slack)).map fun power => power := by
    apply List.map_congr_left
    intro power _hpower
    simpa [Function.comp_def] using
      compactSlackItemDigits_getD_constraint I
        (rowIndex := rowIndex) (slackRow := rowIndex) (power := power) hrow
  rw [hMapEq]
  exact hSelectedId

theorem selectedSlackItemDigitsForConstraint_otherDigit_sum
    (I : IntegerProgrammingInput) {rowIndex slackRow : Nat} (constraint : List Int × Int)
    (bits : List Bool) (hrow : rowIndex < I.constraints.length) (hne : rowIndex ≠ slackRow) :
    ((selectedEntries (compactSlackItemDigitsForConstraint I slackRow constraint) bits).map
        fun digits => digits.getD (varBound I + rowIndex) 0).sum = 0 := by
  rw [compactSlackItemDigitsForConstraint, selectedEntries_map, List.map_map]
  have hZero :
      List.map
          (((fun digits => digits.getD (varBound I + rowIndex) 0) ∘
            fun power => compactSlackItemDigits I slackRow power))
          (selectedEntries (compactSlackPowers constraint) bits) =
        (selectedEntries (compactSlackPowers constraint) bits).map fun _ => 0 := by
    apply List.map_congr_left
    intro power _hpower
    have hDigit :=
      compactSlackItemDigits_getD_constraint I
        (rowIndex := rowIndex) (slackRow := slackRow) (power := power) hrow
    simpa [Function.comp_def, hne] using hDigit
  rw [hZero]
  simp

/-- Recursive contribution of the slack blocks in a suffix to an absolute constraint digit. -/
def compactSlackContributionFrom
    (a : BoolAssignment) : Nat → List (List Int × Int) → Nat → Nat
  | _, [], _ => 0
  | start, constraint :: constraints, rowIndex =>
      (if rowIndex = start then
        compactConstraintBound constraint - compactConstraintValue a constraint.1
      else
        0) + compactSlackContributionFrom a (start + 1) constraints rowIndex

theorem compactSlackContributionFrom_eq_zero_of_lt_start
    (a : BoolAssignment) (constraints : List (List Int × Int))
    {start rowIndex : Nat} (hlt : rowIndex < start) :
    compactSlackContributionFrom a start constraints rowIndex = 0 := by
  induction constraints generalizing start with
  | nil =>
      simp [compactSlackContributionFrom]
  | cons constraint constraints ih =>
      have hne : rowIndex ≠ start := by omega
      rw [compactSlackContributionFrom]
      simp [hne]
      exact ih (by omega)

theorem selectedSlackItemDigitVectorsFrom_constraintDigit_sum
    (I : IntegerProgrammingInput) (a : BoolAssignment)
    (constraints : List (List Int × Int)) (start rowIndex : Nat)
    (hrow : rowIndex < I.constraints.length)
    (hAll : ∀ constraint ∈ constraints,
      compactConstraintValue a constraint.1 ≤ compactConstraintBound constraint) :
    ((selectedEntries (compactSlackItemDigitVectorsFrom I start constraints)
        (compactSlackSelectionsFrom I constraints a)).map fun digits =>
          digits.getD (varBound I + rowIndex) 0).sum =
      compactSlackContributionFrom a start constraints rowIndex := by
  induction constraints generalizing start with
  | nil =>
      simp [compactSlackItemDigitVectorsFrom, compactSlackSelectionsFrom,
        compactSlackContributionFrom, selectedEntries]
  | cons constraint constraints ih =>
      let slack := compactConstraintBound constraint - compactConstraintValue a constraint.1
      have hSlackLe : slack ≤ compactConstraintBound constraint := Nat.sub_le _ _
      have hHeadLength :
          (compactSlackSelection constraint slack).length =
            (compactSlackItemDigitsForConstraint I start constraint).length := by
        simp [slack, compactSlackSelection_length_of_le constraint hSlackLe,
          compactSlackItemDigitsForConstraint, compactSlackPowers_length]
      have hTailAll :
          ∀ tailConstraint ∈ constraints,
            compactConstraintValue a tailConstraint.1 ≤
              compactConstraintBound tailConstraint := by
        intro tailConstraint htail
        exact hAll tailConstraint (by simp [htail])
      rw [compactSlackItemDigitVectorsFrom, compactSlackSelectionsFrom]
      rw [selectedEntries_append_append
        (compactSlackItemDigitsForConstraint I start constraint)
        (compactSlackItemDigitVectorsFrom I (start + 1) constraints)
        (compactSlackSelection constraint slack)
        (compactSlackSelectionsFrom I constraints a) hHeadLength]
      rw [List.map_append, List.sum_append, ih (start + 1) hTailAll]
      by_cases hEq : rowIndex = start
      · subst rowIndex
        have hHead :=
          selectedSlackItemDigitsForConstraint_ownDigit_sum
            (I := I) (rowIndex := start) constraint hrow hSlackLe
        have hTailZero :
            compactSlackContributionFrom a (start + 1) constraints start = 0 :=
          compactSlackContributionFrom_eq_zero_of_lt_start a constraints (by omega)
        have hHead' :
            ((selectedEntries (compactSlackItemDigitsForConstraint I start constraint)
                (compactSlackSelection constraint
                  (compactConstraintBound constraint - compactConstraintValue a constraint.1))).map
                fun digits => digits.getD (varBound I + start) 0).sum =
              compactConstraintBound constraint - compactConstraintValue a constraint.1 := by
          simpa [slack] using hHead
        rw [hHead']
        simp [compactSlackContributionFrom, hTailZero]
      · have hHead :=
          selectedSlackItemDigitsForConstraint_otherDigit_sum
            (I := I) (rowIndex := rowIndex) (slackRow := start) constraint
            (compactSlackSelection constraint slack) hrow hEq
        have hHead' :
            ((selectedEntries (compactSlackItemDigitsForConstraint I start constraint)
                (compactSlackSelection constraint
                  (compactConstraintBound constraint - compactConstraintValue a constraint.1))).map
                fun digits => digits.getD (varBound I + rowIndex) 0).sum = 0 := by
          simpa [slack] using hHead
        rw [hHead']
        simp [compactSlackContributionFrom, hEq]

theorem compactSlackContributionFrom_eq_getD_of_offset
    (a : BoolAssignment) (constraints : List (List Int × Int)) (start idx : Nat)
    (hidx : idx < constraints.length) :
    compactSlackContributionFrom a start constraints (start + idx) =
      compactConstraintBound (constraints.getD idx ([], (0 : Int))) -
        compactConstraintValue a (constraints.getD idx ([], (0 : Int))).1 := by
  induction constraints generalizing start idx with
  | nil =>
      simp at hidx
  | cons constraint constraints ih =>
      cases idx with
      | zero =>
          have hTailZero :
              compactSlackContributionFrom a (start + 1) constraints start = 0 :=
            compactSlackContributionFrom_eq_zero_of_lt_start a constraints (by omega)
          simp [compactSlackContributionFrom, hTailZero]
      | succ idx =>
          have hidxTail : idx < constraints.length := by
            simpa using hidx
          have hrowEq : start + (idx + 1) = start + 1 + idx := by omega
          have hne : start + 1 + idx ≠ start := by omega
          rw [hrowEq]
          simp [compactSlackContributionFrom, hne, ih (start + 1) idx hidxTail]

theorem selectedSlackItemDigitVectors_constraintDigit_sum
    (I : IntegerProgrammingInput) (a : BoolAssignment)
    {rowIndex : Nat} (hrow : rowIndex < I.constraints.length)
    (hAll : ∀ constraint ∈ I.constraints,
      compactConstraintValue a constraint.1 ≤ compactConstraintBound constraint) :
    ((selectedEntries (compactSlackItemDigitVectors I)
        (compactSlackSelections I a)).map fun digits =>
          digits.getD (varBound I + rowIndex) 0).sum =
      compactConstraintBound (I.constraints.getD rowIndex ([], (0 : Int))) -
        compactConstraintValue a (I.constraints.getD rowIndex ([], (0 : Int))).1 := by
  have hSuffix :=
    selectedSlackItemDigitVectorsFrom_constraintDigit_sum
      I a I.constraints 0 rowIndex hrow hAll
  have hContribution :=
    compactSlackContributionFrom_eq_getD_of_offset a I.constraints 0 rowIndex hrow
  have hContribution' :
      compactSlackContributionFrom a 0 I.constraints rowIndex =
        compactConstraintBound (I.constraints.getD rowIndex ([], (0 : Int))) -
          compactConstraintValue a (I.constraints.getD rowIndex ([], (0 : Int))).1 := by
    simpa using hContribution
  rw [hContribution'] at hSuffix
  simpa [compactSlackItemDigitVectors, compactSlackSelections] using hSuffix

theorem compactItemDigitVectors_mem_length
    {I : IntegerProgrammingInput} {digits : List Nat}
    (hdigits : digits ∈ compactItemDigitVectors I) :
    digits.length = compactDigitCount I := by
  rcases List.mem_append.mp hdigits with hVariable | hSlack
  · exact compactVariableItemDigitVectors_mem_length hVariable
  · exact compactSlackItemDigitVectors_mem_length hSlack

theorem compactSelection_length (I : IntegerProgrammingInput) (a : BoolAssignment) :
    (compactSelection I a).length = (compactItemDigitVectors I).length := by
  simp [compactSelection, compactItemDigitVectors, compactVariableItemSelection_length,
    compactSlackSelections_length]

theorem selectedEntries_compactSelection
    (I : IntegerProgrammingInput) (a : BoolAssignment) :
    selectedEntries (compactItemDigitVectors I) (compactSelection I a) =
      selectedEntries (compactVariableItemDigitVectors I) (compactVariableItemSelection I a) ++
        selectedEntries (compactSlackItemDigitVectors I) (compactSlackSelections I a) := by
  rw [compactItemDigitVectors, compactSelection]
  exact selectedEntries_append_append
    (compactVariableItemDigitVectors I) (compactSlackItemDigitVectors I)
    (compactVariableItemSelection I a) (compactSlackSelections I a)
    (compactVariableItemSelection_length I a)

theorem sum_map_eq_zero_of_forall {α : Type} (xs : List α) (f : α → Nat)
    (hZero : ∀ x ∈ xs, f x = 0) :
    (xs.map f).sum = 0 := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : f x = 0 := hZero x (by simp)
      have htail : ∀ y ∈ xs, f y = 0 := by
        intro y hy
        exact hZero y (by simp [hy])
      simp [hx, ih htail]

theorem sum_range_indicator_eq_one {n i : Nat} (hi : i < n) :
    ((List.range n).map fun j => if i = j then 1 else 0).sum = 1 := by
  induction n generalizing i with
  | zero =>
      omega
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      by_cases hLast : i = n
      · subst i
        have hPrefixZero :
            ((List.range n).map fun j => if n = j then 1 else 0).sum = 0 := by
          apply sum_map_eq_zero_of_forall
          intro j hj
          have hjlt : j < n := List.mem_range.mp hj
          simp [Nat.ne_of_gt hjlt]
        simp [hPrefixZero]
      · have hiPrefix : i < n := by omega
        simp [hLast, ih hiPrefix]

theorem selectedVariableItemSelection_variableChoice_sum
    (I : IntegerProgrammingInput) (a : BoolAssignment)
    {i : Nat} (hi : i < varBound I) :
    ((selectedEntries (compactVariableItemDigitVectors I)
        (compactVariableItemSelection I a)).map fun digits => digits.getD i 0).sum = 1 := by
  rw [selectedEntries_compactVariableItemSelection, List.map_map]
  have hMap :
      (List.range (varBound I)).map
          (((fun digits => digits.getD i 0) ∘ fun j =>
            compactVariableItemDigits I j (a j))) =
        (List.range (varBound I)).map fun j => if i = j then 1 else 0 := by
    apply List.map_congr_left
    intro j _hj
    simpa [Function.comp_def] using
      compactVariableItemDigits_getD_variableChoice (I := I) (i := i) (j := j) hi (a j)
  rw [hMap]
  exact sum_range_indicator_eq_one hi

theorem selectedSlackItemDigitVectors_variableChoice_sum
    (I : IntegerProgrammingInput) (a : BoolAssignment)
    {i : Nat} (hi : i < varBound I) :
    ((selectedEntries (compactSlackItemDigitVectors I)
        (compactSlackSelections I a)).map fun digits => digits.getD i 0).sum = 0 := by
  apply sum_map_eq_zero_of_forall
  intro digits hdigits
  exact compactSlackItemDigitVectors_getD_variableChoice_zero (selectedEntries_mem hdigits) hi

theorem selectedCompactSelection_variableChoice_sum
    (I : IntegerProgrammingInput) (a : BoolAssignment)
    {i : Nat} (hi : i < varBound I) :
    ((selectedEntries (compactItemDigitVectors I) (compactSelection I a)).map fun digits =>
        digits.getD i 0).sum = 1 := by
  rw [selectedEntries_compactSelection, List.map_append, List.sum_append]
  rw [selectedVariableItemSelection_variableChoice_sum I a hi]
  rw [selectedSlackItemDigitVectors_variableChoice_sum I a hi]

theorem selectedCompactSelection_constraintDigit_sum
    (I : IntegerProgrammingInput) (a : BoolAssignment)
    {rowIndex : Nat} (hrow : rowIndex < I.constraints.length)
    (hAll : ∀ constraint ∈ I.constraints,
      compactConstraintValue a constraint.1 ≤ compactConstraintBound constraint) :
    ((selectedEntries (compactItemDigitVectors I) (compactSelection I a)).map fun digits =>
        digits.getD (varBound I + rowIndex) 0).sum =
      compactConstraintBound (I.constraints.getD rowIndex ([], (0 : Int))) := by
  have hConstraintMem :
      I.constraints.getD rowIndex ([], (0 : Int)) ∈ I.constraints := by
    rw [List.getD_eq_getElem (l := I.constraints) (d := ([], (0 : Int)))
      (n := rowIndex) hrow]
    exact List.getElem_mem _
  have hCurrentLe :
      compactConstraintValue a (I.constraints.getD rowIndex ([], (0 : Int))).1 ≤
        compactConstraintBound (I.constraints.getD rowIndex ([], (0 : Int))) :=
    hAll (I.constraints.getD rowIndex ([], (0 : Int))) hConstraintMem
  rw [selectedEntries_compactSelection, List.map_append, List.sum_append]
  rw [selectedVariableItemSelection_constraintDigit_sum I a hrow]
  rw [selectedSlackItemDigitVectors_constraintDigit_sum I a hrow hAll]
  omega

theorem selectedCompactSelection_digitwiseSum_getD
    (I : IntegerProgrammingInput) (a : BoolAssignment)
    (hAll : ∀ constraint ∈ I.constraints,
      compactConstraintValue a constraint.1 ≤ compactConstraintBound constraint)
    {idx : Nat} (hidx : idx < compactDigitCount I) :
    (digitwiseSum (compactDigitCount I)
        (selectedEntries (compactItemDigitVectors I) (compactSelection I a))).getD idx 0 =
      (compactTargetDigits I).getD idx 0 := by
  have hDigitwise :
      (digitwiseSum (compactDigitCount I)
          (selectedEntries (compactItemDigitVectors I) (compactSelection I a))).getD idx 0 =
        ((selectedEntries (compactItemDigitVectors I) (compactSelection I a)).map
          fun digits => digits.getD idx 0).sum := by
    exact digitwiseSum_getD_eq_sum_getD
      (vectors := selectedEntries (compactItemDigitVectors I) (compactSelection I a))
      (hLength := by
        intro digits hdigits
        exact compactItemDigitVectors_mem_length (selectedEntries_mem hdigits))
      hidx
  by_cases hVar : idx < varBound I
  · rw [hDigitwise]
    rw [selectedCompactSelection_variableChoice_sum I a hVar]
    exact (compactTargetDigits_getD_variableChoice I hVar).symm
  · let rowIndex := idx - varBound I
    have hrow : rowIndex < I.constraints.length := by
      simp [compactDigitCount] at hidx
      omega
    have hidxEq : idx = varBound I + rowIndex := by
      simp [rowIndex]
      omega
    rw [hidxEq] at hDigitwise
    rw [hidxEq, hDigitwise]
    rw [selectedCompactSelection_constraintDigit_sum I a hrow hAll]
    exact (compactTargetDigits_getD_constraint I rowIndex).symm

theorem selectedCompactSelection_digitwiseSum_eq_targetDigits
    (I : IntegerProgrammingInput) (a : BoolAssignment)
    (hAll : ∀ constraint ∈ I.constraints,
      compactConstraintValue a constraint.1 ≤ compactConstraintBound constraint) :
    digitwiseSum (compactDigitCount I)
        (selectedEntries (compactItemDigitVectors I) (compactSelection I a)) =
      compactTargetDigits I := by
  apply List.ext_get
  · rw [digitwiseSum_length, compactTargetDigits_length]
    intro digits hdigits
    exact compactItemDigitVectors_mem_length (selectedEntries_mem hdigits)
  · intro n hLeft hRight
    have hidx : n < compactDigitCount I := by
      simpa [compactTargetDigits_length] using hRight
    have hGetD :=
      selectedCompactSelection_digitwiseSum_getD I a hAll (idx := n) hidx
    have hLeftGet :
        (digitwiseSum (compactDigitCount I)
            (selectedEntries (compactItemDigitVectors I) (compactSelection I a))).getD n 0 =
          (digitwiseSum (compactDigitCount I)
            (selectedEntries (compactItemDigitVectors I) (compactSelection I a))).get
              ⟨n, hLeft⟩ :=
      List.getD_eq_get
        (l := digitwiseSum (compactDigitCount I)
          (selectedEntries (compactItemDigitVectors I) (compactSelection I a)))
        (d := 0) ⟨n, hLeft⟩
    have hRightGet :
        (compactTargetDigits I).getD n 0 =
          (compactTargetDigits I).get ⟨n, hRight⟩ :=
      List.getD_eq_get (l := compactTargetDigits I) (d := 0) ⟨n, hRight⟩
    rw [hLeftGet, hRightGet] at hGetD
    exact hGetD

theorem compactVariableItemDigitVectors_getD_variableChoice_le_one
    {I : IntegerProgrammingInput} {digits : List Nat}
    (hdigits : digits ∈ compactVariableItemDigitVectors I)
    {i : Nat} (hi : i < varBound I) :
    digits.getD i 0 ≤ 1 := by
  rcases List.mem_flatMap.mp hdigits with ⟨j, _hj, hmem⟩
  simp at hmem
  rcases hmem with rfl | rfl
  · rw [compactVariableItemDigits_getD_variableChoice I hi true]
    split <;> omega
  · rw [compactVariableItemDigits_getD_variableChoice I hi false]
    split <;> omega

theorem compactItemDigitVectors_getD_variableChoice_le_one
    {I : IntegerProgrammingInput} {digits : List Nat}
    (hdigits : digits ∈ compactItemDigitVectors I)
    {i : Nat} (hi : i < varBound I) :
    digits.getD i 0 ≤ 1 := by
  rcases List.mem_append.mp hdigits with hVariable | hSlack
  · exact compactVariableItemDigitVectors_getD_variableChoice_le_one hVariable hi
  · rw [compactSlackItemDigitVectors_getD_variableChoice_zero hSlack hi]
    omega

theorem compactItemDigitVectors_getD_variableChoice_eq_one
    {I : IntegerProgrammingInput} {digits : List Nat}
    (hdigits : digits ∈ compactItemDigitVectors I)
    {i : Nat} (hi : i < varBound I)
    (hget : digits.getD i 0 = 1) :
    ∃ b : Bool, digits = compactVariableItemDigits I i b := by
  rcases List.mem_append.mp hdigits with hVariable | hSlack
  · rcases List.mem_flatMap.mp hVariable with ⟨j, _hj, hmem⟩
    simp at hmem
    rcases hmem with rfl | rfl
    · rw [compactVariableItemDigits_getD_variableChoice I hi true] at hget
      by_cases hEq : i = j
      · subst j
        exact ⟨true, rfl⟩
      · simp [hEq] at hget
    · rw [compactVariableItemDigits_getD_variableChoice I hi false] at hget
      by_cases hEq : i = j
      · subst j
        exact ⟨false, rfl⟩
      · simp [hEq] at hget
  · rw [compactSlackItemDigitVectors_getD_variableChoice_zero hSlack hi] at hget
    omega

theorem exists_mem_eq_one_of_sum_eq_one_of_le_one {xs : List Nat}
    (hSum : xs.sum = 1) (hle : ∀ x ∈ xs, x ≤ 1) :
    ∃ x ∈ xs, x = 1 := by
  induction xs with
  | nil =>
      simp at hSum
  | cons x xs ih =>
      have hxle : x ≤ 1 := hle x (by simp)
      by_cases hx : x = 0
      · have hTailSum : xs.sum = 1 := by
          simp [hx] at hSum
          exact hSum
        have hTailLe : ∀ y ∈ xs, y ≤ 1 := by
          intro y hy
          exact hle y (by simp [hy])
        rcases ih hTailSum hTailLe with ⟨y, hy, hyOne⟩
        exact ⟨y, by simp [hy], hyOne⟩
      · have hxOne : x = 1 := by omega
        exact ⟨x, by simp, hxOne⟩

/-- Decode a Boolean assignment from the selected compact truth items. -/
def decodedCompactAssignment (I : IntegerProgrammingInput) (selected : List Bool) :
    BoolAssignment :=
  fun i =>
    if compactVariableItemDigits I i true ∈
        selectedEntries (compactItemDigitVectors I) selected then
      true
    else
      false

theorem decodedCompactAssignment_eq_true_iff
    (I : IntegerProgrammingInput) (selected : List Bool) (i : Nat) :
    decodedCompactAssignment I selected i = true ↔
      compactVariableItemDigits I i true ∈
        selectedEntries (compactItemDigitVectors I) selected := by
  simp [decodedCompactAssignment]

theorem selectedVariableChoiceExists_of_count_eq_one
    (I : IntegerProgrammingInput) (selected : List Bool)
    {i : Nat} (hi : i < varBound I)
    (hCount : selectedVariableChoiceCount I i selected = 1) :
    ∃ b : Bool,
      compactVariableItemDigits I i b ∈
        selectedEntries (compactItemDigitVectors I) selected := by
  have hEntries :
      ((selectedEntries (compactItemDigitVectors I) selected).map
          fun digits => digits.getD i 0).sum = 1 := by
    have hMap :=
      selectedNatSum_map (compactItemDigitVectors I) selected
        (fun digits => digits.getD i 0)
    rw [selectedVariableChoiceCount, compactVariableChoiceCountWeights] at hCount
    rw [hMap] at hCount
    exact hCount
  have hLe : ∀ x ∈
      ((selectedEntries (compactItemDigitVectors I) selected).map
        fun digits => digits.getD i 0), x ≤ 1 := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨digits, hdigits, rfl⟩
    exact compactItemDigitVectors_getD_variableChoice_le_one
      (selectedEntries_mem hdigits) hi
  rcases exists_mem_eq_one_of_sum_eq_one_of_le_one hEntries hLe with
    ⟨x, hx, hxOne⟩
  rcases List.mem_map.mp hx with ⟨digits, hdigits, hDigitEq⟩
  have hget : digits.getD i 0 = 1 := hDigitEq.trans hxOne
  rcases compactItemDigitVectors_getD_variableChoice_eq_one
      (selectedEntries_mem hdigits) hi hget with ⟨b, hEq⟩
  exact ⟨b, by simpa [← hEq] using hdigits⟩

theorem selectedCompactItemDigitVectors_mem_length
    {I : IntegerProgrammingInput} {selected : List Bool} {digits : List Nat}
    (hdigits : digits ∈ selectedEntries (compactItemDigitVectors I) selected) :
    digits.length = compactDigitCount I := by
  exact compactItemDigitVectors_mem_length (selectedEntries_mem hdigits)

theorem selectedVariableChoiceCount_eq_digitwiseSum_getD
    (I : IntegerProgrammingInput) (selected : List Bool) {i : Nat}
    (hi : i < varBound I) :
    selectedVariableChoiceCount I i selected =
      (digitwiseSum (compactDigitCount I)
        (selectedEntries (compactItemDigitVectors I) selected)).getD i 0 := by
  have hidx : i < compactDigitCount I := by
    simp [compactDigitCount]
    omega
  have hDigitwise :=
    digitwiseSum_getD_eq_sum_getD
      (vectors := selectedEntries (compactItemDigitVectors I) selected)
      (hLength := by
        intro digits hdigits
        exact selectedCompactItemDigitVectors_mem_length hdigits)
      hidx
  rw [hDigitwise]
  simpa [selectedVariableChoiceCount, compactVariableChoiceCountWeights] using
    selectedNatSum_map (compactItemDigitVectors I) selected (fun digits => digits.getD i 0)

theorem selectedCompactItemCodes_sum_eq_ofDigits_digitwiseSum
    (I : IntegerProgrammingInput) (selected : List Bool) :
    ((selectedEntries (compactItemDigitVectors I) selected).map
        (compactDigitCode I)).sum =
      Nat.ofDigits (compactBase I)
        (digitwiseSum (compactDigitCount I)
          (selectedEntries (compactItemDigitVectors I) selected)) := by
  apply sum_digitCodes_eq_ofDigits_digitwiseSum
  intro digits hdigits
  exact selectedCompactItemDigitVectors_mem_length hdigits

theorem selectedNatSum_compactSelection_eq_targetCode
    (I : IntegerProgrammingInput) (a : BoolAssignment)
    (hAll : ∀ constraint ∈ I.constraints,
      compactConstraintValue a constraint.1 ≤ compactConstraintBound constraint) :
    selectedNatSum (compactItemCodes I) (compactSelection I a) = compactTargetCode I := by
  rw [selectedNatSum_compactItemCodes,
    selectedCompactItemCodes_sum_eq_ofDigits_digitwiseSum]
  rw [selectedCompactSelection_digitwiseSum_eq_targetDigits I a hAll]
  simp [compactTargetCode, compactDigitCode]

theorem compactMapCore_knapsack_of_compactConstraints
    (I : IntegerProgrammingInput) (a : BoolAssignment)
    (hAll : ∀ constraint ∈ I.constraints,
      compactConstraintValue a constraint.1 ≤ compactConstraintBound constraint) :
    Combinatorics.Knapsack (compactMapCore I) := by
  rw [compactMapCore_knapsack_iff_selectedNatSum_eq]
  refine ⟨compactSelection I a, ?_, ?_⟩
  · simpa [compactItemCodes] using compactSelection_length I a
  · exact selectedNatSum_compactSelection_eq_targetCode I a hAll

theorem compactMapCore_knapsack_of_zeroOneIP
    (I : IntegerProgrammingInput)
    (hBounds : compactConstraintBoundsNonnegative I)
    (hIP : ZeroOneIntegerProgramming I) :
    Combinatorics.Knapsack (compactMapCore I) := by
  rcases (zeroOneIP_iff_compactConstraints_of_bounds I hBounds).1 hIP with ⟨a, hAll⟩
  exact compactMapCore_knapsack_of_compactConstraints I a hAll

theorem compactMap_knapsack_of_zeroOneIP
    (I : IntegerProgrammingInput) :
    ZeroOneIntegerProgramming I → Combinatorics.Knapsack (compactMap I) := by
  classical
  rintro ⟨a, hSat⟩
  have hBounds : compactConstraintBoundsNonnegative I := by
    intro constraint hConstraint
    by_contra hBound
    exact not_satisfiesConstraint_of_not_compactConstraintBoundNonnegative
      a constraint hBound (hSat constraint hConstraint)
  have hAll :
      ∀ constraint ∈ I.constraints,
        compactConstraintValue a constraint.1 ≤ compactConstraintBound constraint := by
    intro constraint hConstraint
    exact (satisfiesConstraint_iff_compactConstraintValue_le a constraint
      (hBounds constraint hConstraint)).1 (hSat constraint hConstraint)
  simp [compactMap, hBounds, compactMapCore_knapsack_of_compactConstraints I a hAll]

theorem selectedCompactCodeSum_eq_targetCode_to_ofDigits_eq
    (I : IntegerProgrammingInput) (selected : List Bool)
    (hSum : selectedNatSum (compactItemCodes I) selected = compactTargetCode I) :
    Nat.ofDigits (compactBase I)
        (digitwiseSum (compactDigitCount I)
          (selectedEntries (compactItemDigitVectors I) selected)) =
      Nat.ofDigits (compactBase I) (compactTargetDigits I) := by
  rw [selectedNatSum_compactItemCodes,
    selectedCompactItemCodes_sum_eq_ofDigits_digitwiseSum] at hSum
  simpa [compactTargetCode, compactDigitCode] using hSum

theorem zipWith_add_sum_le (xs ys : List Nat) :
    (xs.zipWith (· + ·) ys).sum ≤ xs.sum + ys.sum := by
  induction xs generalizing ys with
  | nil =>
      simp
  | cons x xs ih =>
      cases ys with
      | nil =>
          simp
      | cons y ys =>
          have hTail := ih ys
          simp
          omega

theorem digitwiseSum_sum_le_mass (length : Nat) (vectors : List (List Nat)) :
    (digitwiseSum length vectors).sum ≤ compactDigitVectorsMass vectors := by
  induction vectors with
  | nil =>
      simp [digitwiseSum, compactDigitVectorsMass]
  | cons digits vectors ih =>
      have hZip := zipWith_add_sum_le digits (digitwiseSum length vectors)
      have h :
          (digits.zipWith (· + ·) (digitwiseSum length vectors)).sum ≤
            digits.sum + compactDigitVectorsMass vectors :=
        le_trans hZip (Nat.add_le_add_left ih digits.sum)
      simpa [digitwiseSum, compactDigitVectorsMass] using h

end Knapsack
end Karp21
end ComplexityReduction
