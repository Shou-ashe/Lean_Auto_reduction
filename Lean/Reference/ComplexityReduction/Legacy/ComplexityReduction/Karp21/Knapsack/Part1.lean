/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ZeroOneIP
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ExactCover
import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.Knapsack
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

/-!
P15c arithmetic target: 0-1 Integer Programming to Knapsack.
-/

namespace ComplexityReduction
namespace Karp21
namespace Knapsack

open ComplexityReduction.Combinatorics

/-- Number of Boolean variables touched by one IP constraint row. -/
def constraintVarBound (constraint : List Int × Int) : Nat :=
  constraint.1.length

/-- Structural upper bound for all variable positions mentioned by constraints. -/
def constraintsVarBound : List (List Int × Int) → Nat
  | [] => 0
  | c :: cs => max (constraintVarBound c) (constraintsVarBound cs)

theorem constraintVarBound_le_constraintsVarBound_of_mem {constraints : List (List Int × Int)}
    {constraint : List Int × Int} (h : constraint ∈ constraints) :
    constraintVarBound constraint ≤ constraintsVarBound constraints := by
  induction constraints with
  | nil =>
      simp at h
  | cons head tail ih =>
      simp at h
      rcases h with rfl | h
      · exact Nat.le_max_left _ _
      · exact (ih h).trans (Nat.le_max_right _ _)

/-- Finite variable range used to truncate arbitrary IP assignments.

Only coefficients appearing in constraint rows affect `ZeroOneIntegerProgramming`;
the declared `numVariables` field is semantic metadata in this local encoding and
may be binary-large.  The compact Knapsack route must therefore expand only the
row-touched variables to preserve a polynomial binary output-size certificate.
-/
def varBound (I : IntegerProgrammingInput) : Nat :=
  constraintsVarBound I.constraints

theorem constraint_row_length_le_varBound_of_mem {I : IntegerProgrammingInput}
    {constraint : List Int × Int} (h : constraint ∈ I.constraints) :
    constraint.1.length ≤ varBound I := by
  exact constraintVarBound_le_constraintsVarBound_of_mem h

theorem rowValueFrom_boundedAssignment_eq {n i : Nat} {row : List Int}
    {a : BoolAssignment} {f : Fin n → Bool}
    (hBound : i + row.length ≤ n)
    (hf : ∀ j : Fin n, f j = a j.val) :
    rowValueFrom (Clique.boundedAssignment n f) i row = rowValueFrom a i row := by
  induction row generalizing i with
  | nil =>
      simp [rowValueFrom]
  | cons c cs ih =>
      have hBound' : i + (cs.length + 1) ≤ n := by
        simpa using hBound
      have hi : i < n := by omega
      have htail : i + 1 + cs.length ≤ n := by omega
      have hValue :
          boolValue (Clique.boundedAssignment n f) i = boolValue a i := by
        simp [boolValue, Clique.boundedAssignment, hi, hf ⟨i, hi⟩]
      simp [rowValueFrom, hValue, ih htail]

theorem rowValue_boundedAssignment_eq {n : Nat} {row : List Int}
    {a : BoolAssignment} {f : Fin n → Bool}
    (hBound : row.length ≤ n)
    (hf : ∀ j : Fin n, f j = a j.val) :
    rowValue (Clique.boundedAssignment n f) row = rowValue a row := by
  simpa [rowValue] using
    rowValueFrom_boundedAssignment_eq (n := n) (i := 0) (row := row)
      (a := a) (f := f) (by omega) hf

/-- Bounded assignments satisfying a finite 0-1 IP instance. -/
noncomputable def satisfyingAssignments (I : IntegerProgrammingInput) :
    List (Fin (varBound I) → Bool) := by
  classical
  exact (Clique.assignmentList (varBound I)).filter fun f =>
    decide
      (∀ constraint ∈ I.constraints,
        SatisfiesConstraint (Clique.boundedAssignment (varBound I) f) constraint)

theorem mem_satisfyingAssignments_iff (I : IntegerProgrammingInput)
    (f : Fin (varBound I) → Bool) :
    f ∈ satisfyingAssignments I ↔
      f ∈ Clique.assignmentList (varBound I) ∧
        ∀ constraint ∈ I.constraints,
          SatisfiesConstraint (Clique.boundedAssignment (varBound I) f) constraint := by
  classical
  simp [satisfyingAssignments]

theorem zeroOneIP_iff_satisfyingAssignments_pos (I : IntegerProgrammingInput) :
    ZeroOneIntegerProgramming I ↔ 0 < (satisfyingAssignments I).length := by
  constructor
  · rintro ⟨a, hAll⟩
    let n := varBound I
    let f : Fin n → Bool := fun i => a i.val
    have hf : f ∈ satisfyingAssignments I := by
      refine (mem_satisfyingAssignments_iff I f).2 ?_
      refine ⟨Clique.mem_assignmentList n f, ?_⟩
      intro constraint hConstraint
      have hLen : constraint.1.length ≤ n := by
        simpa [n] using constraint_row_length_le_varBound_of_mem hConstraint
      have hRow :=
        rowValue_boundedAssignment_eq (n := n) (row := constraint.1)
          (a := a) (f := f) hLen (by intro j; rfl)
      unfold SatisfiesConstraint
      rw [hRow]
      exact hAll constraint hConstraint
    exact List.length_pos_of_mem hf
  · intro hPos
    cases hList : satisfyingAssignments I with
    | nil =>
        simp [hList] at hPos
    | cons f rest =>
        have hf : f ∈ satisfyingAssignments I := by
          simp [hList]
        have hAll := (mem_satisfyingAssignments_iff I f).1 hf |>.2
        exact ⟨Clique.boundedAssignment (varBound I) f, hAll⟩

/-! ### Compact signed-row normalization for the P15m replacement route -/

/-- Nonnegative part of an integer coefficient. -/
def intPositivePart : Int → Nat
  | Int.ofNat n => n
  | Int.negSucc _ => 0

/-- Magnitude of the negative part of an integer coefficient. -/
def intNegativePart : Int → Nat
  | Int.ofNat _ => 0
  | Int.negSucc n => n + 1

theorem int_eq_positivePart_sub_negativePart (z : Int) :
    z = (intPositivePart z : Int) - (intNegativePart z : Int) := by
  cases z with
  | ofNat n =>
      simp [intPositivePart, intNegativePart]
  | negSucc n =>
      simp [intPositivePart, intNegativePart]
      omega

/--
Contribution of one signed coefficient to the compact nonnegative row after
choosing either the true item or the false item for its variable.
-/
def compactCoeffContribution (z : Int) (b : Bool) : Nat :=
  if b then intPositivePart z else intNegativePart z

theorem compactCoeffContribution_zero (b : Bool) :
    compactCoeffContribution 0 b = 0 := by
  cases b <;> simp [compactCoeffContribution, intPositivePart, intNegativePart]

theorem compactCoeffContribution_eq_int (z : Int) (b : Bool) :
    (compactCoeffContribution z b : Int) =
      z * (if b then (1 : Int) else 0) + intNegativePart z := by
  cases z with
  | ofNat n =>
      cases b <;> simp [compactCoeffContribution, intPositivePart, intNegativePart]
  | negSucc n =>
      cases b
      · simp [compactCoeffContribution, intNegativePart]
      · simp [compactCoeffContribution, intPositivePart, intNegativePart]
        omega

/-- Sum of negative-coefficient magnitudes in a row. -/
def rowNegativeShift : List Int → Nat
  | [] => 0
  | c :: cs => intNegativePart c + rowNegativeShift cs

/-- Nonnegative compact row value, starting at variable index `i`. -/
def compactConstraintValueFrom (a : BoolAssignment) : Nat → List Int → Nat
  | _, [] => 0
  | i, c :: cs =>
      compactCoeffContribution c (a i) + compactConstraintValueFrom a (i + 1) cs

/-- Nonnegative compact row value for the row at variable index zero. -/
def compactConstraintValue (a : BoolAssignment) (row : List Int) : Nat :=
  compactConstraintValueFrom a 0 row

theorem compactConstraintValueFrom_eq_sum_range_getD
    (a : BoolAssignment) (start : Nat) (row : List Int) :
    compactConstraintValueFrom a start row =
      ((List.range row.length).map fun i =>
        compactCoeffContribution (row.getD i 0) (a (start + i))).sum := by
  induction row generalizing start with
  | nil =>
      simp [compactConstraintValueFrom]
  | cons c cs ih =>
      change compactCoeffContribution c (a start) + compactConstraintValueFrom a (start + 1) cs =
        ((List.range (cs.length + 1)).map fun i =>
          compactCoeffContribution ((c :: cs).getD i 0) (a (start + i))).sum
      rw [List.sum_range_succ']
      simp [ih (start + 1), Nat.add_comm, Nat.add_left_comm]

theorem compactConstraintValueFrom_eq_rowValueFrom_add_shift
    (a : BoolAssignment) (i : Nat) (row : List Int) :
    (compactConstraintValueFrom a i row : Int) =
      rowValueFrom a i row + rowNegativeShift row := by
  induction row generalizing i with
  | nil =>
      simp [compactConstraintValueFrom, rowValueFrom, rowNegativeShift]
  | cons c cs ih =>
      simp [compactConstraintValueFrom, rowValueFrom, rowNegativeShift, ih,
        compactCoeffContribution_eq_int, boolValue]
      ring

theorem compactConstraintValue_eq_rowValue_add_shift
    (a : BoolAssignment) (row : List Int) :
    (compactConstraintValue a row : Int) =
      rowValue a row + rowNegativeShift row := by
  simpa [compactConstraintValue, rowValue] using
    compactConstraintValueFrom_eq_rowValueFrom_add_shift a 0 row

/-- Shifted nonnegative bound for a signed 0-1 IP row. -/
def compactConstraintBound (constraint : List Int × Int) : Nat :=
  Int.toNat (constraint.2 + rowNegativeShift constraint.1)

/-- The shifted row bound is nonnegative; otherwise the compact guarded map will reject. -/
def compactConstraintBoundNonnegative (constraint : List Int × Int) : Prop :=
  0 ≤ constraint.2 + rowNegativeShift constraint.1

theorem satisfiesConstraint_iff_compactConstraintValue_le
    (a : BoolAssignment) (constraint : List Int × Int)
    (hBound : compactConstraintBoundNonnegative constraint) :
    SatisfiesConstraint a constraint ↔
      compactConstraintValue a constraint.1 ≤ compactConstraintBound constraint := by
  constructor
  · intro hSat
    have hInt :
        (compactConstraintValue a constraint.1 : Int) ≤
          constraint.2 + rowNegativeShift constraint.1 := by
      rw [compactConstraintValue_eq_rowValue_add_shift]
      change rowValue a constraint.1 ≤ constraint.2 at hSat
      linarith
    exact Int.ofNat_le.mp (by
      simpa [compactConstraintBound, Int.toNat_of_nonneg hBound] using hInt)
  · intro hCompact
    have hInt :
        (compactConstraintValue a constraint.1 : Int) ≤
          constraint.2 + rowNegativeShift constraint.1 := by
      have hNatCast : (compactConstraintValue a constraint.1 : Int) ≤
          (compactConstraintBound constraint : Int) :=
        Int.ofNat_le.mpr hCompact
      simpa [compactConstraintBound, Int.toNat_of_nonneg hBound] using hNatCast
    rw [compactConstraintValue_eq_rowValue_add_shift] at hInt
    exact le_of_add_le_add_right hInt

/-- All shifted row bounds in an integer-programming instance are nonnegative. -/
def compactConstraintBoundsNonnegative (I : IntegerProgrammingInput) : Prop :=
  ∀ constraint ∈ I.constraints, compactConstraintBoundNonnegative constraint

theorem not_satisfiesConstraint_of_not_compactConstraintBoundNonnegative
    (a : BoolAssignment) (constraint : List Int × Int)
    (hBound : ¬ compactConstraintBoundNonnegative constraint) :
    ¬ SatisfiesConstraint a constraint := by
  intro hSat
  have hInt :
      (compactConstraintValue a constraint.1 : Int) ≤
        constraint.2 + rowNegativeShift constraint.1 := by
    rw [compactConstraintValue_eq_rowValue_add_shift]
    change rowValue a constraint.1 ≤ constraint.2 at hSat
    linarith
  have hNonneg : 0 ≤ (compactConstraintValue a constraint.1 : Int) := Int.natCast_nonneg _
  have hNegative : constraint.2 + rowNegativeShift constraint.1 < 0 :=
    lt_of_not_ge hBound
  linarith

theorem not_zeroOneIP_of_not_compactConstraintBoundNonnegative
    {I : IntegerProgrammingInput} {constraint : List Int × Int}
    (hConstraint : constraint ∈ I.constraints)
    (hBound : ¬ compactConstraintBoundNonnegative constraint) :
    ¬ ZeroOneIntegerProgramming I := by
  rintro ⟨a, hAll⟩
  exact not_satisfiesConstraint_of_not_compactConstraintBoundNonnegative a constraint hBound
    (hAll constraint hConstraint)

theorem zeroOneIP_iff_compactConstraints_of_bounds
    (I : IntegerProgrammingInput) (hBounds : compactConstraintBoundsNonnegative I) :
    ZeroOneIntegerProgramming I ↔
      ∃ a : BoolAssignment,
        ∀ constraint ∈ I.constraints,
          compactConstraintValue a constraint.1 ≤ compactConstraintBound constraint := by
  constructor
  · rintro ⟨a, hAll⟩
    refine ⟨a, ?_⟩
    intro constraint hConstraint
    exact (satisfiesConstraint_iff_compactConstraintValue_le a constraint
      (hBounds constraint hConstraint)).1 (hAll constraint hConstraint)
  · rintro ⟨a, hAll⟩
    refine ⟨a, ?_⟩
    intro constraint hConstraint
    exact (satisfiesConstraint_iff_compactConstraintValue_le a constraint
      (hBounds constraint hConstraint)).2 (hAll constraint hConstraint)

/-- Coefficient at variable index `i`, padding short rows with zero coefficients. -/
def compactCoeffAt (row : List Int) (i : Nat) : Int :=
  row.getD i 0

theorem compactConstraintValue_eq_sum_range_length
    (a : BoolAssignment) (row : List Int) :
    compactConstraintValue a row =
      ((List.range row.length).map fun i =>
        compactCoeffContribution (compactCoeffAt row i) (a i)).sum := by
  simpa [compactConstraintValue, compactCoeffAt] using
    compactConstraintValueFrom_eq_sum_range_getD a 0 row

theorem compactCoeffContribution_compactCoeffAt_eq_zero_of_length_le
    (row : List Int) (a : BoolAssignment) {i : Nat} (hi : row.length ≤ i) :
    compactCoeffContribution (compactCoeffAt row i) (a i) = 0 := by
  rw [compactCoeffAt, List.getD_eq_default (l := row) (d := (0 : Int)) (n := i) hi]
  exact compactCoeffContribution_zero (a i)

theorem compactCoeffContribution_range_sum_eq_length_of_le
    (row : List Int) (a : BoolAssignment) (n : Nat) (hLength : row.length ≤ n) :
    ((List.range n).map fun i =>
        compactCoeffContribution (compactCoeffAt row i) (a i)).sum =
      ((List.range row.length).map fun i =>
        compactCoeffContribution (compactCoeffAt row i) (a i)).sum := by
  induction n with
  | zero =>
      have hRowLength : row.length = 0 := by omega
      simp [hRowLength]
  | succ n ih =>
      by_cases hEq : row.length = n + 1
      · simp [hEq]
      · have hLe : row.length ≤ n := by omega
        rw [List.sum_range_succ]
        rw [compactCoeffContribution_compactCoeffAt_eq_zero_of_length_le row a hLe]
        simp [ih hLe]

theorem compactConstraintValue_eq_sum_range_of_length_le
    (a : BoolAssignment) (row : List Int) {n : Nat} (hLength : row.length ≤ n) :
    compactConstraintValue a row =
      ((List.range n).map fun i =>
        compactCoeffContribution (compactCoeffAt row i) (a i)).sum := by
  rw [compactConstraintValue_eq_sum_range_length]
  exact (compactCoeffContribution_range_sum_eq_length_of_le row a n hLength).symm

/-- Number of base digits used by the compact variable/constraint layout. -/
def compactDigitCount (I : IntegerProgrammingInput) : Nat :=
  varBound I + I.constraints.length

/-- Variable-choice digits: both truth items contribute `1` to their variable position. -/
def compactVariableChoiceDigits (I : IntegerProgrammingInput) (i : Nat) : List Nat :=
  (List.range (varBound I)).map fun j => if j = i then 1 else 0

/--
Constraint digits contributed by one truth item.  Short rows are padded with zero
coefficients so every bounded variable position has a contribution for every row.
-/
def compactVariableConstraintDigits
    (I : IntegerProgrammingInput) (i : Nat) (b : Bool) : List Nat :=
  I.constraints.map fun constraint => compactCoeffContribution (compactCoeffAt constraint.1 i) b

/-- Complete digit vector for one compact truth item. -/
def compactVariableItemDigits
    (I : IntegerProgrammingInput) (i : Nat) (b : Bool) : List Nat :=
  compactVariableChoiceDigits I i ++ compactVariableConstraintDigits I i b

/-- Target digits: choose one truth item per variable and hit each shifted row bound. -/
def compactTargetDigits (I : IntegerProgrammingInput) : List Nat :=
  List.replicate (varBound I) 1 ++ I.constraints.map compactConstraintBound

theorem compactVariableChoiceDigits_length (I : IntegerProgrammingInput) (i : Nat) :
    (compactVariableChoiceDigits I i).length = varBound I := by
  simp [compactVariableChoiceDigits]

theorem compactVariableConstraintDigits_length
    (I : IntegerProgrammingInput) (i : Nat) (b : Bool) :
    (compactVariableConstraintDigits I i b).length = I.constraints.length := by
  simp [compactVariableConstraintDigits]

theorem compactVariableItemDigits_length
    (I : IntegerProgrammingInput) (i : Nat) (b : Bool) :
    (compactVariableItemDigits I i b).length = compactDigitCount I := by
  simp [compactVariableItemDigits, compactDigitCount, compactVariableChoiceDigits,
    compactVariableConstraintDigits]

theorem compactTargetDigits_length (I : IntegerProgrammingInput) :
    (compactTargetDigits I).length = compactDigitCount I := by
  simp [compactTargetDigits, compactDigitCount]

theorem compactTargetDigits_getD_variableChoice
    (I : IntegerProgrammingInput) {i : Nat} (hi : i < varBound I) :
    (compactTargetDigits I).getD i 0 = 1 := by
  have hPrefix : i < (List.replicate (varBound I) 1).length := by
    simpa using hi
  rw [compactTargetDigits]
  rw [List.getD_append (l := List.replicate (varBound I) 1)
    (l' := I.constraints.map compactConstraintBound) (d := 0) (n := i) hPrefix]
  exact List.getD_replicate (x := (1 : Nat)) (y := 0) hi

theorem compactConstraintBound_nil_zero :
    compactConstraintBound ([], (0 : Int)) = 0 := by
  simp [compactConstraintBound, rowNegativeShift]

theorem compactTargetDigits_getD_constraint
    (I : IntegerProgrammingInput) (rowIndex : Nat) :
    (compactTargetDigits I).getD (varBound I + rowIndex) 0 =
      compactConstraintBound (I.constraints.getD rowIndex ([], (0 : Int))) := by
  have hPrefix :
      (List.replicate (varBound I) 1).length ≤ varBound I + rowIndex := by
    simp
  rw [compactTargetDigits]
  rw [List.getD_append_right (l := List.replicate (varBound I) 1)
    (l' := I.constraints.map compactConstraintBound) (d := 0)
    (n := varBound I + rowIndex) hPrefix]
  rw [List.length_replicate, Nat.add_sub_cancel_left]
  rw [← compactConstraintBound_nil_zero]
  rw [List.getD_map (l := I.constraints) (d := ([], (0 : Int))) compactConstraintBound]

theorem compactVariableItemDigits_getD_variableChoice
    (I : IntegerProgrammingInput) {i j : Nat} (hi : i < varBound I) (b : Bool) :
    (compactVariableItemDigits I j b).getD i 0 = if i = j then 1 else 0 := by
  have hChoice : i < (compactVariableChoiceDigits I j).length := by
    simpa [compactVariableChoiceDigits_length] using hi
  rw [compactVariableItemDigits]
  rw [List.getD_append (l := compactVariableChoiceDigits I j)
    (l' := compactVariableConstraintDigits I j b) (d := 0) (n := i) hChoice]
  rw [List.getD_eq_getElem (l := compactVariableChoiceDigits I j) (d := 0)
    (n := i) hChoice]
  simp [compactVariableChoiceDigits]

theorem compactVariableItemDigits_getD_constraint
    (I : IntegerProgrammingInput) (rowIndex i : Nat) (b : Bool) :
    (compactVariableItemDigits I i b).getD (varBound I + rowIndex) 0 =
      compactCoeffContribution
        (compactCoeffAt (I.constraints.getD rowIndex ([], (0 : Int))).1 i) b := by
  have hPrefix :
      (compactVariableChoiceDigits I i).length ≤ varBound I + rowIndex := by
    rw [compactVariableChoiceDigits_length]
    omega
  rw [compactVariableItemDigits]
  rw [List.getD_append_right (l := compactVariableChoiceDigits I i)
    (l' := compactVariableConstraintDigits I i b) (d := 0)
    (n := varBound I + rowIndex) hPrefix]
  rw [compactVariableChoiceDigits_length, Nat.add_sub_cancel_left]
  have hDefault :
      compactCoeffContribution (compactCoeffAt ([] : List Int) i) b = 0 := by
    cases b <;> simp [compactCoeffContribution, compactCoeffAt, intPositivePart, intNegativePart]
  rw [← hDefault]
  rw [compactVariableConstraintDigits]
  rw [List.getD_map (l := I.constraints) (d := ([], (0 : Int)))
    (fun constraint => compactCoeffContribution (compactCoeffAt constraint.1 i) b)]

/-- Number of binary slack powers allocated for one shifted row bound. -/
def compactSlackBitCount (constraint : List Int × Int) : Nat :=
  (Nat.digits 2 (compactConstraintBound constraint)).length

/-- First `n` little-endian binary place values. -/
def compactBinaryPowers : Nat → List Nat
  | 0 => []
  | n + 1 => 1 :: (compactBinaryPowers n).map fun power => 2 * power

/-- Sum the selected natural weights, matching the zip-truncating knapsack convention. -/
def selectedNatSum : List Nat → List Bool → Nat
  | [], _ => 0
  | _, [] => 0
  | weight :: weights, selected :: selections =>
      (if selected then weight else 0) + selectedNatSum weights selections

theorem compactBinaryPowers_length (n : Nat) :
    (compactBinaryPowers n).length = n := by
  induction n with
  | zero =>
      simp [compactBinaryPowers]
  | succ n ih =>
      simp [compactBinaryPowers, ih]

theorem selectedNatSum_map_two_mul (weights : List Nat) (selections : List Bool) :
    selectedNatSum (weights.map fun weight => 2 * weight) selections =
      2 * selectedNatSum weights selections := by
  induction weights generalizing selections with
  | nil =>
      simp [selectedNatSum]
  | cons weight weights ih =>
      cases selections with
      | nil =>
          simp [selectedNatSum]
      | cons selected selections =>
          cases selected <;> simp [selectedNatSum, ih selections, Nat.mul_add]

theorem selectedNatSum_compactBinaryPowers_digits (digits : List Nat)
    (hDigits : ∀ digit ∈ digits, digit < 2) :
    selectedNatSum (compactBinaryPowers digits.length)
        (digits.map fun digit => decide (digit = 1)) =
      Nat.ofDigits 2 digits := by
  induction digits with
  | nil =>
      simp [selectedNatSum, compactBinaryPowers]
  | cons digit digits ih =>
      have hDigit : digit = 0 ∨ digit = 1 := by
        have hlt : digit < 2 := hDigits digit (by simp)
        omega
      have hTail : ∀ tailDigit ∈ digits, tailDigit < 2 := by
        intro tailDigit htail
        exact hDigits tailDigit (by simp [htail])
      rcases hDigit with rfl | rfl
      · simp [selectedNatSum, compactBinaryPowers, selectedNatSum_map_two_mul, ih hTail,
          Nat.ofDigits_cons]
      · simp [selectedNatSum, compactBinaryPowers, selectedNatSum_map_two_mul, ih hTail,
          Nat.ofDigits_cons]

theorem selectedNatSum_append_append
    (weights₁ weights₂ : List Nat) (bits₁ bits₂ : List Bool) :
    bits₁.length = weights₁.length →
      selectedNatSum (weights₁ ++ weights₂) (bits₁ ++ bits₂) =
        selectedNatSum weights₁ bits₁ + selectedNatSum weights₂ bits₂ := by
  intro hLength
  induction weights₁ generalizing bits₁ with
  | nil =>
      cases bits₁ with
      | nil =>
          simp [selectedNatSum]
      | cons bit bits =>
          simp at hLength
  | cons weight weights ih =>
      cases bits₁ with
      | nil =>
          simp at hLength
      | cons bit bits =>
          simp at hLength
          cases bit <;> simp [selectedNatSum, ih bits hLength, Nat.add_assoc]

/-- Binary powers available as slack contributions for one compact row. -/
def compactSlackPowers (constraint : List Int × Int) : List Nat :=
  compactBinaryPowers (compactSlackBitCount constraint)

/--
Digit vector for one slack item.  It contributes only to the constraint digit
with index `rowIndex`; variable-choice digits stay zero.
-/
def compactSlackItemDigits
    (I : IntegerProgrammingInput) (rowIndex power : Nat) : List Nat :=
  List.replicate (varBound I) 0 ++
    (List.range I.constraints.length).map fun j => if j = rowIndex then power else 0

theorem compactSlackItemDigits_getD_variableChoice
    (I : IntegerProgrammingInput) {i rowIndex power : Nat} (hi : i < varBound I) :
    (compactSlackItemDigits I rowIndex power).getD i 0 = 0 := by
  have hPrefix : i < (List.replicate (varBound I) 0).length := by
    simpa using hi
  rw [compactSlackItemDigits]
  rw [List.getD_append (l := List.replicate (varBound I) 0)
    (l' := (List.range I.constraints.length).map fun j =>
      if j = rowIndex then power else 0) (d := 0) (n := i) hPrefix]
  exact List.getD_replicate (x := (0 : Nat)) (y := 0) hi

theorem compactSlackItemDigits_getD_constraint
    (I : IntegerProgrammingInput) {rowIndex slackRow power : Nat}
    (hrow : rowIndex < I.constraints.length) :
    (compactSlackItemDigits I slackRow power).getD (varBound I + rowIndex) 0 =
      if rowIndex = slackRow then power else 0 := by
  have hPrefix :
      (List.replicate (varBound I) 0).length ≤ varBound I + rowIndex := by
    simp
  have hTail :
      rowIndex <
        ((List.range I.constraints.length).map fun j =>
          if j = slackRow then power else 0).length := by
    simpa using hrow
  rw [compactSlackItemDigits]
  rw [List.getD_append_right (l := List.replicate (varBound I) 0)
    (l' := (List.range I.constraints.length).map fun j =>
      if j = slackRow then power else 0) (d := 0)
    (n := varBound I + rowIndex) hPrefix]
  rw [List.length_replicate, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem
    (l := (List.range I.constraints.length).map fun j =>
      if j = slackRow then power else 0) (d := 0) (n := rowIndex) hTail]
  simp

/-- Slack item digit vectors allocated for one source constraint row. -/
def compactSlackItemDigitsForConstraint
    (I : IntegerProgrammingInput) (rowIndex : Nat) (constraint : List Int × Int) :
    List (List Nat) :=
  (compactSlackPowers constraint).map fun power => compactSlackItemDigits I rowIndex power

theorem compactSlackPowers_length (constraint : List Int × Int) :
    (compactSlackPowers constraint).length = compactSlackBitCount constraint := by
  simp [compactSlackPowers, compactBinaryPowers_length]

theorem compactSlackItemDigits_length
    (I : IntegerProgrammingInput) (rowIndex power : Nat) :
    (compactSlackItemDigits I rowIndex power).length = compactDigitCount I := by
  simp [compactSlackItemDigits, compactDigitCount]

theorem compactSlackItemDigitsForConstraint_mem_length
    {I : IntegerProgrammingInput} {rowIndex : Nat} {constraint : List Int × Int}
    {digits : List Nat}
    (hdigits : digits ∈ compactSlackItemDigitsForConstraint I rowIndex constraint) :
    digits.length = compactDigitCount I := by
  rcases List.mem_map.mp hdigits with ⟨power, _hpower, rfl⟩
  exact compactSlackItemDigits_length I rowIndex power

/-- Fixed-length binary slack selection for one row. -/
def compactSlackSelection (constraint : List Int × Int) (slack : Nat) : List Bool :=
  (Nat.digitsAppend 2 (compactSlackBitCount constraint) slack).map fun digit =>
    decide (digit = 1)

theorem compactConstraintBound_lt_two_pow_slackBitCount
    (constraint : List Int × Int) :
    compactConstraintBound constraint < 2 ^ compactSlackBitCount constraint := by
  simpa [compactSlackBitCount] using
    Nat.lt_base_pow_length_digits (b := 2) (m := compactConstraintBound constraint)
      (by decide : 1 < 2)

theorem compactSlackSelection_length_of_le
    (constraint : List Int × Int) {slack : Nat}
    (hSlack : slack ≤ compactConstraintBound constraint) :
    (compactSlackSelection constraint slack).length = compactSlackBitCount constraint := by
  have hSlackPow : slack < 2 ^ compactSlackBitCount constraint :=
    lt_of_le_of_lt hSlack (compactConstraintBound_lt_two_pow_slackBitCount constraint)
  simp [compactSlackSelection,
    Nat.length_digitsAppend (by decide : 1 < 2) (compactSlackBitCount constraint) hSlackPow]

theorem compactSlackSelection_value_of_le
    (constraint : List Int × Int) {slack : Nat}
    (hSlack : slack ≤ compactConstraintBound constraint) :
    selectedNatSum (compactSlackPowers constraint) (compactSlackSelection constraint slack) =
      slack := by
  let digits := Nat.digitsAppend 2 (compactSlackBitCount constraint) slack
  have hSlackPow : slack < 2 ^ compactSlackBitCount constraint :=
    lt_of_le_of_lt hSlack (compactConstraintBound_lt_two_pow_slackBitCount constraint)
  have hLength : digits.length = compactSlackBitCount constraint := by
    simpa [digits] using
      Nat.length_digitsAppend (by decide : 1 < 2) (compactSlackBitCount constraint) hSlackPow
  have hDigitsLt : ∀ digit ∈ digits, digit < 2 := by
    intro digit hdigit
    exact Nat.lt_of_mem_digitsAppend (by decide : 1 < 2)
      (compactSlackBitCount constraint) digit hdigit
  have hSelected := selectedNatSum_compactBinaryPowers_digits digits hDigitsLt
  have hValue : Nat.ofDigits 2 digits = slack := by
    change Nat.ofDigits 2 (Nat.digitsAppend 2 (compactSlackBitCount constraint) slack) = slack
    rw [Nat.digitsAppend, Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]
  simpa [compactSlackPowers, compactSlackSelection, digits, hLength, hValue] using hSelected

/-- Compact truth-item digit vectors for all bounded variables. -/
def compactVariableItemDigitVectors (I : IntegerProgrammingInput) : List (List Nat) :=
  (List.range (varBound I)).flatMap fun i =>
    [compactVariableItemDigits I i true, compactVariableItemDigits I i false]

/-- Selection prefix choosing the truth item matching assignment `a` for each bounded variable. -/
def compactVariableItemSelection (I : IntegerProgrammingInput) (a : BoolAssignment) :
    List Bool :=
  (List.range (varBound I)).flatMap fun i => [a i, !(a i)]

theorem compactVariableItemSelection_length
    (I : IntegerProgrammingInput) (a : BoolAssignment) :
    (compactVariableItemSelection I a).length =
      (compactVariableItemDigitVectors I).length := by
  simp [compactVariableItemSelection, compactVariableItemDigitVectors]

/-- Compact slack digit vectors for all rows, carrying an explicit row index. -/
def compactSlackItemDigitVectorsFrom
    (I : IntegerProgrammingInput) : Nat → List (List Int × Int) → List (List Nat)
  | _, [] => []
  | rowIndex, constraint :: constraints =>
      compactSlackItemDigitsForConstraint I rowIndex constraint ++
        compactSlackItemDigitVectorsFrom I (rowIndex + 1) constraints

/-- Compact slack digit vectors for all source constraints. -/
def compactSlackItemDigitVectors (I : IntegerProgrammingInput) : List (List Nat) :=
  compactSlackItemDigitVectorsFrom I 0 I.constraints

/-- Canonical slack selections for all compact rows under assignment `a`. -/
def compactSlackSelectionsFrom
    (I : IntegerProgrammingInput) : List (List Int × Int) → BoolAssignment → List Bool
  | [], _ => []
  | constraint :: constraints, a =>
      compactSlackSelection constraint
          (compactConstraintBound constraint - compactConstraintValue a constraint.1) ++
        compactSlackSelectionsFrom I constraints a

/-- Canonical slack selections for every source row under assignment `a`. -/
def compactSlackSelections (I : IntegerProgrammingInput) (a : BoolAssignment) : List Bool :=
  compactSlackSelectionsFrom I I.constraints a

/-- All compact Knapsack item digit vectors. -/
def compactItemDigitVectors (I : IntegerProgrammingInput) : List (List Nat) :=
  compactVariableItemDigitVectors I ++ compactSlackItemDigitVectors I

/-- Canonical compact item selection induced by assignment `a` and row slacks. -/
def compactSelection (I : IntegerProgrammingInput) (a : BoolAssignment) : List Bool :=
  compactVariableItemSelection I a ++ compactSlackSelections I a

/-- Total digit mass used to choose a no-carry base. -/
def compactDigitVectorsMass (vectors : List (List Nat)) : Nat :=
  (vectors.map List.sum).sum

/-- Base larger than the total target and item digit mass, preventing carries. -/
def compactBase (I : IntegerProgrammingInput) : Nat :=
  (compactTargetDigits I).sum + compactDigitVectorsMass (compactItemDigitVectors I) + 2

/-- Encode one compact digit vector in the instance-specific no-carry base. -/
def compactDigitCode (I : IntegerProgrammingInput) (digits : List Nat) : Nat :=
  Nat.ofDigits (compactBase I) digits

/-- Encoded compact item codes. -/
def compactItemCodes (I : IntegerProgrammingInput) : List Nat :=
  (compactItemDigitVectors I).map (compactDigitCode I)

/-- Knapsack items with equal weight and value, forcing exact equality to the target code. -/
def compactItems (I : IntegerProgrammingInput) : List (Nat × Nat) :=
  (compactItemCodes I).map fun code => (code, code)

/-- Compact target code shared by capacity and target value. -/
def compactTargetCode (I : IntegerProgrammingInput) : Nat :=
  compactDigitCode I (compactTargetDigits I)

/-- Compact map core for rows whose shifted bounds are all nonnegative. -/
def compactMapCore (I : IntegerProgrammingInput) : KnapsackInput :=
  { items := compactItems I
    capacity := compactTargetCode I
    targetValue := compactTargetCode I }

/-- Fixed Knapsack no-instance used by the negative shifted-bound guard. -/
def compactNoKnapsackInput : KnapsackInput :=
  { items := []
    capacity := 0
    targetValue := 1 }

theorem compactNoKnapsackInput_not :
    ¬ Combinatorics.Knapsack compactNoKnapsackInput := by
  rintro ⟨selected, hLength, _hWeight, hValue⟩
  cases selected with
  | nil =>
      simp [compactNoKnapsackInput, selectedValue] at hValue
  | cons selected selections =>
      simp [compactNoKnapsackInput] at hLength

/--
Guarded compact P15m replacement skeleton.  Correctness and binary-structured
size bounds are the next proof obligations.
-/
noncomputable def compactMap (I : IntegerProgrammingInput) : KnapsackInput := by
  classical
  exact if compactConstraintBoundsNonnegative I then compactMapCore I else compactNoKnapsackInput

theorem selectedWeight_codePairs
    (codes : List Nat) (selected : List Bool) (capacity target : Nat) :
    selectedWeight
        { items := codes.map fun code => (code, code), capacity := capacity, targetValue := target }
        selected =
      selectedNatSum codes selected := by
  induction codes generalizing selected with
  | nil =>
      simp [selectedWeight, selectedNatSum]
  | cons code codes ih =>
      cases selected with
      | nil =>
          simp [selectedWeight, selectedNatSum]
      | cons bit selected =>
          cases bit <;> simpa [selectedWeight, selectedNatSum] using ih selected

theorem selectedValue_codePairs
    (codes : List Nat) (selected : List Bool) (capacity target : Nat) :
    selectedValue
        { items := codes.map fun code => (code, code), capacity := capacity, targetValue := target }
        selected =
      selectedNatSum codes selected := by
  induction codes generalizing selected with
  | nil =>
      simp [selectedValue, selectedNatSum]
  | cons code codes ih =>
      cases selected with
      | nil =>
          simp [selectedValue, selectedNatSum]
      | cons bit selected =>
          cases bit <;> simpa [selectedValue, selectedNatSum] using ih selected

theorem knapsack_codePairs_iff_selectedNatSum_eq (codes : List Nat) (target : Nat) :
    Combinatorics.Knapsack
        { items := codes.map fun code => (code, code), capacity := target, targetValue := target } ↔
      ∃ selected : List Bool,
        selected.length = codes.length ∧ selectedNatSum codes selected = target := by
  constructor
  · rintro ⟨selected, hLength, hWeight, hValue⟩
    have hWeight' : selectedNatSum codes selected ≤ target := by
      simpa [selectedWeight_codePairs codes selected target target] using hWeight
    have hValue' : target ≤ selectedNatSum codes selected := by
      simpa [selectedValue_codePairs codes selected target target] using hValue
    exact ⟨selected, by simpa using hLength, by omega⟩
  · rintro ⟨selected, hLength, hSum⟩
    refine ⟨selected, ?_, ?_, ?_⟩
    · simpa using hLength
    · simp [selectedWeight_codePairs codes selected target target, hSum]
    · simp [selectedValue_codePairs codes selected target target, hSum]

theorem compactMapCore_knapsack_iff_selectedNatSum_eq (I : IntegerProgrammingInput) :
    Combinatorics.Knapsack (compactMapCore I) ↔
      ∃ selected : List Bool,
        selected.length = (compactItemCodes I).length ∧
          selectedNatSum (compactItemCodes I) selected = compactTargetCode I := by
  simpa [compactMapCore, compactItems] using
    knapsack_codePairs_iff_selectedNatSum_eq (compactItemCodes I) (compactTargetCode I)

theorem nat_mem_le_sum {x : Nat} {xs : List Nat} (hx : x ∈ xs) :
    x ≤ xs.sum := by
  induction xs with
  | nil =>
      simp at hx
  | cons y ys ih =>
      simp at hx
      rcases hx with rfl | hx
      · simp
      · have hTail := ih hx
        simp
        omega

theorem compactDigitVectorSum_le_mass {vector : List Nat} {vectors : List (List Nat)}
    (hvector : vector ∈ vectors) :
    vector.sum ≤ compactDigitVectorsMass vectors := by
  apply nat_mem_le_sum
  exact List.mem_map.mpr ⟨vector, hvector, rfl⟩

theorem compactBase_gt_one (I : IntegerProgrammingInput) :
    1 < compactBase I := by
  simp [compactBase]

theorem compactTargetDigit_lt_base {I : IntegerProgrammingInput} {digit : Nat}
    (hdigit : digit ∈ compactTargetDigits I) :
    digit < compactBase I := by
  have hDigitLe : digit ≤ (compactTargetDigits I).sum := nat_mem_le_sum hdigit
  simp [compactBase]
  omega

theorem compactItemDigit_lt_base {I : IntegerProgrammingInput} {digits : List Nat}
    {digit : Nat}
    (hdigits : digits ∈ compactItemDigitVectors I) (hdigit : digit ∈ digits) :
    digit < compactBase I := by
  have hDigitLe : digit ≤ digits.sum := nat_mem_le_sum hdigit
  have hVectorLe : digits.sum ≤ compactDigitVectorsMass (compactItemDigitVectors I) :=
    compactDigitVectorSum_le_mass hdigits
  simp [compactBase]
  omega

/-- Keep exactly the entries whose selector bit is true, truncating like `List.zip`. -/
def selectedEntries {α : Type} : List α → List Bool → List α
  | [], _ => []
  | _, [] => []
  | x :: xs, selected :: selections =>
      if selected then x :: selectedEntries xs selections else selectedEntries xs selections

theorem selectedNatSum_map {α : Type} (xs : List α) (selected : List Bool)
    (weight : α → Nat) :
    selectedNatSum (xs.map weight) selected =
      ((selectedEntries xs selected).map weight).sum := by
  induction xs generalizing selected with
  | nil =>
      simp [selectedNatSum, selectedEntries]
  | cons x xs ih =>
      cases selected with
      | nil =>
          simp [selectedNatSum, selectedEntries]
      | cons bit selected =>
          cases bit
          · simpa [selectedNatSum, selectedEntries] using ih selected
          · simp [selectedNatSum, selectedEntries, ih selected]

theorem selectedNatSum_compactItemCodes
    (I : IntegerProgrammingInput) (selected : List Bool) :
    selectedNatSum (compactItemCodes I) selected =
      ((selectedEntries (compactItemDigitVectors I) selected).map
        (compactDigitCode I)).sum := by
  simpa [compactItemCodes] using
    selectedNatSum_map (compactItemDigitVectors I) selected (compactDigitCode I)

/-- Pointwise sum of equally sized digit vectors, with a fixed zero vector for the empty sum. -/
def digitwiseSum (length : Nat) : List (List Nat) → List Nat
  | [] => List.replicate length 0
  | digits :: vectors => digits.zipWith (· + ·) (digitwiseSum length vectors)

/-- Per-item weights counting contributions to variable-choice digit `i`. -/
def compactVariableChoiceCountWeights (I : IntegerProgrammingInput) (i : Nat) : List Nat :=
  (compactItemDigitVectors I).map fun digits => digits.getD i 0

/-- Number of selected item contributions hitting variable-choice digit `i`. -/
def selectedVariableChoiceCount
    (I : IntegerProgrammingInput) (i : Nat) (selected : List Bool) : Nat :=
  selectedNatSum (compactVariableChoiceCountWeights I i) selected

end Knapsack
end Karp21
end ComplexityReduction
