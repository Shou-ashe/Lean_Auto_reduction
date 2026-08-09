/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.Partition
import ComplexityReduction.Legacy.ComplexityReduction.Combinatorics.Scheduling
import Mathlib.Tactic

/-!
P15e scheduling target: Knapsack to Job Sequencing.
-/

namespace ComplexityReduction
namespace Karp21
namespace JobSequencing

open ComplexityReduction.Combinatorics

/-- Unit job used by the current-schema nonempty-witness family. -/
def unitJob : Job where
  processingTime := 1
  deadline := 1
  profit := 1

/-- `m` copies of the unit job; target profit forces at least one selected job. -/
def unitJobInput (m : Nat) : JobSequencingInput where
  jobs := List.replicate m unitJob
  targetProfit := 1

theorem unitJob_feasible_singleton :
    FeasibleJobSequence [unitJob] := by
  intro pref j suffix hEq
  cases pref with
  | nil =>
      cases suffix with
      | nil =>
          simp at hEq
          subst j
          simp [unitJob, totalProcessingTime]
      | cons first rest =>
          simp at hEq
  | cons first rest =>
      simp at hEq

theorem unitJobInput_correct (m : Nat) :
    JobSequencing (unitJobInput m) ↔ 0 < m := by
  constructor
  · rintro ⟨selected, hSublist, _hFeasible, hProfit⟩
    cases m with
    | zero =>
        have hSelected : selected = [] := by
          simpa [unitJobInput] using hSublist
        subst selected
        simp [unitJobInput, totalProfit] at hProfit
    | succ m =>
        omega
  · intro hm
    cases m with
    | zero =>
        omega
    | succ m =>
        refine ⟨[unitJob], ?_, unitJob_feasible_singleton, ?_⟩
        · simp [unitJobInput]
        · simp [unitJobInput, totalProfit, unitJob]

/-- P15e syntax map from Knapsack to Job Sequencing. -/
def map (I : KnapsackInput) : JobSequencingInput :=
  unitJobInput (Partition.satisfyingSelections I).length

theorem map_correct (I : KnapsackInput) :
    knapsackKarpDecisionProblem.isYes I ↔ JobSequencing (map I) := by
  change Knapsack I ↔ JobSequencing (map I)
  rw [Partition.knapsack_iff_satisfyingSelections_pos]
  exact (unitJobInput_correct (Partition.satisfyingSelections I).length).symm

theorem totalProcessingTime_append (xs ys : List Job) :
    totalProcessingTime (xs ++ ys) = totalProcessingTime xs + totalProcessingTime ys := by
  simp [totalProcessingTime]

theorem totalProfit_append (xs ys : List Job) :
    totalProfit (xs ++ ys) = totalProfit xs + totalProfit ys := by
  simp [totalProfit]

def textbookJob (capacity : Nat) (_index : Nat) (item : Nat × Nat) : Job where
  processingTime := item.1
  deadline := capacity
  profit := item.2

def textbookJobsFrom (capacity index : Nat) : List (Nat × Nat) → List Job
  | [] => []
  | item :: items => textbookJob capacity index item :: textbookJobsFrom capacity (index + 1) items

def selectedTextbookJobsFrom (capacity index : Nat) : List (Nat × Nat) → List Bool → List Job
  | item :: items, true :: bits =>
      textbookJob capacity index item :: selectedTextbookJobsFrom capacity (index + 1) items bits
  | _item :: items, false :: bits =>
      selectedTextbookJobsFrom capacity (index + 1) items bits
  | _, _ => []

def selectedTextbookJobs (I : KnapsackInput) (bits : List Bool) : List Job :=
  selectedTextbookJobsFrom I.capacity 0 I.items bits

/-- P15p syntax-only map: one job per knapsack item. -/
def textbookMap (I : KnapsackInput) : JobSequencingInput :=
  { jobs := textbookJobsFrom I.capacity 0 I.items
    targetProfit := I.targetValue }

theorem selectedTextbookJobsFrom_sublist (capacity index : Nat)
    (items : List (Nat × Nat)) (bits : List Bool) :
    List.Sublist (selectedTextbookJobsFrom capacity index items bits)
      (textbookJobsFrom capacity index items) := by
  induction items generalizing index bits with
  | nil =>
      simp [selectedTextbookJobsFrom, textbookJobsFrom]
  | cons item items ih =>
      cases bits with
      | nil =>
          simp [selectedTextbookJobsFrom, textbookJobsFrom]
      | cons b bits =>
          cases b
          · exact (ih (index + 1) bits).cons _
          · exact (ih (index + 1) bits).cons₂ _

theorem selectedTextbookJobs_sublist (I : KnapsackInput) (bits : List Bool) :
    List.Sublist (selectedTextbookJobs I bits) (textbookMap I).jobs := by
  simpa [selectedTextbookJobs, textbookMap] using
    selectedTextbookJobsFrom_sublist I.capacity 0 I.items bits

theorem selectedTextbookJobsFrom_processingTime (capacity index : Nat)
    (items : List (Nat × Nat)) (bits : List Bool) :
    totalProcessingTime (selectedTextbookJobsFrom capacity index items bits) =
      selectedWeight { items := items, capacity := capacity, targetValue := 0 } bits := by
  induction items generalizing index bits with
  | nil =>
      simp [selectedTextbookJobsFrom, selectedWeight, totalProcessingTime]
  | cons item items ih =>
      cases bits with
      | nil =>
          simp [selectedTextbookJobsFrom, selectedWeight, totalProcessingTime]
      | cons b bits =>
          cases b
          · simpa [selectedTextbookJobsFrom, selectedWeight, totalProcessingTime] using
              ih (index + 1) bits
          · calc
              totalProcessingTime
                  (selectedTextbookJobsFrom capacity index (item :: items) (true :: bits))
                  = item.1 +
                    totalProcessingTime
                      (selectedTextbookJobsFrom capacity (index + 1) items bits) := by
                    simp [selectedTextbookJobsFrom, textbookJob, totalProcessingTime]
              _ = item.1 +
                    selectedWeight { items := items, capacity := capacity, targetValue := 0 }
                      bits := by
                    rw [ih (index + 1) bits]
              _ = selectedWeight
                    { items := item :: items, capacity := capacity, targetValue := 0 }
                    (true :: bits) := by
                    simp [selectedWeight]

theorem selectedTextbookJobs_processingTime (I : KnapsackInput) (bits : List Bool) :
    totalProcessingTime (selectedTextbookJobs I bits) = selectedWeight I bits := by
  simpa [selectedTextbookJobs, selectedWeight] using
    selectedTextbookJobsFrom_processingTime I.capacity 0 I.items bits

theorem selectedTextbookJobsFrom_profit (capacity index : Nat)
    (items : List (Nat × Nat)) (bits : List Bool) :
    totalProfit (selectedTextbookJobsFrom capacity index items bits) =
      selectedValue { items := items, capacity := capacity, targetValue := 0 } bits := by
  induction items generalizing index bits with
  | nil =>
      simp [selectedTextbookJobsFrom, selectedValue, totalProfit]
  | cons item items ih =>
      cases bits with
      | nil =>
          simp [selectedTextbookJobsFrom, selectedValue, totalProfit]
      | cons b bits =>
          cases b
          · simpa [selectedTextbookJobsFrom, selectedValue, totalProfit] using
              ih (index + 1) bits
          · calc
              totalProfit
                  (selectedTextbookJobsFrom capacity index (item :: items) (true :: bits))
                  = item.2 +
                    totalProfit
                      (selectedTextbookJobsFrom capacity (index + 1) items bits) := by
                    simp [selectedTextbookJobsFrom, textbookJob, totalProfit]
              _ = item.2 +
                    selectedValue { items := items, capacity := capacity, targetValue := 0 }
                      bits := by
                    rw [ih (index + 1) bits]
              _ = selectedValue
                    { items := item :: items, capacity := capacity, targetValue := 0 }
                    (true :: bits) := by
                    simp [selectedValue]

theorem selectedTextbookJobs_profit (I : KnapsackInput) (bits : List Bool) :
    totalProfit (selectedTextbookJobs I bits) = selectedValue I bits := by
  simpa [selectedTextbookJobs, selectedValue] using
    selectedTextbookJobsFrom_profit I.capacity 0 I.items bits

theorem selectedTextbookJobsFrom_deadline {capacity index : Nat}
    {items : List (Nat × Nat)} {bits : List Bool} {j : Job}
    (hj : j ∈ selectedTextbookJobsFrom capacity index items bits) :
    j.deadline = capacity := by
  induction items generalizing index bits with
  | nil =>
      simp [selectedTextbookJobsFrom] at hj
  | cons item items ih =>
      cases bits with
      | nil =>
          simp [selectedTextbookJobsFrom] at hj
      | cons b bits =>
          cases b
          · simp [selectedTextbookJobsFrom] at hj
            exact ih hj
          · simp [selectedTextbookJobsFrom, textbookJob] at hj
            rcases hj with h | h
            · exact h ▸ rfl
            · exact ih h

theorem textbookJobsFrom_deadline {capacity index : Nat}
    {items : List (Nat × Nat)} {j : Job}
    (hj : j ∈ textbookJobsFrom capacity index items) :
    j.deadline = capacity := by
  induction items generalizing index with
  | nil =>
      simp [textbookJobsFrom] at hj
  | cons item items ih =>
      simp [textbookJobsFrom, textbookJob] at hj ⊢
      rcases hj with h | h
      · exact h ▸ rfl
      · exact ih h

theorem totalProcessingTime_prefix_le_append (pref suffix : List Job) (j : Job) :
    totalProcessingTime (pref ++ [j]) ≤
      totalProcessingTime (pref ++ [j] ++ suffix) := by
  calc
    totalProcessingTime (pref ++ [j])
        ≤ totalProcessingTime (pref ++ [j]) + totalProcessingTime suffix :=
      Nat.le_add_right _ _
    _ = totalProcessingTime (pref ++ [j] ++ suffix) := by
      simpa using (totalProcessingTime_append (pref ++ [j]) suffix).symm

theorem selectedTextbookJobs_feasible (I : KnapsackInput) {bits : List Bool}
    (hWeight : selectedWeight I bits ≤ I.capacity) :
    FeasibleJobSequence (selectedTextbookJobs I bits) := by
  intro pref j suffix hEq
  have hj : j ∈ selectedTextbookJobs I bits := by
    rw [hEq]
    simp
  have hDeadline := selectedTextbookJobsFrom_deadline
    (capacity := I.capacity) (index := 0) (items := I.items) (bits := bits) hj
  have hPrefix :
      totalProcessingTime (pref ++ [j]) ≤ totalProcessingTime (selectedTextbookJobs I bits) := by
    rw [hEq]
    exact totalProcessingTime_prefix_le_append pref suffix j
  have hTotal := selectedTextbookJobs_processingTime I bits
  exact hPrefix.trans (by simpa [hTotal, hDeadline] using hWeight)

theorem feasible_totalProcessingTime_le_of_uniform_deadline (jobs : List Job) (capacity : Nat)
    (hDeadline : ∀ j ∈ jobs, j.deadline = capacity)
    (hFeasible : FeasibleJobSequence jobs) :
    totalProcessingTime jobs ≤ capacity := by
  by_cases hEmpty : jobs = []
  · simp [hEmpty, totalProcessingTime]
  · have hFeasibleLast :=
      hFeasible jobs.dropLast (jobs.getLast hEmpty) [] (by
        simpa using (List.dropLast_append_getLast hEmpty).symm)
    have hDeadlineLast := hDeadline (jobs.getLast hEmpty) (List.getLast_mem hEmpty)
    simpa [hDeadlineLast, List.dropLast_append_getLast hEmpty] using hFeasibleLast

theorem decode_textbookJobsFrom {capacity index targetValue : Nat}
    {items : List (Nat × Nat)} {selected : List Job}
    (hSublist : List.Sublist selected (textbookJobsFrom capacity index items)) :
    ∃ bits : List Bool,
      bits.length = items.length ∧
        selectedWeight { items := items, capacity := capacity, targetValue := targetValue } bits =
          totalProcessingTime selected ∧
        selectedValue { items := items, capacity := capacity, targetValue := targetValue } bits =
          totalProfit selected := by
  induction items generalizing index selected with
  | nil =>
      have hSelected : selected = [] := by
        simpa [textbookJobsFrom] using hSublist
      subst selected
      exact ⟨[], by simp [selectedWeight, selectedValue, totalProcessingTime, totalProfit]⟩
  | cons item items ih =>
      cases selected with
      | nil =>
          rcases ih (index := index + 1) (selected := []) (by
            simp) with ⟨bits, hLen, hWeight, hValue⟩
          refine ⟨false :: bits, ?_, ?_, ?_⟩
          · simp [hLen]
          · simpa [selectedWeight, hWeight]
          · simpa [selectedValue, hValue]
      | cons j rest =>
          have hCases :
              List.Sublist (j :: rest) (textbookJobsFrom capacity (index + 1) items) ∨
                j = textbookJob capacity index item ∧
                  List.Sublist rest (textbookJobsFrom capacity (index + 1) items) := by
            exact (List.cons_sublist_cons'
              (a := j) (b := textbookJob capacity index item)
              (l₁ := rest) (l₂ := textbookJobsFrom capacity (index + 1) items)).1
              (by simpa [textbookJobsFrom] using hSublist)
          rcases hCases with hSkip | ⟨hHead, hRest⟩
          · rcases ih (index := index + 1) (selected := j :: rest) hSkip with
              ⟨bits, hLen, hWeight, hValue⟩
            refine ⟨false :: bits, ?_, ?_, ?_⟩
            · simp [hLen]
            · simpa [selectedWeight, hWeight]
            · simpa [selectedValue, hValue]
          · rcases ih (index := index + 1) (selected := rest) hRest with
              ⟨bits, hLen, hWeight, hValue⟩
            refine ⟨true :: bits, ?_, ?_, ?_⟩
            · simp [hLen]
            · subst j
              have hWeightTail :
                  (List.map (fun p => if p.2 then p.1.1 else 0) (items.zip bits)).sum =
                    (List.map Job.processingTime rest).sum := by
                simpa [selectedWeight, totalProcessingTime] using hWeight
              simp [selectedWeight, totalProcessingTime, textbookJob, hWeightTail]
            · subst j
              have hValueTail :
                  (List.map (fun p => if p.2 then p.1.2 else 0) (items.zip bits)).sum =
                    (List.map Job.profit rest).sum := by
                simpa [selectedValue, totalProfit] using hValue
              simp [selectedValue, totalProfit, textbookJob, hValueTail]

theorem textbookMap_correct (I : KnapsackInput) :
    knapsackKarpDecisionProblem.isYes I ↔ JobSequencing (textbookMap I) := by
  change Knapsack I ↔ JobSequencing (textbookMap I)
  constructor
  · rintro ⟨bits, hLen, hWeight, hValue⟩
    refine ⟨selectedTextbookJobs I bits, selectedTextbookJobs_sublist I bits, ?_, ?_⟩
    · exact selectedTextbookJobs_feasible I hWeight
    · simpa [selectedTextbookJobs_profit] using hValue
  · rintro ⟨selected, hSublist, hFeasible, hProfit⟩
    have hSublist' :
        List.Sublist selected (textbookJobsFrom I.capacity 0 I.items) := by
      simpa [textbookMap] using hSublist
    rcases decode_textbookJobsFrom
        (capacity := I.capacity) (index := 0) (targetValue := I.targetValue)
        (items := I.items) (selected := selected) hSublist' with
      ⟨bits, hLen, hWeight, hValue⟩
    refine ⟨bits, hLen, ?_, ?_⟩
    · have hDeadline : ∀ j ∈ selected, j.deadline = I.capacity := by
        intro j hj
        exact textbookJobsFrom_deadline
          (capacity := I.capacity) (index := 0) (items := I.items)
          (hSublist'.subset hj)
      have hBound :=
        feasible_totalProcessingTime_le_of_uniform_deadline selected I.capacity hDeadline hFeasible
      simpa [hWeight] using hBound
    · simpa [hValue] using hProfit

/-! ### Structured finite-alphabet size bound for the textbook route -/

theorem jobStructured_inputSize_eq (j : Job) :
    jobStructuredEncodedType.inputSize j =
      j.processingTime + j.deadline + j.profit + 5 := by
  change jobTupleStructuredEncodedType.inputSize
      (j.processingTime, (j.deadline, j.profit)) =
    j.processingTime + j.deadline + j.profit + 5
  simp [jobTupleStructuredEncodedType]
  omega

theorem jobListStructured_inputSize_eq (jobs : List Job) :
    jobListStructuredEncodedType.inputSize jobs =
      (jobs.map Job.processingTime).sum + (jobs.map Job.deadline).sum +
        (jobs.map Job.profit).sum + 6 * jobs.length := by
  induction jobs with
  | nil =>
      change (EncodedType.list jobStructuredEncodedType).inputSize ([] : List Job) = 0
      exact EncodedType.inputSize_list_nil jobStructuredEncodedType
  | cons j jobs ih =>
      calc
        jobListStructuredEncodedType.inputSize (j :: jobs)
            = jobStructuredEncodedType.inputSize j + 1 +
                jobListStructuredEncodedType.inputSize jobs := by
              exact EncodedType.inputSize_list_cons jobStructuredEncodedType j jobs
        _ = (j.processingTime + j.deadline + j.profit + 5) + 1 +
              ((jobs.map Job.processingTime).sum + (jobs.map Job.deadline).sum +
                (jobs.map Job.profit).sum + 6 * jobs.length) := by
              rw [jobStructured_inputSize_eq, ih]
        _ = ((j :: jobs).map Job.processingTime).sum +
              ((j :: jobs).map Job.deadline).sum +
              ((j :: jobs).map Job.profit).sum + 6 * (j :: jobs).length := by
              simp
              omega

theorem jobSequencingStructured_inputSize_eq (I : JobSequencingInput) :
    jobSequencingStructuredEncodedType.inputSize I =
      jobListStructuredEncodedType.inputSize I.jobs + I.targetProfit + 2 := by
  change jobSequencingTupleStructuredEncodedType.inputSize (I.jobs, I.targetProfit) =
    jobListStructuredEncodedType.inputSize I.jobs + I.targetProfit + 2
  simp [jobSequencingTupleStructuredEncodedType]
  omega

theorem textbookJobsFrom_length (capacity index : Nat) (items : List (Nat × Nat)) :
    (textbookJobsFrom capacity index items).length = items.length := by
  induction items generalizing index with
  | nil =>
      simp [textbookJobsFrom]
  | cons item items ih =>
      simp [textbookJobsFrom, ih]

theorem textbookJobsFrom_processingTime_sum (capacity index : Nat)
    (items : List (Nat × Nat)) :
    ((textbookJobsFrom capacity index items).map Job.processingTime).sum =
      Partition.itemWeightTotal items := by
  induction items generalizing index with
  | nil =>
      simp [textbookJobsFrom, Partition.itemWeightTotal]
  | cons item items ih =>
      rcases item with ⟨w, v⟩
      simp [textbookJobsFrom, textbookJob, Partition.itemWeightTotal, ih]

theorem textbookJobsFrom_deadline_sum (capacity index : Nat)
    (items : List (Nat × Nat)) :
    ((textbookJobsFrom capacity index items).map Job.deadline).sum =
      capacity * items.length := by
  induction items generalizing index with
  | nil =>
      simp [textbookJobsFrom]
  | cons item items ih =>
      simp [textbookJobsFrom, textbookJob, ih, Nat.mul_succ, Nat.add_comm]

theorem textbookJobsFrom_profit_sum (capacity index : Nat)
    (items : List (Nat × Nat)) :
    ((textbookJobsFrom capacity index items).map Job.profit).sum =
      Partition.itemValueTotal items := by
  induction items generalizing index with
  | nil =>
      simp [textbookJobsFrom, Partition.itemValueTotal]
  | cons item items ih =>
      rcases item with ⟨w, v⟩
      simp [textbookJobsFrom, textbookJob, Partition.itemValueTotal, ih]

theorem jobSequencingStructured_inputSize_textbookMap_eq (I : KnapsackInput) :
    jobSequencingStructuredEncodedType.inputSize (textbookMap I) =
      Partition.itemWeightTotal I.items + I.capacity * I.items.length +
        Partition.itemValueTotal I.items + 6 * I.items.length + I.targetValue + 2 := by
  rw [jobSequencingStructured_inputSize_eq, jobListStructured_inputSize_eq]
  simp [textbookMap, textbookJobsFrom_processingTime_sum, textbookJobsFrom_deadline_sum,
    textbookJobsFrom_profit_sum, textbookJobsFrom_length, Nat.add_comm, Nat.add_left_comm]

theorem jobSequencingStructured_inputSize_textbookMap_le_knapsack_poly (I : KnapsackInput) :
    jobSequencingStructuredEncodedType.inputSize (textbookMap I) ≤
      1000 * (knapsackStructuredEncodedType.inputSize I) ^ 2 + 1000 := by
  let S := knapsackStructuredEncodedType.inputSize I
  have hWeight : Partition.itemWeightTotal I.items ≤ S := by
    simpa [S] using Partition.itemWeightTotal_le_knapsackStructured_inputSize I
  have hValue : Partition.itemValueTotal I.items ≤ S := by
    simpa [S] using Partition.itemValueTotal_le_knapsackStructured_inputSize I
  have hLength : I.items.length ≤ S := by
    simpa [S] using Partition.itemLength_le_knapsackStructured_inputSize I
  have hCapacity : I.capacity ≤ S := by
    simpa [S] using Partition.capacity_le_knapsackStructured_inputSize I
  have hTarget : I.targetValue ≤ S := by
    simpa [S] using Partition.targetValue_le_knapsackStructured_inputSize I
  have hCapLength : I.capacity * I.items.length ≤ S * S :=
    Nat.mul_le_mul hCapacity hLength
  have hOutput := jobSequencingStructured_inputSize_textbookMap_eq I
  have hCoarse :
      jobSequencingStructuredEncodedType.inputSize (textbookMap I) ≤ S * S + 9 * S + 2 := by
    rw [hOutput]
    omega
  calc
    jobSequencingStructuredEncodedType.inputSize (textbookMap I) ≤ S * S + 9 * S + 2 :=
      hCoarse
    _ ≤ 1000 * S ^ 2 + 1000 := by
      cases S with
      | zero =>
          norm_num
      | succ S =>
          ring_nf
          omega

theorem knapsackToJobSequencingStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : KnapsackInput => knapsackStructuredEncodedType.inputSize I)
      (fun J : JobSequencingInput => jobSequencingStructuredEncodedType.inputSize J)
      textbookMap := by
  refine PolynomialSizeBound.intro_with 2 1000 1000 ?_
  intro I
  exact jobSequencingStructured_inputSize_textbookMap_le_knapsack_poly I

/-! ### Binary-structured finite-alphabet size bound for the textbook route -/

theorem jobBinaryStructured_inputSize_eq (j : Job) :
    jobBinaryStructuredEncodedType.inputSize j =
      EncodedType.binaryNat.inputSize j.processingTime + 1 +
        (EncodedType.binaryNat.inputSize j.deadline + 1 +
          EncodedType.binaryNat.inputSize j.profit) := by
  change jobTupleBinaryStructuredEncodedType.inputSize
      (j.processingTime, (j.deadline, j.profit)) =
    EncodedType.binaryNat.inputSize j.processingTime + 1 +
      (EncodedType.binaryNat.inputSize j.deadline + 1 +
        EncodedType.binaryNat.inputSize j.profit)
  simp [jobTupleBinaryStructuredEncodedType]

theorem jobSequencingBinaryStructured_inputSize_eq (I : JobSequencingInput) :
    jobSequencingBinaryStructuredEncodedType.inputSize I =
      jobListBinaryStructuredEncodedType.inputSize I.jobs + 1 +
        EncodedType.binaryNat.inputSize I.targetProfit := by
  change jobSequencingTupleBinaryStructuredEncodedType.inputSize (I.jobs, I.targetProfit) =
    jobListBinaryStructuredEncodedType.inputSize I.jobs + 1 +
      EncodedType.binaryNat.inputSize I.targetProfit
  simp [jobSequencingTupleBinaryStructuredEncodedType]

theorem textbookJobsFrom_mem_fields {capacity index : Nat}
    {items : List (Nat × Nat)} {j : Job}
    (hj : j ∈ textbookJobsFrom capacity index items) :
    ∃ item ∈ items,
      j.processingTime = item.1 ∧ j.deadline = capacity ∧ j.profit = item.2 := by
  induction items generalizing index with
  | nil =>
      simp [textbookJobsFrom] at hj
  | cons item items ih =>
      simp [textbookJobsFrom] at hj
      rcases hj with hHead | hTail
      · subst j
        refine ⟨item, by simp, ?_, ?_, ?_⟩ <;> simp [textbookJob]
      · rcases ih (index := index + 1) hTail with ⟨source, hSource, hp, hd, hv⟩
        exact ⟨source, by simp [hSource], hp, hd, hv⟩

theorem textbookJob_binaryStructured_inputSize_le_source_succ {I : KnapsackInput}
    {j : Job} (hj : j ∈ (textbookMap I).jobs) :
    jobBinaryStructuredEncodedType.inputSize j ≤
      3 * (knapsackBinaryStructuredEncodedType.inputSize I + 1) + 2 := by
  let T := knapsackBinaryStructuredEncodedType.inputSize I + 1
  have hJobs : j ∈ textbookJobsFrom I.capacity 0 I.items := by
    simpa [textbookMap] using hj
  rcases textbookJobsFrom_mem_fields hJobs with ⟨item, hitem, hProcessing, hDeadline, hProfit⟩
  have hProcessingSize :
      EncodedType.binaryNat.inputSize j.processingTime ≤ T := by
    rw [hProcessing]
    exact Knapsack.binaryNat_inputSize_le_of_lt_two_pow
      (by simpa [T] using Partition.knapsackItem_weight_lt_two_pow_sourceSucc hitem)
  have hDeadlineSize :
      EncodedType.binaryNat.inputSize j.deadline ≤ T := by
    rw [hDeadline]
    exact Knapsack.binaryNat_inputSize_le_of_lt_two_pow
      (by simpa [T] using Partition.capacity_lt_two_pow_sourceSucc I)
  have hProfitSize :
      EncodedType.binaryNat.inputSize j.profit ≤ T := by
    rw [hProfit]
    exact Knapsack.binaryNat_inputSize_le_of_lt_two_pow
      (by simpa [T] using Partition.knapsackItem_value_lt_two_pow_sourceSucc hitem)
  rw [jobBinaryStructured_inputSize_eq]
  omega

theorem jobListBinaryStructured_inputSize_textbookMap_le_source_succ (I : KnapsackInput) :
    jobListBinaryStructuredEncodedType.inputSize (textbookMap I).jobs ≤
      knapsackBinaryStructuredEncodedType.inputSize I *
        (3 * (knapsackBinaryStructuredEncodedType.inputSize I + 1) + 3) := by
  let S := knapsackBinaryStructuredEncodedType.inputSize I
  let B := 3 * (S + 1) + 2
  have hEach :
      ∀ j ∈ (textbookMap I).jobs, jobBinaryStructuredEncodedType.inputSize j ≤ B := by
    intro j hj
    simpa [B, S] using textbookJob_binaryStructured_inputSize_le_source_succ (I := I) hj
  have hList :=
    Clique.encodedList_inputSize_le_length_mul_bound jobBinaryStructuredEncodedType
      (textbookMap I).jobs B hEach
  have hLen : (textbookMap I).jobs.length ≤ S := by
    have hItems := Partition.knapsackItems_length_le_binaryStructured_inputSize I
    simpa [textbookMap, textbookJobsFrom_length, S] using hItems
  calc
    jobListBinaryStructuredEncodedType.inputSize (textbookMap I).jobs
        ≤ (textbookMap I).jobs.length * (B + 1) := hList
    _ ≤ S * (B + 1) := Nat.mul_le_mul_right (B + 1) hLen
    _ = S * (3 * (S + 1) + 3) := by
      dsimp [B]

theorem jobSequencingBinaryStructured_inputSize_textbookMap_le_knapsack_poly_succ
    (I : KnapsackInput) :
    jobSequencingBinaryStructuredEncodedType.inputSize (textbookMap I) ≤
      1000 * (knapsackBinaryStructuredEncodedType.inputSize I + 1) ^ 2 := by
  let S := knapsackBinaryStructuredEncodedType.inputSize I
  let T := S + 1
  have hList : jobListBinaryStructuredEncodedType.inputSize (textbookMap I).jobs ≤
      S * (3 * (S + 1) + 3) := by
    simpa [S] using jobListBinaryStructured_inputSize_textbookMap_le_source_succ I
  have hTarget :
      EncodedType.binaryNat.inputSize (textbookMap I).targetProfit ≤ T := by
    change EncodedType.binaryNat.inputSize I.targetValue ≤ T
    exact Knapsack.binaryNat_inputSize_le_of_lt_two_pow
      (by simpa [T, S] using Partition.targetValue_lt_two_pow_sourceSucc I)
  have hOutput :
      jobSequencingBinaryStructuredEncodedType.inputSize (textbookMap I) ≤
        S * (3 * (S + 1) + 3) + 1 + T := by
    rw [jobSequencingBinaryStructured_inputSize_eq]
    exact Nat.add_le_add (Nat.add_le_add hList le_rfl) hTarget
  have hCoarse : S * (3 * (S + 1) + 3) + 1 + T ≤ 1000 * T ^ 2 := by
    have hT : 1 ≤ T := by dsimp [T]; omega
    have hSleT : S ≤ T := by dsimp [T]; omega
    nlinarith
  exact hOutput.trans (by simpa [T, S] using hCoarse)

theorem jobSequencingBinaryStructured_inputSize_textbookMap_le_knapsack_poly
    (I : KnapsackInput) :
    jobSequencingBinaryStructuredEncodedType.inputSize (textbookMap I) ≤
      4000 * (knapsackBinaryStructuredEncodedType.inputSize I) ^ 2 := by
  let S := knapsackBinaryStructuredEncodedType.inputSize I
  have hSucc := jobSequencingBinaryStructured_inputSize_textbookMap_le_knapsack_poly_succ I
  have hPos : 0 < S := by
    simpa [S] using Partition.knapsackBinaryStructured_inputSize_pos I
  have hSuccLe : S + 1 ≤ 2 * S := by omega
  have hPow : (S + 1) ^ 2 ≤ (2 * S) ^ 2 :=
    Nat.pow_le_pow_left hSuccLe 2
  calc
    jobSequencingBinaryStructuredEncodedType.inputSize (textbookMap I)
        ≤ 1000 * (S + 1) ^ 2 := by simpa [S] using hSucc
    _ ≤ 1000 * (2 * S) ^ 2 := Nat.mul_le_mul_left 1000 hPow
    _ = 4000 * S ^ 2 := by ring

theorem knapsackToJobSequencingBinaryStructured_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : KnapsackInput => knapsackBinaryStructuredEncodedType.inputSize I)
      (fun J : JobSequencingInput => jobSequencingBinaryStructuredEncodedType.inputSize J)
      textbookMap := by
  refine PolynomialSizeBound.intro_with 2 4000 0 ?_
  intro I
  exact jobSequencingBinaryStructured_inputSize_textbookMap_le_knapsack_poly I

/-- Costed Karp reduction from Knapsack to Job Sequencing. -/
noncomputable def knapsackToJobSequencingTMBackedKarpReduction :
    TMBackedCostedReduction knapsackKarpDecisionProblem jobSequencingDecisionProblem := by
  simpa [jobSequencingDecisionProblem, jobSequencingEncodedType] using
    rawCodomainTMBackedReduction
      knapsackKarpDecisionProblem
      Combinatorics.JobSequencing
      map
      map_correct

/-- Costed Karp reduction from Knapsack to Job Sequencing. -/
noncomputable def knapsackToJobSequencingKarpReduction :
    KarpReductionM CostedPolyTimeModel knapsackKarpDecisionProblem
      jobSequencingDecisionProblem :=
  knapsackToJobSequencingTMBackedKarpReduction.toCostedKarpReduction

/-- Costed P15p textbook Karp reduction from Knapsack to Job Sequencing. -/
noncomputable def knapsackToJobSequencing_textbookTMBackedKarpReduction :
    TMBackedCostedReduction knapsackKarpDecisionProblem jobSequencingDecisionProblem := by
  simpa [jobSequencingDecisionProblem, jobSequencingEncodedType] using
    rawCodomainTMBackedReduction
      knapsackKarpDecisionProblem
      Combinatorics.JobSequencing
      textbookMap
      textbookMap_correct

/-- Costed P15p textbook Karp reduction from Knapsack to Job Sequencing. -/
noncomputable def knapsackToJobSequencing_textbookKarpReduction :
    KarpReductionM CostedPolyTimeModel knapsackKarpDecisionProblem
      jobSequencingDecisionProblem :=
  knapsackToJobSequencing_textbookTMBackedKarpReduction.toCostedKarpReduction

theorem jobSequencingStructuredEncoding_faithful :
    jobSequencingStructuredDecisionProblem.FaithfulEncoding where
  injective := jobSequencingStructuredEncodedType_encode_injective

theorem jobSequencingStructuredEncoding_predicateRespects :
    jobSequencingStructuredDecisionProblem.PredicateRespectsEncoding :=
  jobSequencingStructuredEncoding_faithful.predicateRespects

theorem jobSequencingStructuredEncoding_accepts_encode_iff (I : JobSequencingInput) :
    jobSequencingStructuredDecisionProblem.toEncodedLanguage.accepts
        (jobSequencingStructuredEncodedType.encode I) ↔
      JobSequencing I :=
  jobSequencingStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

theorem jobSequencingBinaryStructuredEncoding_faithful :
    jobSequencingBinaryStructuredDecisionProblem.FaithfulEncoding where
  injective := jobSequencingBinaryStructuredEncodedType_encode_injective

theorem jobSequencingBinaryStructuredEncoding_predicateRespects :
    jobSequencingBinaryStructuredDecisionProblem.PredicateRespectsEncoding :=
  jobSequencingBinaryStructuredEncoding_faithful.predicateRespects

theorem jobSequencingBinaryStructuredEncoding_accepts_encode_iff (I : JobSequencingInput) :
    jobSequencingBinaryStructuredDecisionProblem.toEncodedLanguage.accepts
        (jobSequencingBinaryStructuredEncodedType.encode I) ↔
      JobSequencing I :=
  jobSequencingBinaryStructuredEncoding_faithful.toEncodedLanguage_accepts_encode_iff I

/-- Job Sequencing is locally in NP for the project-local costed model. -/
theorem jobSequencingInNP :
    InNPEnc CostedPolyTimeModel jobSequencingDecisionProblem :=
  decidableInNP jobSequencingDecisionProblem

/-- Local NP-completeness of Job Sequencing via Knapsack. -/
theorem jobSequencingNPComplete :
    NPCompleteEnc CostedPolyTimeModel jobSequencingDecisionProblem :=
  NPCompleteEnc.transfer
    Knapsack.knapsackNPComplete
    ⟨knapsackToJobSequencingKarpReduction⟩
    jobSequencingInNP

/-- Local NP-completeness of Job Sequencing via the P15p textbook deadline/profit route. -/
theorem jobSequencing_textbookNPComplete :
    NPCompleteEnc CostedPolyTimeModel jobSequencingDecisionProblem :=
  NPCompleteEnc.transfer
    Knapsack.knapsack_textbookNPComplete
    ⟨knapsackToJobSequencing_textbookKarpReduction⟩
    jobSequencingInNP

end JobSequencing
end Karp21
end ComplexityReduction
