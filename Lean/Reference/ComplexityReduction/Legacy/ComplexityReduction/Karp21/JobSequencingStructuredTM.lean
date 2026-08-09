/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.JobSequencing
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Maps.InvariantFold

/-!
Direct TM-backed structured assembly for the Knapsack to Job Sequencing textbook route.
-/

namespace ComplexityReduction
namespace Karp21
namespace JobSequencing

open ComplexityReduction.Combinatorics

def knapsackTupleOfInput (I : KnapsackInput) :
    knapsackTupleStructuredEncodedType.Carrier :=
  (I.items, (I.capacity, I.targetValue))

theorem knapsackTupleOfInput_encode (I : KnapsackInput) :
    knapsackTupleStructuredEncodedType.encode (knapsackTupleOfInput I) =
      knapsackStructuredEncodedType.encode I := by
  rfl

noncomputable def knapsackTupleOfInputTMBackedMap :
    TMBackedCostedMap
      knapsackStructuredEncodedType
      knapsackTupleStructuredEncodedType
      knapsackTupleOfInput :=
  TMBackedCostedMap.ofEncodingEquiv
    knapsackStructuredEncodedType knapsackTupleStructuredEncodedType knapsackTupleOfInput
    (Equiv.refl knapsackTupleStructuredEncodedType.Symbol)
    (by
      intro I
      change knapsackTupleStructuredEncodedType.encode (knapsackTupleOfInput I) =
        (knapsackStructuredEncodedType.encode I).map id
      simp [knapsackTupleOfInput_encode])

def jobTupleToJob (p : jobTupleStructuredEncodedType.Carrier) : Job where
  processingTime := p.1
  deadline := p.2.1
  profit := p.2.2

theorem jobTupleToJob_encode (p : jobTupleStructuredEncodedType.Carrier) :
    jobStructuredEncodedType.encode (jobTupleToJob p) =
      jobTupleStructuredEncodedType.encode p := by
  rcases p with ⟨processingTime, deadline, profit⟩
  rfl

noncomputable def jobTupleToJobTMBackedMap :
    TMBackedCostedMap
      jobTupleStructuredEncodedType
      jobStructuredEncodedType
      jobTupleToJob :=
  TMBackedCostedMap.ofEncodingEquiv
    jobTupleStructuredEncodedType jobStructuredEncodedType jobTupleToJob
    (Equiv.refl jobTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change jobStructuredEncodedType.encode (jobTupleToJob p) =
        (jobTupleStructuredEncodedType.encode p).map id
      simp [jobTupleToJob_encode])

def jobSequencingTupleToInput (p : jobSequencingTupleStructuredEncodedType.Carrier) :
    JobSequencingInput where
  jobs := p.1
  targetProfit := p.2

theorem jobSequencingTupleToInput_encode
    (p : jobSequencingTupleStructuredEncodedType.Carrier) :
    jobSequencingStructuredEncodedType.encode (jobSequencingTupleToInput p) =
      jobSequencingTupleStructuredEncodedType.encode p := by
  rcases p with ⟨jobs, targetProfit⟩
  rfl

noncomputable def jobSequencingTupleToInputTMBackedMap :
    TMBackedCostedMap
      jobSequencingTupleStructuredEncodedType
      jobSequencingStructuredEncodedType
      jobSequencingTupleToInput :=
  TMBackedCostedMap.ofEncodingEquiv
    jobSequencingTupleStructuredEncodedType jobSequencingStructuredEncodedType
    jobSequencingTupleToInput
    (Equiv.refl jobSequencingTupleStructuredEncodedType.Symbol)
    (by
      intro p
      change jobSequencingStructuredEncodedType.encode (jobSequencingTupleToInput p) =
        (jobSequencingTupleStructuredEncodedType.encode p).map id
      simp [jobSequencingTupleToInput_encode])

def jobFromInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat knapsackItemStructuredEncodedType

def jobFromInstruction (p : Nat × (Nat × Nat)) : Job :=
  textbookJob p.1 0 p.2

theorem jobFromInstruction_tm_polytime :
    TMPolyTimeMap
      jobFromInstructionEncodedType
      jobStructuredEncodedType
      jobFromInstruction := by
  let X := jobFromInstructionEncodedType
  have hCapacity :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1) := by
    simpa [X, jobFromInstructionEncodedType] using
      TMPolyTimeMap.fst EncodedType.nat knapsackItemStructuredEncodedType
  have hItem :
      TMPolyTimeMap X knapsackItemStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, jobFromInstructionEncodedType] using
      TMPolyTimeMap.snd EncodedType.nat knapsackItemStructuredEncodedType
  have hProcessing :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hItem
    simpa [Function.comp, X, knapsackItemStructuredEncodedType] using hComp
  have hProfit :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hItem
    simpa [Function.comp, X, knapsackItemStructuredEncodedType] using hComp
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier => (p.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hCapacity hProfit
  have hTuple :
      TMPolyTimeMap X jobTupleStructuredEncodedType
        (fun p : X.Carrier => (p.2.1, (p.1, p.2.2))) :=
    TMPolyTimeMap.prod_mk hProcessing hTail
  have hJob := TMPolyTimeMap.comp jobTupleToJobTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, jobFromInstruction, textbookJob, jobTupleToJob, X] using hJob

def jobFoldInstructionEncodedType : EncodedType :=
  EncodedType.sum EncodedType.nat knapsackItemStructuredEncodedType

def jobFoldInstructionListEncodedType : EncodedType :=
  EncodedType.list jobFoldInstructionEncodedType

def jobFoldAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat jobListStructuredEncodedType

def jobFoldInit : jobFoldAccEncodedType.Carrier :=
  ((0 : Nat), ([] : List Job))

def jobFoldLeftStep (capacity : Nat) : jobFoldAccEncodedType.Carrier :=
  (capacity, ([] : List Job))

def jobFoldRightStep
    (p : jobFoldAccEncodedType.Carrier × (Nat × Nat)) :
    jobFoldAccEncodedType.Carrier :=
  let capacity : Nat := p.1.1
  let out : List Job := p.1.2
  (capacity, out ++ [jobFromInstruction (capacity, p.2)])

def jobFoldStep
    (p : jobFoldAccEncodedType.Carrier × jobFoldInstructionEncodedType.Carrier) :
    jobFoldAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl capacity => jobFoldLeftStep capacity
  | Sum.inr item => jobFoldRightStep (p.1, item)

def jobFoldInstructions (I : KnapsackInput) :
    List jobFoldInstructionEncodedType.Carrier :=
  Sum.inl I.capacity :: I.items.map Sum.inr

def textbookJobsTM (I : KnapsackInput) : List Job :=
  ((jobFoldInstructions I).foldl
    (fun acc instr => jobFoldStep (acc, instr)) jobFoldInit).2

def knapsackToJobSequencingStructuredTMMap (I : KnapsackInput) : JobSequencingInput where
  jobs := textbookJobsTM I
  targetProfit := I.targetValue

theorem textbookJobsFrom_index_eq (capacity i j : Nat) (items : List (Nat × Nat)) :
    textbookJobsFrom capacity i items = textbookJobsFrom capacity j items := by
  induction items generalizing i j with
  | nil =>
      simp [textbookJobsFrom]
  | cons item items ih =>
      simpa [textbookJobsFrom, textbookJob] using ih (i + 1) (j + 1)

theorem jobFold_items_eq
    (capacity : Nat) (items : List (Nat × Nat)) (out : List Job) :
    (items.map Sum.inr).foldl
        (fun acc instr => jobFoldStep (acc, instr))
        (capacity, out) =
      (capacity, out ++ textbookJobsFrom capacity 0 items) := by
  induction items generalizing out with
  | nil =>
      simp [textbookJobsFrom]
      rfl
  | cons item items ih =>
      change
        (items.map Sum.inr).foldl
            (fun acc instr => jobFoldStep (acc, instr))
            (jobFoldRightStep ((capacity, out), item)) =
          (capacity, out ++ textbookJobsFrom capacity 0 (item :: items))
      simp only [jobFoldRightStep, jobFromInstruction, textbookJob]
      rw [ih]
      simp [textbookJobsFrom, textbookJob, List.append_assoc,
        textbookJobsFrom_index_eq capacity 0 1 items]

theorem textbookJobsTM_eq_textbookJobs (I : KnapsackInput) :
    textbookJobsTM I = textbookJobsFrom I.capacity 0 I.items := by
  unfold textbookJobsTM jobFoldInstructions
  rw [List.foldl_cons]
  simpa [jobFoldInit, jobFoldStep, jobFoldLeftStep] using
    congrArg Prod.snd (jobFold_items_eq I.capacity I.items [])

theorem knapsackToJobSequencingStructuredTMMap_eq_textbookMap (I : KnapsackInput) :
    knapsackToJobSequencingStructuredTMMap I = textbookMap I := by
  cases I with
  | mk items capacity targetValue =>
      simp [knapsackToJobSequencingStructuredTMMap, textbookMap,
        textbookJobsTM_eq_textbookJobs]

theorem jobFoldLeftStep_tm_polytime :
    TMPolyTimeMap EncodedType.nat jobFoldAccEncodedType jobFoldLeftStep := by
  have hCapacity : TMPolyTimeMap EncodedType.nat EncodedType.nat id :=
    TMPolyTimeMap.id EncodedType.nat
  have hOut :
      TMPolyTimeMap EncodedType.nat jobListStructuredEncodedType
        (fun _ : Nat => ([] : List Job)) :=
    TMPolyTimeMap.const EncodedType.nat jobListStructuredEncodedType []
  have hPair := TMPolyTimeMap.prod_mk hCapacity hOut
  simpa [jobFoldLeftStep, Function.comp, jobFoldAccEncodedType] using hPair

theorem jobFoldRightStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod jobFoldAccEncodedType knapsackItemStructuredEncodedType)
      jobFoldAccEncodedType
      jobFoldRightStep := by
  let X := EncodedType.prod jobFoldAccEncodedType knapsackItemStructuredEncodedType
  have hAcc :
      TMPolyTimeMap X jobFoldAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst jobFoldAccEncodedType knapsackItemStructuredEncodedType
  have hCapacity :
      TMPolyTimeMap X EncodedType.nat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat jobListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, X, jobFoldAccEncodedType] using hComp
  have hOut :
      TMPolyTimeMap X jobListStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat jobListStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, X, jobFoldAccEncodedType] using hComp
  have hItem :
      TMPolyTimeMap X knapsackItemStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd jobFoldAccEncodedType knapsackItemStructuredEncodedType
  have hJobInput :
      TMPolyTimeMap X jobFromInstructionEncodedType (fun p : X.Carrier => (p.1.1, p.2)) :=
    TMPolyTimeMap.prod_mk hCapacity hItem
  have hJob :
      TMPolyTimeMap X jobStructuredEncodedType
        (fun p : X.Carrier => jobFromInstruction (p.1.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp jobFromInstruction_tm_polytime hJobInput
    simpa [Function.comp, X] using hComp
  have hSingleton :
      TMPolyTimeMap X jobListStructuredEncodedType
        (fun p : X.Carrier => [jobFromInstruction (p.1.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_singleton jobStructuredEncodedType) hJob
    simpa [Function.comp, jobListStructuredEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod jobListStructuredEncodedType jobListStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show List Job from p.1.2), [jobFromInstruction (p.1.1, p.2)])) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend :
      TMPolyTimeMap X jobListStructuredEncodedType
        (fun p : X.Carrier =>
          (show List Job from p.1.2) ++ [jobFromInstruction (p.1.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append jobStructuredEncodedType)
      hAppendInput
    simpa [Function.comp, jobListStructuredEncodedType, X] using hComp
  have hPair := TMPolyTimeMap.prod_mk hCapacity hAppend
  simpa [jobFoldRightStep, jobFoldAccEncodedType, X] using hPair

theorem jobFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod jobFoldAccEncodedType jobFoldInstructionEncodedType)
      jobFoldAccEncodedType
      jobFoldStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      jobFoldAccEncodedType EncodedType.nat knapsackItemStructuredEncodedType
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim jobFoldLeftStep_tm_polytime
      jobFoldRightStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

/-! ### Growth bound for the job-instruction fold -/

def jobFoldAccBound (N : Nat) (acc : jobFoldAccEncodedType.Carrier) : Prop :=
  EncodedType.nat.inputSize acc.1 ≤ N + 1

noncomputable def jobFoldGrowPolynomial : Polynomial Nat :=
  Polynomial.C 10 * Polynomial.X + Polynomial.C 30

@[simp] theorem jobFoldGrowPolynomial_eval (N : Nat) :
    jobFoldGrowPolynomial.eval N = 10 * N + 30 := by
  simp [jobFoldGrowPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

theorem jobListStructured_inputSize_append_singleton (jobs : List Job) (j : Job) :
    jobListStructuredEncodedType.inputSize (jobs ++ [j]) =
      jobListStructuredEncodedType.inputSize jobs + jobStructuredEncodedType.inputSize j + 1 := by
  rw [jobListStructured_inputSize_eq, jobListStructured_inputSize_eq]
  simp [jobStructured_inputSize_eq]
  omega

theorem jobFromInstruction_inputSize_succ_le
    (capacity : Nat) (item : Nat × Nat) {N : Nat}
    (hCapacity : EncodedType.nat.inputSize capacity ≤ N + 1)
    (hItem : knapsackItemStructuredEncodedType.inputSize item ≤ N) :
    jobStructuredEncodedType.inputSize (jobFromInstruction (capacity, item)) + 1 ≤
      jobFoldGrowPolynomial.eval N := by
  rcases item with ⟨weight, value⟩
  have hCapacitySize : capacity + 1 ≤ N + 1 := by
    simpa [EncodedType.inputSize_nat] using hCapacity
  have hWeight : weight ≤ N := by
    have h := hItem
    simp [knapsackItemStructuredEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_nat] at h
    omega
  have hValue : value ≤ N := by
    have h := hItem
    simp [knapsackItemStructuredEncodedType, EncodedType.inputSize_prod,
      EncodedType.inputSize_nat] at h
    omega
  simp [jobFoldGrowPolynomial_eval, jobFromInstruction, textbookJob,
    jobStructured_inputSize_eq]
  nlinarith

theorem jobFoldStep_growth
    (source : List jobFoldInstructionEncodedType.Carrier)
    (acc : jobFoldAccEncodedType.Carrier)
    (instr : jobFoldInstructionEncodedType.Carrier)
    (hAcc :
      jobFoldAccBound
        (jobFoldInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      jobFoldInstructionEncodedType.inputSize instr ≤
        jobFoldInstructionListEncodedType.inputSize source) :
    jobFoldAccBound
        (jobFoldInstructionListEncodedType.inputSize source)
        (jobFoldStep (acc, instr)) ∧
      jobFoldAccEncodedType.inputSize (jobFoldStep (acc, instr)) ≤
        jobFoldAccEncodedType.inputSize acc +
          jobFoldGrowPolynomial.eval
            (jobFoldInstructionListEncodedType.inputSize source) := by
  let N := jobFoldInstructionListEncodedType.inputSize source
  cases instr with
  | inl capacity =>
      change Nat at capacity
      have hCapacityTagged :
          EncodedType.nat.inputSize capacity + 1 ≤ N := by
        simpa [jobFoldInstructionEncodedType, EncodedType.inputSize, EncodedType.sum,
          N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
      have hCapacity : EncodedType.nat.inputSize capacity ≤ N + 1 := by
        omega
      constructor
      · simpa [jobFoldAccBound, jobFoldStep, jobFoldLeftStep, N] using hCapacity
      · have hNil :
            jobListStructuredEncodedType.inputSize ([] : List Job) = 0 := by
          change (EncodedType.list jobStructuredEncodedType).inputSize ([] : List Job) = 0
          exact EncodedType.inputSize_list_nil jobStructuredEncodedType
        have hCapacityNat : capacity ≤ N := by
          simpa [EncodedType.inputSize_nat] using hCapacity
        simp [jobFoldStep, jobFoldLeftStep, jobFoldAccEncodedType,
          EncodedType.inputSize_prod, hNil]
        omega
  | inr item =>
      change Nat × Nat at item
      have hItemTagged :
          knapsackItemStructuredEncodedType.inputSize item + 1 ≤ N := by
        simpa [jobFoldInstructionEncodedType, EncodedType.inputSize, EncodedType.sum,
          N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
      have hItem : knapsackItemStructuredEncodedType.inputSize item ≤ N := by
        omega
      constructor
      · simpa [jobFoldAccBound, jobFoldStep, jobFoldRightStep, N] using hAcc
      · let out : List Job := acc.2
        let job : Job := jobFromInstruction (acc.1, item)
        have hJob :
            jobStructuredEncodedType.inputSize job + 1 ≤
              jobFoldGrowPolynomial.eval N := by
          simpa [job] using
            jobFromInstruction_inputSize_succ_le acc.1 item (N := N) hAcc hItem
        have hJob' :
            jobStructuredEncodedType.inputSize job + 1 ≤ 10 * N + 30 := by
          simpa [jobFoldGrowPolynomial_eval] using hJob
        have hAppend :
            jobListStructuredEncodedType.inputSize (out ++ [job]) =
              jobListStructuredEncodedType.inputSize out +
                jobStructuredEncodedType.inputSize job + 1 := by
          exact jobListStructured_inputSize_append_singleton out job
        have hStepEq :
            jobFoldStep (acc, Sum.inr item) = (acc.1, out ++ [job]) := by
          rfl
        rw [hStepEq]
        simp [jobFoldAccEncodedType, EncodedType.inputSize_prod]
        rw [hAppend]
        dsimp [out]
        omega

theorem jobFold_tm_polytime :
    TMPolyTimeMap
      jobFoldInstructionListEncodedType
      jobFoldAccEncodedType
      (fun xs : List jobFoldInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => jobFoldStep (acc, instr)) jobFoldInit) := by
  rcases jobFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      jobFoldInstructionEncodedType jobFoldAccEncodedType
      jobFoldStep jobFoldInit hStep
      (Polynomial.C 5) jobFoldGrowPolynomial
      jobFoldAccBound ?_ ?_
  · intro xs
    constructor
    · simp [jobFoldAccBound, jobFoldInit, EncodedType.inputSize_nat]
    · have hNil :
          jobListStructuredEncodedType.inputSize ([] : List Job) = 0 := by
        change (EncodedType.list jobStructuredEncodedType).inputSize ([] : List Job) = 0
        exact EncodedType.inputSize_list_nil jobStructuredEncodedType
      simp [jobFoldInit, jobFoldAccEncodedType, EncodedType.inputSize_prod,
        EncodedType.inputSize_nat, hNil]
  · intro source acc instr hAcc hInstr
    simpa [jobFoldInstructionListEncodedType] using
      jobFoldStep_growth source acc instr hAcc hInstr

theorem jobFoldInstructions_tm_polytime :
    TMPolyTimeMap
      knapsackStructuredEncodedType
      jobFoldInstructionListEncodedType
      jobFoldInstructions := by
  let X := knapsackStructuredEncodedType
  have hTuple :
      TMPolyTimeMap X knapsackTupleStructuredEncodedType
        knapsackTupleOfInput := by
    simpa [X] using knapsackTupleOfInputTMBackedMap.tm_polytime
  have hItems :
      TMPolyTimeMap X knapsackItemListStructuredEncodedType
        (fun I : X.Carrier => I.items) := by
    have hFst := TMPolyTimeMap.fst knapsackItemListStructuredEncodedType
      knapsackBoundsStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTuple
    simpa [Function.comp, knapsackTupleOfInput, knapsackTupleStructuredEncodedType, X]
      using hComp
  have hBounds :
      TMPolyTimeMap X knapsackBoundsStructuredEncodedType
        (fun I : X.Carrier => (I.capacity, I.targetValue)) := by
    have hSnd := TMPolyTimeMap.snd knapsackItemListStructuredEncodedType
      knapsackBoundsStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTuple
    simpa [Function.comp, knapsackTupleOfInput, knapsackTupleStructuredEncodedType, X]
      using hComp
  have hCapacity :
      TMPolyTimeMap X EncodedType.nat
        (fun I : X.Carrier => I.capacity) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hBounds
    simpa [Function.comp, knapsackBoundsStructuredEncodedType, X] using hComp
  have hInit :
      TMPolyTimeMap X jobFoldInstructionEncodedType
        (fun I : X.Carrier => Sum.inl I.capacity) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl EncodedType.nat knapsackItemStructuredEncodedType)
      hCapacity
    simpa [Function.comp, jobFoldInstructionEncodedType, X] using hComp
  have hItemInstruction :
      TMPolyTimeMap knapsackItemStructuredEncodedType jobFoldInstructionEncodedType
        (fun item : knapsackItemStructuredEncodedType.Carrier => Sum.inr item) := by
    simpa [jobFoldInstructionEncodedType] using
      TMPolyTimeMap.inr EncodedType.nat knapsackItemStructuredEncodedType
  have hMappedItems :
      TMPolyTimeMap X jobFoldInstructionListEncodedType
        (fun I : X.Carrier => I.items.map Sum.inr) := by
    have hMap := TMPolyTimeMap.list_map hItemInstruction
    have hComp := TMPolyTimeMap.comp hMap hItems
    simpa [Function.comp, jobFoldInstructionListEncodedType,
      knapsackItemListStructuredEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod jobFoldInstructionEncodedType jobFoldInstructionListEncodedType)
        (fun I : X.Carrier => (Sum.inl I.capacity, I.items.map Sum.inr)) :=
    TMPolyTimeMap.prod_mk hInit hMappedItems
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons jobFoldInstructionEncodedType)
      hConsInput
  simpa [Function.comp, jobFoldInstructions, jobFoldInstructionListEncodedType, X]
    using hCons

theorem textbookJobsTM_tm_polytime :
    TMPolyTimeMap
      knapsackStructuredEncodedType
      jobListStructuredEncodedType
      textbookJobsTM := by
  have hFold :=
    TMPolyTimeMap.comp jobFold_tm_polytime jobFoldInstructions_tm_polytime
  have hOut :=
    TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.nat jobListStructuredEncodedType)
      hFold
  simpa [Function.comp, textbookJobsTM, jobFoldAccEncodedType] using hOut

theorem knapsackToJobSequencingStructuredTMMap_inputSize_le_knapsack_poly
    (I : KnapsackInput) :
    jobSequencingStructuredEncodedType.inputSize (knapsackToJobSequencingStructuredTMMap I) ≤
      1000 * (knapsackStructuredEncodedType.inputSize I) ^ 2 + 1000 := by
  rw [knapsackToJobSequencingStructuredTMMap_eq_textbookMap]
  exact jobSequencingStructured_inputSize_textbookMap_le_knapsack_poly I

theorem knapsackToJobSequencingStructuredTMMap_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : KnapsackInput => knapsackStructuredEncodedType.inputSize I)
      (fun J : JobSequencingInput => jobSequencingStructuredEncodedType.inputSize J)
      knapsackToJobSequencingStructuredTMMap := by
  refine PolynomialSizeBound.intro_with 2 1000 1000 ?_
  intro I
  exact knapsackToJobSequencingStructuredTMMap_inputSize_le_knapsack_poly I

theorem knapsackToJobSequencingStructured_tm_polytime :
    TMPolyTimeMap
      knapsackStructuredEncodedType
      jobSequencingStructuredEncodedType
      knapsackToJobSequencingStructuredTMMap := by
  let X := knapsackStructuredEncodedType
  have hTuple :
      TMPolyTimeMap X knapsackTupleStructuredEncodedType
        knapsackTupleOfInput := by
    simpa [X] using knapsackTupleOfInputTMBackedMap.tm_polytime
  have hBounds :
      TMPolyTimeMap X knapsackBoundsStructuredEncodedType
        (fun I : X.Carrier => (I.capacity, I.targetValue)) := by
    have hSnd := TMPolyTimeMap.snd knapsackItemListStructuredEncodedType
      knapsackBoundsStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTuple
    simpa [Function.comp, knapsackTupleOfInput, knapsackTupleStructuredEncodedType, X]
      using hComp
  have hTarget :
      TMPolyTimeMap X EncodedType.nat
        (fun I : X.Carrier => I.targetValue) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hBounds
    simpa [Function.comp, knapsackBoundsStructuredEncodedType, X] using hComp
  have hJobs :
      TMPolyTimeMap X jobListStructuredEncodedType
        textbookJobsTM := by
    simpa [X] using textbookJobsTM_tm_polytime
  have hOutTuple :
      TMPolyTimeMap X jobSequencingTupleStructuredEncodedType
        (fun I : X.Carrier => (textbookJobsTM I, I.targetValue)) :=
    TMPolyTimeMap.prod_mk hJobs hTarget
  have hInput :=
    TMPolyTimeMap.comp jobSequencingTupleToInputTMBackedMap.tm_polytime hOutTuple
  simpa [Function.comp, jobSequencingTupleToInput, knapsackToJobSequencingStructuredTMMap,
    X] using hInput

noncomputable def knapsackToJobSequencingStructuredTMBackedMap :
    TMBackedCostedMap
      knapsackStructuredEncodedType
      jobSequencingStructuredEncodedType
      knapsackToJobSequencingStructuredTMMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      knapsackToJobSequencingStructuredTMMap_polynomialSizeBound
  tm_polytime := knapsackToJobSequencingStructured_tm_polytime

theorem knapsackToJobSequencingStructuredTMMap_correct (I : KnapsackInput) :
    knapsackStructuredDecisionProblem.isYes I ↔
      jobSequencingStructuredDecisionProblem.isYes
        (knapsackToJobSequencingStructuredTMMap I) := by
  rw [knapsackToJobSequencingStructuredTMMap_eq_textbookMap]
  simpa [knapsackStructuredDecisionProblem, jobSequencingStructuredDecisionProblem]
    using textbookMap_correct I

noncomputable def knapsackToJobSequencingStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      knapsackStructuredDecisionProblem
      jobSequencingStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    knapsackToJobSequencingStructuredTMBackedMap
    (by
      intro I
      exact knapsackToJobSequencingStructuredTMMap_correct I)

/--
Public P16c structured finite-alphabet Knapsack-to-Job-Sequencing reduction,
projected from the direct TM-backed witness.
-/
noncomputable def knapsackToJobSequencingStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      knapsackStructuredDecisionProblem
      jobSequencingStructuredDecisionProblem :=
  knapsackToJobSequencingStructuredTMBackedKarpReduction.toCostedKarpReduction

/-- Compatibility alias for the former size-only structured wrapper. -/
noncomputable def knapsackToJobSequencingStructuredCostedKarpReduction :
    KarpReductionM CostedPolyTimeModel
      knapsackStructuredDecisionProblem jobSequencingStructuredDecisionProblem :=
  knapsackToJobSequencingStructuredKarpReduction

/-- Direct TM-facing structured Knapsack-to-Job-Sequencing reduction. -/
noncomputable def knapsackToJobSequencingStructuredTMKarpReduction :
    TMKarpReduction
      knapsackStructuredDecisionProblem
      jobSequencingStructuredDecisionProblem :=
  knapsackToJobSequencingStructuredTMBackedKarpReduction.toTMKarpReduction

end JobSequencing
end Karp21
end ComplexityReduction
