/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.JobSequencingStructuredTM

/-!
Direct TM-backed binary-numeric structured assembly for the Knapsack to Job
Sequencing textbook route.
-/

namespace ComplexityReduction
namespace Karp21
namespace JobSequencing

open ComplexityReduction.Combinatorics

def knapsackTupleBinaryOfInput (I : KnapsackInput) :
    knapsackTupleBinaryStructuredEncodedType.Carrier :=
  (I.items, (I.capacity, I.targetValue))

theorem knapsackTupleBinaryOfInput_encode (I : KnapsackInput) :
    knapsackTupleBinaryStructuredEncodedType.encode (knapsackTupleBinaryOfInput I) =
      knapsackBinaryStructuredEncodedType.encode I := by
  rfl

noncomputable def knapsackTupleBinaryOfInputTMBackedMap :
    TMBackedCostedMap
      knapsackBinaryStructuredEncodedType
      knapsackTupleBinaryStructuredEncodedType
      knapsackTupleBinaryOfInput :=
  TMBackedCostedMap.ofEncodingEquiv
    knapsackBinaryStructuredEncodedType knapsackTupleBinaryStructuredEncodedType
    knapsackTupleBinaryOfInput
    (Equiv.refl knapsackTupleBinaryStructuredEncodedType.Symbol)
    (by
      intro I
      change knapsackTupleBinaryStructuredEncodedType.encode (knapsackTupleBinaryOfInput I) =
        (knapsackBinaryStructuredEncodedType.encode I).map id
      simp [knapsackTupleBinaryOfInput_encode])

theorem jobTupleToJob_binary_encode (p : jobTupleBinaryStructuredEncodedType.Carrier) :
    jobBinaryStructuredEncodedType.encode (jobTupleToJob p) =
      jobTupleBinaryStructuredEncodedType.encode p := by
  rcases p with ⟨processingTime, deadline, profit⟩
  rfl

noncomputable def jobTupleToJobBinaryTMBackedMap :
    TMBackedCostedMap
      jobTupleBinaryStructuredEncodedType
      jobBinaryStructuredEncodedType
      jobTupleToJob :=
  TMBackedCostedMap.ofEncodingEquiv
    jobTupleBinaryStructuredEncodedType jobBinaryStructuredEncodedType jobTupleToJob
    (Equiv.refl jobTupleBinaryStructuredEncodedType.Symbol)
    (by
      intro p
      change jobBinaryStructuredEncodedType.encode (jobTupleToJob p) =
        (jobTupleBinaryStructuredEncodedType.encode p).map id
      simp [jobTupleToJob_binary_encode])

theorem jobSequencingTupleToInput_binary_encode
    (p : jobSequencingTupleBinaryStructuredEncodedType.Carrier) :
    jobSequencingBinaryStructuredEncodedType.encode (jobSequencingTupleToInput p) =
      jobSequencingTupleBinaryStructuredEncodedType.encode p := by
  rcases p with ⟨jobs, targetProfit⟩
  rfl

noncomputable def jobSequencingTupleToInputBinaryTMBackedMap :
    TMBackedCostedMap
      jobSequencingTupleBinaryStructuredEncodedType
      jobSequencingBinaryStructuredEncodedType
      jobSequencingTupleToInput :=
  TMBackedCostedMap.ofEncodingEquiv
    jobSequencingTupleBinaryStructuredEncodedType jobSequencingBinaryStructuredEncodedType
    jobSequencingTupleToInput
    (Equiv.refl jobSequencingTupleBinaryStructuredEncodedType.Symbol)
    (by
      intro p
      change jobSequencingBinaryStructuredEncodedType.encode (jobSequencingTupleToInput p) =
        (jobSequencingTupleBinaryStructuredEncodedType.encode p).map id
      simp [jobSequencingTupleToInput_binary_encode])

def jobFromBinaryInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat knapsackItemBinaryStructuredEncodedType

theorem jobFromBinaryInstruction_tm_polytime :
    TMPolyTimeMap
      jobFromBinaryInstructionEncodedType
      jobBinaryStructuredEncodedType
      jobFromInstruction := by
  let X := jobFromBinaryInstructionEncodedType
  have hCapacity :
      TMPolyTimeMap X EncodedType.binaryNat (fun p : X.Carrier => p.1) := by
    simpa [X, jobFromBinaryInstructionEncodedType] using
      TMPolyTimeMap.fst EncodedType.binaryNat knapsackItemBinaryStructuredEncodedType
  have hItem :
      TMPolyTimeMap X knapsackItemBinaryStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X, jobFromBinaryInstructionEncodedType] using
      TMPolyTimeMap.snd EncodedType.binaryNat knapsackItemBinaryStructuredEncodedType
  have hProcessing :
      TMPolyTimeMap X EncodedType.binaryNat (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hItem
    simpa [Function.comp, X, knapsackItemBinaryStructuredEncodedType] using hComp
  have hProfit :
      TMPolyTimeMap X EncodedType.binaryNat (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hSnd hItem
    simpa [Function.comp, X, knapsackItemBinaryStructuredEncodedType] using hComp
  have hTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : X.Carrier => (p.1, p.2.2)) :=
    TMPolyTimeMap.prod_mk hCapacity hProfit
  have hTuple :
      TMPolyTimeMap X jobTupleBinaryStructuredEncodedType
        (fun p : X.Carrier => (p.2.1, (p.1, p.2.2))) :=
    TMPolyTimeMap.prod_mk hProcessing hTail
  have hJob := TMPolyTimeMap.comp jobTupleToJobBinaryTMBackedMap.tm_polytime hTuple
  simpa [Function.comp, jobFromInstruction, textbookJob, jobTupleToJob, X] using hJob

def jobFoldBinaryInstructionEncodedType : EncodedType :=
  EncodedType.sum EncodedType.binaryNat knapsackItemBinaryStructuredEncodedType

def jobFoldBinaryInstructionListEncodedType : EncodedType :=
  EncodedType.list jobFoldBinaryInstructionEncodedType

def jobFoldBinaryAccEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat jobListBinaryStructuredEncodedType

def jobFoldBinaryInit : jobFoldBinaryAccEncodedType.Carrier :=
  ((0 : Nat), ([] : List Job))

def jobFoldBinaryLeftStep (capacity : Nat) : jobFoldBinaryAccEncodedType.Carrier :=
  (capacity, ([] : List Job))

def jobFoldBinaryRightStep
    (p : jobFoldBinaryAccEncodedType.Carrier × (Nat × Nat)) :
    jobFoldBinaryAccEncodedType.Carrier :=
  let capacity : Nat := p.1.1
  let out : List Job := p.1.2
  (capacity, out ++ [jobFromInstruction (capacity, p.2)])

def jobFoldBinaryStep
    (p : jobFoldBinaryAccEncodedType.Carrier × jobFoldBinaryInstructionEncodedType.Carrier) :
    jobFoldBinaryAccEncodedType.Carrier :=
  match p.2 with
  | Sum.inl capacity => jobFoldBinaryLeftStep capacity
  | Sum.inr item => jobFoldBinaryRightStep (p.1, item)

def jobFoldBinaryInstructions (I : KnapsackInput) :
    List jobFoldBinaryInstructionEncodedType.Carrier :=
  Sum.inl I.capacity :: I.items.map Sum.inr

def textbookJobsBinaryTM (I : KnapsackInput) : List Job :=
  ((jobFoldBinaryInstructions I).foldl
    (fun acc instr => jobFoldBinaryStep (acc, instr)) jobFoldBinaryInit).2

def knapsackToJobSequencingBinaryStructuredTMMap (I : KnapsackInput) : JobSequencingInput where
  jobs := textbookJobsBinaryTM I
  targetProfit := I.targetValue

theorem jobFoldBinary_items_eq
    (capacity : Nat) (items : List (Nat × Nat)) (out : List Job) :
    (items.map Sum.inr).foldl
        (fun acc instr => jobFoldBinaryStep (acc, instr))
        (capacity, out) =
      (capacity, out ++ textbookJobsFrom capacity 0 items) := by
  induction items generalizing out with
  | nil =>
      simp [textbookJobsFrom]
      rfl
  | cons item items ih =>
      change
        (items.map Sum.inr).foldl
            (fun acc instr => jobFoldBinaryStep (acc, instr))
            (jobFoldBinaryRightStep ((capacity, out), item)) =
          (capacity, out ++ textbookJobsFrom capacity 0 (item :: items))
      simp only [jobFoldBinaryRightStep, jobFromInstruction, textbookJob]
      rw [ih]
      simp [textbookJobsFrom, textbookJob, List.append_assoc,
        textbookJobsFrom_index_eq capacity 0 1 items]

theorem textbookJobsBinaryTM_eq_textbookJobs (I : KnapsackInput) :
    textbookJobsBinaryTM I = textbookJobsFrom I.capacity 0 I.items := by
  unfold textbookJobsBinaryTM jobFoldBinaryInstructions
  rw [List.foldl_cons]
  simpa [jobFoldBinaryInit, jobFoldBinaryStep, jobFoldBinaryLeftStep] using
    congrArg Prod.snd (jobFoldBinary_items_eq I.capacity I.items [])

theorem knapsackToJobSequencingBinaryStructuredTMMap_eq_textbookMap (I : KnapsackInput) :
    knapsackToJobSequencingBinaryStructuredTMMap I = textbookMap I := by
  cases I with
  | mk items capacity targetValue =>
      simp [knapsackToJobSequencingBinaryStructuredTMMap, textbookMap,
        textbookJobsBinaryTM_eq_textbookJobs]

theorem jobFoldBinaryLeftStep_tm_polytime :
    TMPolyTimeMap EncodedType.binaryNat jobFoldBinaryAccEncodedType
      jobFoldBinaryLeftStep := by
  have hCapacity : TMPolyTimeMap EncodedType.binaryNat EncodedType.binaryNat id :=
    TMPolyTimeMap.id EncodedType.binaryNat
  have hOut :
      TMPolyTimeMap EncodedType.binaryNat jobListBinaryStructuredEncodedType
        (fun _ : Nat => ([] : List Job)) :=
    TMPolyTimeMap.const EncodedType.binaryNat jobListBinaryStructuredEncodedType []
  have hPair := TMPolyTimeMap.prod_mk hCapacity hOut
  simpa [jobFoldBinaryLeftStep, Function.comp, jobFoldBinaryAccEncodedType] using hPair

theorem jobFoldBinaryRightStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod jobFoldBinaryAccEncodedType knapsackItemBinaryStructuredEncodedType)
      jobFoldBinaryAccEncodedType
      jobFoldBinaryRightStep := by
  let X := EncodedType.prod jobFoldBinaryAccEncodedType knapsackItemBinaryStructuredEncodedType
  have hAcc :
      TMPolyTimeMap X jobFoldBinaryAccEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst jobFoldBinaryAccEncodedType
      knapsackItemBinaryStructuredEncodedType
  have hCapacity :
      TMPolyTimeMap X EncodedType.binaryNat (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat jobListBinaryStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, X, jobFoldBinaryAccEncodedType] using hComp
  have hOut :
      TMPolyTimeMap X jobListBinaryStructuredEncodedType (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat jobListBinaryStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, X, jobFoldBinaryAccEncodedType] using hComp
  have hItem :
      TMPolyTimeMap X knapsackItemBinaryStructuredEncodedType (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd jobFoldBinaryAccEncodedType
      knapsackItemBinaryStructuredEncodedType
  have hJobInput :
      TMPolyTimeMap X jobFromBinaryInstructionEncodedType
        (fun p : X.Carrier => (p.1.1, p.2)) :=
    TMPolyTimeMap.prod_mk hCapacity hItem
  have hJob :
      TMPolyTimeMap X jobBinaryStructuredEncodedType
        (fun p : X.Carrier => jobFromInstruction (p.1.1, p.2)) := by
    have hComp := TMPolyTimeMap.comp jobFromBinaryInstruction_tm_polytime hJobInput
    simpa [Function.comp, X] using hComp
  have hSingleton :
      TMPolyTimeMap X jobListBinaryStructuredEncodedType
        (fun p : X.Carrier => [jobFromInstruction (p.1.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton jobBinaryStructuredEncodedType) hJob
    simpa [Function.comp, jobListBinaryStructuredEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod jobListBinaryStructuredEncodedType jobListBinaryStructuredEncodedType)
        (fun p : X.Carrier =>
          ((show List Job from p.1.2), [jobFromInstruction (p.1.1, p.2)])) :=
    TMPolyTimeMap.prod_mk hOut hSingleton
  have hAppend :
      TMPolyTimeMap X jobListBinaryStructuredEncodedType
        (fun p : X.Carrier =>
          (show List Job from p.1.2) ++ [jobFromInstruction (p.1.1, p.2)]) := by
    have hComp := TMPolyTimeMap.comp (TMPolyTimeMap.list_append jobBinaryStructuredEncodedType)
      hAppendInput
    simpa [Function.comp, jobListBinaryStructuredEncodedType, X] using hComp
  have hPair := TMPolyTimeMap.prod_mk hCapacity hAppend
  simpa [jobFoldBinaryRightStep, jobFoldBinaryAccEncodedType, X] using hPair

theorem jobFoldBinaryStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod jobFoldBinaryAccEncodedType jobFoldBinaryInstructionEncodedType)
      jobFoldBinaryAccEncodedType
      jobFoldBinaryStep := by
  have hChoice :=
    Partition.prodSumChoice_tm_polytime
      jobFoldBinaryAccEncodedType EncodedType.binaryNat knapsackItemBinaryStructuredEncodedType
  have hBranches :=
    Partition.TMPolyTimeMap.sum_elim jobFoldBinaryLeftStep_tm_polytime
      jobFoldBinaryRightStep_tm_polytime
  have hComp := TMPolyTimeMap.comp hBranches hChoice
  convert hComp using 1
  funext p
  rcases p with ⟨acc, instr⟩
  cases instr <;> rfl

def jobFoldBinaryAccBound (N : Nat) (acc : jobFoldBinaryAccEncodedType.Carrier) : Prop :=
  EncodedType.binaryNat.inputSize acc.1 ≤ N + 1

noncomputable def jobFoldBinaryGrowPolynomial : Polynomial Nat :=
  Polynomial.C 10 * Polynomial.X + Polynomial.C 30

@[simp] theorem jobFoldBinaryGrowPolynomial_eval (N : Nat) :
    jobFoldBinaryGrowPolynomial.eval N = 10 * N + 30 := by
  simp [jobFoldBinaryGrowPolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]

theorem jobListBinaryStructured_inputSize_append_singleton (jobs : List Job) (j : Job) :
    jobListBinaryStructuredEncodedType.inputSize (jobs ++ [j]) =
      jobListBinaryStructuredEncodedType.inputSize jobs +
        jobBinaryStructuredEncodedType.inputSize j + 1 := by
  induction jobs with
  | nil =>
      change (EncodedType.list jobBinaryStructuredEncodedType).inputSize (j :: []) =
        (EncodedType.list jobBinaryStructuredEncodedType).inputSize ([] : List Job) +
          jobBinaryStructuredEncodedType.inputSize j + 1
      have hCons :
          (EncodedType.list jobBinaryStructuredEncodedType).inputSize (j :: []) =
            jobBinaryStructuredEncodedType.inputSize j + 1 +
              (EncodedType.list jobBinaryStructuredEncodedType).inputSize ([] : List Job) :=
        EncodedType.inputSize_list_cons jobBinaryStructuredEncodedType j []
      have hNil :
          (EncodedType.list jobBinaryStructuredEncodedType).inputSize ([] : List Job) = 0 :=
        EncodedType.inputSize_list_nil jobBinaryStructuredEncodedType
      rw [hCons, hNil]
      omega
  | cons head tail ih =>
      change (EncodedType.list jobBinaryStructuredEncodedType).inputSize
          (head :: (tail ++ [j])) =
        (EncodedType.list jobBinaryStructuredEncodedType).inputSize (head :: tail) +
          jobBinaryStructuredEncodedType.inputSize j + 1
      rw [EncodedType.inputSize_list_cons, EncodedType.inputSize_list_cons]
      change jobBinaryStructuredEncodedType.inputSize head + 1 +
          jobListBinaryStructuredEncodedType.inputSize (tail ++ [j]) =
        jobBinaryStructuredEncodedType.inputSize head + 1 +
            jobListBinaryStructuredEncodedType.inputSize tail +
          jobBinaryStructuredEncodedType.inputSize j + 1
      rw [ih]
      omega

theorem jobFromBinaryInstruction_inputSize_succ_le
    (capacity : Nat) (item : Nat × Nat) {N : Nat}
    (hCapacity : EncodedType.binaryNat.inputSize capacity ≤ N + 1)
    (hItem : knapsackItemBinaryStructuredEncodedType.inputSize item ≤ N) :
    jobBinaryStructuredEncodedType.inputSize (jobFromInstruction (capacity, item)) + 1 ≤
      jobFoldBinaryGrowPolynomial.eval N := by
  rcases item with ⟨weight, value⟩
  have hItem' := hItem
  simp [knapsackItemBinaryStructuredEncodedType, EncodedType.inputSize_prod] at hItem'
  simp [jobFoldBinaryGrowPolynomial_eval, jobFromInstruction, textbookJob,
    jobBinaryStructured_inputSize_eq]
  omega

theorem jobFoldBinaryStep_growth
    (source : List jobFoldBinaryInstructionEncodedType.Carrier)
    (acc : jobFoldBinaryAccEncodedType.Carrier)
    (instr : jobFoldBinaryInstructionEncodedType.Carrier)
    (hAcc :
      jobFoldBinaryAccBound
        (jobFoldBinaryInstructionListEncodedType.inputSize source) acc)
    (hInstr :
      jobFoldBinaryInstructionEncodedType.inputSize instr ≤
        jobFoldBinaryInstructionListEncodedType.inputSize source) :
    jobFoldBinaryAccBound
        (jobFoldBinaryInstructionListEncodedType.inputSize source)
        (jobFoldBinaryStep (acc, instr)) ∧
      jobFoldBinaryAccEncodedType.inputSize (jobFoldBinaryStep (acc, instr)) ≤
        jobFoldBinaryAccEncodedType.inputSize acc +
          jobFoldBinaryGrowPolynomial.eval
            (jobFoldBinaryInstructionListEncodedType.inputSize source) := by
  let N := jobFoldBinaryInstructionListEncodedType.inputSize source
  cases instr with
  | inl capacity =>
      change Nat at capacity
      have hCapacityTagged :
          EncodedType.binaryNat.inputSize capacity + 1 ≤ N := by
        simpa [jobFoldBinaryInstructionEncodedType, EncodedType.inputSize, EncodedType.sum,
          N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
      have hCapacity : EncodedType.binaryNat.inputSize capacity ≤ N + 1 := by
        omega
      constructor
      · simpa [jobFoldBinaryAccBound, jobFoldBinaryStep, jobFoldBinaryLeftStep, N] using hCapacity
      · have hNil :
            jobListBinaryStructuredEncodedType.inputSize ([] : List Job) = 0 := by
          change (EncodedType.list jobBinaryStructuredEncodedType).inputSize ([] : List Job) = 0
          exact EncodedType.inputSize_list_nil jobBinaryStructuredEncodedType
        simp [jobFoldBinaryStep, jobFoldBinaryLeftStep, jobFoldBinaryAccEncodedType,
          EncodedType.inputSize_prod, hNil]
        omega
  | inr item =>
      change Nat × Nat at item
      have hItemTagged :
          knapsackItemBinaryStructuredEncodedType.inputSize item + 1 ≤ N := by
        simpa [jobFoldBinaryInstructionEncodedType, EncodedType.inputSize, EncodedType.sum,
          N, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hInstr
      have hItem : knapsackItemBinaryStructuredEncodedType.inputSize item ≤ N := by
        omega
      constructor
      · simpa [jobFoldBinaryAccBound, jobFoldBinaryStep, jobFoldBinaryRightStep, N] using hAcc
      · let out : List Job := acc.2
        let job : Job := jobFromInstruction (acc.1, item)
        have hJob :
            jobBinaryStructuredEncodedType.inputSize job + 1 ≤
              jobFoldBinaryGrowPolynomial.eval N := by
          simpa [job] using
            jobFromBinaryInstruction_inputSize_succ_le acc.1 item (N := N) hAcc hItem
        have hJob' :
            jobBinaryStructuredEncodedType.inputSize job + 1 ≤ 10 * N + 30 := by
          simpa [jobFoldBinaryGrowPolynomial_eval] using hJob
        have hAppend :
            jobListBinaryStructuredEncodedType.inputSize (out ++ [job]) =
              jobListBinaryStructuredEncodedType.inputSize out +
                jobBinaryStructuredEncodedType.inputSize job + 1 := by
          exact jobListBinaryStructured_inputSize_append_singleton out job
        have hStepEq :
            jobFoldBinaryStep (acc, Sum.inr item) = (acc.1, out ++ [job]) := by
          rfl
        rw [hStepEq]
        simp [jobFoldBinaryAccEncodedType, EncodedType.inputSize_prod]
        rw [hAppend]
        dsimp [out]
        omega

theorem jobFoldBinary_tm_polytime :
    TMPolyTimeMap
      jobFoldBinaryInstructionListEncodedType
      jobFoldBinaryAccEncodedType
      (fun xs : List jobFoldBinaryInstructionEncodedType.Carrier =>
        xs.foldl (fun acc instr => jobFoldBinaryStep (acc, instr)) jobFoldBinaryInit) := by
  rcases jobFoldBinaryStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_invariant_growth_bounded
      jobFoldBinaryInstructionEncodedType jobFoldBinaryAccEncodedType
      jobFoldBinaryStep jobFoldBinaryInit hStep
      (Polynomial.C 5) jobFoldBinaryGrowPolynomial
      jobFoldBinaryAccBound ?_ ?_
  · intro xs
    constructor
    · simp [jobFoldBinaryAccBound, jobFoldBinaryInit, EncodedType.inputSize,
        EncodedType.binaryNat]
    ·
      have hZero : EncodedType.binaryNat.inputSize (0 : Nat) = 0 := by
        simp [EncodedType.inputSize, EncodedType.binaryNat, Nat.digits_zero]
      have hNil :
          jobListBinaryStructuredEncodedType.inputSize ([] : List Job) = 0 := by
        change (EncodedType.list jobBinaryStructuredEncodedType).inputSize ([] : List Job) = 0
        exact EncodedType.inputSize_list_nil jobBinaryStructuredEncodedType
      have hZeroLt : EncodedType.binaryNat.inputSize (0 : Nat) < 5 := by
        rw [hZero]
        norm_num
      simp [jobFoldBinaryInit, jobFoldBinaryAccEncodedType, EncodedType.inputSize_prod,
        hNil] at hZeroLt ⊢
  · intro source acc instr hAcc hInstr
    simpa [jobFoldBinaryInstructionListEncodedType] using
      jobFoldBinaryStep_growth source acc instr hAcc hInstr

theorem jobFoldBinaryInstructions_tm_polytime :
    TMPolyTimeMap
      knapsackBinaryStructuredEncodedType
      jobFoldBinaryInstructionListEncodedType
      jobFoldBinaryInstructions := by
  let X := knapsackBinaryStructuredEncodedType
  have hTuple :
      TMPolyTimeMap X knapsackTupleBinaryStructuredEncodedType
        knapsackTupleBinaryOfInput := by
    simpa [X] using knapsackTupleBinaryOfInputTMBackedMap.tm_polytime
  have hItems :
      TMPolyTimeMap X knapsackItemListBinaryStructuredEncodedType
        (fun I : X.Carrier => I.items) := by
    have hFst := TMPolyTimeMap.fst knapsackItemListBinaryStructuredEncodedType
      knapsackBoundsBinaryStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hTuple
    simpa [Function.comp, knapsackTupleBinaryOfInput, knapsackTupleBinaryStructuredEncodedType, X]
      using hComp
  have hBounds :
      TMPolyTimeMap X knapsackBoundsBinaryStructuredEncodedType
        (fun I : X.Carrier => (I.capacity, I.targetValue)) := by
    have hSnd := TMPolyTimeMap.snd knapsackItemListBinaryStructuredEncodedType
      knapsackBoundsBinaryStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTuple
    simpa [Function.comp, knapsackTupleBinaryOfInput, knapsackTupleBinaryStructuredEncodedType, X]
      using hComp
  have hCapacity :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun I : X.Carrier => I.capacity) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hBounds
    simpa [Function.comp, knapsackBoundsBinaryStructuredEncodedType, X] using hComp
  have hInit :
      TMPolyTimeMap X jobFoldBinaryInstructionEncodedType
        (fun I : X.Carrier => Sum.inl I.capacity) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.inl EncodedType.binaryNat knapsackItemBinaryStructuredEncodedType)
      hCapacity
    simpa [Function.comp, jobFoldBinaryInstructionEncodedType, X] using hComp
  have hItemInstruction :
      TMPolyTimeMap knapsackItemBinaryStructuredEncodedType jobFoldBinaryInstructionEncodedType
        (fun item : knapsackItemBinaryStructuredEncodedType.Carrier => Sum.inr item) := by
    simpa [jobFoldBinaryInstructionEncodedType] using
      TMPolyTimeMap.inr EncodedType.binaryNat knapsackItemBinaryStructuredEncodedType
  have hMappedItems :
      TMPolyTimeMap X jobFoldBinaryInstructionListEncodedType
        (fun I : X.Carrier => I.items.map Sum.inr) := by
    have hMap := TMPolyTimeMap.list_map hItemInstruction
    have hComp := TMPolyTimeMap.comp hMap hItems
    simpa [Function.comp, jobFoldBinaryInstructionListEncodedType,
      knapsackItemListBinaryStructuredEncodedType, X] using hComp
  have hConsInput :
      TMPolyTimeMap X
        (EncodedType.prod jobFoldBinaryInstructionEncodedType jobFoldBinaryInstructionListEncodedType)
        (fun I : X.Carrier => (Sum.inl I.capacity, I.items.map Sum.inr)) :=
    TMPolyTimeMap.prod_mk hInit hMappedItems
  have hCons :=
    TMPolyTimeMap.comp (TMPolyTimeMap.list_cons jobFoldBinaryInstructionEncodedType)
      hConsInput
  simpa [Function.comp, jobFoldBinaryInstructions, jobFoldBinaryInstructionListEncodedType, X]
    using hCons

theorem textbookJobsBinaryTM_tm_polytime :
    TMPolyTimeMap
      knapsackBinaryStructuredEncodedType
      jobListBinaryStructuredEncodedType
      textbookJobsBinaryTM := by
  have hFold :=
    TMPolyTimeMap.comp jobFoldBinary_tm_polytime jobFoldBinaryInstructions_tm_polytime
  have hOut :=
    TMPolyTimeMap.comp
      (TMPolyTimeMap.snd EncodedType.binaryNat jobListBinaryStructuredEncodedType)
      hFold
  simpa [Function.comp, textbookJobsBinaryTM, jobFoldBinaryAccEncodedType] using hOut

theorem knapsackToJobSequencingBinaryStructured_tm_polytime :
    TMPolyTimeMap
      knapsackBinaryStructuredEncodedType
      jobSequencingBinaryStructuredEncodedType
      knapsackToJobSequencingBinaryStructuredTMMap := by
  let X := knapsackBinaryStructuredEncodedType
  have hTuple :
      TMPolyTimeMap X knapsackTupleBinaryStructuredEncodedType
        knapsackTupleBinaryOfInput := by
    simpa [X] using knapsackTupleBinaryOfInputTMBackedMap.tm_polytime
  have hBounds :
      TMPolyTimeMap X knapsackBoundsBinaryStructuredEncodedType
        (fun I : X.Carrier => (I.capacity, I.targetValue)) := by
    have hSnd := TMPolyTimeMap.snd knapsackItemListBinaryStructuredEncodedType
      knapsackBoundsBinaryStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hTuple
    simpa [Function.comp, knapsackTupleBinaryOfInput, knapsackTupleBinaryStructuredEncodedType, X]
      using hComp
  have hTarget :
      TMPolyTimeMap X EncodedType.binaryNat
        (fun I : X.Carrier => I.targetValue) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hSnd hBounds
    simpa [Function.comp, knapsackBoundsBinaryStructuredEncodedType, X] using hComp
  have hJobs :
      TMPolyTimeMap X jobListBinaryStructuredEncodedType
        textbookJobsBinaryTM := by
    simpa [X] using textbookJobsBinaryTM_tm_polytime
  have hOutTuple :
      TMPolyTimeMap X jobSequencingTupleBinaryStructuredEncodedType
        (fun I : X.Carrier => (textbookJobsBinaryTM I, I.targetValue)) :=
    TMPolyTimeMap.prod_mk hJobs hTarget
  have hInput :=
    TMPolyTimeMap.comp jobSequencingTupleToInputBinaryTMBackedMap.tm_polytime hOutTuple
  simpa [Function.comp, jobSequencingTupleToInput,
    knapsackToJobSequencingBinaryStructuredTMMap, X] using hInput

theorem knapsackToJobSequencingBinaryStructuredTMMap_polynomialSizeBound :
    PolynomialSizeBound
      (fun I : KnapsackInput => knapsackBinaryStructuredEncodedType.inputSize I)
      (fun J : JobSequencingInput => jobSequencingBinaryStructuredEncodedType.inputSize J)
      knapsackToJobSequencingBinaryStructuredTMMap := by
  convert knapsackToJobSequencingBinaryStructured_polynomialSizeBound using 1
  funext I
  exact knapsackToJobSequencingBinaryStructuredTMMap_eq_textbookMap I

noncomputable def knapsackToJobSequencingBinaryStructuredTMBackedMap :
    TMBackedCostedMap
      knapsackBinaryStructuredEncodedType
      jobSequencingBinaryStructuredEncodedType
      knapsackToJobSequencingBinaryStructuredTMMap where
  costed :=
    CostedMap.of_encodedPolynomialSizeBound
      knapsackToJobSequencingBinaryStructuredTMMap_polynomialSizeBound
  tm_polytime := knapsackToJobSequencingBinaryStructured_tm_polytime

theorem knapsackToJobSequencingBinaryStructuredTMMap_correct (I : KnapsackInput) :
    knapsackBinaryStructuredDecisionProblem.isYes I ↔
      jobSequencingBinaryStructuredDecisionProblem.isYes
        (knapsackToJobSequencingBinaryStructuredTMMap I) := by
  rw [knapsackToJobSequencingBinaryStructuredTMMap_eq_textbookMap]
  simpa [knapsackBinaryStructuredDecisionProblem, jobSequencingBinaryStructuredDecisionProblem]
    using textbookMap_correct I

noncomputable def knapsackToJobSequencingBinaryStructuredTMBackedKarpReduction :
    TMBackedCostedReduction
      knapsackBinaryStructuredDecisionProblem
      jobSequencingBinaryStructuredDecisionProblem :=
  TMBackedCostedReduction.ofTMBackedCostedMap
    knapsackToJobSequencingBinaryStructuredTMBackedMap
    (by
      intro I
      exact knapsackToJobSequencingBinaryStructuredTMMap_correct I)

/-- Binary-numeric structured Knapsack-to-Job-Sequencing reduction. -/
noncomputable def knapsackToJobSequencingBinaryStructuredKarpReduction :
    KarpReductionM CostedPolyTimeModel
      knapsackBinaryStructuredDecisionProblem
      jobSequencingBinaryStructuredDecisionProblem :=
  knapsackToJobSequencingBinaryStructuredTMBackedKarpReduction.toCostedKarpReduction

noncomputable def knapsackToJobSequencingBinaryStructuredTMKarpReduction :
    TMKarpReduction
      knapsackBinaryStructuredDecisionProblem
      jobSequencingBinaryStructuredDecisionProblem :=
  knapsackToJobSequencingBinaryStructuredTMBackedKarpReduction.toTMKarpReduction

end JobSequencing
end Karp21
end ComplexityReduction
