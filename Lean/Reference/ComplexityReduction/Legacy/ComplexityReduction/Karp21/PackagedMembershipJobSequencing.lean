/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.JobSequencingStructuredTM
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipSetSystemBounds
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.ThreeSATFiniteVerifierTM
import Mathlib.Tactic

/-! Direct standard-TM verifier core for faithful structured Job Sequencing. -/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics

namespace JobSequencing

abbrev jobSequencingCertificateEncodedType : EncodedType :=
  SAT.finiteAssignmentCertEncodedType

abbrev JobSequencingCertificate := List Bool

/-! ### Structured Job-Sequencing projection -/

def jobSequencingInputToTuple (I : JobSequencingInput) :
    jobSequencingTupleStructuredEncodedType.Carrier :=
  (I.jobs, I.targetProfit)

theorem jobSequencingInputToTuple_encode (I : JobSequencingInput) :
    jobSequencingTupleStructuredEncodedType.encode (jobSequencingInputToTuple I) =
      jobSequencingStructuredEncodedType.encode I := by
  rfl

noncomputable def jobSequencingInputToTupleTMBackedMap :
    TMBackedCostedMap
      jobSequencingStructuredEncodedType
      jobSequencingTupleStructuredEncodedType
      jobSequencingInputToTuple :=
  TMBackedCostedMap.ofEncodingEquiv
    jobSequencingStructuredEncodedType
    jobSequencingTupleStructuredEncodedType
    jobSequencingInputToTuple
    (Equiv.refl jobSequencingTupleStructuredEncodedType.Symbol)
    (by
      intro I
      change jobSequencingTupleStructuredEncodedType.encode (jobSequencingInputToTuple I) =
        (jobSequencingStructuredEncodedType.encode I).map id
      simp [jobSequencingInputToTuple_encode])

def jobToTupleForMembership (j : Job) : jobTupleStructuredEncodedType.Carrier :=
  (j.processingTime, (j.deadline, j.profit))

theorem jobToTupleForMembership_encode (j : Job) :
    jobTupleStructuredEncodedType.encode (jobToTupleForMembership j) =
      jobStructuredEncodedType.encode j := by
  rfl

noncomputable def jobToTupleForMembershipTMBackedMap :
    TMBackedCostedMap
      jobStructuredEncodedType
      jobTupleStructuredEncodedType
      jobToTupleForMembership :=
  TMBackedCostedMap.ofEncodingEquiv
    jobStructuredEncodedType
    jobTupleStructuredEncodedType
    jobToTupleForMembership
    (Equiv.refl jobTupleStructuredEncodedType.Symbol)
    (by
      intro j
      change jobTupleStructuredEncodedType.encode (jobToTupleForMembership j) =
        (jobStructuredEncodedType.encode j).map id
      simp [jobToTupleForMembership_encode])

/-! ### Semantic certificate decoding -/

def selectedJobsFrom : List Job → JobSequencingCertificate → Nat → List Job
  | [], _, _ => []
  | j :: jobs, bits, idx =>
      if SAT.lookupBoolAt (bits, idx) then
        j :: selectedJobsFrom jobs bits (idx + 1)
      else
        selectedJobsFrom jobs bits (idx + 1)

@[simp] theorem selectedJobsFrom_length_le
    (jobs : List Job) (bits : JobSequencingCertificate) (idx : Nat) :
    (selectedJobsFrom jobs bits idx).length ≤ jobs.length := by
  induction jobs generalizing idx with
  | nil =>
      simp [selectedJobsFrom]
  | cons j jobs ih =>
      by_cases h : SAT.lookupBoolAt (bits, idx)
      · simp [selectedJobsFrom, h, ih]
      · simpa [selectedJobsFrom, h] using (ih (idx + 1)).trans (Nat.le_succ _)

theorem selectedJobsFrom_sublist
    (jobs : List Job) (bits : JobSequencingCertificate) (idx : Nat) :
    List.Sublist (selectedJobsFrom jobs bits idx) jobs := by
  induction jobs generalizing idx with
  | nil =>
      simp [selectedJobsFrom]
  | cons j jobs ih =>
      by_cases h : SAT.lookupBoolAt (bits, idx)
      · simpa [selectedJobsFrom, h] using (ih (idx + 1)).cons₂ j
      · simpa [selectedJobsFrom, h] using (ih (idx + 1)).cons j

@[simp] theorem jobSeqLookup_cons_zero (b : Bool) (bits : List Bool) :
    SAT.lookupBoolAt (b :: bits, 0) = b := by
  simp [SAT.lookupBoolAt_eq_getD]

@[simp] theorem jobSeqLookup_cons_succ
    (b : Bool) (bits : List Bool) (idx : Nat) :
    SAT.lookupBoolAt (b :: bits, idx + 1) = SAT.lookupBoolAt (bits, idx) := by
  simp [SAT.lookupBoolAt_eq_getD]

theorem selectedJobsFrom_cons_succ
    (jobs : List Job) (b : Bool) (bits : List Bool) (idx : Nat) :
    selectedJobsFrom jobs (b :: bits) (idx + 1) =
      selectedJobsFrom jobs bits idx := by
  induction jobs generalizing idx with
  | nil =>
      simp [selectedJobsFrom]
  | cons j jobs ih =>
      by_cases h : SAT.lookupBoolAt (bits, idx)
      · simp [selectedJobsFrom, h, ih]
      · simp [selectedJobsFrom, h, ih]

theorem exists_jobSequencingCertificate_of_sublist
    {selected jobs : List Job} (hSub : List.Sublist selected jobs) :
    ∃ bits : JobSequencingCertificate,
      bits.length = jobs.length ∧ selectedJobsFrom jobs bits 0 = selected := by
  induction hSub with
  | slnil =>
      exact ⟨[], rfl, by simp [selectedJobsFrom]⟩
  | cons job hSub ih =>
      rcases ih with ⟨bits, hLen, hSelected⟩
      refine ⟨false :: bits, by simp [hLen], ?_⟩
      simp [selectedJobsFrom, selectedJobsFrom_cons_succ, hSelected]
  | cons₂ job hSub ih =>
      rcases ih with ⟨bits, hLen, hSelected⟩
      refine ⟨true :: bits, by simp [hLen], ?_⟩
      simp [selectedJobsFrom, selectedJobsFrom_cons_succ, hSelected]

def selectedProcessingFrom : List Job → JobSequencingCertificate → Nat → Nat
  | [], _, _ => 0
  | j :: jobs, bits, idx =>
      (if SAT.lookupBoolAt (bits, idx) then j.processingTime else 0) +
        selectedProcessingFrom jobs bits (idx + 1)

def selectedProfitFrom : List Job → JobSequencingCertificate → Nat → Nat
  | [], _, _ => 0
  | j :: jobs, bits, idx =>
      (if SAT.lookupBoolAt (bits, idx) then j.profit else 0) +
        selectedProfitFrom jobs bits (idx + 1)

theorem selectedProcessingFrom_eq_totalProcessingTime
    (jobs : List Job) (bits : JobSequencingCertificate) (idx : Nat) :
    selectedProcessingFrom jobs bits idx =
      totalProcessingTime (selectedJobsFrom jobs bits idx) := by
  induction jobs generalizing idx with
  | nil =>
      simp [selectedProcessingFrom, selectedJobsFrom, totalProcessingTime]
  | cons j jobs ih =>
      by_cases h : SAT.lookupBoolAt (bits, idx)
      · simp [selectedProcessingFrom, selectedJobsFrom, totalProcessingTime, h, ih]
      · simp [selectedProcessingFrom, selectedJobsFrom, totalProcessingTime, h, ih]

theorem selectedProfitFrom_eq_totalProfit
    (jobs : List Job) (bits : JobSequencingCertificate) (idx : Nat) :
    selectedProfitFrom jobs bits idx =
      totalProfit (selectedJobsFrom jobs bits idx) := by
  induction jobs generalizing idx with
  | nil =>
      simp [selectedProfitFrom, selectedJobsFrom, totalProfit]
  | cons j jobs ih =>
      by_cases h : SAT.lookupBoolAt (bits, idx)
      · simp [selectedProfitFrom, selectedJobsFrom, totalProfit, h, ih]
      · simp [selectedProfitFrom, selectedJobsFrom, totalProfit, h, ih]

def scheduleOKFrom : List Job → JobSequencingCertificate → Nat → Nat → Bool
  | [], _, _, _ => true
  | j :: jobs, bits, idx, elapsed =>
      if SAT.lookupBoolAt (bits, idx) then
        let completion := elapsed + j.processingTime
        graphBoolAndPair
          (HittingSet.natLeBool (completion, j.deadline),
            scheduleOKFrom jobs bits (idx + 1) completion)
      else
        scheduleOKFrom jobs bits (idx + 1) elapsed

def FeasibleFrom
    (jobs : List Job) (bits : JobSequencingCertificate) (idx elapsed : Nat) : Prop :=
  ∀ pref j suffix,
    selectedJobsFrom jobs bits idx = pref ++ [j] ++ suffix →
      elapsed + totalProcessingTime (pref ++ [j]) ≤ j.deadline

theorem scheduleOKFrom_eq_true_iff_feasibleFrom
    (jobs : List Job) (bits : JobSequencingCertificate) (idx elapsed : Nat) :
    scheduleOKFrom jobs bits idx elapsed = true ↔
      FeasibleFrom jobs bits idx elapsed := by
  induction jobs generalizing idx elapsed with
  | nil =>
      constructor
      · intro _ pref j suffix h
        simp [selectedJobsFrom] at h
      · intro _h
        simp [scheduleOKFrom]
  | cons job jobs ih =>
      by_cases hBit : SAT.lookupBoolAt (bits, idx)
      · constructor
        · intro hOK pref j suffix hSel
          rcases (graphBoolAndPair_eq_true_iff _).1 (by
            simpa [scheduleOKFrom, hBit] using hOK) with ⟨hDeadline, hTailOK⟩
          have hTailFeasible := (ih (idx + 1) (elapsed + job.processingTime)).1 hTailOK
          simp [selectedJobsFrom, hBit] at hSel
          cases pref with
          | nil =>
              simp at hSel
              rcases hSel with ⟨hJob, _hSuffix⟩
              subst j
              exact (HittingSet.natLeBool_eq_true_iff _).1 hDeadline
          | cons first rest =>
              simp at hSel
              rcases hSel with ⟨hFirst, hTailEq⟩
              subst first
              have hTail :=
                hTailFeasible rest j suffix (by simpa using hTailEq)
              simpa [totalProcessingTime, Nat.add_assoc, Nat.add_left_comm,
                Nat.add_comm] using hTail
        · intro hFeasible
          have hAnd :
              graphBoolAndPair
                  (HittingSet.natLeBool (elapsed + job.processingTime, job.deadline),
                    scheduleOKFrom jobs bits (idx + 1) (elapsed + job.processingTime)) =
                true := by
            refine (graphBoolAndPair_eq_true_iff _).2 ⟨?_, ?_⟩
            · exact (HittingSet.natLeBool_eq_true_iff _).2
                (hFeasible [] job (selectedJobsFrom jobs bits (idx + 1)) (by
                  simp [selectedJobsFrom, hBit]))
            · exact (ih (idx + 1) (elapsed + job.processingTime)).2 (by
              intro pref j suffix hTail
              have hAll :=
                hFeasible (job :: pref) j suffix (by
                  simp [selectedJobsFrom, hBit, hTail])
              simpa [totalProcessingTime, Nat.add_assoc, Nat.add_left_comm,
                Nat.add_comm] using hAll)
          simpa [scheduleOKFrom, hBit] using hAnd
      · constructor
        · intro hOK
          have hTail := (ih (idx + 1) elapsed).1 (by
            simpa [scheduleOKFrom, hBit] using hOK)
          intro pref j suffix hSel
          exact hTail pref j suffix (by simpa [selectedJobsFrom, hBit] using hSel)
        · intro hFeasible
          simpa [scheduleOKFrom, hBit] using (ih (idx + 1) elapsed).2 (by
            intro pref j suffix hTail
            exact hFeasible pref j suffix (by simpa [selectedJobsFrom, hBit] using hTail))

theorem feasibleFrom_zero_iff
    (jobs : List Job) (bits : JobSequencingCertificate) :
    FeasibleFrom jobs bits 0 0 ↔
      FeasibleJobSequence (selectedJobsFrom jobs bits 0) := by
  constructor
  · intro h pref j suffix hEq
    have h := h pref j suffix hEq
    simpa using h
  · intro h pref j suffix hEq
    simpa using h pref j suffix hEq

/-! ### Instruction-list runner for direct TM verification -/

def jobSeqFoldInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod jobSequencingCertificateEncodedType jobStructuredEncodedType)

def jobSeqFoldInstructionListEncodedType : EncodedType :=
  EncodedType.list jobSeqFoldInstructionEncodedType

def jobSeqFoldInputEncodedType : EncodedType :=
  EncodedType.prod jobListStructuredEncodedType jobSequencingCertificateEncodedType

def jobSeqFoldAccEncodedType : EncodedType :=
  EncodedType.prod jobSequencingCertificateEncodedType
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.nat
        (EncodedType.prod EncodedType.nat EncodedType.bool)))

abbrev JobSeqFoldInstruction :=
  Bool × (JobSequencingCertificate × Job)

abbrev JobSeqFoldAcc :=
  JobSequencingCertificate × (Nat × (Nat × (Nat × Bool)))

def jobSeqFoldInitInstruction
    (bits : JobSequencingCertificate) : JobSeqFoldInstruction :=
  (false, (bits, { processingTime := 0, deadline := 0, profit := 0 }))

def jobSeqFoldJobInstruction (job : Job) : JobSeqFoldInstruction :=
  (true, ([], job))

def jobSeqFoldInstructions
    (p : List Job × JobSequencingCertificate) :
    List JobSeqFoldInstruction :=
  jobSeqFoldInitInstruction p.2 :: p.1.map jobSeqFoldJobInstruction

def jobSeqFoldRunnerInit : JobSeqFoldAcc :=
  ([], (0, (0, (0, true))))

def jobSeqFoldStep
    (p : JobSeqFoldAcc × JobSeqFoldInstruction) :
    JobSeqFoldAcc :=
  if p.2.1 then
    let bits := p.1.1
    let idx := p.1.2.1
    let elapsed := p.1.2.2.1
    let profit := p.1.2.2.2.1
    let ok := p.1.2.2.2.2
    let job := p.2.2.2
    if SAT.lookupBoolAt (bits, idx) then
      let completion := elapsed + job.processingTime
      let profit' := profit + job.profit
      let ok' := graphBoolAndPair (ok, HittingSet.natLeBool (completion, job.deadline))
      (bits, (idx + 1, (completion, (profit', ok'))))
    else
      (bits, (idx + 1, (elapsed, (profit, ok))))
  else
    (p.2.2.1, (0, (0, (0, true))))

def jobSeqFoldFromInstructions
    (xs : List JobSeqFoldInstruction) : Nat × Bool :=
  let acc := xs.foldl (fun acc x => jobSeqFoldStep (acc, x)) jobSeqFoldRunnerInit
  (acc.2.2.2.1, acc.2.2.2.2)

def jobSeqCertificateResult
    (p : List Job × JobSequencingCertificate) : Nat × Bool :=
  jobSeqFoldFromInstructions (jobSeqFoldInstructions p)

theorem graphBoolAndPair_right_true (b : Bool) :
    graphBoolAndPair (b, true) = b := by
  cases b <;> rfl

theorem graphBoolAndPair_assoc (a b c : Bool) :
    graphBoolAndPair (graphBoolAndPair (a, b), c) =
      graphBoolAndPair (a, graphBoolAndPair (b, c)) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem jobSeqFoldElementInstructions_fold_eq
    (jobs : List Job) (bits : JobSequencingCertificate)
    (idx elapsed profit : Nat) (ok : Bool) :
    (jobs.map jobSeqFoldJobInstruction).foldl
        (fun acc instr => jobSeqFoldStep (acc, instr))
        (bits, (idx, (elapsed, (profit, ok)))) =
      (bits,
        (idx + jobs.length,
          (elapsed + selectedProcessingFrom jobs bits idx,
            (profit + selectedProfitFrom jobs bits idx,
              graphBoolAndPair (ok, scheduleOKFrom jobs bits idx elapsed))))) := by
  induction jobs generalizing idx elapsed profit ok with
  | nil =>
      simp [selectedProcessingFrom, selectedProfitFrom, scheduleOKFrom,
        graphBoolAndPair_right_true]
  | cons job jobs ih =>
      rw [List.map_cons, List.foldl_cons]
      by_cases hBit : SAT.lookupBoolAt (bits, idx)
      · have h :=
          ih (idx + 1) (elapsed + job.processingTime) (profit + job.profit)
          (graphBoolAndPair (ok,
            HittingSet.natLeBool (elapsed + job.processingTime, job.deadline)))
        simpa [jobSeqFoldJobInstruction, jobSeqFoldStep, hBit, selectedProcessingFrom,
          selectedProfitFrom, scheduleOKFrom, graphBoolAndPair_assoc,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
      · have h := ih (idx + 1) elapsed profit ok
        simpa [jobSeqFoldJobInstruction, jobSeqFoldStep, hBit, selectedProcessingFrom,
          selectedProfitFrom, scheduleOKFrom, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using h

theorem jobSeqCertificateResult_eq
    (jobs : List Job) (bits : JobSequencingCertificate) :
    jobSeqCertificateResult (jobs, bits) =
      (totalProfit (selectedJobsFrom jobs bits 0),
        scheduleOKFrom jobs bits 0 0) := by
  change
    jobSeqFoldFromInstructions
        (jobSeqFoldInitInstruction bits :: jobs.map jobSeqFoldJobInstruction) = _
  simp [jobSeqFoldFromInstructions, jobSeqFoldInitInstruction, jobSeqFoldStep,
    jobSeqFoldRunnerInit]
  have hFold :=
    jobSeqFoldElementInstructions_fold_eq jobs bits 0 0 0 true
  simp [selectedProcessingFrom_eq_totalProcessingTime,
    selectedProfitFrom_eq_totalProfit] at hFold
  simpa using congrArg (fun acc : JobSeqFoldAcc => (acc.2.2.2.1, acc.2.2.2.2)) hFold

def jobSequencingStructuredFiniteVerify
    (I : JobSequencingInput) (bits : JobSequencingCertificate) : Bool :=
  let result := jobSeqCertificateResult (I.jobs, bits)
  graphBoolAndPair
    (result.2, HittingSet.natLeBool (I.targetProfit, result.1))

theorem jobSequencingStructuredFiniteVerify_eq_true_iff
    (I : JobSequencingInput) (bits : JobSequencingCertificate) :
    jobSequencingStructuredFiniteVerify I bits = true ↔
      FeasibleJobSequence (selectedJobsFrom I.jobs bits 0) ∧
        I.targetProfit ≤ totalProfit (selectedJobsFrom I.jobs bits 0) := by
  rw [jobSequencingStructuredFiniteVerify, jobSeqCertificateResult_eq,
    graphBoolAndPair_eq_true_iff, HittingSet.natLeBool_eq_true_iff,
    scheduleOKFrom_eq_true_iff_feasibleFrom, feasibleFrom_zero_iff]

/-! ### Direct TM witnesses -/

theorem jobSeqFoldInitInstruction_tm_polytime :
    TMPolyTimeMap
      jobSequencingCertificateEncodedType
      jobSeqFoldInstructionEncodedType
      jobSeqFoldInitInstruction := by
  let X := jobSequencingCertificateEncodedType
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hBits : TMPolyTimeMap X jobSequencingCertificateEncodedType id :=
    TMPolyTimeMap.id X
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hZeroTail :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun _ : X.Carrier => ((0 : Nat), (0 : Nat))) :=
    TMPolyTimeMap.prod_mk hZero hZero
  have hJobTuple :
      TMPolyTimeMap X jobTupleStructuredEncodedType
        (fun _ : X.Carrier => ((0 : Nat), ((0 : Nat), (0 : Nat)))) :=
    TMPolyTimeMap.prod_mk hZero hZeroTail
  have hJob : TMPolyTimeMap X jobStructuredEncodedType
      (fun _ : X.Carrier => { processingTime := 0, deadline := 0, profit := 0 }) := by
    have hComp := TMPolyTimeMap.comp jobTupleToJobTMBackedMap.tm_polytime hJobTuple
    simpa [Function.comp, jobTupleToJob, X] using hComp
  have hPayload :
      TMPolyTimeMap X
        (EncodedType.prod jobSequencingCertificateEncodedType jobStructuredEncodedType)
        (fun bits : X.Carrier =>
          (bits, { processingTime := 0, deadline := 0, profit := 0 })) :=
    TMPolyTimeMap.prod_mk hBits hJob
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [jobSeqFoldInitInstruction, jobSeqFoldInstructionEncodedType, X] using hOut

theorem jobSeqFoldJobInstruction_tm_polytime :
    TMPolyTimeMap
      jobStructuredEncodedType
      jobSeqFoldInstructionEncodedType
      jobSeqFoldJobInstruction := by
  let X := jobStructuredEncodedType
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hBits : TMPolyTimeMap X jobSequencingCertificateEncodedType
      (fun _ : X.Carrier => ([] : List Bool)) :=
    TMPolyTimeMap.const X jobSequencingCertificateEncodedType []
  have hJob : TMPolyTimeMap X jobStructuredEncodedType id :=
    TMPolyTimeMap.id X
  have hPayload :
      TMPolyTimeMap X
        (EncodedType.prod jobSequencingCertificateEncodedType jobStructuredEncodedType)
        (fun job : X.Carrier => (([] : List Bool), job)) :=
    TMPolyTimeMap.prod_mk hBits hJob
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [jobSeqFoldJobInstruction, jobSeqFoldInstructionEncodedType, X] using hOut

theorem jobSeqFoldInstructions_tm_polytime :
    TMPolyTimeMap
      jobSeqFoldInputEncodedType
      jobSeqFoldInstructionListEncodedType
      jobSeqFoldInstructions := by
  let X := jobSeqFoldInputEncodedType
  have hJobs : TMPolyTimeMap X jobListStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, jobSeqFoldInputEncodedType] using
      TMPolyTimeMap.fst jobListStructuredEncodedType jobSequencingCertificateEncodedType
  have hBits : TMPolyTimeMap X jobSequencingCertificateEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X, jobSeqFoldInputEncodedType] using
      TMPolyTimeMap.snd jobListStructuredEncodedType jobSequencingCertificateEncodedType
  have hInit :
      TMPolyTimeMap X jobSeqFoldInstructionEncodedType
        (fun p : X.Carrier => jobSeqFoldInitInstruction p.2) := by
    have hComp := TMPolyTimeMap.comp jobSeqFoldInitInstruction_tm_polytime hBits
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X jobSeqFoldInstructionListEncodedType
        (fun p : X.Carrier => [jobSeqFoldInitInstruction p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton jobSeqFoldInstructionEncodedType) hInit
    simpa [Function.comp, jobSeqFoldInstructionListEncodedType, X] using hComp
  have hJobInstructions :
      TMPolyTimeMap X jobSeqFoldInstructionListEncodedType
        (fun p : X.Carrier => p.1.map jobSeqFoldJobInstruction) := by
    have hMap := TMPolyTimeMap.list_map jobSeqFoldJobInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hJobs
    simpa [Function.comp, jobSeqFoldInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod jobSeqFoldInstructionListEncodedType
          jobSeqFoldInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([jobSeqFoldInitInstruction p.2],
            p.1.map jobSeqFoldJobInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hJobInstructions
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append jobSeqFoldInstructionEncodedType) hAppendInput
  simpa [Function.comp, jobSeqFoldInstructions, jobSeqFoldInstructionListEncodedType, X]
    using hOut

theorem jobSeqFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod jobSeqFoldAccEncodedType jobSeqFoldInstructionEncodedType)
      jobSeqFoldAccEncodedType
      jobSeqFoldStep := by
  let X := EncodedType.prod jobSeqFoldAccEncodedType jobSeqFoldInstructionEncodedType
  let A := jobSeqFoldAccEncodedType
  let ProfitOk := EncodedType.prod EncodedType.nat EncodedType.bool
  let Tail := EncodedType.prod EncodedType.nat ProfitOk
  let Rest := EncodedType.prod EncodedType.nat Tail
  let Payload := EncodedType.prod jobSequencingCertificateEncodedType jobStructuredEncodedType
  let JobTail := EncodedType.prod EncodedType.nat EncodedType.nat
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X, A] using TMPolyTimeMap.fst A jobSeqFoldInstructionEncodedType
  have hInstr : TMPolyTimeMap X jobSeqFoldInstructionEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd A jobSeqFoldInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, jobSeqFoldInstructionEncodedType, Payload, X] using hComp
  have hPayload : TMPolyTimeMap X Payload (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, jobSeqFoldInstructionEncodedType, Payload, X] using hComp
  have hAccBits : TMPolyTimeMap X jobSequencingCertificateEncodedType
      (fun p : X.Carrier => p.1.1) := by
    have hFst := TMPolyTimeMap.fst jobSequencingCertificateEncodedType Rest
    have hComp := TMPolyTimeMap.comp hFst hAcc
    simpa [Function.comp, A, Rest, X] using hComp
  have hAccRest : TMPolyTimeMap X Rest (fun p : X.Carrier => p.1.2) := by
    have hSnd := TMPolyTimeMap.snd jobSequencingCertificateEncodedType Rest
    have hComp := TMPolyTimeMap.comp hSnd hAcc
    simpa [Function.comp, A, Rest, X] using hComp
  have hAccIdx : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.1.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat Tail
    have hComp := TMPolyTimeMap.comp hFst hAccRest
    simpa [Function.comp, Rest, Tail, X] using hComp
  have hAccTail : TMPolyTimeMap X Tail
      (fun p : X.Carrier => p.1.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat Tail
    have hComp := TMPolyTimeMap.comp hSnd hAccRest
    simpa [Function.comp, Rest, Tail, X] using hComp
  have hElapsed : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.1.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat ProfitOk
    have hComp := TMPolyTimeMap.comp hFst hAccTail
    simpa [Function.comp, Tail, ProfitOk, X] using hComp
  have hProfitOk : TMPolyTimeMap X ProfitOk
      (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat ProfitOk
    have hComp := TMPolyTimeMap.comp hSnd hAccTail
    simpa [Function.comp, Tail, ProfitOk, X] using hComp
  have hProfit : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.1.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hProfitOk
    simpa [Function.comp, ProfitOk, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => p.1.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hProfitOk
    simpa [Function.comp, ProfitOk, X] using hComp
  have hPayloadBits : TMPolyTimeMap X jobSequencingCertificateEncodedType
      (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst jobSequencingCertificateEncodedType
      jobStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPayloadJob : TMPolyTimeMap X jobStructuredEncodedType
      (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd jobSequencingCertificateEncodedType
      jobStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hJobTuple : TMPolyTimeMap X jobTupleStructuredEncodedType
      (fun p : X.Carrier => jobToTupleForMembership p.2.2.2) := by
    have hComp := TMPolyTimeMap.comp jobToTupleForMembershipTMBackedMap.tm_polytime
      hPayloadJob
    simpa [Function.comp, X] using hComp
  have hProcessing : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.2.2.processingTime) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat JobTail
    have hComp := TMPolyTimeMap.comp hFst hJobTuple
    simpa [Function.comp, jobToTupleForMembership, jobTupleStructuredEncodedType,
      JobTail, X] using hComp
  have hJobTail : TMPolyTimeMap X JobTail
      (fun p : X.Carrier => (p.2.2.2.deadline, p.2.2.2.profit)) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat JobTail
    have hComp := TMPolyTimeMap.comp hSnd hJobTuple
    simpa [Function.comp, jobToTupleForMembership, jobTupleStructuredEncodedType,
      JobTail, X] using hComp
  have hDeadline : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.2.2.deadline) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hJobTail
    simpa [Function.comp, JobTail, X] using hComp
  have hJobProfit : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.2.2.2.profit) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hJobTail
    simpa [Function.comp, JobTail, X] using hComp
  have hLookupInput :
      TMPolyTimeMap X SAT.lookupBoolInputEncodedType
        (fun p : X.Carrier => (p.1.1, p.1.2.1)) :=
    TMPolyTimeMap.prod_mk hAccBits hAccIdx
  have hLookup : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => SAT.lookupBoolAt (p.1.1, p.1.2.1)) := by
    have hComp := TMPolyTimeMap.comp SAT.lookupBoolAt_tm_polytime hLookupInput
    simpa [Function.comp, SAT.lookupBoolInputEncodedType] using hComp
  have hOne : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (1 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (1 : Nat)
  have hNextIdxInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : X.Carrier => (p.1.2.1, (1 : Nat))) :=
    TMPolyTimeMap.prod_mk hAccIdx hOne
  have hNextIdx : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => (show Nat from p.1.2.1) + 1) := by
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hNextIdxInput
    simpa [Function.comp, natAddInputEncodedType] using hComp
  have hCompletionInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : X.Carrier => (p.1.2.2.1, p.2.2.2.processingTime)) :=
    TMPolyTimeMap.prod_mk hElapsed hProcessing
  have hCompletion : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier =>
        (show Nat from p.1.2.2.1) + p.2.2.2.processingTime) := by
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hCompletionInput
    simpa [Function.comp, natAddInputEncodedType] using hComp
  have hProfitAddInput :
      TMPolyTimeMap X natAddInputEncodedType
        (fun p : X.Carrier => (p.1.2.2.2.1, p.2.2.2.profit)) :=
    TMPolyTimeMap.prod_mk hProfit hJobProfit
  have hProfitAdd : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier =>
        (show Nat from p.1.2.2.2.1) + p.2.2.2.profit) := by
    have hComp := TMPolyTimeMap.comp natAdd_tm_polytime hProfitAddInput
    simpa [Function.comp, natAddInputEncodedType] using hComp
  have hDeadlineInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
        (fun p : X.Carrier =>
          ((show Nat from p.1.2.2.1) + p.2.2.2.processingTime,
            p.2.2.2.deadline)) :=
    TMPolyTimeMap.prod_mk hCompletion hDeadline
  have hDeadlineOK : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        HittingSet.natLeBool
          ((show Nat from p.1.2.2.1) + p.2.2.2.processingTime,
            p.2.2.2.deadline)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.natLeBool_tm_polytime hDeadlineInput
    simpa [Function.comp] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (p.1.2.2.2.2,
            HittingSet.natLeBool
              ((show Nat from p.1.2.2.1) + p.2.2.2.processingTime,
                p.2.2.2.deadline))) :=
    TMPolyTimeMap.prod_mk hOk hDeadlineOK
  have hAnd : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (p.1.2.2.2.2,
            HittingSet.natLeBool
              ((show Nat from p.1.2.2.1) + p.2.2.2.processingTime,
                p.2.2.2.deadline))) := by
    have hComp := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
    simpa [Function.comp] using hComp
  have hSelectedProfitOk :
      TMPolyTimeMap X ProfitOk
        (fun p : X.Carrier =>
          ((show Nat from p.1.2.2.2.1) + p.2.2.2.profit,
            graphBoolAndPair
              (p.1.2.2.2.2,
                HittingSet.natLeBool
                  ((show Nat from p.1.2.2.1) + p.2.2.2.processingTime,
                    p.2.2.2.deadline)))) :=
    TMPolyTimeMap.prod_mk hProfitAdd hAnd
  have hSelectedTail :
      TMPolyTimeMap X Tail
        (fun p : X.Carrier =>
          ((show Nat from p.1.2.2.1) + p.2.2.2.processingTime,
            ((show Nat from p.1.2.2.2.1) + p.2.2.2.profit,
              graphBoolAndPair
                (p.1.2.2.2.2,
                  HittingSet.natLeBool
                    ((show Nat from p.1.2.2.1) + p.2.2.2.processingTime,
                      p.2.2.2.deadline))))) :=
    TMPolyTimeMap.prod_mk hCompletion hSelectedProfitOk
  have hSelectedRest :
      TMPolyTimeMap X Rest
        (fun p : X.Carrier =>
          ((show Nat from p.1.2.1) + 1,
            ((show Nat from p.1.2.2.1) + p.2.2.2.processingTime,
              ((show Nat from p.1.2.2.2.1) + p.2.2.2.profit,
                graphBoolAndPair
                  (p.1.2.2.2.2,
                    HittingSet.natLeBool
                      ((show Nat from p.1.2.2.1) + p.2.2.2.processingTime,
                        p.2.2.2.deadline)))))) :=
    TMPolyTimeMap.prod_mk hNextIdx hSelectedTail
  have hUnselectedRest :
      TMPolyTimeMap X Rest
        (fun p : X.Carrier =>
          ((show Nat from p.1.2.1) + 1, p.1.2.2)) :=
    TMPolyTimeMap.prod_mk hNextIdx hAccTail
  have hTrueSelectedBranch : TMPolyTimeMap X A
      (fun p : X.Carrier =>
        (p.1.1,
          ((show Nat from p.1.2.1) + 1,
            ((show Nat from p.1.2.2.1) + p.2.2.2.processingTime,
              ((show Nat from p.1.2.2.2.1) + p.2.2.2.profit,
                graphBoolAndPair
                  (p.1.2.2.2.2,
                    HittingSet.natLeBool
                      ((show Nat from p.1.2.2.1) + p.2.2.2.processingTime,
                        p.2.2.2.deadline))))))) :=
    TMPolyTimeMap.prod_mk hAccBits hSelectedRest
  have hTrueUnselectedBranch : TMPolyTimeMap X A
      (fun p : X.Carrier =>
        (p.1.1, ((show Nat from p.1.2.1) + 1, p.1.2.2))) :=
    TMPolyTimeMap.prod_mk hAccBits hUnselectedRest
  have hInnerInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (SAT.lookupBoolAt (p.1.1, p.1.2.1), p)) :=
    TMPolyTimeMap.prod_mk hLookup (TMPolyTimeMap.id X)
  have hInnerBranch :=
    graphBoolProduct_dispatch_tm_polytime X A
      (fFalse := fun p : X.Carrier =>
        (p.1.1, ((show Nat from p.1.2.1) + 1, p.1.2.2)))
      (fTrue := fun p : X.Carrier =>
        (p.1.1,
          ((show Nat from p.1.2.1) + 1,
            ((show Nat from p.1.2.2.1) + p.2.2.2.processingTime,
              ((show Nat from p.1.2.2.2.1) + p.2.2.2.profit,
                graphBoolAndPair
                  (p.1.2.2.2.2,
                    HittingSet.natLeBool
                      ((show Nat from p.1.2.2.1) + p.2.2.2.processingTime,
                        p.2.2.2.deadline)))))))
      hTrueUnselectedBranch hTrueSelectedBranch
  have hTrueBranch := TMPolyTimeMap.comp hInnerBranch hInnerInput
  have hZero : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hTrueConst : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hZeroProfitOk :
      TMPolyTimeMap X ProfitOk (fun _ : X.Carrier => ((0 : Nat), true)) :=
    TMPolyTimeMap.prod_mk hZero hTrueConst
  have hZeroTail :
      TMPolyTimeMap X Tail
        (fun _ : X.Carrier => ((0 : Nat), ((0 : Nat), true))) :=
    TMPolyTimeMap.prod_mk hZero hZeroProfitOk
  have hZeroRest :
      TMPolyTimeMap X Rest
        (fun _ : X.Carrier => ((0 : Nat), ((0 : Nat), ((0 : Nat), true)))) :=
    TMPolyTimeMap.prod_mk hZero hZeroTail
  have hFalseBranch : TMPolyTimeMap X A
      (fun p : X.Carrier =>
        (p.2.2.1, ((0 : Nat), ((0 : Nat), ((0 : Nat), true))))) :=
    TMPolyTimeMap.prod_mk hPayloadBits hZeroRest
  have hOuterInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool X)
        (fun p : X.Carrier => (p.2.1, p)) :=
    TMPolyTimeMap.prod_mk hTag (TMPolyTimeMap.id X)
  have hOuterBranch :=
    graphBoolProduct_dispatch_tm_polytime X A hFalseBranch hTrueBranch
  have hOut := TMPolyTimeMap.comp hOuterBranch hOuterInput
  convert hOut using 1
  funext p
  rcases p with ⟨⟨bits, idx, elapsed, profit, ok⟩, ⟨tag, payloadBits, job⟩⟩
  cases tag
  · simp [Function.comp, jobSeqFoldStep]
    rfl
  · by_cases h : SAT.lookupBoolAt (bits, idx)
    · simp [Function.comp, jobSeqFoldStep, h]
      rfl
    · simp [Function.comp, jobSeqFoldStep, h]
      rfl

theorem jobSeqFoldStep_growth
    (source : jobSeqFoldInstructionListEncodedType.Carrier)
    (acc : jobSeqFoldAccEncodedType.Carrier)
    (instr : jobSeqFoldInstructionEncodedType.Carrier)
    (hInstr :
      jobSeqFoldInstructionEncodedType.inputSize instr ≤
        jobSeqFoldInstructionListEncodedType.inputSize source) :
    jobSeqFoldAccEncodedType.inputSize (jobSeqFoldStep (acc, instr)) ≤
      jobSeqFoldAccEncodedType.inputSize acc +
        (Polynomial.C 2 * Polynomial.X + Polynomial.C 30).eval
          (jobSeqFoldInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨bits, idx, elapsed, profit, ok⟩
  rcases instr with ⟨tag, payloadBits, job⟩
  change Nat at idx elapsed profit
  cases tag
  · have hLocal :
        jobSeqFoldAccEncodedType.inputSize
            (payloadBits, ((0 : Nat), ((0 : Nat), ((0 : Nat), true)))) ≤
          jobSeqFoldInstructionEncodedType.inputSize (false, (payloadBits, job)) + 20 := by
      simp [jobSeqFoldAccEncodedType, jobSeqFoldInstructionEncodedType,
        EncodedType.inputSize_prod, EncodedType.inputSize_bool, EncodedType.inputSize_nat]
      omega
    have hBound := hLocal.trans (Nat.add_le_add_right hInstr 20)
    simpa [jobSeqFoldStep, Polynomial.eval_add, Polynomial.eval_mul] using
      hBound.trans (by omega)
  · have hProcessing :
        job.processingTime ≤
          jobSeqFoldInstructionEncodedType.inputSize (true, (payloadBits, job)) := by
      simp [jobSeqFoldInstructionEncodedType, jobStructured_inputSize_eq,
        EncodedType.inputSize_prod, EncodedType.inputSize_bool]
      omega
    have hProfit :
        job.profit ≤
          jobSeqFoldInstructionEncodedType.inputSize (true, (payloadBits, job)) := by
      simp [jobSeqFoldInstructionEncodedType, jobStructured_inputSize_eq,
        EncodedType.inputSize_prod, EncodedType.inputSize_bool]
      omega
    have hProcessingSource :
        job.processingTime ≤ jobSeqFoldInstructionListEncodedType.inputSize source :=
      hProcessing.trans hInstr
    have hProfitSource :
        job.profit ≤ jobSeqFoldInstructionListEncodedType.inputSize source :=
      hProfit.trans hInstr
    cases hBit : SAT.lookupBoolAt (bits, idx)
    · have hLocal :
          jobSeqFoldAccEncodedType.inputSize
              (bits, (idx + 1, (elapsed, (profit, ok)))) ≤
            jobSeqFoldAccEncodedType.inputSize (bits, (idx, (elapsed, (profit, ok)))) + 5 := by
        simp [jobSeqFoldAccEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat]
        omega
      simpa [jobSeqFoldStep, hBit, Polynomial.eval_add, Polynomial.eval_mul] using
        hLocal.trans (by omega)
    · have hLocal :
          jobSeqFoldAccEncodedType.inputSize
              (bits,
                (idx + 1,
                  (elapsed + job.processingTime,
                    (profit + job.profit,
                      graphBoolAndPair
                        (ok,
                          HittingSet.natLeBool
                            (elapsed + job.processingTime, job.deadline)))))) ≤
            jobSeqFoldAccEncodedType.inputSize (bits, (idx, (elapsed, (profit, ok)))) +
              job.processingTime + job.profit + 10 := by
        simp [jobSeqFoldAccEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat, EncodedType.inputSize_bool]
        omega
      simpa [jobSeqFoldStep, hBit, Polynomial.eval_add, Polynomial.eval_mul] using
        hLocal.trans (by omega)

theorem jobSeqFoldAcc_tm_polytime :
    TMPolyTimeMap jobSeqFoldInstructionListEncodedType jobSeqFoldAccEncodedType
      (fun xs : jobSeqFoldInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc x => jobSeqFoldStep (acc, x))
          jobSeqFoldRunnerInit) := by
  rcases jobSeqFoldStep_tm_polytime with ⟨hStep⟩
  let base : Polynomial Nat := Polynomial.C 20
  let grow : Polynomial Nat := Polynomial.C 2 * Polynomial.X + Polynomial.C 30
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      jobSeqFoldInstructionEncodedType jobSeqFoldAccEncodedType
      jobSeqFoldStep jobSeqFoldRunnerInit hStep base grow ?_ ?_
  · intro xs
    change jobSeqFoldAccEncodedType.inputSize jobSeqFoldRunnerInit ≤
      (Polynomial.C 20).eval
        (jobSeqFoldInstructionEncodedType.list.inputSize xs)
    have hInit : jobSeqFoldAccEncodedType.inputSize jobSeqFoldRunnerInit ≤ 20 := by
      native_decide
    simpa using hInit
  · intro source acc instr hInstr
    have hInstr' :
        jobSeqFoldInstructionEncodedType.inputSize instr ≤
          jobSeqFoldInstructionListEncodedType.inputSize source := by
      simpa [jobSeqFoldInstructionListEncodedType] using hInstr
    simpa [jobSeqFoldInstructionListEncodedType, grow] using
      jobSeqFoldStep_growth source acc instr hInstr'

theorem jobSeqFoldFromInstructions_tm_polytime :
    TMPolyTimeMap jobSeqFoldInstructionListEncodedType
      (EncodedType.prod EncodedType.nat EncodedType.bool)
      jobSeqFoldFromInstructions := by
  have hFold := jobSeqFoldAcc_tm_polytime
  let ProfitOk := EncodedType.prod EncodedType.nat EncodedType.bool
  let Tail := EncodedType.prod EncodedType.nat ProfitOk
  let Rest := EncodedType.prod EncodedType.nat Tail
  have hRest : TMPolyTimeMap jobSeqFoldAccEncodedType Rest
      (fun acc : JobSeqFoldAcc => acc.2) := by
    simpa [jobSeqFoldAccEncodedType, Rest] using
      TMPolyTimeMap.snd jobSequencingCertificateEncodedType Rest
  have hTail : TMPolyTimeMap Rest Tail (fun rest : Nat × Tail.Carrier => rest.2) := by
    simpa [Rest] using TMPolyTimeMap.snd EncodedType.nat Tail
  have hProfitOk : TMPolyTimeMap Tail ProfitOk
      (fun tail : Nat × ProfitOk.Carrier => tail.2) := by
    simpa [Tail] using TMPolyTimeMap.snd EncodedType.nat ProfitOk
  have hProjection := TMPolyTimeMap.comp hProfitOk (TMPolyTimeMap.comp hTail hRest)
  have hComp := TMPolyTimeMap.comp hProjection hFold
  simpa [Function.comp, jobSeqFoldFromInstructions, jobSeqFoldAccEncodedType,
    ProfitOk, Tail, Rest] using hComp

theorem jobSeqCertificateResult_tm_polytime :
    TMPolyTimeMap jobSeqFoldInputEncodedType
      (EncodedType.prod EncodedType.nat EncodedType.bool)
      jobSeqCertificateResult := by
  have hComp := TMPolyTimeMap.comp jobSeqFoldFromInstructions_tm_polytime
    jobSeqFoldInstructions_tm_polytime
  simpa [Function.comp, jobSeqCertificateResult] using hComp

theorem jobSequencingStructuredFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod jobSequencingStructuredEncodedType jobSequencingCertificateEncodedType)
      EncodedType.bool
      (fun p : JobSequencingInput × JobSequencingCertificate =>
        jobSequencingStructuredFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod jobSequencingStructuredEncodedType jobSequencingCertificateEncodedType
  have hInstance : TMPolyTimeMap X jobSequencingStructuredEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst jobSequencingStructuredEncodedType
      jobSequencingCertificateEncodedType
  have hBits : TMPolyTimeMap X jobSequencingCertificateEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd jobSequencingStructuredEncodedType
      jobSequencingCertificateEncodedType
  have hTuple : TMPolyTimeMap X jobSequencingTupleStructuredEncodedType
      (fun p : X.Carrier => jobSequencingInputToTuple p.1) := by
    have hComp := TMPolyTimeMap.comp jobSequencingInputToTupleTMBackedMap.tm_polytime
      hInstance
    simpa [Function.comp, X] using hComp
  have hJobs : TMPolyTimeMap X jobListStructuredEncodedType
      (fun p : X.Carrier => p.1.jobs) := by
    have hFst := TMPolyTimeMap.fst jobListStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hFst hTuple
    simpa [Function.comp, jobSequencingInputToTuple, jobSequencingTupleStructuredEncodedType,
      X] using hComp
  have hTarget : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => p.1.targetProfit) := by
    have hSnd := TMPolyTimeMap.snd jobListStructuredEncodedType EncodedType.nat
    have hComp := TMPolyTimeMap.comp hSnd hTuple
    simpa [Function.comp, jobSequencingInputToTuple, jobSequencingTupleStructuredEncodedType,
      X] using hComp
  have hResultInput : TMPolyTimeMap X jobSeqFoldInputEncodedType
      (fun p : X.Carrier => (p.1.jobs, p.2)) :=
    TMPolyTimeMap.prod_mk hJobs hBits
  have hResult : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.bool)
      (fun p : X.Carrier => jobSeqCertificateResult (p.1.jobs, p.2)) := by
    have hComp := TMPolyTimeMap.comp jobSeqCertificateResult_tm_polytime hResultInput
    simpa [Function.comp, jobSeqFoldInputEncodedType, X] using hComp
  have hProfit : TMPolyTimeMap X EncodedType.nat
      (fun p : X.Carrier => (jobSeqCertificateResult (p.1.jobs, p.2)).1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hResult
    simpa [Function.comp, X] using hComp
  have hOK : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => (jobSeqCertificateResult (p.1.jobs, p.2)).2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.nat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hResult
    simpa [Function.comp, X] using hComp
  have hLeInput : TMPolyTimeMap X (EncodedType.prod EncodedType.nat EncodedType.nat)
      (fun p : X.Carrier =>
        (p.1.targetProfit, (jobSeqCertificateResult (p.1.jobs, p.2)).1)) :=
    TMPolyTimeMap.prod_mk hTarget hProfit
  have hLe : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        HittingSet.natLeBool
          (p.1.targetProfit, (jobSeqCertificateResult (p.1.jobs, p.2)).1)) := by
    have hComp := TMPolyTimeMap.comp HittingSet.natLeBool_tm_polytime hLeInput
    simpa [Function.comp] using hComp
  have hAndInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        ((jobSeqCertificateResult (p.1.jobs, p.2)).2,
          HittingSet.natLeBool
            (p.1.targetProfit, (jobSeqCertificateResult (p.1.jobs, p.2)).1))) :=
    TMPolyTimeMap.prod_mk hOK hLe
  have hAnd := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
  simpa [Function.comp, jobSequencingStructuredFiniteVerify, X] using hAnd

theorem jobSequencingCertificate_inputSize_le_linear
    (I : JobSequencingInput) (bits : JobSequencingCertificate)
    (hLen : bits.length = I.jobs.length) :
    jobSequencingCertificateEncodedType.inputSize bits ≤
      jobSequencingStructuredEncodedType.inputSize I := by
  rw [SAT.boolList_inputSize_eq_two_mul_length, hLen,
    jobSequencingStructured_inputSize_eq, jobListStructured_inputSize_eq]
  omega

end JobSequencing

end Karp21
end ComplexityReduction
