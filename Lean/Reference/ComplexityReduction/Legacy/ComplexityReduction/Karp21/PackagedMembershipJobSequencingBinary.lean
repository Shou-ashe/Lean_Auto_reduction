/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipJobSequencingVerifier
import ComplexityReduction.Legacy.ComplexityReduction.Karp21.PackagedMembershipKnapsackBinary

/-!
Direct standard-TM verifier for faithful binary-structured Job Sequencing.

The semantic certificate is the same Boolean selection list used by the unary
structured verifier.  The machine witness below is separate: numeric fields are
read and accumulated through `binaryNat` arithmetic, so this does not rely on a
binary-to-unary encoding expansion.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics

namespace JobSequencing

/-! ### Binary projections -/

def jobSequencingBinaryInputToTuple (I : JobSequencingInput) :
    jobSequencingTupleBinaryStructuredEncodedType.Carrier :=
  (I.jobs, I.targetProfit)

theorem jobSequencingBinaryInputToTuple_encode (I : JobSequencingInput) :
    jobSequencingTupleBinaryStructuredEncodedType.encode
        (jobSequencingBinaryInputToTuple I) =
      jobSequencingBinaryStructuredEncodedType.encode I := by
  rfl

noncomputable def jobSequencingBinaryInputToTupleTMBackedMap :
    TMBackedCostedMap
      jobSequencingBinaryStructuredEncodedType
      jobSequencingTupleBinaryStructuredEncodedType
      jobSequencingBinaryInputToTuple :=
  TMBackedCostedMap.ofEncodingEquiv
    jobSequencingBinaryStructuredEncodedType
    jobSequencingTupleBinaryStructuredEncodedType
    jobSequencingBinaryInputToTuple
    (Equiv.refl jobSequencingTupleBinaryStructuredEncodedType.Symbol)
    (by
      intro I
      change jobSequencingTupleBinaryStructuredEncodedType.encode
          (jobSequencingBinaryInputToTuple I) =
        (jobSequencingBinaryStructuredEncodedType.encode I).map id
      simp [jobSequencingBinaryInputToTuple_encode])

def jobToBinaryTupleForMembership (j : Job) :
    jobTupleBinaryStructuredEncodedType.Carrier :=
  (j.processingTime, (j.deadline, j.profit))

theorem jobToBinaryTupleForMembership_encode (j : Job) :
    jobTupleBinaryStructuredEncodedType.encode (jobToBinaryTupleForMembership j) =
      jobBinaryStructuredEncodedType.encode j := by
  rfl

noncomputable def jobToBinaryTupleForMembershipTMBackedMap :
    TMBackedCostedMap
      jobBinaryStructuredEncodedType
      jobTupleBinaryStructuredEncodedType
      jobToBinaryTupleForMembership :=
  TMBackedCostedMap.ofEncodingEquiv
    jobBinaryStructuredEncodedType
    jobTupleBinaryStructuredEncodedType
    jobToBinaryTupleForMembership
    (Equiv.refl jobTupleBinaryStructuredEncodedType.Symbol)
    (by
      intro j
      change jobTupleBinaryStructuredEncodedType.encode
          (jobToBinaryTupleForMembership j) =
        (jobBinaryStructuredEncodedType.encode j).map id
      simp [jobToBinaryTupleForMembership_encode])

theorem binaryNatLeBool_eq_natLeBool (p : Nat × Nat) :
    Knapsack.binaryNatLeBool p = HittingSet.natLeBool p := by
  by_cases h : p.1 ≤ p.2
  · have hBinary := (Knapsack.binaryNatLeBool_eq_true_iff p).2 h
    have hUnary := (HittingSet.natLeBool_eq_true_iff p).2 h
    rw [hBinary, hUnary]
  · have hBinary : Knapsack.binaryNatLeBool p = false := by
      cases hb : Knapsack.binaryNatLeBool p
      · rfl
      · exact False.elim (h ((Knapsack.binaryNatLeBool_eq_true_iff p).1 hb))
    have hUnary : HittingSet.natLeBool p = false := by
      cases hu : HittingSet.natLeBool p
      · rfl
      · exact False.elim (h ((HittingSet.natLeBool_eq_true_iff p).1 hu))
    rw [hBinary, hUnary]

/-! ### Binary instruction-list runner -/

def jobSeqBinaryFoldInstructionEncodedType : EncodedType :=
  EncodedType.prod EncodedType.bool
    (EncodedType.prod jobSequencingCertificateEncodedType jobBinaryStructuredEncodedType)

def jobSeqBinaryFoldInstructionListEncodedType : EncodedType :=
  EncodedType.list jobSeqBinaryFoldInstructionEncodedType

def jobSeqBinaryFoldInputEncodedType : EncodedType :=
  EncodedType.prod jobListBinaryStructuredEncodedType jobSequencingCertificateEncodedType

def jobSeqBinaryFoldAccEncodedType : EncodedType :=
  EncodedType.prod jobSequencingCertificateEncodedType
    (EncodedType.prod EncodedType.nat
      (EncodedType.prod EncodedType.binaryNat
        (EncodedType.prod EncodedType.binaryNat EncodedType.bool)))

abbrev JobSeqBinaryFoldInstruction :=
  Bool × (JobSequencingCertificate × Job)

abbrev JobSeqBinaryFoldAcc :=
  JobSequencingCertificate × (Nat × (Nat × (Nat × Bool)))

def jobSeqBinaryFoldInitInstruction
    (bits : JobSequencingCertificate) : JobSeqBinaryFoldInstruction :=
  (false, (bits, { processingTime := 0, deadline := 0, profit := 0 }))

def jobSeqBinaryFoldJobInstruction (job : Job) : JobSeqBinaryFoldInstruction :=
  (true, ([], job))

def jobSeqBinaryFoldInstructions
    (p : List Job × JobSequencingCertificate) :
    List JobSeqBinaryFoldInstruction :=
  jobSeqBinaryFoldInitInstruction p.2 :: p.1.map jobSeqBinaryFoldJobInstruction

def jobSeqBinaryFoldRunnerInit : JobSeqBinaryFoldAcc :=
  ([], (0, (0, (0, true))))

def jobSeqBinaryFoldStep
    (p : JobSeqBinaryFoldAcc × JobSeqBinaryFoldInstruction) :
    JobSeqBinaryFoldAcc :=
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
      let ok' :=
        graphBoolAndPair (ok, Knapsack.binaryNatLeBool (completion, job.deadline))
      (bits, (idx + 1, (completion, (profit', ok'))))
    else
      (bits, (idx + 1, (elapsed, (profit, ok))))
  else
    (p.2.2.1, (0, (0, (0, true))))

def jobSeqBinaryFoldFromInstructions
    (xs : List JobSeqBinaryFoldInstruction) : Nat × Bool :=
  let acc := xs.foldl (fun acc x => jobSeqBinaryFoldStep (acc, x))
    jobSeqBinaryFoldRunnerInit
  (acc.2.2.2.1, acc.2.2.2.2)

def jobSeqBinaryCertificateResult
    (p : List Job × JobSequencingCertificate) : Nat × Bool :=
  jobSeqBinaryFoldFromInstructions (jobSeqBinaryFoldInstructions p)

theorem jobSeqBinaryFoldInstructions_eq
    (p : List Job × JobSequencingCertificate) :
    jobSeqBinaryFoldInstructions p = jobSeqFoldInstructions p := by
  rfl

theorem jobSeqBinaryFoldStep_eq_jobSeqFoldStep
    (p : JobSeqBinaryFoldAcc × JobSeqBinaryFoldInstruction) :
    jobSeqBinaryFoldStep p = jobSeqFoldStep p := by
  rcases p with ⟨⟨bits, idx, elapsed, profit, ok⟩, ⟨tag, payloadBits, job⟩⟩
  cases tag
  · rfl
  · by_cases h : SAT.lookupBoolAt (bits, idx)
    · simp [jobSeqBinaryFoldStep, jobSeqFoldStep, h, binaryNatLeBool_eq_natLeBool]
    · simp [jobSeqBinaryFoldStep, jobSeqFoldStep, h]

theorem jobSeqBinaryFoldFromInstructions_eq
    (xs : List JobSeqBinaryFoldInstruction) :
    jobSeqBinaryFoldFromInstructions xs = jobSeqFoldFromInstructions xs := by
  have hStep :
      (fun acc x => jobSeqBinaryFoldStep (acc, x)) =
        (fun acc x => jobSeqFoldStep (acc, x)) := by
    funext acc x
    exact jobSeqBinaryFoldStep_eq_jobSeqFoldStep (acc, x)
  simp [jobSeqBinaryFoldFromInstructions, jobSeqFoldFromInstructions,
    jobSeqBinaryFoldRunnerInit, jobSeqFoldRunnerInit, hStep]

theorem jobSeqBinaryCertificateResult_eq
    (p : List Job × JobSequencingCertificate) :
    jobSeqBinaryCertificateResult p = jobSeqCertificateResult p := by
  simp [jobSeqBinaryCertificateResult, jobSeqCertificateResult,
    jobSeqBinaryFoldInstructions_eq, jobSeqBinaryFoldFromInstructions_eq]

/-! ### Direct TM witnesses -/

theorem jobSeqBinaryFoldInitInstruction_tm_polytime :
    TMPolyTimeMap
      jobSequencingCertificateEncodedType
      jobSeqBinaryFoldInstructionEncodedType
      jobSeqBinaryFoldInitInstruction := by
  let X := jobSequencingCertificateEncodedType
  have hFalse : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => false) :=
    TMPolyTimeMap.const X EncodedType.bool false
  have hBits : TMPolyTimeMap X jobSequencingCertificateEncodedType id :=
    TMPolyTimeMap.id X
  have hJob : TMPolyTimeMap X jobBinaryStructuredEncodedType
      (fun _ : X.Carrier => { processingTime := 0, deadline := 0, profit := 0 }) :=
    TMPolyTimeMap.const X jobBinaryStructuredEncodedType
      { processingTime := 0, deadline := 0, profit := 0 }
  have hPayload :
      TMPolyTimeMap X
        (EncodedType.prod jobSequencingCertificateEncodedType jobBinaryStructuredEncodedType)
        (fun bits : X.Carrier =>
          (bits, { processingTime := 0, deadline := 0, profit := 0 })) :=
    TMPolyTimeMap.prod_mk hBits hJob
  have hOut := TMPolyTimeMap.prod_mk hFalse hPayload
  simpa [jobSeqBinaryFoldInitInstruction, jobSeqBinaryFoldInstructionEncodedType, X] using hOut

theorem jobSeqBinaryFoldJobInstruction_tm_polytime :
    TMPolyTimeMap
      jobBinaryStructuredEncodedType
      jobSeqBinaryFoldInstructionEncodedType
      jobSeqBinaryFoldJobInstruction := by
  let X := jobBinaryStructuredEncodedType
  have hTrue : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hBits : TMPolyTimeMap X jobSequencingCertificateEncodedType
      (fun _ : X.Carrier => ([] : List Bool)) :=
    TMPolyTimeMap.const X jobSequencingCertificateEncodedType []
  have hJob : TMPolyTimeMap X jobBinaryStructuredEncodedType id :=
    TMPolyTimeMap.id X
  have hPayload :
      TMPolyTimeMap X
        (EncodedType.prod jobSequencingCertificateEncodedType jobBinaryStructuredEncodedType)
        (fun job : X.Carrier => (([] : List Bool), job)) :=
    TMPolyTimeMap.prod_mk hBits hJob
  have hOut := TMPolyTimeMap.prod_mk hTrue hPayload
  simpa [jobSeqBinaryFoldJobInstruction, jobSeqBinaryFoldInstructionEncodedType, X] using hOut

theorem jobSeqBinaryFoldInstructions_tm_polytime :
    TMPolyTimeMap
      jobSeqBinaryFoldInputEncodedType
      jobSeqBinaryFoldInstructionListEncodedType
      jobSeqBinaryFoldInstructions := by
  let X := jobSeqBinaryFoldInputEncodedType
  have hJobs : TMPolyTimeMap X jobListBinaryStructuredEncodedType (fun p : X.Carrier => p.1) := by
    simpa [X, jobSeqBinaryFoldInputEncodedType] using
      TMPolyTimeMap.fst jobListBinaryStructuredEncodedType jobSequencingCertificateEncodedType
  have hBits : TMPolyTimeMap X jobSequencingCertificateEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X, jobSeqBinaryFoldInputEncodedType] using
      TMPolyTimeMap.snd jobListBinaryStructuredEncodedType jobSequencingCertificateEncodedType
  have hInit :
      TMPolyTimeMap X jobSeqBinaryFoldInstructionEncodedType
        (fun p : X.Carrier => jobSeqBinaryFoldInitInstruction p.2) := by
    have hComp := TMPolyTimeMap.comp jobSeqBinaryFoldInitInstruction_tm_polytime hBits
    simpa [Function.comp, X] using hComp
  have hInitSingleton :
      TMPolyTimeMap X jobSeqBinaryFoldInstructionListEncodedType
        (fun p : X.Carrier => [jobSeqBinaryFoldInitInstruction p.2]) := by
    have hComp := TMPolyTimeMap.comp
      (TMPolyTimeMap.list_singleton jobSeqBinaryFoldInstructionEncodedType) hInit
    simpa [Function.comp, jobSeqBinaryFoldInstructionListEncodedType, X] using hComp
  have hJobInstructions :
      TMPolyTimeMap X jobSeqBinaryFoldInstructionListEncodedType
        (fun p : X.Carrier => p.1.map jobSeqBinaryFoldJobInstruction) := by
    have hMap := TMPolyTimeMap.list_map jobSeqBinaryFoldJobInstruction_tm_polytime
    have hComp := TMPolyTimeMap.comp hMap hJobs
    simpa [Function.comp, jobSeqBinaryFoldInstructionListEncodedType, X] using hComp
  have hAppendInput :
      TMPolyTimeMap X
        (EncodedType.prod jobSeqBinaryFoldInstructionListEncodedType
          jobSeqBinaryFoldInstructionListEncodedType)
        (fun p : X.Carrier =>
          ([jobSeqBinaryFoldInitInstruction p.2],
            p.1.map jobSeqBinaryFoldJobInstruction)) :=
    TMPolyTimeMap.prod_mk hInitSingleton hJobInstructions
  have hOut := TMPolyTimeMap.comp
    (TMPolyTimeMap.list_append jobSeqBinaryFoldInstructionEncodedType) hAppendInput
  simpa [Function.comp, jobSeqBinaryFoldInstructions,
    jobSeqBinaryFoldInstructionListEncodedType, X] using hOut

theorem jobSeqBinaryFoldStep_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod jobSeqBinaryFoldAccEncodedType jobSeqBinaryFoldInstructionEncodedType)
      jobSeqBinaryFoldAccEncodedType
      jobSeqBinaryFoldStep := by
  let X := EncodedType.prod jobSeqBinaryFoldAccEncodedType jobSeqBinaryFoldInstructionEncodedType
  let A := jobSeqBinaryFoldAccEncodedType
  let ProfitOk := EncodedType.prod EncodedType.binaryNat EncodedType.bool
  let Tail := EncodedType.prod EncodedType.binaryNat ProfitOk
  let Rest := EncodedType.prod EncodedType.nat Tail
  let Payload := EncodedType.prod jobSequencingCertificateEncodedType jobBinaryStructuredEncodedType
  let JobTail := EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat
  have hAcc : TMPolyTimeMap X A (fun p : X.Carrier => p.1) := by
    simpa [X, A] using TMPolyTimeMap.fst A jobSeqBinaryFoldInstructionEncodedType
  have hInstr : TMPolyTimeMap X jobSeqBinaryFoldInstructionEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd A jobSeqBinaryFoldInstructionEncodedType
  have hTag : TMPolyTimeMap X EncodedType.bool (fun p : X.Carrier => p.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hFst hInstr
    simpa [Function.comp, jobSeqBinaryFoldInstructionEncodedType, Payload, X] using hComp
  have hPayload : TMPolyTimeMap X Payload (fun p : X.Carrier => p.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.bool Payload
    have hComp := TMPolyTimeMap.comp hSnd hInstr
    simpa [Function.comp, jobSeqBinaryFoldInstructionEncodedType, Payload, X] using hComp
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
  have hElapsed : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : X.Carrier => p.1.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat ProfitOk
    have hComp := TMPolyTimeMap.comp hFst hAccTail
    simpa [Function.comp, Tail, ProfitOk, X] using hComp
  have hProfitOk : TMPolyTimeMap X ProfitOk
      (fun p : X.Carrier => p.1.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat ProfitOk
    have hComp := TMPolyTimeMap.comp hSnd hAccTail
    simpa [Function.comp, Tail, ProfitOk, X] using hComp
  have hProfit : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : X.Carrier => p.1.2.2.2.1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hProfitOk
    simpa [Function.comp, ProfitOk, X] using hComp
  have hOk : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => p.1.2.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hProfitOk
    simpa [Function.comp, ProfitOk, X] using hComp
  have hPayloadBits : TMPolyTimeMap X jobSequencingCertificateEncodedType
      (fun p : X.Carrier => p.2.2.1) := by
    have hFst := TMPolyTimeMap.fst jobSequencingCertificateEncodedType
      jobBinaryStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hFst hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hPayloadJob : TMPolyTimeMap X jobBinaryStructuredEncodedType
      (fun p : X.Carrier => p.2.2.2) := by
    have hSnd := TMPolyTimeMap.snd jobSequencingCertificateEncodedType
      jobBinaryStructuredEncodedType
    have hComp := TMPolyTimeMap.comp hSnd hPayload
    simpa [Function.comp, Payload, X] using hComp
  have hJobTuple : TMPolyTimeMap X jobTupleBinaryStructuredEncodedType
      (fun p : X.Carrier => jobToBinaryTupleForMembership p.2.2.2) := by
    have hComp := TMPolyTimeMap.comp jobToBinaryTupleForMembershipTMBackedMap.tm_polytime
      hPayloadJob
    simpa [Function.comp, X] using hComp
  have hProcessing : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : X.Carrier => p.2.2.2.processingTime) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat JobTail
    have hComp := TMPolyTimeMap.comp hFst hJobTuple
    simpa [Function.comp, jobToBinaryTupleForMembership,
      jobTupleBinaryStructuredEncodedType, JobTail, X] using hComp
  have hJobTail : TMPolyTimeMap X JobTail
      (fun p : X.Carrier => (p.2.2.2.deadline, p.2.2.2.profit)) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat JobTail
    have hComp := TMPolyTimeMap.comp hSnd hJobTuple
    simpa [Function.comp, jobToBinaryTupleForMembership,
      jobTupleBinaryStructuredEncodedType, JobTail, X] using hComp
  have hDeadline : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : X.Carrier => p.2.2.2.deadline) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hJobTail
    simpa [Function.comp, JobTail, X] using hComp
  have hJobProfit : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : X.Carrier => p.2.2.2.profit) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.binaryNat
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
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : X.Carrier => (p.1.2.2.1, p.2.2.2.processingTime)) :=
    TMPolyTimeMap.prod_mk hElapsed hProcessing
  have hCompletion : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : X.Carrier =>
        (show Nat from p.1.2.2.1) + p.2.2.2.processingTime) := by
    have hComp := TMPolyTimeMap.comp Knapsack.binaryNatAdd_tm_polytime hCompletionInput
    simpa [Function.comp, X] using hComp
  have hProfitAddInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : X.Carrier => (p.1.2.2.2.1, p.2.2.2.profit)) :=
    TMPolyTimeMap.prod_mk hProfit hJobProfit
  have hProfitAdd : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : X.Carrier =>
        (show Nat from p.1.2.2.2.1) + p.2.2.2.profit) := by
    have hComp := TMPolyTimeMap.comp Knapsack.binaryNatAdd_tm_polytime hProfitAddInput
    simpa [Function.comp, X] using hComp
  have hDeadlineInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
        (fun p : X.Carrier =>
          ((show Nat from p.1.2.2.1) + p.2.2.2.processingTime,
            p.2.2.2.deadline)) :=
    TMPolyTimeMap.prod_mk hCompletion hDeadline
  have hDeadlineOK : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        Knapsack.binaryNatLeBool
          ((show Nat from p.1.2.2.1) + p.2.2.2.processingTime,
            p.2.2.2.deadline)) := by
    have hComp := TMPolyTimeMap.comp Knapsack.binaryNatLeBool_tm_polytime hDeadlineInput
    simpa [Function.comp] using hComp
  have hAndInput :
      TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
        (fun p : X.Carrier =>
          (p.1.2.2.2.2,
            Knapsack.binaryNatLeBool
              ((show Nat from p.1.2.2.1) + p.2.2.2.processingTime,
                p.2.2.2.deadline))) :=
    TMPolyTimeMap.prod_mk hOk hDeadlineOK
  have hAnd : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        graphBoolAndPair
          (p.1.2.2.2.2,
            Knapsack.binaryNatLeBool
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
                Knapsack.binaryNatLeBool
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
                  Knapsack.binaryNatLeBool
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
                    Knapsack.binaryNatLeBool
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
                    Knapsack.binaryNatLeBool
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
                    Knapsack.binaryNatLeBool
                      ((show Nat from p.1.2.2.1) + p.2.2.2.processingTime,
                        p.2.2.2.deadline)))))))
      hTrueUnselectedBranch hTrueSelectedBranch
  have hTrueBranch := TMPolyTimeMap.comp hInnerBranch hInnerInput
  have hZeroNat : TMPolyTimeMap X EncodedType.nat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.nat (0 : Nat)
  have hZeroBin : TMPolyTimeMap X EncodedType.binaryNat (fun _ : X.Carrier => (0 : Nat)) :=
    TMPolyTimeMap.const X EncodedType.binaryNat (0 : Nat)
  have hTrueConst : TMPolyTimeMap X EncodedType.bool (fun _ : X.Carrier => true) :=
    TMPolyTimeMap.const X EncodedType.bool true
  have hZeroProfitOk :
      TMPolyTimeMap X ProfitOk (fun _ : X.Carrier => ((0 : Nat), true)) :=
    TMPolyTimeMap.prod_mk hZeroBin hTrueConst
  have hZeroTail :
      TMPolyTimeMap X Tail
        (fun _ : X.Carrier => ((0 : Nat), ((0 : Nat), true))) :=
    TMPolyTimeMap.prod_mk hZeroBin hZeroProfitOk
  have hZeroRest :
      TMPolyTimeMap X Rest
        (fun _ : X.Carrier => ((0 : Nat), ((0 : Nat), ((0 : Nat), true)))) :=
    TMPolyTimeMap.prod_mk hZeroNat hZeroTail
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
  · simp [Function.comp, jobSeqBinaryFoldStep]
    rfl
  · by_cases h : SAT.lookupBoolAt (bits, idx)
    · simp [Function.comp, jobSeqBinaryFoldStep, h]
      rfl
    · simp [Function.comp, jobSeqBinaryFoldStep, h]
      rfl

theorem jobSeqBinaryFoldStep_growth
    (source : jobSeqBinaryFoldInstructionListEncodedType.Carrier)
    (acc : jobSeqBinaryFoldAccEncodedType.Carrier)
    (instr : jobSeqBinaryFoldInstructionEncodedType.Carrier)
    (hInstr :
      jobSeqBinaryFoldInstructionEncodedType.inputSize instr ≤
        jobSeqBinaryFoldInstructionListEncodedType.inputSize source) :
    jobSeqBinaryFoldAccEncodedType.inputSize (jobSeqBinaryFoldStep (acc, instr)) ≤
      jobSeqBinaryFoldAccEncodedType.inputSize acc +
        (Polynomial.C 10 * Polynomial.X + Polynomial.C 50).eval
          (jobSeqBinaryFoldInstructionListEncodedType.inputSize source) := by
  rcases acc with ⟨bits, idx, elapsed, profit, ok⟩
  rcases instr with ⟨tag, payloadBits, job⟩
  change Nat at idx elapsed profit
  cases tag
  · have hLocal :
        jobSeqBinaryFoldAccEncodedType.inputSize
            (payloadBits, ((0 : Nat), ((0 : Nat), ((0 : Nat), true)))) ≤
          jobSeqBinaryFoldInstructionEncodedType.inputSize
            (false, (payloadBits, job)) + 20 := by
      simp [jobSeqBinaryFoldAccEncodedType, jobSeqBinaryFoldInstructionEncodedType,
        jobBinaryStructured_inputSize_eq, EncodedType.inputSize_prod,
        EncodedType.inputSize_nat, EncodedType.inputSize_bool]
      omega
    have hBound := hLocal.trans (Nat.add_le_add_right hInstr 20)
    simpa [jobSeqBinaryFoldStep, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X] using hBound.trans (by omega)
  · have hProcessing :
        EncodedType.binaryNat.inputSize job.processingTime ≤
          jobSeqBinaryFoldInstructionEncodedType.inputSize (true, (payloadBits, job)) := by
      simp [jobSeqBinaryFoldInstructionEncodedType, jobBinaryStructured_inputSize_eq,
        EncodedType.inputSize_prod, EncodedType.inputSize_bool]
      omega
    have hProfit :
        EncodedType.binaryNat.inputSize job.profit ≤
          jobSeqBinaryFoldInstructionEncodedType.inputSize (true, (payloadBits, job)) := by
      simp [jobSeqBinaryFoldInstructionEncodedType, jobBinaryStructured_inputSize_eq,
        EncodedType.inputSize_prod, EncodedType.inputSize_bool]
      omega
    have hProcessingSource :
        EncodedType.binaryNat.inputSize job.processingTime ≤
          jobSeqBinaryFoldInstructionListEncodedType.inputSize source :=
      hProcessing.trans hInstr
    have hProfitSource :
        EncodedType.binaryNat.inputSize job.profit ≤
          jobSeqBinaryFoldInstructionListEncodedType.inputSize source :=
      hProfit.trans hInstr
    cases hBit : SAT.lookupBoolAt (bits, idx)
    · have hLocal :
          jobSeqBinaryFoldAccEncodedType.inputSize
              (bits, (idx + 1, (elapsed, (profit, ok)))) ≤
            jobSeqBinaryFoldAccEncodedType.inputSize
              (bits, (idx, (elapsed, (profit, ok)))) + 5 := by
        simp [jobSeqBinaryFoldAccEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat]
        omega
      simpa [jobSeqBinaryFoldStep, hBit, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X] using hLocal.trans (by omega)
    · have hAddElapsed := Knapsack.binaryNatAdd_inputSize_le elapsed job.processingTime
      have hAddProfit := Knapsack.binaryNatAdd_inputSize_le profit job.profit
      have hLocal :
          jobSeqBinaryFoldAccEncodedType.inputSize
              (bits,
                (idx + 1,
                  (elapsed + job.processingTime,
                    (profit + job.profit,
                      graphBoolAndPair
                        (ok,
                          Knapsack.binaryNatLeBool
                            (elapsed + job.processingTime, job.deadline)))))) ≤
            jobSeqBinaryFoldAccEncodedType.inputSize
              (bits, (idx, (elapsed, (profit, ok)))) +
              EncodedType.binaryNat.inputSize job.processingTime +
              EncodedType.binaryNat.inputSize job.profit + 10 := by
        simp [jobSeqBinaryFoldAccEncodedType, EncodedType.inputSize_prod,
          EncodedType.inputSize_nat, EncodedType.inputSize_bool] at hAddElapsed hAddProfit ⊢
        omega
      simpa [jobSeqBinaryFoldStep, hBit, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X] using hLocal.trans (by omega)

theorem jobSeqBinaryFoldAcc_tm_polytime :
    TMPolyTimeMap jobSeqBinaryFoldInstructionListEncodedType jobSeqBinaryFoldAccEncodedType
      (fun xs : jobSeqBinaryFoldInstructionListEncodedType.Carrier =>
        xs.foldl (fun acc x => jobSeqBinaryFoldStep (acc, x))
          jobSeqBinaryFoldRunnerInit) := by
  rcases jobSeqBinaryFoldStep_tm_polytime with ⟨hStep⟩
  refine
    TMPolyTimeMap.list_foldl_typed_growth_bounded
      jobSeqBinaryFoldInstructionEncodedType jobSeqBinaryFoldAccEncodedType
      jobSeqBinaryFoldStep jobSeqBinaryFoldRunnerInit hStep
      (Polynomial.C 20) (Polynomial.C 10 * Polynomial.X + Polynomial.C 50) ?_ ?_
  · intro xs
    change jobSeqBinaryFoldAccEncodedType.inputSize jobSeqBinaryFoldRunnerInit ≤
      (Polynomial.C 20).eval
        (jobSeqBinaryFoldInstructionEncodedType.list.inputSize xs)
    have hInit : jobSeqBinaryFoldAccEncodedType.inputSize jobSeqBinaryFoldRunnerInit ≤ 20 := by
      native_decide
    simpa using hInit
  · intro source acc instr hInstr
    have hInstr' :
        jobSeqBinaryFoldInstructionEncodedType.inputSize instr ≤
          jobSeqBinaryFoldInstructionListEncodedType.inputSize source := by
      simpa [jobSeqBinaryFoldInstructionListEncodedType] using hInstr
    simpa [jobSeqBinaryFoldInstructionListEncodedType] using
      jobSeqBinaryFoldStep_growth source acc instr hInstr'

theorem jobSeqBinaryFoldFromInstructions_tm_polytime :
    TMPolyTimeMap jobSeqBinaryFoldInstructionListEncodedType
      (EncodedType.prod EncodedType.binaryNat EncodedType.bool)
      jobSeqBinaryFoldFromInstructions := by
  have hFold := jobSeqBinaryFoldAcc_tm_polytime
  let ProfitOk := EncodedType.prod EncodedType.binaryNat EncodedType.bool
  let Tail := EncodedType.prod EncodedType.binaryNat ProfitOk
  let Rest := EncodedType.prod EncodedType.nat Tail
  have hRest : TMPolyTimeMap jobSeqBinaryFoldAccEncodedType Rest
      (fun acc : JobSeqBinaryFoldAcc => acc.2) := by
    simpa [jobSeqBinaryFoldAccEncodedType, Rest] using
      TMPolyTimeMap.snd jobSequencingCertificateEncodedType Rest
  have hTail : TMPolyTimeMap Rest Tail (fun rest : Nat × Tail.Carrier => rest.2) := by
    simpa [Rest] using TMPolyTimeMap.snd EncodedType.nat Tail
  have hProfitOk : TMPolyTimeMap Tail ProfitOk
      (fun tail : Nat × ProfitOk.Carrier => tail.2) := by
    simpa [Tail] using TMPolyTimeMap.snd EncodedType.binaryNat ProfitOk
  have hProjection := TMPolyTimeMap.comp hProfitOk (TMPolyTimeMap.comp hTail hRest)
  have hComp := TMPolyTimeMap.comp hProjection hFold
  simpa [Function.comp, jobSeqBinaryFoldFromInstructions,
    jobSeqBinaryFoldAccEncodedType, ProfitOk, Tail, Rest] using hComp

theorem jobSeqBinaryCertificateResult_tm_polytime :
    TMPolyTimeMap jobSeqBinaryFoldInputEncodedType
      (EncodedType.prod EncodedType.binaryNat EncodedType.bool)
      jobSeqBinaryCertificateResult := by
  have hComp := TMPolyTimeMap.comp jobSeqBinaryFoldFromInstructions_tm_polytime
    jobSeqBinaryFoldInstructions_tm_polytime
  simpa [Function.comp, jobSeqBinaryCertificateResult] using hComp

/-! ### Finite verifier -/

def jobSequencingBinaryFiniteVerify
    (I : JobSequencingInput) (bits : JobSequencingCertificate) : Bool :=
  let result := jobSeqBinaryCertificateResult (I.jobs, bits)
  graphBoolAndPair
    (result.2, Knapsack.binaryNatLeBool (I.targetProfit, result.1))

theorem jobSequencingBinaryFiniteVerify_eq_structured
    (I : JobSequencingInput) (bits : JobSequencingCertificate) :
    jobSequencingBinaryFiniteVerify I bits =
      jobSequencingStructuredFiniteVerify I bits := by
  simp [jobSequencingBinaryFiniteVerify, jobSequencingStructuredFiniteVerify,
    jobSeqBinaryCertificateResult_eq, binaryNatLeBool_eq_natLeBool]

theorem jobSequencingBinaryFiniteVerify_eq_true_iff
    (I : JobSequencingInput) (bits : JobSequencingCertificate) :
    jobSequencingBinaryFiniteVerify I bits = true ↔
      FeasibleJobSequence (selectedJobsFrom I.jobs bits 0) ∧
        I.targetProfit ≤ totalProfit (selectedJobsFrom I.jobs bits 0) := by
  rw [jobSequencingBinaryFiniteVerify_eq_structured,
    jobSequencingStructuredFiniteVerify_eq_true_iff]

theorem jobSequencingBinaryFiniteVerify_tm_polytime :
    TMPolyTimeMap
      (EncodedType.prod jobSequencingBinaryStructuredEncodedType
        jobSequencingCertificateEncodedType)
      EncodedType.bool
      (fun p : JobSequencingInput × JobSequencingCertificate =>
        jobSequencingBinaryFiniteVerify p.1 p.2) := by
  let X := EncodedType.prod jobSequencingBinaryStructuredEncodedType
    jobSequencingCertificateEncodedType
  have hInstance : TMPolyTimeMap X jobSequencingBinaryStructuredEncodedType
      (fun p : X.Carrier => p.1) := by
    simpa [X] using TMPolyTimeMap.fst jobSequencingBinaryStructuredEncodedType
      jobSequencingCertificateEncodedType
  have hBits : TMPolyTimeMap X jobSequencingCertificateEncodedType
      (fun p : X.Carrier => p.2) := by
    simpa [X] using TMPolyTimeMap.snd jobSequencingBinaryStructuredEncodedType
      jobSequencingCertificateEncodedType
  have hTuple : TMPolyTimeMap X jobSequencingTupleBinaryStructuredEncodedType
      (fun p : X.Carrier => jobSequencingBinaryInputToTuple p.1) := by
    have hComp := TMPolyTimeMap.comp jobSequencingBinaryInputToTupleTMBackedMap.tm_polytime
      hInstance
    simpa [Function.comp, X] using hComp
  have hJobs : TMPolyTimeMap X jobListBinaryStructuredEncodedType
      (fun p : X.Carrier => p.1.jobs) := by
    have hFst := TMPolyTimeMap.fst jobListBinaryStructuredEncodedType EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hFst hTuple
    simpa [Function.comp, jobSequencingBinaryInputToTuple,
      jobSequencingTupleBinaryStructuredEncodedType, X] using hComp
  have hTarget : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : X.Carrier => p.1.targetProfit) := by
    have hSnd := TMPolyTimeMap.snd jobListBinaryStructuredEncodedType EncodedType.binaryNat
    have hComp := TMPolyTimeMap.comp hSnd hTuple
    simpa [Function.comp, jobSequencingBinaryInputToTuple,
      jobSequencingTupleBinaryStructuredEncodedType, X] using hComp
  have hResultInput : TMPolyTimeMap X jobSeqBinaryFoldInputEncodedType
      (fun p : X.Carrier => (p.1.jobs, p.2)) :=
    TMPolyTimeMap.prod_mk hJobs hBits
  have hResult : TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.bool)
      (fun p : X.Carrier => jobSeqBinaryCertificateResult (p.1.jobs, p.2)) := by
    have hComp := TMPolyTimeMap.comp jobSeqBinaryCertificateResult_tm_polytime hResultInput
    simpa [Function.comp, jobSeqBinaryFoldInputEncodedType, X] using hComp
  have hProfit : TMPolyTimeMap X EncodedType.binaryNat
      (fun p : X.Carrier => (jobSeqBinaryCertificateResult (p.1.jobs, p.2)).1) := by
    have hFst := TMPolyTimeMap.fst EncodedType.binaryNat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hFst hResult
    simpa [Function.comp, X] using hComp
  have hOK : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier => (jobSeqBinaryCertificateResult (p.1.jobs, p.2)).2) := by
    have hSnd := TMPolyTimeMap.snd EncodedType.binaryNat EncodedType.bool
    have hComp := TMPolyTimeMap.comp hSnd hResult
    simpa [Function.comp, X] using hComp
  have hLeInput : TMPolyTimeMap X (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)
      (fun p : X.Carrier =>
        (p.1.targetProfit, (jobSeqBinaryCertificateResult (p.1.jobs, p.2)).1)) :=
    TMPolyTimeMap.prod_mk hTarget hProfit
  have hLe : TMPolyTimeMap X EncodedType.bool
      (fun p : X.Carrier =>
        Knapsack.binaryNatLeBool
          (p.1.targetProfit, (jobSeqBinaryCertificateResult (p.1.jobs, p.2)).1)) := by
    have hComp := TMPolyTimeMap.comp Knapsack.binaryNatLeBool_tm_polytime hLeInput
    simpa [Function.comp] using hComp
  have hAndInput : TMPolyTimeMap X (EncodedType.prod EncodedType.bool EncodedType.bool)
      (fun p : X.Carrier =>
        ((jobSeqBinaryCertificateResult (p.1.jobs, p.2)).2,
          Knapsack.binaryNatLeBool
            (p.1.targetProfit, (jobSeqBinaryCertificateResult (p.1.jobs, p.2)).1))) :=
    TMPolyTimeMap.prod_mk hOK hLe
  have hAnd := TMPolyTimeMap.comp graphBoolAndPair_tm_polytime hAndInput
  simpa [Function.comp, jobSequencingBinaryFiniteVerify, X] using hAnd

theorem jobListBinary_inputSize_ge_two_mul_length (jobs : List Job) :
    2 * jobs.length ≤ jobListBinaryStructuredEncodedType.inputSize jobs := by
  induction jobs with
  | nil =>
      simp [jobListBinaryStructuredEncodedType]
  | cons job jobs ih =>
      change
        2 * (job :: jobs).length ≤
          (EncodedType.list jobBinaryStructuredEncodedType).inputSize (job :: jobs)
      rw [EncodedType.inputSize_list_cons]
      change
        2 * (job :: jobs).length ≤
          jobBinaryStructuredEncodedType.inputSize job + 1 +
            jobListBinaryStructuredEncodedType.inputSize jobs
      have hJobPos : 1 ≤ jobBinaryStructuredEncodedType.inputSize job := by
        rw [jobBinaryStructured_inputSize_eq]
        omega
      simp only [List.length_cons]
      omega

theorem jobSequencingBinaryCertificate_inputSize_le_linear
    (I : JobSequencingInput) (bits : JobSequencingCertificate)
    (hLen : bits.length = I.jobs.length) :
    jobSequencingCertificateEncodedType.inputSize bits ≤
      jobSequencingBinaryStructuredEncodedType.inputSize I := by
  have hJobs := jobListBinary_inputSize_ge_two_mul_length I.jobs
  calc
    jobSequencingCertificateEncodedType.inputSize bits = 2 * bits.length := by
      rw [SAT.boolList_inputSize_eq_two_mul_length]
    _ = 2 * I.jobs.length := by rw [hLen]
    _ ≤ jobListBinaryStructuredEncodedType.inputSize I.jobs := hJobs
    _ ≤ jobSequencingBinaryStructuredEncodedType.inputSize I := by
      change
        (jobListBinaryStructuredEncodedType.encode I.jobs).length ≤
          (jobSequencingTupleBinaryStructuredEncodedType.encode
            (I.jobs, I.targetProfit)).length
      simp [jobSequencingTupleBinaryStructuredEncodedType, EncodedType.prod]

end JobSequencing

/-- Direct finite-certificate TM verifier for faithful binary-structured Job Sequencing. -/
noncomputable def jobSequencingBinaryStructuredFiniteTMVerifier :
    TMVerifier jobSequencingBinaryStructuredDecisionProblem where
  Cert := JobSequencing.jobSequencingCertificateEncodedType
  verify := JobSequencing.jobSequencingBinaryFiniteVerify
  verifier_polytime := JobSequencing.jobSequencingBinaryFiniteVerify_tm_polytime
  cert_bound := by
    refine ⟨1, 1, 0, ?_⟩
    intro I hYes
    rcases hYes with ⟨selected, hSublist, hFeasible, hProfit⟩
    rcases JobSequencing.exists_jobSequencingCertificate_of_sublist hSublist with
      ⟨bits, hLen, hSelected⟩
    refine ⟨bits, ?_, ?_⟩
    · simpa using
        JobSequencing.jobSequencingBinaryCertificate_inputSize_le_linear I bits hLen
    · exact (JobSequencing.jobSequencingBinaryFiniteVerify_eq_true_iff I bits).2
        ⟨by simpa [hSelected] using hFeasible, by simpa [hSelected] using hProfit⟩
  sound := by
    intro I bits hVerify
    have hSem :=
      (JobSequencing.jobSequencingBinaryFiniteVerify_eq_true_iff I bits).1 hVerify
    refine ⟨JobSequencing.selectedJobsFrom I.jobs bits 0,
      JobSequencing.selectedJobsFrom_sublist I.jobs bits 0, hSem.1, hSem.2⟩

theorem jobSequencingBinaryStructured_TMInNP :
    TMInNP jobSequencingBinaryStructuredDecisionProblem :=
  TMInNP.intro jobSequencingBinaryStructuredFiniteTMVerifier

end Karp21
end ComplexityReduction
