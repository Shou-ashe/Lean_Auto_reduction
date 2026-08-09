/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Core

namespace ComplexityReduction
namespace Combinatorics

/-- Basic scheduling schema with processing times, machine count, and deadline. -/
structure SchedulingInput where
  machines : Nat
  processingTimes : List Nat
  deadline : Nat
  deriving Repr

def schedulingEncodedType : EncodedType :=
  EncodedType.raw SchedulingInput

def schedulingDecisionProblem (P : SchedulingInput → Prop) : EncodedDecisionProblem where
  Instance := schedulingEncodedType
  isYes := P

/-- A scheduled job with processing time, deadline, and profit. -/
structure Job where
  processingTime : Nat
  deadline : Nat
  profit : Nat
  deriving DecidableEq, Repr

/-- Karp-style job-sequencing instance. -/
structure JobSequencingInput where
  jobs : List Job
  targetProfit : Nat
  deriving Repr

def jobSequencingEncodedType : EncodedType :=
  EncodedType.raw JobSequencingInput

/-- Tuple-shaped finite-alphabet encoding for one job `(processingTime, deadline, profit)`. -/
def jobTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.nat
    (EncodedType.prod EncodedType.nat EncodedType.nat)

/-- Structured finite-alphabet encoding for one job. -/
def jobStructuredEncodedType : EncodedType where
  Carrier := Job
  Symbol := jobTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun j => jobTupleStructuredEncodedType.encode
    (j.processingTime, (j.deadline, j.profit))

/-- Structured finite-alphabet encoding for the job list. -/
def jobListStructuredEncodedType : EncodedType :=
  EncodedType.list jobStructuredEncodedType

/-- Tuple-shaped finite-alphabet encoding for Job Sequencing fields. -/
def jobSequencingTupleStructuredEncodedType : EncodedType :=
  EncodedType.prod jobListStructuredEncodedType EncodedType.nat

/-- Concrete finite-alphabet Job Sequencing encoding. -/
def jobSequencingStructuredEncodedType : EncodedType where
  Carrier := JobSequencingInput
  Symbol := jobSequencingTupleStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => jobSequencingTupleStructuredEncodedType.encode (I.jobs, I.targetProfit)

/-- Tuple-shaped binary-numeric finite-alphabet encoding for one job. -/
def jobTupleBinaryStructuredEncodedType : EncodedType :=
  EncodedType.prod EncodedType.binaryNat
    (EncodedType.prod EncodedType.binaryNat EncodedType.binaryNat)

/-- Binary-numeric finite-alphabet encoding for one job. -/
def jobBinaryStructuredEncodedType : EncodedType where
  Carrier := Job
  Symbol := jobTupleBinaryStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun j => jobTupleBinaryStructuredEncodedType.encode
    (j.processingTime, (j.deadline, j.profit))

/-- Binary-numeric finite-alphabet encoding for the job list. -/
def jobListBinaryStructuredEncodedType : EncodedType :=
  EncodedType.list jobBinaryStructuredEncodedType

/-- Tuple-shaped binary-numeric finite-alphabet encoding for Job Sequencing fields. -/
def jobSequencingTupleBinaryStructuredEncodedType : EncodedType :=
  EncodedType.prod jobListBinaryStructuredEncodedType EncodedType.binaryNat

/-- Concrete binary-numeric finite-alphabet Job Sequencing encoding. -/
def jobSequencingBinaryStructuredEncodedType : EncodedType where
  Carrier := JobSequencingInput
  Symbol := jobSequencingTupleBinaryStructuredEncodedType.Symbol
  finite_symbol := inferInstance
  encode := fun I => jobSequencingTupleBinaryStructuredEncodedType.encode
    (I.jobs, I.targetProfit)

theorem jobStructuredEncodedType_encode_injective :
    Function.Injective jobStructuredEncodedType.encode := by
  intro j k henc
  have htuple : (j.processingTime, (j.deadline, j.profit)) =
      (k.processingTime, (k.deadline, k.profit)) :=
    (EncodedType.prod_encode_injective
      EncodedType.nat_encode_injective
      (EncodedType.prod_encode_injective
        EncodedType.nat_encode_injective
        EncodedType.nat_encode_injective)) (by
          simpa [jobStructuredEncodedType] using henc)
  cases j
  cases k
  simp at htuple
  rcases htuple with ⟨rfl, rfl, rfl⟩
  rfl

theorem jobListStructuredEncodedType_encode_injective :
    Function.Injective jobListStructuredEncodedType.encode :=
  EncodedType.list_encode_injective jobStructuredEncodedType_encode_injective

theorem jobSequencingTupleStructuredEncodedType_encode_injective :
    Function.Injective jobSequencingTupleStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    jobListStructuredEncodedType_encode_injective
    EncodedType.nat_encode_injective

theorem jobSequencingStructuredEncodedType_encode_injective :
    Function.Injective jobSequencingStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.jobs, I.targetProfit) = (J.jobs, J.targetProfit) :=
    jobSequencingTupleStructuredEncodedType_encode_injective (by
      simpa [jobSequencingStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

theorem jobBinaryStructuredEncodedType_encode_injective :
    Function.Injective jobBinaryStructuredEncodedType.encode := by
  intro j k henc
  have htuple : (j.processingTime, (j.deadline, j.profit)) =
      (k.processingTime, (k.deadline, k.profit)) :=
    (EncodedType.prod_encode_injective
      EncodedType.binaryNat_encode_injective
      (EncodedType.prod_encode_injective
        EncodedType.binaryNat_encode_injective
        EncodedType.binaryNat_encode_injective)) (by
          simpa [jobBinaryStructuredEncodedType] using henc)
  cases j
  cases k
  simp at htuple
  rcases htuple with ⟨rfl, rfl, rfl⟩
  rfl

theorem jobListBinaryStructuredEncodedType_encode_injective :
    Function.Injective jobListBinaryStructuredEncodedType.encode :=
  EncodedType.list_encode_injective jobBinaryStructuredEncodedType_encode_injective

theorem jobSequencingTupleBinaryStructuredEncodedType_encode_injective :
    Function.Injective jobSequencingTupleBinaryStructuredEncodedType.encode :=
  EncodedType.prod_encode_injective
    jobListBinaryStructuredEncodedType_encode_injective
    EncodedType.binaryNat_encode_injective

theorem jobSequencingBinaryStructuredEncodedType_encode_injective :
    Function.Injective jobSequencingBinaryStructuredEncodedType.encode := by
  intro I J henc
  have htuple : (I.jobs, I.targetProfit) = (J.jobs, J.targetProfit) :=
    jobSequencingTupleBinaryStructuredEncodedType_encode_injective (by
      simpa [jobSequencingBinaryStructuredEncodedType] using henc)
  cases I
  cases J
  simp at htuple
  rcases htuple with ⟨rfl, rfl⟩
  rfl

/-- Total processing time of a selected list of jobs. -/
def totalProcessingTime (jobs : List Job) : Nat :=
  (jobs.map Job.processingTime).sum

/-- Total profit of a selected list of jobs. -/
def totalProfit (jobs : List Job) : Nat :=
  (jobs.map Job.profit).sum

/--
Semantic job-sequencing predicate.  A selected ordered sublist is feasible when
each job completes no later than its own deadline in that order.
-/
def FeasibleJobSequence (jobs : List Job) : Prop :=
  ∀ pref j suffix, jobs = pref ++ [j] ++ suffix →
    j.deadline ≥ totalProcessingTime (pref ++ [j])

def JobSequencing (I : JobSequencingInput) : Prop :=
  ∃ selected : List Job,
    List.Sublist selected I.jobs ∧
      FeasibleJobSequence selected ∧
      I.targetProfit ≤ totalProfit selected

def jobSequencingDecisionProblem : EncodedDecisionProblem where
  Instance := jobSequencingEncodedType
  isYes := JobSequencing

/-- Job Sequencing over the structured finite-alphabet encoding. -/
def jobSequencingStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := jobSequencingStructuredEncodedType
  isYes := JobSequencing

/-- Job Sequencing over the binary-numeric finite-alphabet encoding. -/
def jobSequencingBinaryStructuredDecisionProblem : EncodedDecisionProblem where
  Instance := jobSequencingBinaryStructuredEncodedType
  isYes := JobSequencing

end Combinatorics
end ComplexityReduction
