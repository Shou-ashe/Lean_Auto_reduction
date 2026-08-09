/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.Karp21.SatisfiabilitySuffixDecoderTM

/-!
Checked finite-Boolean suffix decoders for Karp21 verifiers with `List Bool`
certificates.

These instances reuse `tmVerifierFiniteBoolCheckedSuffixDecoder`.  They only
show that the checked suffix CNF enforces the concrete finite Boolean
certificate image for each named verifier.  They do not prove the stronger
raw accepting-run decoding obligation.
-/

namespace ComplexityReduction
namespace Karp21

open ComplexityReduction.Combinatorics
open ComplexityReduction.Combinatorics.Graph

/-! ### Partition -/

theorem partitionStructuredFiniteBoolCertificateSymbols_eq_encode (bits : List Bool) :
    SAT.tmVerifierFiniteBoolCertificateSymbols
        (V := partitionStructuredFiniteTMVerifier) (fun b : Bool => some b) none bits =
      SAT.finiteAssignmentCertEncodedType.encode bits := by
  induction bits with
  | nil =>
      rfl
  | cons b bits ih =>
      change
        some b :: none ::
            SAT.tmVerifierFiniteBoolCertificateSymbols
              (V := partitionStructuredFiniteTMVerifier) (fun b : Bool => some b) none bits =
          some b :: none :: SAT.finiteAssignmentCertEncodedType.encode bits
      rw [ih]

theorem partitionStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols
    (bits : List Bool) :
    SAT.tmVerifierCertificateInputSuffixEncoded partitionStructuredFiniteTMVerifier bits =
      (SAT.tmVerifierFiniteBoolCertificateSymbols
          (V := partitionStructuredFiniteTMVerifier)
          (fun b : Bool => some b) none bits).map (fun s => some (Sum.inr s)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded, partitionStructuredFiniteTMVerifier,
    Partition.partitionCertificateEncodedType] using
    congrArg
      (fun xs : List SAT.finiteAssignmentCertEncodedType.Symbol =>
        xs.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType partitionStructuredFiniteTMVerifier).Symbol)))
      (partitionStructuredFiniteBoolCertificateSymbols_eq_encode bits).symm

noncomputable def partitionStructuredFiniteEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder partitionStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofCertificateDecoder
    partitionStructuredFiniteTMVerifier
    SAT.finiteAssignmentCertDecode
    (by
      intro symbols bits h
      exact SAT.finiteAssignmentCertDecode_sound h)
    SAT.finiteAssignmentCertDecode_complete

noncomputable def partitionStructuredFiniteCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder partitionStructuredFiniteTMVerifier :=
  SAT.tmVerifierFiniteBoolCheckedSuffixDecoder
    partitionStructuredFiniteTMVerifier
    (fun b : Bool => some b) none
    partitionStructuredFiniteEncodedSuffixDecoder
    (fun bits : List Bool => bits)
    (fun bits : List Bool => bits)
    (by
      intro bits
      exact partitionStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)
    (by
      intro bits
      exact partitionStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)

theorem partitionStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder partitionStructuredDecisionProblem :=
  ⟨⟨partitionStructuredFiniteTMVerifier, partitionStructuredFiniteCheckedSuffixDecoder⟩⟩

/-! ### Binary Partition -/

theorem partitionBinaryStructuredFiniteBoolCertificateSymbols_eq_encode (bits : List Bool) :
    SAT.tmVerifierFiniteBoolCertificateSymbols
        (V := partitionBinaryStructuredFiniteTMVerifier) (fun b : Bool => some b) none bits =
      SAT.finiteAssignmentCertEncodedType.encode bits := by
  induction bits with
  | nil =>
      rfl
  | cons b bits ih =>
      change
        some b :: none ::
            SAT.tmVerifierFiniteBoolCertificateSymbols
              (V := partitionBinaryStructuredFiniteTMVerifier)
              (fun b : Bool => some b) none bits =
          some b :: none :: SAT.finiteAssignmentCertEncodedType.encode bits
      rw [ih]

theorem partitionBinaryStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols
    (bits : List Bool) :
    SAT.tmVerifierCertificateInputSuffixEncoded partitionBinaryStructuredFiniteTMVerifier bits =
      (SAT.tmVerifierFiniteBoolCertificateSymbols
          (V := partitionBinaryStructuredFiniteTMVerifier)
          (fun b : Bool => some b) none bits).map (fun s => some (Sum.inr s)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded, partitionBinaryStructuredFiniteTMVerifier,
    Partition.partitionCertificateEncodedType] using
    congrArg
      (fun xs : List SAT.finiteAssignmentCertEncodedType.Symbol =>
        xs.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType partitionBinaryStructuredFiniteTMVerifier).Symbol)))
      (partitionBinaryStructuredFiniteBoolCertificateSymbols_eq_encode bits).symm

noncomputable def partitionBinaryStructuredFiniteEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder partitionBinaryStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofCertificateDecoder
    partitionBinaryStructuredFiniteTMVerifier
    SAT.finiteAssignmentCertDecode
    (by
      intro symbols bits h
      exact SAT.finiteAssignmentCertDecode_sound h)
    SAT.finiteAssignmentCertDecode_complete

noncomputable def partitionBinaryStructuredFiniteCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder partitionBinaryStructuredFiniteTMVerifier :=
  SAT.tmVerifierFiniteBoolCheckedSuffixDecoder
    partitionBinaryStructuredFiniteTMVerifier
    (fun b : Bool => some b) none
    partitionBinaryStructuredFiniteEncodedSuffixDecoder
    (fun bits : List Bool => bits)
    (fun bits : List Bool => bits)
    (by
      intro bits
      exact
        partitionBinaryStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)
    (by
      intro bits
      exact
        partitionBinaryStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)

theorem partitionBinaryStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder partitionBinaryStructuredDecisionProblem :=
  ⟨⟨partitionBinaryStructuredFiniteTMVerifier,
      partitionBinaryStructuredFiniteCheckedSuffixDecoder⟩⟩

/-! ### Job Sequencing -/

theorem jobSequencingStructuredFiniteBoolCertificateSymbols_eq_encode (bits : List Bool) :
    SAT.tmVerifierFiniteBoolCertificateSymbols
        (V := jobSequencingStructuredFiniteTMVerifier) (fun b : Bool => some b) none bits =
      SAT.finiteAssignmentCertEncodedType.encode bits := by
  induction bits with
  | nil =>
      rfl
  | cons b bits ih =>
      change
        some b :: none ::
            SAT.tmVerifierFiniteBoolCertificateSymbols
              (V := jobSequencingStructuredFiniteTMVerifier)
              (fun b : Bool => some b) none bits =
          some b :: none :: SAT.finiteAssignmentCertEncodedType.encode bits
      rw [ih]

theorem jobSequencingStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols
    (bits : List Bool) :
    SAT.tmVerifierCertificateInputSuffixEncoded jobSequencingStructuredFiniteTMVerifier bits =
      (SAT.tmVerifierFiniteBoolCertificateSymbols
          (V := jobSequencingStructuredFiniteTMVerifier)
          (fun b : Bool => some b) none bits).map (fun s => some (Sum.inr s)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded, jobSequencingStructuredFiniteTMVerifier,
    JobSequencing.jobSequencingCertificateEncodedType] using
    congrArg
      (fun xs : List SAT.finiteAssignmentCertEncodedType.Symbol =>
        xs.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType jobSequencingStructuredFiniteTMVerifier).Symbol)))
      (jobSequencingStructuredFiniteBoolCertificateSymbols_eq_encode bits).symm

noncomputable def jobSequencingStructuredFiniteEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder jobSequencingStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofCertificateDecoder
    jobSequencingStructuredFiniteTMVerifier
    SAT.finiteAssignmentCertDecode
    (by
      intro symbols bits h
      exact SAT.finiteAssignmentCertDecode_sound h)
    SAT.finiteAssignmentCertDecode_complete

noncomputable def jobSequencingStructuredFiniteCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder jobSequencingStructuredFiniteTMVerifier :=
  SAT.tmVerifierFiniteBoolCheckedSuffixDecoder
    jobSequencingStructuredFiniteTMVerifier
    (fun b : Bool => some b) none
    jobSequencingStructuredFiniteEncodedSuffixDecoder
    (fun bits : List Bool => bits)
    (fun bits : List Bool => bits)
    (by
      intro bits
      exact jobSequencingStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)
    (by
      intro bits
      exact jobSequencingStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)

theorem jobSequencingStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder jobSequencingStructuredDecisionProblem :=
  ⟨⟨jobSequencingStructuredFiniteTMVerifier,
      jobSequencingStructuredFiniteCheckedSuffixDecoder⟩⟩

/-! ### Binary Job Sequencing -/

theorem jobSequencingBinaryStructuredFiniteBoolCertificateSymbols_eq_encode (bits : List Bool) :
    SAT.tmVerifierFiniteBoolCertificateSymbols
        (V := jobSequencingBinaryStructuredFiniteTMVerifier)
        (fun b : Bool => some b) none bits =
      SAT.finiteAssignmentCertEncodedType.encode bits := by
  induction bits with
  | nil =>
      rfl
  | cons b bits ih =>
      change
        some b :: none ::
            SAT.tmVerifierFiniteBoolCertificateSymbols
              (V := jobSequencingBinaryStructuredFiniteTMVerifier)
              (fun b : Bool => some b) none bits =
          some b :: none :: SAT.finiteAssignmentCertEncodedType.encode bits
      rw [ih]

theorem jobSequencingBinaryStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols
    (bits : List Bool) :
    SAT.tmVerifierCertificateInputSuffixEncoded jobSequencingBinaryStructuredFiniteTMVerifier bits =
      (SAT.tmVerifierFiniteBoolCertificateSymbols
          (V := jobSequencingBinaryStructuredFiniteTMVerifier)
          (fun b : Bool => some b) none bits).map (fun s => some (Sum.inr s)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded,
    jobSequencingBinaryStructuredFiniteTMVerifier,
    JobSequencing.jobSequencingCertificateEncodedType] using
    congrArg
      (fun xs : List SAT.finiteAssignmentCertEncodedType.Symbol =>
        xs.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType
              jobSequencingBinaryStructuredFiniteTMVerifier).Symbol)))
      (jobSequencingBinaryStructuredFiniteBoolCertificateSymbols_eq_encode bits).symm

noncomputable def jobSequencingBinaryStructuredFiniteEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder jobSequencingBinaryStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofCertificateDecoder
    jobSequencingBinaryStructuredFiniteTMVerifier
    SAT.finiteAssignmentCertDecode
    (by
      intro symbols bits h
      exact SAT.finiteAssignmentCertDecode_sound h)
    SAT.finiteAssignmentCertDecode_complete

noncomputable def jobSequencingBinaryStructuredFiniteCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder jobSequencingBinaryStructuredFiniteTMVerifier :=
  SAT.tmVerifierFiniteBoolCheckedSuffixDecoder
    jobSequencingBinaryStructuredFiniteTMVerifier
    (fun b : Bool => some b) none
    jobSequencingBinaryStructuredFiniteEncodedSuffixDecoder
    (fun bits : List Bool => bits)
    (fun bits : List Bool => bits)
    (by
      intro bits
      exact
        jobSequencingBinaryStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)
    (by
      intro bits
      exact
        jobSequencingBinaryStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)

theorem jobSequencingBinaryStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder jobSequencingBinaryStructuredDecisionProblem :=
  ⟨⟨jobSequencingBinaryStructuredFiniteTMVerifier,
      jobSequencingBinaryStructuredFiniteCheckedSuffixDecoder⟩⟩

/-! ### Binary Knapsack -/

theorem knapsackBinaryStructuredFiniteBoolCertificateSymbols_eq_encode (bits : List Bool) :
    SAT.tmVerifierFiniteBoolCertificateSymbols
        (V := knapsackBinaryStructuredFiniteTMVerifier) (fun b : Bool => some b) none bits =
      SAT.finiteAssignmentCertEncodedType.encode bits := by
  induction bits with
  | nil =>
      rfl
  | cons b bits ih =>
      change
        some b :: none ::
            SAT.tmVerifierFiniteBoolCertificateSymbols
              (V := knapsackBinaryStructuredFiniteTMVerifier)
              (fun b : Bool => some b) none bits =
          some b :: none :: SAT.finiteAssignmentCertEncodedType.encode bits
      rw [ih]

theorem knapsackBinaryStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols
    (bits : List Bool) :
    SAT.tmVerifierCertificateInputSuffixEncoded knapsackBinaryStructuredFiniteTMVerifier bits =
      (SAT.tmVerifierFiniteBoolCertificateSymbols
          (V := knapsackBinaryStructuredFiniteTMVerifier)
          (fun b : Bool => some b) none bits).map (fun s => some (Sum.inr s)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded, knapsackBinaryStructuredFiniteTMVerifier,
    Knapsack.knapsackBinaryCertificateEncodedType] using
    congrArg
      (fun xs : List SAT.finiteAssignmentCertEncodedType.Symbol =>
        xs.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType knapsackBinaryStructuredFiniteTMVerifier).Symbol)))
      (knapsackBinaryStructuredFiniteBoolCertificateSymbols_eq_encode bits).symm

noncomputable def knapsackBinaryStructuredFiniteEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder knapsackBinaryStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofCertificateDecoder
    knapsackBinaryStructuredFiniteTMVerifier
    SAT.finiteAssignmentCertDecode
    (by
      intro symbols bits h
      exact SAT.finiteAssignmentCertDecode_sound h)
    SAT.finiteAssignmentCertDecode_complete

noncomputable def knapsackBinaryStructuredFiniteCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder knapsackBinaryStructuredFiniteTMVerifier :=
  SAT.tmVerifierFiniteBoolCheckedSuffixDecoder
    knapsackBinaryStructuredFiniteTMVerifier
    (fun b : Bool => some b) none
    knapsackBinaryStructuredFiniteEncodedSuffixDecoder
    (fun bits : List Bool => bits)
    (fun bits : List Bool => bits)
    (by
      intro bits
      exact knapsackBinaryStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)
    (by
      intro bits
      exact knapsackBinaryStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)

theorem knapsackBinaryStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder knapsackBinaryStructuredDecisionProblem :=
  ⟨⟨knapsackBinaryStructuredFiniteTMVerifier,
      knapsackBinaryStructuredFiniteCheckedSuffixDecoder⟩⟩

/-! ### Max Cut -/

theorem maxCutStructuredFiniteBoolCertificateSymbols_eq_encode (bits : List Bool) :
    SAT.tmVerifierFiniteBoolCertificateSymbols
        (V := maxCutStructuredFiniteTMVerifier) (fun b : Bool => some b) none bits =
      SAT.finiteAssignmentCertEncodedType.encode bits := by
  induction bits with
  | nil =>
      rfl
  | cons b bits ih =>
      change
        some b :: none ::
            SAT.tmVerifierFiniteBoolCertificateSymbols
              (V := maxCutStructuredFiniteTMVerifier) (fun b : Bool => some b) none bits =
          some b :: none :: SAT.finiteAssignmentCertEncodedType.encode bits
      rw [ih]

theorem maxCutStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols
    (bits : List Bool) :
    SAT.tmVerifierCertificateInputSuffixEncoded maxCutStructuredFiniteTMVerifier bits =
      (SAT.tmVerifierFiniteBoolCertificateSymbols
          (V := maxCutStructuredFiniteTMVerifier)
          (fun b : Bool => some b) none bits).map (fun s => some (Sum.inr s)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded, maxCutStructuredFiniteTMVerifier,
    MaxCut.maxCutCertificateEncodedType] using
    congrArg
      (fun xs : List SAT.finiteAssignmentCertEncodedType.Symbol =>
        xs.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType maxCutStructuredFiniteTMVerifier).Symbol)))
      (maxCutStructuredFiniteBoolCertificateSymbols_eq_encode bits).symm

noncomputable def maxCutStructuredFiniteEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder maxCutStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofCertificateDecoder
    maxCutStructuredFiniteTMVerifier
    SAT.finiteAssignmentCertDecode
    (by
      intro symbols bits h
      exact SAT.finiteAssignmentCertDecode_sound h)
    SAT.finiteAssignmentCertDecode_complete

noncomputable def maxCutStructuredFiniteCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder maxCutStructuredFiniteTMVerifier :=
  SAT.tmVerifierFiniteBoolCheckedSuffixDecoder
    maxCutStructuredFiniteTMVerifier
    (fun b : Bool => some b) none
    maxCutStructuredFiniteEncodedSuffixDecoder
    (fun bits : List Bool => bits)
    (fun bits : List Bool => bits)
    (by
      intro bits
      exact maxCutStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)
    (by
      intro bits
      exact maxCutStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)

theorem maxCutStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder maxCutStructuredDecisionProblem :=
  ⟨⟨maxCutStructuredFiniteTMVerifier, maxCutStructuredFiniteCheckedSuffixDecoder⟩⟩

/-! ### Binary Max Cut -/

theorem maxCutBinaryStructuredFiniteBoolCertificateSymbols_eq_encode (bits : List Bool) :
    SAT.tmVerifierFiniteBoolCertificateSymbols
        (V := maxCutBinaryStructuredFiniteTMVerifier) (fun b : Bool => some b) none bits =
      SAT.finiteAssignmentCertEncodedType.encode bits := by
  induction bits with
  | nil =>
      rfl
  | cons b bits ih =>
      change
        some b :: none ::
            SAT.tmVerifierFiniteBoolCertificateSymbols
              (V := maxCutBinaryStructuredFiniteTMVerifier)
              (fun b : Bool => some b) none bits =
          some b :: none :: SAT.finiteAssignmentCertEncodedType.encode bits
      rw [ih]

theorem maxCutBinaryStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols
    (bits : List Bool) :
    SAT.tmVerifierCertificateInputSuffixEncoded maxCutBinaryStructuredFiniteTMVerifier bits =
      (SAT.tmVerifierFiniteBoolCertificateSymbols
          (V := maxCutBinaryStructuredFiniteTMVerifier)
          (fun b : Bool => some b) none bits).map (fun s => some (Sum.inr s)) := by
  simpa [SAT.tmVerifierCertificateInputSuffixEncoded, maxCutBinaryStructuredFiniteTMVerifier,
    MaxCut.maxCutCertificateEncodedType] using
    congrArg
      (fun xs : List SAT.finiteAssignmentCertEncodedType.Symbol =>
        xs.map (fun s =>
          (some (Sum.inr s) :
            (SAT.tmVerifierInputEncodedType maxCutBinaryStructuredFiniteTMVerifier).Symbol)))
      (maxCutBinaryStructuredFiniteBoolCertificateSymbols_eq_encode bits).symm

noncomputable def maxCutBinaryStructuredFiniteEncodedSuffixDecoder :
    SAT.TMVerifierXOnlyEncodedSuffixDecoder maxCutBinaryStructuredFiniteTMVerifier :=
  SAT.TMVerifierXOnlyEncodedSuffixDecoder.ofCertificateDecoder
    maxCutBinaryStructuredFiniteTMVerifier
    SAT.finiteAssignmentCertDecode
    (by
      intro symbols bits h
      exact SAT.finiteAssignmentCertDecode_sound h)
    SAT.finiteAssignmentCertDecode_complete

noncomputable def maxCutBinaryStructuredFiniteCheckedSuffixDecoder :
    SAT.TMVerifierXOnlyCheckedSuffixDecoder maxCutBinaryStructuredFiniteTMVerifier :=
  SAT.tmVerifierFiniteBoolCheckedSuffixDecoder
    maxCutBinaryStructuredFiniteTMVerifier
    (fun b : Bool => some b) none
    maxCutBinaryStructuredFiniteEncodedSuffixDecoder
    (fun bits : List Bool => bits)
    (fun bits : List Bool => bits)
    (by
      intro bits
      exact maxCutBinaryStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)
    (by
      intro bits
      exact maxCutBinaryStructuredFiniteCertificateInputSuffixEncoded_eq_finiteBoolSymbols bits)

theorem maxCutBinaryStructured_TMInNPWithCheckedSuffixDecoder :
    SAT.TMInNPWithCheckedSuffixDecoder maxCutBinaryStructuredDecisionProblem :=
  ⟨⟨maxCutBinaryStructuredFiniteTMVerifier,
      maxCutBinaryStructuredFiniteCheckedSuffixDecoder⟩⟩

end Karp21
end ComplexityReduction
