/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauBlocks
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.SeqComp.Part2

/-!
Certificate-independent bounds for the x-only global Cook-Levin tableau.

The fixed-pair tableau uses bounds computed from `(x, c)`. A many-one reduction
from `x` to SAT must instead emit one formula whose dimensions are determined by
`x` alone, with the certificate suffix represented by SAT variables. This file
defines those x-only dimensions and proves that every certificate within the
chosen verifier certificate bound embeds its fixed-pair dimensions into them.
-/

namespace ComplexityReduction
namespace SAT

/-! ### x-only tableau bounds -/

/-- Time bound for the verifier tableau when only the instance `x` is fixed. -/
noncomputable def tmVerifierXOnlyTimeBound {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) : Nat :=
  (tmVerifierComputableWitness V).time.eval (tmVerifierXOnlyInputLengthBound V x)

/-- Cell bound for the verifier tableau when only the instance `x` is fixed. -/
noncomputable def tmVerifierXOnlyCellBound {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) : Nat :=
  tmVerifierXOnlyInputLengthBound V x +
    tmVerifierXOnlyTimeBound V x * TM2Programs.finTM2StepPushBound (tmVerifierTM V) +
    (tmVerifierBoolOutputWord V true).length + 1

/-- Macro time rows of the x-only verifier tableau. -/
noncomputable def tmVerifierXOnlyTableauTimeRange {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) : List Nat :=
  List.range (tmVerifierXOnlyTimeBound V x + 1)

/-- Macro transition rows of the x-only verifier tableau. -/
noncomputable def tmVerifierXOnlyTransitionTimeRange {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) : List Nat :=
  List.range (tmVerifierXOnlyTimeBound V x)

/-- Cell coordinates of the x-only verifier tableau. -/
noncomputable def tmVerifierXOnlyCellRange {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) : List Nat :=
  List.range (tmVerifierXOnlyCellBound V x + 1)

/-- Cell coordinates whose successor is still inside the x-only cell range. -/
noncomputable def tmVerifierXOnlyCellSuccessorRange {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) : List Nat :=
  List.range (tmVerifierXOnlyCellBound V x)

/-- First SAT time coordinate reserved for x-only transition micro-rows. -/
noncomputable def tmVerifierXOnlyFixedMicroBase {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) : Nat :=
  tmVerifierXOnlyTimeBound V x + 1

/-- X-only micro-row coordinate for a macro transition row and action index. -/
noncomputable def tmVerifierXOnlyFixedMicroTime {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) (t micro : Nat) : Nat :=
  tmVerifierXOnlyFixedMicroBase V x + Nat.pair t micro

/-- Payload part of an x-only micro-row coordinate. -/
noncomputable def tmVerifierXOnlyFixedMicroPayload {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) (u : Nat) : Nat :=
  u - tmVerifierXOnlyFixedMicroBase V x

theorem tmVerifierXOnlyFixedMicroBase_le_time {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (t micro : Nat) :
    tmVerifierXOnlyFixedMicroBase V x ≤ tmVerifierXOnlyFixedMicroTime V x t micro := by
  simp [tmVerifierXOnlyFixedMicroTime]

theorem tmVerifierXOnlyFixedMicroTime_ne_of_lt_base {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    {u t micro : Nat} (hu : u < tmVerifierXOnlyFixedMicroBase V x) :
    tmVerifierXOnlyFixedMicroTime V x t micro ≠ u := by
  intro h
  have hle := tmVerifierXOnlyFixedMicroBase_le_time V x t micro
  rw [h] at hle
  exact Nat.not_lt_of_ge hle hu

theorem tmVerifierXOnlyFixedMicroTime_ne_macro_of_le_timeBound
    {L : EncodedDecisionProblem} (V : TMVerifier L) (x : L.Instance.Carrier)
    {u t micro : Nat} (hu : u ≤ tmVerifierXOnlyTimeBound V x) :
    tmVerifierXOnlyFixedMicroTime V x t micro ≠ u := by
  exact tmVerifierXOnlyFixedMicroTime_ne_of_lt_base V x
    (by simpa [tmVerifierXOnlyFixedMicroBase] using Nat.lt_succ_of_le hu)

theorem tmVerifierXOnlyFixedMicroTime_ne_macro {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    {t micro : Nat} (ht : t ≤ tmVerifierXOnlyTimeBound V x) :
    tmVerifierXOnlyFixedMicroTime V x t micro ≠ t :=
  tmVerifierXOnlyFixedMicroTime_ne_macro_of_le_timeBound V x ht

theorem tmVerifierXOnlyFixedMicroTime_ne_macro_succ {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    {t micro : Nat} (ht : t < tmVerifierXOnlyTimeBound V x) :
    tmVerifierXOnlyFixedMicroTime V x t micro ≠ t + 1 :=
  tmVerifierXOnlyFixedMicroTime_ne_macro_of_le_timeBound V x (Nat.succ_le_of_lt ht)

@[simp]
theorem tmVerifierXOnlyFixedMicroPayload_time {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (t micro : Nat) :
    tmVerifierXOnlyFixedMicroPayload V x (tmVerifierXOnlyFixedMicroTime V x t micro) =
      Nat.pair t micro := by
  simp [tmVerifierXOnlyFixedMicroPayload, tmVerifierXOnlyFixedMicroTime]

@[simp]
theorem tmVerifierXOnlyFixedMicroTime_unpair_first {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (t micro : Nat) :
    (Nat.unpair (tmVerifierXOnlyFixedMicroPayload V x
      (tmVerifierXOnlyFixedMicroTime V x t micro))).1 = t := by
  simp [Nat.unpair_pair]

@[simp]
theorem tmVerifierXOnlyFixedMicroTime_unpair_second {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (t micro : Nat) :
    (Nat.unpair (tmVerifierXOnlyFixedMicroPayload V x
      (tmVerifierXOnlyFixedMicroTime V x t micro))).2 = micro := by
  simp [Nat.unpair_pair]

/-! ### Fixed-pair bounds embed into x-only bounds -/

theorem tmVerifierInputEncoded_length_le_xOnlyInputLengthBound_of_cert_size_le
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x) :
    ((tmVerifierInputEncodedType V).encode (x, c)).length ≤
      tmVerifierXOnlyInputLengthBound V x := by
  have hWord :=
    tmVerifierInputWord_length_le_xOnlyInputLengthBound_of_cert_size_le V x c hSize
  simpa [tmVerifierInputWord] using hWord

theorem tmVerifierTimeBound_le_xOnlyTimeBound_of_cert_size_le
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x) :
    tmVerifierTimeBound V (x, c) ≤ tmVerifierXOnlyTimeBound V x := by
  exact TM2Programs.polynomialNat_eval_mono (tmVerifierComputableWitness V).time
    (tmVerifierInputEncoded_length_le_xOnlyInputLengthBound_of_cert_size_le V x c hSize)

theorem tmVerifierCellBound_le_xOnlyCellBound_of_cert_size_le
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x) :
    tmVerifierCellBound V (x, c) ≤ tmVerifierXOnlyCellBound V x := by
  have hInput :=
    tmVerifierInputWord_length_le_xOnlyInputLengthBound_of_cert_size_le V x c hSize
  have hTime := tmVerifierTimeBound_le_xOnlyTimeBound_of_cert_size_le V x c hSize
  have hPush :
      tmVerifierTimeBound V (x, c) * TM2Programs.finTM2StepPushBound (tmVerifierTM V) ≤
        tmVerifierXOnlyTimeBound V x * TM2Programs.finTM2StepPushBound (tmVerifierTM V) :=
    Nat.mul_le_mul_right _ hTime
  simp [tmVerifierCellBound, tmVerifierXOnlyCellBound] at *
  omega

theorem tmVerifierFixedMicroBase_le_xOnlyFixedMicroBase_of_cert_size_le
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x) :
    tmVerifierFixedMicroBase V (x, c) ≤ tmVerifierXOnlyFixedMicroBase V x := by
  have hTime := tmVerifierTimeBound_le_xOnlyTimeBound_of_cert_size_le V x c hSize
  simp [tmVerifierFixedMicroBase, tmVerifierXOnlyFixedMicroBase]
  omega

theorem tmVerifierFixedMicroTime_le_xOnlyFixedMicroTime_of_cert_size_le
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x)
    (t micro : Nat) :
    tmVerifierFixedMicroTime V (x, c) t micro ≤
      tmVerifierXOnlyFixedMicroTime V x t micro := by
  have hBase :=
    tmVerifierFixedMicroBase_le_xOnlyFixedMicroBase_of_cert_size_le V x c hSize
  simp [tmVerifierFixedMicroTime, tmVerifierXOnlyFixedMicroTime]
  omega

/-! ### Range membership and inclusion lemmas -/

theorem tmVerifierXOnlyTableauTimeRange_mem_of_le {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) {t : Nat}
    (ht : t ≤ tmVerifierXOnlyTimeBound V x) :
    t ∈ tmVerifierXOnlyTableauTimeRange V x := by
  simp [tmVerifierXOnlyTableauTimeRange, ht]

theorem tmVerifierXOnlyTransitionTimeRange_mem_of_lt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) {t : Nat}
    (ht : t < tmVerifierXOnlyTimeBound V x) :
    t ∈ tmVerifierXOnlyTransitionTimeRange V x := by
  simpa [tmVerifierXOnlyTransitionTimeRange] using ht

theorem tmVerifierXOnlyCellRange_mem_of_le {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) {cell : Nat}
    (hcell : cell ≤ tmVerifierXOnlyCellBound V x) :
    cell ∈ tmVerifierXOnlyCellRange V x := by
  simp [tmVerifierXOnlyCellRange, hcell]

theorem tmVerifierXOnlyCellSuccessorRange_mem_of_lt {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) {cell : Nat}
    (hcell : cell < tmVerifierXOnlyCellBound V x) :
    cell ∈ tmVerifierXOnlyCellSuccessorRange V x := by
  simpa [tmVerifierXOnlyCellSuccessorRange] using hcell

theorem tmVerifierTableauTimeRange_mem_xOnly_of_cert_size_le
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x)
    {t : Nat} (ht : t ∈ tmVerifierTableauTimeRange V (x, c)) :
    t ∈ tmVerifierXOnlyTableauTimeRange V x := by
  have hTime := tmVerifierTimeBound_le_xOnlyTimeBound_of_cert_size_le V x c hSize
  rw [tmVerifierTableauTimeRange, List.mem_range] at ht
  rw [tmVerifierXOnlyTableauTimeRange, List.mem_range]
  omega

theorem tmVerifierTransitionTimeRange_mem_xOnly_of_cert_size_le
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, c)) :
    t ∈ tmVerifierXOnlyTransitionTimeRange V x := by
  have hTime := tmVerifierTimeBound_le_xOnlyTimeBound_of_cert_size_le V x c hSize
  rw [tmVerifierTransitionTimeRange, List.mem_range] at ht
  rw [tmVerifierXOnlyTransitionTimeRange, List.mem_range]
  omega

theorem tmVerifierCellRange_mem_xOnly_of_cert_size_le
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x)
    {cell : Nat} (hcell : cell ∈ tmVerifierCellRange V (x, c)) :
    cell ∈ tmVerifierXOnlyCellRange V x := by
  have hCell := tmVerifierCellBound_le_xOnlyCellBound_of_cert_size_le V x c hSize
  rw [tmVerifierCellRange, List.mem_range] at hcell
  rw [tmVerifierXOnlyCellRange, List.mem_range]
  omega

theorem tmVerifierCellSuccessorRange_mem_xOnly_of_cert_size_le
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x)
    {cell : Nat} (hcell : cell ∈ tmVerifierCellSuccessorRange V (x, c)) :
    cell ∈ tmVerifierXOnlyCellSuccessorRange V x := by
  have hCell := tmVerifierCellBound_le_xOnlyCellBound_of_cert_size_le V x c hSize
  rw [tmVerifierCellSuccessorRange, List.mem_range] at hcell
  rw [tmVerifierXOnlyCellSuccessorRange, List.mem_range]
  omega

end SAT
end ComplexityReduction
