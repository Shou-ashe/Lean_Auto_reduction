/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMRoot
import ComplexityReduction.Legacy.ComplexityReduction.Bridges.CostedToTM.Programs.PrefixSuffix.Part1

/-!
Standard-TM verifier data for the future Cook-Levin tableau construction.

This file does not construct the Cook tableau CNF.  It normalizes the concrete
`TM2ComputableInPolyTime` witness extracted from a `TMVerifier` into the words,
time bounds, configuration endpoints, and SAT-variable namespace that later CNF
blocks should consume.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Concrete extracted machine words and bounds -/

/-- The concrete bundled TM2 machine extracted from a direct `TMVerifier`. -/
noncomputable abbrev tmVerifierTM {L : EncodedDecisionProblem} (V : TMVerifier L) :
    Turing.FinTM2 :=
  (tmVerifierComputableWitness V).tm

/-- The concrete TM2 input word for an instance/certificate pair. -/
noncomputable def tmVerifierInputWord {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    List ((tmVerifierTM V).Γ (tmVerifierTM V).k₀) :=
  List.map (tmVerifierComputableWitness V).inputAlphabet.invFun
    ((tmVerifierInputEncodedType V).encode p)

/-- The concrete TM2 output word encoding one verifier Boolean result. -/
noncomputable def tmVerifierBoolOutputWord {L : EncodedDecisionProblem}
    (V : TMVerifier L) (b : Bool) :
    List ((tmVerifierTM V).Γ (tmVerifierTM V).k₁) :=
  List.map (tmVerifierComputableWitness V).outputAlphabet.invFun
    (EncodedType.bool.encode b)

/-- The polynomial time bound supplied by the extracted verifier witness. -/
noncomputable def tmVerifierTimeBound {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) : Nat :=
  (tmVerifierComputableWitness V).time.eval ((tmVerifierInputEncodedType V).encode p).length

/-- A conservative cell bound for future bounded tableau coordinates. -/
noncomputable def tmVerifierCellBound {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) : Nat :=
  (tmVerifierInputWord V p).length +
    tmVerifierTimeBound V p * TM2Programs.finTM2StepPushBound (tmVerifierTM V) +
    (tmVerifierBoolOutputWord V true).length + 1

/-- Time indices used by the bounded verifier tableau. -/
noncomputable abbrev tmVerifierTimeIndex {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) : Type :=
  Fin (tmVerifierTimeBound V p + 1)

/-! ### Fixed-pair micro-row namespace -/

/--
First SAT time coordinate reserved for transition micro-rows in the fixed-pair
tableau.  Macro rows occupy `0, ..., tmVerifierTimeBound V p`.
-/
noncomputable def tmVerifierFixedMicroBase {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) : Nat :=
  tmVerifierTimeBound V p + 1

/--
Micro-row coordinate for the fixed `(V,p)` tableau.

Unlike the older row-local `tmVerifierMicroTime`, this coordinate is globally
outside the macro tableau time range for the fixed pair.
-/
noncomputable def tmVerifierFixedMicroTime {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t micro : Nat) : Nat :=
  tmVerifierFixedMicroBase V p + Nat.pair t micro

/-- Payload part of a fixed-pair micro-row coordinate. -/
noncomputable def tmVerifierFixedMicroPayload {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) (u : Nat) : Nat :=
  u - tmVerifierFixedMicroBase V p

theorem tmVerifierFixedMicroBase_le_time {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t micro : Nat) :
    tmVerifierFixedMicroBase V p ≤ tmVerifierFixedMicroTime V p t micro := by
  simp [tmVerifierFixedMicroTime]

theorem tmVerifierFixedMicroTime_ne_of_lt_base {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    {u t micro : Nat} (hu : u < tmVerifierFixedMicroBase V p) :
    tmVerifierFixedMicroTime V p t micro ≠ u := by
  intro h
  have hle := tmVerifierFixedMicroBase_le_time V p t micro
  rw [h] at hle
  exact Nat.not_lt_of_ge hle hu

theorem tmVerifierFixedMicroTime_ne_macro_of_le_timeBound {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    {u t micro : Nat} (hu : u ≤ tmVerifierTimeBound V p) :
    tmVerifierFixedMicroTime V p t micro ≠ u := by
  exact tmVerifierFixedMicroTime_ne_of_lt_base V p
    (by simpa [tmVerifierFixedMicroBase] using Nat.lt_succ_of_le hu)

theorem tmVerifierFixedMicroTime_ne_macro {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    {t micro : Nat} (ht : t ≤ tmVerifierTimeBound V p) :
    tmVerifierFixedMicroTime V p t micro ≠ t :=
  tmVerifierFixedMicroTime_ne_macro_of_le_timeBound V p ht

theorem tmVerifierFixedMicroTime_ne_macro_succ {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    {t micro : Nat} (ht : t < tmVerifierTimeBound V p) :
    tmVerifierFixedMicroTime V p t micro ≠ t + 1 :=
  tmVerifierFixedMicroTime_ne_macro_of_le_timeBound V p (Nat.succ_le_of_lt ht)

@[simp]
theorem tmVerifierFixedMicroPayload_time {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t micro : Nat) :
    tmVerifierFixedMicroPayload V p (tmVerifierFixedMicroTime V p t micro) =
      Nat.pair t micro := by
  simp [tmVerifierFixedMicroPayload, tmVerifierFixedMicroTime]

@[simp]
theorem tmVerifierFixedMicroTime_unpair_first {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t micro : Nat) :
    (Nat.unpair (tmVerifierFixedMicroPayload V p
      (tmVerifierFixedMicroTime V p t micro))).1 = t := by
  simp [Nat.unpair_pair]

@[simp]
theorem tmVerifierFixedMicroTime_unpair_second {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t micro : Nat) :
    (Nat.unpair (tmVerifierFixedMicroPayload V p
      (tmVerifierFixedMicroTime V p t micro))).2 = micro := by
  simp [Nat.unpair_pair]

/-- Cell indices used by the bounded verifier tableau. -/
noncomputable abbrev tmVerifierCellIndex {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) : Type :=
  Fin (tmVerifierCellBound V p + 1)

/-- Stack indices of the extracted TM2 machine. -/
noncomputable abbrev tmVerifierStackIndex {L : EncodedDecisionProblem}
    (V : TMVerifier L) : Type :=
  (tmVerifierTM V).K

/-- The initial configuration for the extracted verifier machine on one pair. -/
noncomputable def tmVerifierInitialCfg {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) : (tmVerifierTM V).Cfg :=
  Turing.initList (tmVerifierTM V) (tmVerifierInputWord V p)

/-- The final output configuration for one Boolean output word. -/
noncomputable def tmVerifierOutputCfg {L : EncodedDecisionProblem} (V : TMVerifier L)
    (b : Bool) : (tmVerifierTM V).Cfg :=
  Turing.haltList (tmVerifierTM V) (tmVerifierBoolOutputWord V b)

/-- Output-in-time predicate normalized through the local verifier data names. -/
noncomputable abbrev tmVerifierOutputsBoolInTime {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) (b : Bool) : Type :=
  Turing.TM2OutputsInTime (tmVerifierTM V) (tmVerifierInputWord V p)
    (some (tmVerifierBoolOutputWord V b)) (tmVerifierTimeBound V p)

/-- The extracted machine outputs the verifier's Boolean result within its time bound. -/
noncomputable def tmVerifierOutputsVerifyBoolInTime {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier) :
    tmVerifierOutputsBoolInTime V p (V.verify p.1 p.2) := by
  simpa [tmVerifierOutputsBoolInTime, tmVerifierTM, tmVerifierInputWord,
    tmVerifierBoolOutputWord, tmVerifierTimeBound] using
    tmVerifierComputableWitness_outputs V p

/-! ### Run objects for accepting and rejecting verifier computations -/

/--
An accepting extracted verifier run.

The `verify_true` field is retained intentionally: until the full deterministic
tableau correctness theorem is proved, later CNF slices can target this run
object and then erase it back to the original `TMVerifier` semantics.
-/
structure TMVerifierAcceptedRun {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) : Type where
  verify_true : V.verify x c = true
  output_true : tmVerifierOutputsBoolInTime V (x, c) true

namespace TMVerifierAcceptedRun

/-- Build the accepting run object from a true verifier result. -/
noncomputable def of_verify_eq_true {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) (h : V.verify x c = true) :
    TMVerifierAcceptedRun V x c where
  verify_true := h
  output_true := by
    simpa [h] using tmVerifierOutputsVerifyBoolInTime V (x, c)

/-- The normalized accepting-run object is equivalent to the verifier accepting. -/
theorem nonempty_iff_verify_eq_true {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) :
    Nonempty (TMVerifierAcceptedRun V x c) ↔ V.verify x c = true := by
  constructor
  · rintro ⟨run⟩
    exact run.verify_true
  · intro h
    exact ⟨of_verify_eq_true V x c h⟩

end TMVerifierAcceptedRun

/-- A rejecting extracted verifier run. -/
structure TMVerifierRejectedRun {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) : Type where
  verify_false : V.verify x c = false
  output_false : tmVerifierOutputsBoolInTime V (x, c) false

namespace TMVerifierRejectedRun

/-- Build the rejecting run object from a false verifier result. -/
noncomputable def of_verify_eq_false {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) (h : V.verify x c = false) :
    TMVerifierRejectedRun V x c where
  verify_false := h
  output_false := by
    simpa [h] using tmVerifierOutputsVerifyBoolInTime V (x, c)

/-- The normalized rejecting-run object is equivalent to the verifier rejecting. -/
theorem nonempty_iff_verify_eq_false {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier) :
    Nonempty (TMVerifierRejectedRun V x c) ↔ V.verify x c = false := by
  constructor
  · rintro ⟨run⟩
    exact run.verify_false
  · intro h
    exact ⟨of_verify_eq_false V x c h⟩

end TMVerifierRejectedRun

/-! ### SAT-variable namespace for future TM tableau CNF blocks -/

/-- Variable families for the standard-TM verifier tableau. -/
inductive TMVerifierTableauVarKind where
  | label
  | state
  | stackSymbol
  | stackEmpty
  | output
  | aux
deriving DecidableEq, Repr

namespace TMVerifierTableauVarKind

/-- Stable numeric tag for a verifier-tableau variable family. -/
def tag : TMVerifierTableauVarKind → Nat
  | label => 0
  | state => 1
  | stackSymbol => 2
  | stackEmpty => 3
  | output => 4
  | aux => 5

theorem tag_injective : Function.Injective tag := by
  intro a b h
  cases a <;> cases b <;> simp [tag] at h ⊢

end TMVerifierTableauVarKind

/-- Stable SAT variable number for one future TM-tableau atom. -/
def tmVerifierTableauVar (kind : TMVerifierTableauVarKind)
    (time stack cell payload : Nat) : Nat :=
  Nat.pair kind.tag (Nat.pair time (Nat.pair stack (Nat.pair cell payload)))

/-- Positive future TM-tableau atom. -/
def tmVerifierTableauAtom (kind : TMVerifierTableauVarKind)
    (time stack cell payload : Nat) : Literal :=
  { var := tmVerifierTableauVar kind time stack cell payload, neg := false }

/-- Negative future TM-tableau atom. -/
def negTMVerifierTableauAtom (kind : TMVerifierTableauVarKind)
    (time stack cell payload : Nat) : Literal :=
  { var := tmVerifierTableauVar kind time stack cell payload, neg := true }

end SAT
end ComplexityReduction
