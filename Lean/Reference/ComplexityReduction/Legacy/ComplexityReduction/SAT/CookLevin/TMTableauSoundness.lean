/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauRun

/-!
Positive soundness for satisfied standard-TM Cook-Levin tableaux.

This file compares the true-output run extracted from a satisfied tableau with
the verifier witness run supplied by `TM2ComputableInPolyTime`.  The comparison
uses only deterministic `FinTM2` execution: two halted outputs reached from the
same input must have the same halt configuration.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Deterministic output uniqueness for `TM2OutputsInTime` -/

theorem optionStep_iterate_none {σ : Type} (f : σ → Option σ) (n : Nat) :
    (flip bind f)^[n] none = none := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      rfl

theorem evalsToInTime_some_unique_of_step_none_of_steps_le {σ : Type}
    {f : σ → Option σ} {a b c : σ} {m n : Nat}
    (hbStop : f b = none)
    (h₁ : StateTransition.EvalsToInTime f a (some b) m)
    (h₂ : StateTransition.EvalsToInTime f a (some c) n)
    (hle : h₁.steps ≤ h₂.steps) :
    b = c := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
  have h₂steps : h₂.steps = d + h₁.steps := by
    simpa [Nat.add_comm] using hd
  have hRun₂ :
      (flip bind f)^[d + h₁.steps] (some a) = some c := by
    simpa [h₂steps] using h₂.evals_in_steps
  rw [Function.iterate_add_apply, h₁.evals_in_steps] at hRun₂
  cases d with
  | zero =>
      simpa using hRun₂
  | succ d =>
      have hNone :
          (flip bind f)^[d.succ] (some b) = none := by
        rw [Function.iterate_succ_apply]
        change (flip bind f)^[d] (f b) = none
        rw [hbStop]
        exact optionStep_iterate_none f d
      rw [hNone] at hRun₂
      cases hRun₂

theorem evalsToInTime_some_unique_of_step_none {σ : Type} {f : σ → Option σ}
    {a b c : σ} {m n : Nat}
    (hbStop : f b = none) (hcStop : f c = none)
    (h₁ : StateTransition.EvalsToInTime f a (some b) m)
    (h₂ : StateTransition.EvalsToInTime f a (some c) n) :
    b = c := by
  rcases le_total h₁.steps h₂.steps with hle | hle
  · exact evalsToInTime_some_unique_of_step_none_of_steps_le hbStop h₁ h₂ hle
  · exact
      (evalsToInTime_some_unique_of_step_none_of_steps_le hcStop h₂ h₁ hle).symm

theorem tm2OutputsInTime_some_unique {tm : Turing.FinTM2}
    {input : List (tm.Γ tm.k₀)} {out₁ out₂ : List (tm.Γ tm.k₁)} {m n : Nat}
    (h₁ : Turing.TM2OutputsInTime tm input (some out₁) m)
    (h₂ : Turing.TM2OutputsInTime tm input (some out₂) n) :
    out₁ = out₂ := by
  have hCfg :
      Turing.haltList tm out₁ = Turing.haltList tm out₂ :=
    evalsToInTime_some_unique_of_step_none
      (f := tm.step) (a := Turing.initList tm input)
      (b := Turing.haltList tm out₁) (c := Turing.haltList tm out₂)
      (by
        simp [Turing.FinTM2.step, Turing.TM2.step, Turing.haltList]
        rfl)
      (by
        simp [Turing.FinTM2.step, Turing.TM2.step, Turing.haltList]
        rfl) h₁ h₂
  have hStack := congrArg (fun cfg : tm.Cfg => cfg.stk tm.k₁) hCfg
  simpa [Turing.haltList] using hStack

/-! ### Boolean verifier-output consequences -/

theorem tmVerifierBoolOutputWord_injective {L : EncodedDecisionProblem}
    (V : TMVerifier L) :
    Function.Injective (tmVerifierBoolOutputWord V) := by
  intro b c h
  have hEncode :
      EncodedType.bool.encode b = EncodedType.bool.encode c := by
    have hMap := congrArg
      (List.map (tmVerifierComputableWitness V).outputAlphabet) h
    simpa [tmVerifierBoolOutputWord, List.map_map, Function.comp_def] using hMap
  exact EncodedType.bool_encode_injective hEncode

theorem tmVerifierBoolOutputWord_eq_true_iff {L : EncodedDecisionProblem}
    (V : TMVerifier L) (b : Bool) :
    tmVerifierBoolOutputWord V b = tmVerifierBoolOutputWord V true ↔ b = true := by
  constructor
  · intro h
    exact tmVerifierBoolOutputWord_injective V h
  · intro h
    simp [h]

theorem tmVerifier_verify_eq_true_of_outputs_true_in_time
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (hTrue : tmVerifierOutputsBoolInTime V p true) :
    V.verify p.1 p.2 = true := by
  have hOut :
      tmVerifierBoolOutputWord V true =
        tmVerifierBoolOutputWord V (V.verify p.1 p.2) :=
    tm2OutputsInTime_some_unique hTrue (tmVerifierOutputsVerifyBoolInTime V p)
  exact (tmVerifierBoolOutputWord_injective V hOut.symm)

namespace TMVerifierXOnlyTableauSeed

/-- A satisfied x-only tableau seed forces its chosen certificate to be accepted. -/
theorem verify_eq_true
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a) :
    V.verify x wSeed.cert = true :=
  tmVerifier_verify_eq_true_of_outputs_true_in_time V (x, wSeed.cert)
    wSeed.outputs_true_in_time

/-- A satisfied x-only tableau seed yields a bounded accepting certificate. -/
def boundedAcceptingCertificate
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a) :
    TMVerifierBoundedAcceptingCertificate V x where
  cert := wSeed.cert
  cert_size := wSeed.cert_size
  verify_true := wSeed.verify_eq_true

/-- Seed-level positive soundness: the tableau seed gives an accepted certificate. -/
theorem exists_verify_eq_true
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a) :
    ∃ c, V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x ∧
      V.verify x c = true :=
  ⟨wSeed.cert, wSeed.cert_size, wSeed.verify_eq_true⟩

/-- Seed-level language soundness via the verifier's soundness field. -/
theorem isYes
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a) :
    L.isYes x :=
  V.sound x wSeed.cert wSeed.verify_eq_true

end TMVerifierXOnlyTableauSeed

/-- CNF-level positive soundness for the current x-only tableau-seed surface. -/
theorem tmVerifierXOnlyTableauSeed_satisfiable_sound
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (x : L.Instance.Carrier) :
    (∃ a, Nonempty (TMVerifierXOnlyTableauSeed V B x a)) →
      ∃ c, V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x ∧
        V.verify x c = true := by
  rintro ⟨a, ⟨wSeed⟩⟩
  exact wSeed.exists_verify_eq_true

/-- CNF-level positive language soundness for the current x-only tableau-seed surface. -/
theorem tmVerifierXOnlyTableauSeed_satisfiable_isYes
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (x : L.Instance.Carrier) :
    (∃ a, Nonempty (TMVerifierXOnlyTableauSeed V B x a)) → L.isYes x := by
  intro h
  rcases tmVerifierXOnlyTableauSeed_satisfiable_sound V B x h with
    ⟨c, _hSize, hVerify⟩
  exact V.sound x c hVerify

/-- Bounded-certificate packaging of x-only tableau-seed positive soundness. -/
theorem tmVerifierXOnlyTableauSeed_satisfiable_boundedCertificate
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (B : TMVerifierPushPayloadBoundary V) (x : L.Instance.Carrier) :
    (∃ a, Nonempty (TMVerifierXOnlyTableauSeed V B x a)) →
      Nonempty (TMVerifierBoundedAcceptingCertificate V x) := by
  rintro ⟨a, ⟨wSeed⟩⟩
  exact ⟨wSeed.boundedAcceptingCertificate⟩

end SAT
end ComplexityReduction
