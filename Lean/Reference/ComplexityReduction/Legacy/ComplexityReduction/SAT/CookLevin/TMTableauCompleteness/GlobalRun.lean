/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Nat.Find
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauRun
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.GlobalMacroStepSoundness

/-!
Run extraction from satisfied global fixed-micro Cook-Levin tableaux.

This is the global-micro analogue of `TMTableauRun`: it chains only genuine
nonhalting macro rows by `Turing.TM2.step`, then uses halted padding rows only
as tableau stutter equalities to identify the first halted row with the true
output endpoint.
-/

namespace ComplexityReduction
namespace SAT

namespace TMVerifierGlobalTableauEvidence

/--
Chain genuine nonhalting transition rows from time `0` to time `n` for a global
fixed-micro tableau.
-/
noncomputable def evalsToInTime_decodedCfg_of_forall_nonhalt
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    {n : Nat} (hn : n ≤ tmVerifierTimeBound V p)
    (hNonhalt :
      ∀ u, u < n →
        ∃ ht : u ∈ tmVerifierTableauTimeRange V p,
          ∃ l : (tmVerifierTM V).Λ, (E.controlRow u ht).label = some l) :
    StateTransition.EvalsToInTime (tmVerifierTM V).step
      (E.decodedCfg 0 (tmVerifierTableauTimeRange_zero_mem V p))
      (some (E.decodedCfg n (tmVerifierTableauTimeRange_mem_of_le V p hn))) n := by
  induction n with
  | zero =>
      have hcfg :
          E.decodedCfg 0 (tmVerifierTableauTimeRange_zero_mem V p) =
            E.decodedCfg 0 (tmVerifierTableauTimeRange_mem_of_le V p hn) :=
        E.decodedCfg_proof_irrel _ _
      simpa [hcfg] using
        StateTransition.EvalsToInTime.refl (tmVerifierTM V).step
          (E.decodedCfg 0 (tmVerifierTableauTimeRange_zero_mem V p))
  | succ n ih =>
      have hnPrev : n ≤ tmVerifierTimeBound V p := by omega
      have hnlt : n < tmVerifierTimeBound V p := by omega
      have hprevNonhalt :
          ∀ u, u < n →
            ∃ ht : u ∈ tmVerifierTableauTimeRange V p,
              ∃ l : (tmVerifierTM V).Λ, (E.controlRow u ht).label = some l := by
        intro u hu
        exact hNonhalt u (by omega)
      have hPrev := ih hnPrev hprevNonhalt
      let htAny := Classical.choose (hNonhalt n (by omega))
      let hlabelExists := Classical.choose_spec (hNonhalt n (by omega))
      let l := Classical.choose hlabelExists
      have hLabelAny : (E.controlRow n htAny).label = some l :=
        Classical.choose_spec hlabelExists
      let htTrans := tmVerifierTransitionTimeRange_mem_of_lt V p hnlt
      let htTransRow := tmVerifierTransitionTimeRange_mem_tableauTimeRange V p htTrans
      let htSuccRow := tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V p htTrans
      let htPrev := tmVerifierTableauTimeRange_mem_of_le V p hnPrev
      let htSucc := tmVerifierTableauTimeRange_mem_of_le V p hn
      have hLabelTrans : (E.controlRow n htTransRow).label = some l := by
        calc
          (E.controlRow n htTransRow).label = (E.controlRow n htAny).label :=
            E.controlRow_label_proof_irrel _ _
          _ = some l := hLabelAny
      have hStepRaw :
          (tmVerifierTM V).step (E.decodedCfg n htTransRow) =
            some (E.decodedCfg (n + 1) htSuccRow) :=
        E.transitionDecodedCfg_step htTrans hLabelTrans
      have hStep :
          (tmVerifierTM V).step (E.decodedCfg n htPrev) =
            some (E.decodedCfg (n + 1) htSucc) := by
        calc
          (tmVerifierTM V).step (E.decodedCfg n htPrev)
              = (tmVerifierTM V).step (E.decodedCfg n htTransRow) := by
                rw [E.decodedCfg_proof_irrel htPrev htTransRow]
          _ = some (E.decodedCfg (n + 1) htSuccRow) := hStepRaw
          _ = some (E.decodedCfg (n + 1) htSucc) := by
                rw [E.decodedCfg_proof_irrel htSuccRow htSucc]
      have hOne :
          StateTransition.EvalsToInTime (tmVerifierTM V).step
            (E.decodedCfg n htPrev) (some (E.decodedCfg (n + 1) htSucc)) 1 :=
        stateTransitionEvalsToInTime_one hStep
      have hAll :=
        StateTransition.EvalsToInTime.trans (tmVerifierTM V).step n 1
          (E.decodedCfg 0 (tmVerifierTableauTimeRange_zero_mem V p))
          (E.decodedCfg n htPrev) (some (E.decodedCfg (n + 1) htSucc)) hPrev hOne
      simpa [Nat.add_comm] using hAll

/--
If a global row is halted, halted-row clauses identify it with the endpoint
decoded configuration.  These clauses are used only as CNF stutter equalities.
-/
theorem decodedCfg_eq_endpoint_of_halted_at
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    {h : Nat} (hh : h ≤ tmVerifierTimeBound V p)
    (hLabel :
      (E.controlRow h (tmVerifierTableauTimeRange_mem_of_le V p hh)).label = none) :
    E.decodedCfg h (tmVerifierTableauTimeRange_mem_of_le V p hh) =
      E.decodedCfg (tmVerifierTimeBound V p) (tmVerifierTableauTimeRange_timeBound_mem V p) := by
  let N := tmVerifierTimeBound V p
  let hMem := tmVerifierTableauTimeRange_mem_of_le V p hh
  have hAll :
      ∀ d, (hd : h + d ≤ N) →
        E.decodedCfg (h + d)
            (tmVerifierTableauTimeRange_mem_of_le V p (by simpa [N] using hd)) =
            E.decodedCfg h hMem ∧
          (E.controlRow (h + d)
              (tmVerifierTableauTimeRange_mem_of_le V p (by simpa [N] using hd))).label =
            none := by
    intro d hd
    induction d with
    | zero =>
        constructor
        · exact E.decodedCfg_proof_irrel _ _
        · calc
            (E.controlRow h
                (tmVerifierTableauTimeRange_mem_of_le V p (by omega))).label =
                (E.controlRow h hMem).label := E.controlRow_label_proof_irrel _ _
            _ = none := hLabel
    | succ d ih =>
        have hdPrev : h + d ≤ N := by omega
        have hdltN : h + d < N := by omega
        let htPrev : h + d ∈ tmVerifierTableauTimeRange V p :=
          tmVerifierTableauTimeRange_mem_of_le V p (by omega)
        let htSucc : h + (d + 1) ∈ tmVerifierTableauTimeRange V p :=
          tmVerifierTableauTimeRange_mem_of_le V p (by omega)
        rcases ih hdPrev with ⟨hCfgPrev, hLabelPrev⟩
        let htTrans := tmVerifierTransitionTimeRange_mem_of_lt V p (by
          simpa [N] using hdltN)
        let htTransRow := tmVerifierTransitionTimeRange_mem_tableauTimeRange V p htTrans
        let htSuccRow := tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V p htTrans
        have hLabelTrans : (E.controlRow (h + d) htTransRow).label = none := by
          calc
            (E.controlRow (h + d) htTransRow).label = (E.controlRow (h + d) htPrev).label :=
              E.controlRow_label_proof_irrel _ _
            _ = none := hLabelPrev
        have hStepRaw :
            E.decodedCfg (h + d + 1) htSuccRow = E.decodedCfg (h + d) htTransRow :=
          E.transitionDecodedCfg_halted htTrans hLabelTrans
        have hStep :
            E.decodedCfg (h + (d + 1)) htSucc = E.decodedCfg (h + d) htPrev := by
          calc
            E.decodedCfg (h + (d + 1)) htSucc = E.decodedCfg (h + d + 1) htSuccRow :=
              E.decodedCfg_eq_of_time_eq htSucc htSuccRow (by omega)
            _ = E.decodedCfg (h + d) htTransRow := hStepRaw
            _ = E.decodedCfg (h + d) htPrev := E.decodedCfg_proof_irrel _ _
        have hLabelEq :
            (E.controlRow (h + (d + 1)) htSucc).label =
              (E.controlRow (h + d) htPrev).label := by
          have hcfg := congrArg Turing.TM2.Cfg.l hStep
          simpa [decodedCfg] using hcfg
        exact ⟨hStep.trans hCfgPrev, hLabelEq.trans hLabelPrev⟩
  have hEnd := hAll (N - h) (by omega)
  have hEndTime : h + (N - h) = N := by omega
  let htEndBySub : h + (N - h) ∈ tmVerifierTableauTimeRange V p :=
    tmVerifierTableauTimeRange_mem_of_le V p (by omega)
  have hEndProof :
      E.decodedCfg (h + (N - h)) htEndBySub =
        E.decodedCfg (tmVerifierTimeBound V p)
          (tmVerifierTableauTimeRange_timeBound_mem V p) := by
    let htEndByN : N ∈ tmVerifierTableauTimeRange V p :=
      tmVerifierTableauTimeRange_mem_of_le V p (by simp [N])
    have hSub :
        E.decodedCfg (h + (N - h)) htEndBySub = E.decodedCfg N htEndByN := by
      exact E.decodedCfg_eq_of_time_eq htEndBySub htEndByN hEndTime
    exact hSub.trans (E.decodedCfg_proof_irrel _ _)
  exact (hEnd.1.symm).trans hEndProof

/-- A satisfied global fixed-micro tableau yields a true-output run of the verifier TM. -/
noncomputable def outputs_true_in_time
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a) :
    tmVerifierOutputsBoolInTime V p true := by
  classical
  let HaltedAt : Nat → Prop := fun t =>
    ∃ ht : t ∈ tmVerifierTableauTimeRange V p, (E.controlRow t ht).label = none
  have hExists : ∃ t, HaltedAt t := by
    exact
      ⟨tmVerifierTimeBound V p, tmVerifierTableauTimeRange_timeBound_mem V p,
        E.endpointControlRow_label⟩
  let h := Nat.find hExists
  have hSpec : HaltedAt h := Nat.find_spec hExists
  let hMemAny := Classical.choose hSpec
  have hLabelAny : (E.controlRow h hMemAny).label = none :=
    Classical.choose_spec hSpec
  have hLe : h ≤ tmVerifierTimeBound V p := by
    have hRange := hMemAny
    simp [tmVerifierTableauTimeRange, List.mem_range] at hRange
    omega
  let hMem := tmVerifierTableauTimeRange_mem_of_le V p hLe
  have hLabel : (E.controlRow h hMem).label = none := by
    calc
      (E.controlRow h hMem).label = (E.controlRow h hMemAny).label :=
        E.controlRow_label_proof_irrel _ _
      _ = none := hLabelAny
  have hNonhalt :
      ∀ u, u < h →
        ∃ ht : u ∈ tmVerifierTableauTimeRange V p,
          ∃ l : (tmVerifierTM V).Λ, (E.controlRow u ht).label = some l := by
    intro u hu
    have hnot : ¬ HaltedAt u := Nat.find_min hExists hu
    have huLe : u ≤ tmVerifierTimeBound V p := by omega
    let huMem := tmVerifierTableauTimeRange_mem_of_le V p huLe
    have hne : (E.controlRow u huMem).label ≠ none := by
      intro hnone
      exact hnot ⟨huMem, hnone⟩
    cases hlabel : (E.controlRow u huMem).label with
    | none => exact False.elim (hne hlabel)
    | some l => exact ⟨huMem, l, hlabel⟩
  have hRunToH :
      StateTransition.EvalsToInTime (tmVerifierTM V).step
        (E.decodedCfg 0 (tmVerifierTableauTimeRange_zero_mem V p))
        (some (E.decodedCfg h hMem)) h :=
    E.evalsToInTime_decodedCfg_of_forall_nonhalt hLe hNonhalt
  have hHaltedEndpoint :
      E.decodedCfg h hMem =
        E.decodedCfg (tmVerifierTimeBound V p)
          (tmVerifierTableauTimeRange_timeBound_mem V p) :=
    E.decodedCfg_eq_endpoint_of_halted_at hLe hLabel
  have hHaltedOutput : E.decodedCfg h hMem = tmVerifierOutputCfg V true :=
    hHaltedEndpoint.trans E.decodedCfg_endpoint_true
  have hRunOutput :
      StateTransition.EvalsToInTime (tmVerifierTM V).step
        (tmVerifierInitialCfg V p) (some (tmVerifierOutputCfg V true)) h := by
    simpa [E.decodedCfg_initial, hHaltedOutput] using hRunToH
  have hRunBound :
      StateTransition.EvalsToInTime (tmVerifierTM V).step
        (tmVerifierInitialCfg V p) (some (tmVerifierOutputCfg V true))
        (tmVerifierTimeBound V p) :=
    stateTransitionEvalsToInTime_mono hRunOutput hLe
  simpa [tmVerifierOutputsBoolInTime, tmVerifierInitialCfg, tmVerifierOutputCfg] using hRunBound

end TMVerifierGlobalTableauEvidence

namespace TMVerifierXOnlyGlobalTableauSeed

/-- A satisfied x-only global tableau seed yields a true-output run for its certificate. -/
noncomputable def outputs_true_in_time
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyGlobalTableauSeed V B x a) :
    tmVerifierOutputsBoolInTime V (x, wSeed.cert) true :=
  wSeed.globalEvidence.outputs_true_in_time

end TMVerifierXOnlyGlobalTableauSeed

end SAT
end ComplexityReduction
