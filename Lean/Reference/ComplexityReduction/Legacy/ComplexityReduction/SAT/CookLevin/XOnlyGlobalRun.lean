/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Nat.Find
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauRun
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyGlobalStepSoundness

/-!
Raw run extraction from satisfied x-only global fixed-micro tableaux.

This layer deliberately stops at the raw decoded x-only initial configuration.
It does not interpret the arbitrary input-stack suffix as a typed certificate.
-/

namespace ComplexityReduction
namespace SAT

namespace TMVerifierXOnlyGlobalTableauEvidence

/-- Chain genuine nonhalting transition rows from time `0` to time `n`. -/
noncomputable def evalsToInTime_decodedCfg_of_forall_nonhalt
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {n : Nat} (hn : n ≤ tmVerifierXOnlyTimeBound V x)
    (hNonhalt :
      ∀ u, u < n →
        ∃ ht : u ∈ tmVerifierXOnlyTableauTimeRange V x,
          ∃ l : (tmVerifierTM V).Λ, (E.controlRow u ht).label = some l) :
    StateTransition.EvalsToInTime (tmVerifierTM V).step
      (E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x))
      (some (E.decodedCfg n (tmVerifierXOnlyTableauTimeRange_mem_of_le V x hn))) n := by
  induction n with
  | zero =>
      have hcfg :
          E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x) =
            E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_mem_of_le V x hn) :=
        E.decodedCfg_proof_irrel _ _
      simpa [hcfg] using
        StateTransition.EvalsToInTime.refl (tmVerifierTM V).step
          (E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x))
  | succ n ih =>
      have hnPrev : n ≤ tmVerifierXOnlyTimeBound V x := by omega
      have hnlt : n < tmVerifierXOnlyTimeBound V x := by omega
      have hprevNonhalt :
          ∀ u, u < n →
            ∃ ht : u ∈ tmVerifierXOnlyTableauTimeRange V x,
              ∃ l : (tmVerifierTM V).Λ, (E.controlRow u ht).label = some l := by
        intro u hu
        exact hNonhalt u (by omega)
      have hPrev := ih hnPrev hprevNonhalt
      let htAny := Classical.choose (hNonhalt n (by omega))
      let hlabelExists := Classical.choose_spec (hNonhalt n (by omega))
      let l := Classical.choose hlabelExists
      have hLabelAny : (E.controlRow n htAny).label = some l :=
        Classical.choose_spec hlabelExists
      let htTrans := tmVerifierXOnlyTransitionTimeRange_mem_of_lt V x hnlt
      let htTransRow := tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x htTrans
      let htSuccRow := tmVerifierXOnlyTransitionTimeRange_succ_mem_tableauTimeRange V x htTrans
      let htPrev := tmVerifierXOnlyTableauTimeRange_mem_of_le V x hnPrev
      let htSucc := tmVerifierXOnlyTableauTimeRange_mem_of_le V x hn
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
          (E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x))
          (E.decodedCfg n htPrev) (some (E.decodedCfg (n + 1) htSucc)) hPrev hOne
      simpa [Nat.add_comm] using hAll

/-- A halted x-only row is identified with the true-output endpoint by stutter clauses. -/
theorem decodedCfg_eq_endpoint_of_halted_at
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a)
    {h : Nat} (hh : h ≤ tmVerifierXOnlyTimeBound V x)
    (hLabel :
      (E.controlRow h (tmVerifierXOnlyTableauTimeRange_mem_of_le V x hh)).label = none) :
    E.decodedCfg h (tmVerifierXOnlyTableauTimeRange_mem_of_le V x hh) =
      E.decodedCfg (tmVerifierXOnlyTimeBound V x)
        (tmVerifierXOnlyTableauTimeRange_timeBound_mem V x) := by
  let N := tmVerifierXOnlyTimeBound V x
  let hMem := tmVerifierXOnlyTableauTimeRange_mem_of_le V x hh
  have hAll :
      ∀ d, (hd : h + d ≤ N) →
        E.decodedCfg (h + d)
            (tmVerifierXOnlyTableauTimeRange_mem_of_le V x (by simpa [N] using hd)) =
            E.decodedCfg h hMem ∧
          (E.controlRow (h + d)
              (tmVerifierXOnlyTableauTimeRange_mem_of_le V x (by simpa [N] using hd))).label =
            none := by
    intro d hd
    induction d with
    | zero =>
        constructor
        · exact E.decodedCfg_proof_irrel _ _
        · calc
            (E.controlRow h
                (tmVerifierXOnlyTableauTimeRange_mem_of_le V x (by omega))).label =
                (E.controlRow h hMem).label := E.controlRow_label_proof_irrel _ _
            _ = none := hLabel
    | succ d ih =>
        have hdPrev : h + d ≤ N := by omega
        have hdltN : h + d < N := by omega
        let htPrev : h + d ∈ tmVerifierXOnlyTableauTimeRange V x :=
          tmVerifierXOnlyTableauTimeRange_mem_of_le V x (by omega)
        let htSucc : h + (d + 1) ∈ tmVerifierXOnlyTableauTimeRange V x :=
          tmVerifierXOnlyTableauTimeRange_mem_of_le V x (by omega)
        rcases ih hdPrev with ⟨hCfgPrev, hLabelPrev⟩
        let htTrans := tmVerifierXOnlyTransitionTimeRange_mem_of_lt V x (by
          simpa [N] using hdltN)
        let htTransRow := tmVerifierXOnlyTransitionTimeRange_mem_tableauTimeRange V x htTrans
        let htSuccRow := tmVerifierXOnlyTransitionTimeRange_succ_mem_tableauTimeRange V x htTrans
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
  let htEndBySub : h + (N - h) ∈ tmVerifierXOnlyTableauTimeRange V x :=
    tmVerifierXOnlyTableauTimeRange_mem_of_le V x (by omega)
  have hEndProof :
      E.decodedCfg (h + (N - h)) htEndBySub =
        E.decodedCfg (tmVerifierXOnlyTimeBound V x)
          (tmVerifierXOnlyTableauTimeRange_timeBound_mem V x) := by
    let htEndByN : N ∈ tmVerifierXOnlyTableauTimeRange V x :=
      tmVerifierXOnlyTableauTimeRange_mem_of_le V x (by simp [N])
    have hSub :
        E.decodedCfg (h + (N - h)) htEndBySub = E.decodedCfg N htEndByN := by
      exact E.decodedCfg_eq_of_time_eq htEndBySub htEndByN hEndTime
    exact hSub.trans (E.decodedCfg_proof_irrel _ _)
  exact (hEnd.1.symm).trans hEndProof

/-- A satisfied x-only global tableau yields a raw true-output run from its decoded start. -/
noncomputable def rawOutputsTrueInTime
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (E : TMVerifierXOnlyGlobalTableauEvidence V B x a) :
    StateTransition.EvalsToInTime (tmVerifierTM V).step
      (E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x))
      (some (tmVerifierOutputCfg V true)) (tmVerifierXOnlyTimeBound V x) := by
  classical
  let HaltedAt : Nat → Prop := fun t =>
    ∃ ht : t ∈ tmVerifierXOnlyTableauTimeRange V x, (E.controlRow t ht).label = none
  have hExists : ∃ t, HaltedAt t := by
    exact
      ⟨tmVerifierXOnlyTimeBound V x, tmVerifierXOnlyTableauTimeRange_timeBound_mem V x,
        E.endpointControlRow_label⟩
  let h := Nat.find hExists
  have hSpec : HaltedAt h := Nat.find_spec hExists
  let hMemAny := Classical.choose hSpec
  have hLabelAny : (E.controlRow h hMemAny).label = none :=
    Classical.choose_spec hSpec
  have hLe : h ≤ tmVerifierXOnlyTimeBound V x := by
    have hRange := hMemAny
    simp [tmVerifierXOnlyTableauTimeRange, List.mem_range] at hRange
    omega
  let hMem := tmVerifierXOnlyTableauTimeRange_mem_of_le V x hLe
  have hLabel : (E.controlRow h hMem).label = none := by
    calc
      (E.controlRow h hMem).label = (E.controlRow h hMemAny).label :=
        E.controlRow_label_proof_irrel _ _
      _ = none := hLabelAny
  have hNonhalt :
      ∀ u, u < h →
        ∃ ht : u ∈ tmVerifierXOnlyTableauTimeRange V x,
          ∃ l : (tmVerifierTM V).Λ, (E.controlRow u ht).label = some l := by
    intro u hu
    have hnot : ¬ HaltedAt u := Nat.find_min hExists hu
    have huLe : u ≤ tmVerifierXOnlyTimeBound V x := by omega
    let huMem := tmVerifierXOnlyTableauTimeRange_mem_of_le V x huLe
    have hne : (E.controlRow u huMem).label ≠ none := by
      intro hnone
      exact hnot ⟨huMem, hnone⟩
    cases hlabel : (E.controlRow u huMem).label with
    | none => exact False.elim (hne hlabel)
    | some l => exact ⟨huMem, l, hlabel⟩
  have hRunToH :
      StateTransition.EvalsToInTime (tmVerifierTM V).step
        (E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x))
        (some (E.decodedCfg h hMem)) h :=
    E.evalsToInTime_decodedCfg_of_forall_nonhalt hLe hNonhalt
  have hHaltedEndpoint :
      E.decodedCfg h hMem =
        E.decodedCfg (tmVerifierXOnlyTimeBound V x)
          (tmVerifierXOnlyTableauTimeRange_timeBound_mem V x) :=
    E.decodedCfg_eq_endpoint_of_halted_at hLe hLabel
  have hHaltedOutput : E.decodedCfg h hMem = tmVerifierOutputCfg V true :=
    hHaltedEndpoint.trans E.decodedCfg_endpoint_true
  have hRunOutput :
      StateTransition.EvalsToInTime (tmVerifierTM V).step
        (E.decodedCfg 0 (tmVerifierXOnlyTableauTimeRange_zero_mem V x))
        (some (tmVerifierOutputCfg V true)) h := by
    simpa [hHaltedOutput] using hRunToH
  exact stateTransitionEvalsToInTime_mono hRunOutput hLe

end TMVerifierXOnlyGlobalTableauEvidence

end SAT
end ComplexityReduction
