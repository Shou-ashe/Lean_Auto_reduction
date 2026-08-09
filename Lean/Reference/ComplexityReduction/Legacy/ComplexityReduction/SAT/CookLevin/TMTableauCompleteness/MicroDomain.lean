/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.StackFamily

namespace ComplexityReduction
namespace SAT

/-! ### Concrete statement-window micro-row assignment -/

noncomputable def tmVerifierWindowMicroStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) (micro : Nat) :
    ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k) :=
  tmVerifierWindowActionsApplyStacks (w.actions.take micro) (tmVerifierRunCfgAt V p t).stk

noncomputable def tmVerifierWindowMicroStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) (micro : Nat) : Assignment :=
  tmVerifierConcreteStackAssignment V p (tmVerifierMicroTime t micro)
    (tmVerifierWindowMicroStacks V p t w micro)

theorem tmVerifierWindowMicroStacks_stacksActive
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (micro : Nat) :
    tmVerifierStacksActive V (tmVerifierWindowMicroStacks V p t w micro) := by
  unfold tmVerifierWindowMicroStacks
  exact tmVerifierWindowActionsApplyStacks_stacksActive (w.actions.take micro)
    (tmVerifierRunCfgAt_stacksActive V p t) (by
      intro act hact
      have hmem : act ∈ w.actions := by
        exact (List.take_sublist micro w.actions).subset hact
      have hAll :=
        tmVerifierStmtWindowsAt_actions_pushSymbolMem_of_stmt V t ((tmVerifierTM V).m l)
          s hw (fun sym hsym => tmVerifierControlPushSymbols_label_mem V l sym hsym)
      exact hAll act hmem)

theorem tmVerifierWindowMicroStacks_length_le
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    {t : Nat} (ht : t < tmVerifierTimeBound V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (micro : Nat) (k : tmVerifierStackIndex V) :
    (tmVerifierWindowMicroStacks V p t w micro k).length ≤
      tmVerifierCellBound V p := by
  have hStart :=
    tmVerifierRunCfgAt_stack_length_le_input_prefix_output_slack V p t k
  have hTrace :=
    tmVerifierWindowActionsApplyStacks_length_le (w.actions.take micro)
      (tmVerifierRunCfgAt V p t).stk k
  have hTake :=
    tmVerifierStackActionsPushCount_take_le w.actions micro
  have hWindow :=
    tmVerifierStmtWindowsAt_actions_pushCount_le_stmtPushCount V t ((tmVerifierTM V).m l) s hw
  have hStmtBound :
      tmVerifierStackActionsPushCount (w.actions.take micro) ≤
        TM2Programs.finTM2StepPushBound (tmVerifierTM V) :=
    hTake.trans
      (hWindow.trans (TM2Programs.stmtPushCount_le_finTM2StepPushBound (tmVerifierTM V) l))
  have htSucc : t + 1 ≤ tmVerifierTimeBound V p := Nat.succ_le_of_lt ht
  have hTimeMul :
      (t + 1) * TM2Programs.finTM2StepPushBound (tmVerifierTM V) ≤
        tmVerifierTimeBound V p * TM2Programs.finTM2StepPushBound (tmVerifierTM V) :=
    Nat.mul_le_mul_right _ htSucc
  calc
    (tmVerifierWindowMicroStacks V p t w micro k).length
        ≤ ((tmVerifierRunCfgAt V p t).stk k).length +
            tmVerifierStackActionsPushCount (w.actions.take micro) := by
          simpa [tmVerifierWindowMicroStacks] using hTrace
    _ ≤ ((tmVerifierInputWord V p).length +
            t * TM2Programs.finTM2StepPushBound (tmVerifierTM V) +
            (tmVerifierBoolOutputWord V true).length + 1) +
            TM2Programs.finTM2StepPushBound (tmVerifierTM V) := by
          exact Nat.add_le_add hStart hStmtBound
    _ ≤ tmVerifierCellBound V p := by
          rw [show
              ((tmVerifierInputWord V p).length +
                    t * TM2Programs.finTM2StepPushBound (tmVerifierTM V) +
                    (tmVerifierBoolOutputWord V true).length + 1) +
                  TM2Programs.finTM2StepPushBound (tmVerifierTM V) =
                (tmVerifierInputWord V p).length +
                  (t + 1) * TM2Programs.finTM2StepPushBound (tmVerifierTM V) +
                  (tmVerifierBoolOutputWord V true).length + 1 by
            rw [Nat.add_mul, one_mul]
            omega]
          simp [tmVerifierCellBound]
          omega

theorem tmVerifierStackWellFormedCNFAt_satisfies_windowMicroStackAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    {t : Nat} (ht : t < tmVerifierTimeBound V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (micro : Nat) (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t micro) k)
      (tmVerifierWindowMicroStackAssignment V p t w micro) := by
  simpa [tmVerifierWindowMicroStackAssignment] using
    tmVerifierStackWellFormedCNFAt_satisfies_concreteStackAssignment V p
      (tmVerifierMicroTime t micro) (tmVerifierWindowMicroStacks V p t w micro)
      (tmVerifierWindowMicroStacks_stacksActive V p t hw micro) k
      (tmVerifierWindowMicroStacks_length_le V p ht hw micro k)

noncomputable def tmVerifierWindowMicroStackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) : Assignment :=
  tmVerifierStackFamilyAssignment V p fun u =>
    tmVerifierWindowMicroStacks V p t w ((Nat.unpair u).2)

theorem tmVerifierStackWellFormedCNFAt_satisfies_windowMicroStackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    {t : Nat} (ht : t < tmVerifierTimeBound V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (micro : Nat) (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t micro) k)
      (tmVerifierWindowMicroStackFamilyAssignment V p t w) := by
  have hUnpair : (Nat.unpair (tmVerifierMicroTime t micro)).2 = micro := by
    simp
  simpa [tmVerifierWindowMicroStackFamilyAssignment, hUnpair] using
    tmVerifierStackWellFormedCNFAt_satisfies_stackFamilyAssignment V p
      (fun u => tmVerifierWindowMicroStacks V p t w ((Nat.unpair u).2))
      (tmVerifierMicroTime t micro) k
      (by simpa [hUnpair] using tmVerifierWindowMicroStacks_stacksActive V p t hw micro)
      (by simpa [hUnpair] using tmVerifierWindowMicroStacks_length_le V p ht hw micro k)

theorem tmVerifierWindowMicroDomainCNFAt_satisfies_windowMicroStackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    {t : Nat} (ht : t < tmVerifierTimeBound V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    CNF.Satisfies (tmVerifierWindowMicroDomainCNFAt V p t w)
      (tmVerifierWindowMicroStackFamilyAssignment V p t w) := by
  intro c hc
  rw [tmVerifierWindowMicroDomainCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨micro, _hmicro, hc⟩
  rcases List.mem_flatMap.mp hc with ⟨k, _hk, hc⟩
  exact tmVerifierStackWellFormedCNFAt_satisfies_windowMicroStackFamilyAssignment V p ht hw
    micro k c hc

theorem tmVerifierWindowMicroDomainCNFAt_satisfies_stackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    {t : Nat} (_ht : t < tmVerifierTimeBound V p)
    (w : TMVerifierStmtWindow V)
    (hActive :
      ∀ micro ∈ tmVerifierWindowMicroTimeRange V w,
        tmVerifierStacksActive V (stkAt (tmVerifierMicroTime t micro)))
    (hlen :
      ∀ micro ∈ tmVerifierWindowMicroTimeRange V w,
        ∀ k : tmVerifierStackIndex V,
          (stkAt (tmVerifierMicroTime t micro) k).length ≤ tmVerifierCellBound V p) :
    CNF.Satisfies (tmVerifierWindowMicroDomainCNFAt V p t w)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro c hc
  rw [tmVerifierWindowMicroDomainCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨micro, hmicro, hc⟩
  rcases List.mem_flatMap.mp hc with ⟨k, _hk, hc⟩
  exact tmVerifierStackWellFormedCNFAt_satisfies_stackFamilyAssignment V p stkAt
    (tmVerifierMicroTime t micro) k (hActive micro hmicro) (hlen micro hmicro k) c hc

theorem tmVerifierTransitionMicroDomainCNFAt_satisfies_stackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    {t : Nat} (ht : t < tmVerifierTimeBound V p)
    (hActive :
      ∀ l ∈ tmVerifierLabelList V,
        ∀ s ∈ tmVerifierStateList V,
          ∀ w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s,
            ∀ micro ∈ tmVerifierWindowMicroTimeRange V w,
              tmVerifierStacksActive V (stkAt (tmVerifierMicroTime t micro)))
    (hlen :
      ∀ l ∈ tmVerifierLabelList V,
        ∀ s ∈ tmVerifierStateList V,
          ∀ w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s,
            ∀ micro ∈ tmVerifierWindowMicroTimeRange V w,
              ∀ k : tmVerifierStackIndex V,
                (stkAt (tmVerifierMicroTime t micro) k).length ≤
                  tmVerifierCellBound V p) :
    CNF.Satisfies (tmVerifierTransitionMicroDomainCNFAt V p t)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro c hc
  rw [tmVerifierTransitionMicroDomainCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨l, hl, hc⟩
  rcases List.mem_flatMap.mp hc with ⟨s, hs, hc⟩
  rcases List.mem_flatMap.mp hc with ⟨w, hw, hc⟩
  exact tmVerifierWindowMicroDomainCNFAt_satisfies_stackFamilyAssignment V p stkAt ht w
    (fun micro hmicro => hActive l hl s hs w hw micro hmicro)
    (fun micro hmicro k => hlen l hl s hs w hw micro hmicro k) c hc

theorem tmVerifierTransitionMicroDomainRowsCNF_satisfies_stackFamilyAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hActive :
      ∀ t ∈ tmVerifierTransitionTimeRange V p,
        ∀ l ∈ tmVerifierLabelList V,
          ∀ s ∈ tmVerifierStateList V,
            ∀ w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s,
              ∀ micro ∈ tmVerifierWindowMicroTimeRange V w,
                tmVerifierStacksActive V (stkAt (tmVerifierMicroTime t micro)))
    (hlen :
      ∀ t ∈ tmVerifierTransitionTimeRange V p,
        ∀ l ∈ tmVerifierLabelList V,
          ∀ s ∈ tmVerifierStateList V,
            ∀ w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s,
              ∀ micro ∈ tmVerifierWindowMicroTimeRange V w,
                ∀ k : tmVerifierStackIndex V,
                  (stkAt (tmVerifierMicroTime t micro) k).length ≤
                    tmVerifierCellBound V p) :
    CNF.Satisfies (tmVerifierTransitionMicroDomainRowsCNF V p)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro c hc
  rw [tmVerifierTransitionMicroDomainRowsCNF] at hc
  rcases List.mem_flatMap.mp hc with ⟨t, ht, hc⟩
  have htLt : t < tmVerifierTimeBound V p := by
    simpa [tmVerifierTransitionTimeRange, List.mem_range] using ht
  exact tmVerifierTransitionMicroDomainCNFAt_satisfies_stackFamilyAssignment V p stkAt htLt
    (fun l hl s hs w hw micro hmicro => hActive t ht l hl s hs w hw micro hmicro)
    (fun l hl s hs w hw micro hmicro k => hlen t ht l hl s hs w hw micro hmicro k) c hc

end SAT
end ComplexityReduction
