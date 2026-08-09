/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.GlobalSelectedWindow

/-!
Accepted-run stack assignment over fixed-pair global micro rows.

This file starts the row-global reverse assignment needed for Cook-Levin
completeness.  Macro rows read from the accepting run; fixed micro rows decode
their `(t,micro)` payload and use the selected statement window for that macro
row.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Selected windows for accepting-run macro rows -/

noncomputable def tmVerifierRunSelectedWindowExists
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) :
    Prop :=
  ∃ l : (tmVerifierTM V).Λ, ∃ s : (tmVerifierTM V).σ,
    (tmVerifierRunCfgAt V p t).l = some l ∧
      (tmVerifierRunCfgAt V p t).var = s ∧
        ∃ w : TMVerifierStmtWindow V,
          w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s

noncomputable def tmVerifierRunSelectedWindow
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) :
    TMVerifierStmtWindow V := by
  classical
  exact match (tmVerifierRunCfgAt V p t).l with
  | some l =>
      Classical.choose
        (tmVerifierStmtWindowsAt_exists_true_actionReadGuards_topStack V p t l
          (tmVerifierRunCfgAt V p t).var)
  | none =>
    { guards := [], actions := [], nextLabel := none
      nextState := (tmVerifierRunCfgAt V p t).var }

theorem tmVerifierRunSelectedWindow_mem
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) {t : Nat}
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s) :
    tmVerifierRunSelectedWindow V p t ∈
      tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s := by
  classical
  have hspec :=
    Classical.choose_spec
      (tmVerifierStmtWindowsAt_exists_true_actionReadGuards_topStack V p t l
        (tmVerifierRunCfgAt V p t).var)
  simpa [tmVerifierRunSelectedWindow, hl, hs] using hspec.1

/-! ### Global fixed micro-row stack family -/

noncomputable def tmVerifierAcceptedRunGlobalStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k) := by
  classical
  exact fun u =>
    if h : u ≤ tmVerifierTimeBound V p then
      (tmVerifierRunCfgAt V p u).stk
    else
      let decoded := Nat.unpair (tmVerifierFixedMicroPayload V p u)
      tmVerifierWindowMicroStacks V p decoded.1
        (tmVerifierRunSelectedWindow V p decoded.1) decoded.2

theorem tmVerifierAcceptedRunGlobalStacks_at_macro
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    {u : Nat} (hu : u ≤ tmVerifierTimeBound V p) :
    tmVerifierAcceptedRunGlobalStacks V p u = (tmVerifierRunCfgAt V p u).stk := by
  simp [tmVerifierAcceptedRunGlobalStacks, hu]

theorem tmVerifierAcceptedRunGlobalStacks_at_fixed_micro
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t micro : Nat) :
    tmVerifierAcceptedRunGlobalStacks V p (tmVerifierFixedMicroTime V p t micro) =
      tmVerifierWindowMicroStacks V p t (tmVerifierRunSelectedWindow V p t) micro := by
  have hnot : ¬ tmVerifierFixedMicroTime V p t micro ≤ tmVerifierTimeBound V p := by
    intro hle
    have hbase := tmVerifierFixedMicroBase_le_time V p t micro
    simp [tmVerifierFixedMicroBase] at hbase
    omega
  simp [tmVerifierAcceptedRunGlobalStacks, hnot]

/-! ### Global fixed micro-domain satisfaction -/

theorem tmVerifierAcceptedRunGlobalStacks_fixedMicro_stacksActive
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    {t : Nat} (_ht : t < tmVerifierTimeBound V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s)
    (micro : Nat) :
    tmVerifierStacksActive V
      (tmVerifierAcceptedRunGlobalStacks V p (tmVerifierFixedMicroTime V p t micro)) := by
  have hw := tmVerifierRunSelectedWindow_mem V p (t := t) hl hs
  rw [tmVerifierAcceptedRunGlobalStacks_at_fixed_micro]
  exact tmVerifierWindowMicroStacks_stacksActive V p t hw micro

theorem tmVerifierAcceptedRunGlobalStacks_fixedMicro_stacksActive_any
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t micro : Nat) :
    tmVerifierStacksActive V
      (tmVerifierAcceptedRunGlobalStacks V p (tmVerifierFixedMicroTime V p t micro)) := by
  cases hLabel : (tmVerifierRunCfgAt V p t).l with
  | none =>
      rw [tmVerifierAcceptedRunGlobalStacks_at_fixed_micro]
      simpa [tmVerifierRunSelectedWindow, hLabel, tmVerifierWindowMicroStacks,
        tmVerifierWindowActionsApplyStacks] using tmVerifierRunCfgAt_stacksActive V p t
  | some l =>
      have hw := tmVerifierRunSelectedWindow_mem V p (t := t) hLabel rfl
      rw [tmVerifierAcceptedRunGlobalStacks_at_fixed_micro]
      exact tmVerifierWindowMicroStacks_stacksActive V p t hw micro

theorem tmVerifierAcceptedRunGlobalStacks_fixedMicro_length_le
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    {t : Nat} (ht : t < tmVerifierTimeBound V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s)
    (micro : Nat) (k : tmVerifierStackIndex V) :
    (tmVerifierAcceptedRunGlobalStacks V p
        (tmVerifierFixedMicroTime V p t micro) k).length ≤
      tmVerifierCellBound V p := by
  have hw := tmVerifierRunSelectedWindow_mem V p (t := t) hl hs
  rw [tmVerifierAcceptedRunGlobalStacks_at_fixed_micro]
  exact tmVerifierWindowMicroStacks_length_le V p ht hw micro k

theorem tmVerifierAcceptedRunGlobalStacks_fixedMicro_length_le_any
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    {t : Nat} (ht : t < tmVerifierTimeBound V p)
    (micro : Nat) (k : tmVerifierStackIndex V) :
    (tmVerifierAcceptedRunGlobalStacks V p
        (tmVerifierFixedMicroTime V p t micro) k).length ≤
      tmVerifierCellBound V p := by
  cases hLabel : (tmVerifierRunCfgAt V p t).l with
  | none =>
      rw [tmVerifierAcceptedRunGlobalStacks_at_fixed_micro]
      simpa [tmVerifierRunSelectedWindow, hLabel, tmVerifierWindowMicroStacks,
        tmVerifierWindowActionsApplyStacks] using
        tmVerifierRunCfgAt_stack_length_le_cellBound V p (Nat.le_of_lt ht) k
  | some l =>
      have hw := tmVerifierRunSelectedWindow_mem V p (t := t) hLabel rfl
      rw [tmVerifierAcceptedRunGlobalStacks_at_fixed_micro]
      exact tmVerifierWindowMicroStacks_length_le V p ht hw micro k

theorem tmVerifierWindowFixedMicroDomainCNFAt_satisfies_acceptedRunGlobalStacks_any
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    {t : Nat} (ht : t < tmVerifierTimeBound V p)
    (w : TMVerifierStmtWindow V) :
    CNF.Satisfies (tmVerifierWindowFixedMicroDomainCNFAt V p t w)
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) := by
  intro c hc
  rw [tmVerifierWindowFixedMicroDomainCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨micro, _hmicro, hc⟩
  rcases List.mem_flatMap.mp hc with ⟨k, _hk, hc⟩
  exact tmVerifierStackWellFormedCNFAt_satisfies_stackFamilyAssignment V p
    (tmVerifierAcceptedRunGlobalStacks V p) (tmVerifierFixedMicroTime V p t micro) k
    (tmVerifierAcceptedRunGlobalStacks_fixedMicro_stacksActive_any V p t micro)
    (tmVerifierAcceptedRunGlobalStacks_fixedMicro_length_le_any V p ht micro k) c hc

theorem tmVerifierWindowFixedMicroDomainCNFAt_satisfies_acceptedRunGlobalStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    {t : Nat} (ht : t < tmVerifierTimeBound V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    (_hl : (tmVerifierRunCfgAt V p t).l = some l)
    (_hs : (tmVerifierRunCfgAt V p t).var = s)
    (w : TMVerifierStmtWindow V) :
    CNF.Satisfies (tmVerifierWindowFixedMicroDomainCNFAt V p t w)
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) := by
  exact tmVerifierWindowFixedMicroDomainCNFAt_satisfies_acceptedRunGlobalStacks_any
    V p ht w

theorem tmVerifierTransitionFixedMicroDomainCNFAt_satisfies_acceptedRunGlobalStacks_any
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    {t : Nat} (ht : t < tmVerifierTimeBound V p) :
    CNF.Satisfies (tmVerifierTransitionFixedMicroDomainCNFAt V p t)
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) := by
  intro c hc
  rw [tmVerifierTransitionFixedMicroDomainCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨l', _hl', hc⟩
  rcases List.mem_flatMap.mp hc with ⟨s', _hs', hc⟩
  rcases List.mem_flatMap.mp hc with ⟨w, _hw, hc⟩
  exact tmVerifierWindowFixedMicroDomainCNFAt_satisfies_acceptedRunGlobalStacks_any V p
    ht w c hc

theorem tmVerifierTransitionFixedMicroDomainCNFAt_satisfies_acceptedRunGlobalStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    {t : Nat} (ht : t < tmVerifierTimeBound V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    (_hl : (tmVerifierRunCfgAt V p t).l = some l)
    (_hs : (tmVerifierRunCfgAt V p t).var = s) :
    CNF.Satisfies (tmVerifierTransitionFixedMicroDomainCNFAt V p t)
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) :=
  tmVerifierTransitionFixedMicroDomainCNFAt_satisfies_acceptedRunGlobalStacks_any V p ht

theorem tmVerifierTransitionFixedMicroDomainRowsCNF_satisfies_acceptedRunGlobalStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    CNF.Satisfies (tmVerifierTransitionFixedMicroDomainRowsCNF V p)
      (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) := by
  intro c hc
  rw [tmVerifierTransitionFixedMicroDomainRowsCNF] at hc
  rcases List.mem_flatMap.mp hc with ⟨t, ht, hc⟩
  have htLt : t < tmVerifierTimeBound V p := by
    simpa [tmVerifierTransitionTimeRange, List.mem_range] using ht
  exact tmVerifierTransitionFixedMicroDomainCNFAt_satisfies_acceptedRunGlobalStacks_any
    V p htLt c hc

end SAT
end ComplexityReduction
