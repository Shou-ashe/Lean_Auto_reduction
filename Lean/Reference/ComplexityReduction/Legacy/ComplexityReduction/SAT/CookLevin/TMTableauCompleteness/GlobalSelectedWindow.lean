/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.GlobalMicro
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.TransitionRows

/-!
Selected-window completeness helpers for fixed-pair global micro rows.

This file mirrors the local selected-window stack-family lemmas from
`TransitionRows`, but names all action micro rows with
`tmVerifierFixedMicroTime V p t micro`.
-/

namespace ComplexityReduction
namespace SAT

theorem TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_times_stack_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt₁ stkAt₂ :
      Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (time₁ time₂ : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k)
    (hStack : stkAt₁ time₁ k = stkAt₂ time₂ k) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) time₁ cell choice).eval
        (tmVerifierStackFamilyAssignment V p stkAt₁) =
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) time₂ cell choice).eval
        (tmVerifierStackFamilyAssignment V p stkAt₂) := by
  cases choice with
  | empty =>
      by_cases hcell₁ : cell < (stkAt₁ time₁ k).length
      · have hcell₂ : cell < (stkAt₂ time₂ k).length := by
          simpa [hStack] using hcell₁
        simp [TMVerifierStackReadChoice.atomAt,
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_selected V p stkAt₁
            time₁ k hcell₁,
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_selected V p stkAt₂
            time₂ k hcell₂]
      · have hcell₂ : ¬ cell < (stkAt₂ time₂ k).length := by
          simpa [hStack] using hcell₁
        simp [TMVerifierStackReadChoice.atomAt,
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt₁
            (u := time₁) (j := k) (cell := cell) hcell₁,
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt₂
            (u := time₂) (j := k) (cell := cell) hcell₂]
  | symbol payload symbol =>
      by_cases hcell₁ : cell < (stkAt₁ time₁ k).length
      · have hcell₂ : cell < (stkAt₂ time₂ k).length := by
          simpa [hStack] using hcell₁
        have hget :
            ((stkAt₂ time₂ k)[cell]'hcell₂) = ((stkAt₁ time₁ k)[cell]'hcell₁) := by
          simp [hStack]
        by_cases hp :
            payload = tmVerifierActiveStackSymbolPayload V k ((stkAt₁ time₁ k)[cell]'hcell₁)
        · have hp₂ :
            payload =
              tmVerifierActiveStackSymbolPayload V k ((stkAt₂ time₂ k)[cell]'hcell₂) := by
            simpa [hget] using hp
          simp [TMVerifierStackReadChoice.atomAt,
            tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_selected_payload V p stkAt₁
              time₁ k hcell₁ hp,
            tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_selected_payload V p stkAt₂
              time₂ k hcell₂ hp₂]
        · have hp₂ :
            payload ≠
              tmVerifierActiveStackSymbolPayload V k ((stkAt₂ time₂ k)[cell]'hcell₂) := by
            simpa [hget] using hp
          simp [TMVerifierStackReadChoice.atomAt,
            tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_selected_ne_payload V p
              stkAt₁ time₁ k hcell₁ hp,
            tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_selected_ne_payload V p
              stkAt₂ time₂ k hcell₂ hp₂]
      · have hcell₂ : ¬ cell < (stkAt₂ time₂ k).length := by
          simpa [hStack] using hcell₁
        simp [TMVerifierStackReadChoice.atomAt,
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt₁
            (u := time₁) (j := k) (cell := cell) (payload := payload) hcell₁,
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt₂
            (u := time₂) (j := k) (cell := cell) (payload := payload) hcell₂]

/-! ### Single selected-window stack family over global micro rows -/

noncomputable def tmVerifierSelectedWindowFixedRunStacks
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) :
    Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k) :=
  fun u =>
    if u = t then
      (tmVerifierRunCfgAt V p t).stk
    else if u = t + 1 then
      (tmVerifierRunCfgAt V p (t + 1)).stk
    else
      tmVerifierWindowMicroStacks V p t w
        ((Nat.unpair (tmVerifierFixedMicroPayload V p u)).2)

theorem tmVerifierSelectedWindowFixedRunStacks_at_start
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) :
    tmVerifierSelectedWindowFixedRunStacks V p t w t = (tmVerifierRunCfgAt V p t).stk := by
  simp [tmVerifierSelectedWindowFixedRunStacks]

theorem tmVerifierSelectedWindowFixedRunStacks_at_succ
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) :
    tmVerifierSelectedWindowFixedRunStacks V p t w (t + 1) =
      (tmVerifierRunCfgAt V p (t + 1)).stk := by
  by_cases hEq : t + 1 = t
  · omega
  · simp [tmVerifierSelectedWindowFixedRunStacks]

theorem tmVerifierSelectedWindowFixedRunStacks_at_micro
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    {t : Nat} (ht : t < tmVerifierTimeBound V p)
    (w : TMVerifierStmtWindow V) (micro : Nat) :
    tmVerifierSelectedWindowFixedRunStacks V p t w
        (tmVerifierFixedMicroTime V p t micro) =
      tmVerifierWindowMicroStacks V p t w micro := by
  have hNeStart :
      tmVerifierFixedMicroTime V p t micro ≠ t :=
    tmVerifierFixedMicroTime_ne_macro V p (Nat.le_of_lt ht)
  have hNeSucc :
      tmVerifierFixedMicroTime V p t micro ≠ t + 1 :=
    tmVerifierFixedMicroTime_ne_macro_succ V p ht
  simp [tmVerifierSelectedWindowFixedRunStacks, hNeStart, hNeSucc]

theorem tmVerifierSelectedWindowFixedRunStacks_micro_start_eq_macro
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    {t : Nat} (ht : t < tmVerifierTimeBound V p) (w : TMVerifierStmtWindow V) :
    ∀ k : tmVerifierStackIndex V,
      tmVerifierSelectedWindowFixedRunStacks V p t w
          (tmVerifierFixedMicroTime V p t 0) k =
        tmVerifierSelectedWindowFixedRunStacks V p t w t k := by
  intro k
  rw [tmVerifierSelectedWindowFixedRunStacks_at_micro V p ht w 0,
    tmVerifierSelectedWindowFixedRunStacks_at_start]
  simp [tmVerifierWindowMicroStacks, tmVerifierWindowActionsApplyStacks]

theorem tmVerifierSelectedWindowFixedRunStacks_final_eq_macro_succ
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V)
    (ht : t < tmVerifierTimeBound V p)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hMatch : tmVerifierWindowActionsMatchStacks w.actions (tmVerifierRunCfgAt V p t).stk)
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s) :
    ∀ k : tmVerifierStackIndex V,
      tmVerifierSelectedWindowFixedRunStacks V p t w (t + 1) k =
        tmVerifierSelectedWindowFixedRunStacks V p t w
          (tmVerifierFixedMicroTime V p t w.actions.length) k := by
  have hAgree :=
    tmVerifierStmtWindowsAt_stepAux_agrees V t ((tmVerifierTM V).m l) s
      (tmVerifierRunCfgAt V p t).stk hw hMatch
  have hSucc := tmVerifierRunCfgAt_succ_of_label_some V p t hl hs
  have hFinal :
      tmVerifierWindowMicroStacks V p t w w.actions.length =
        (tmVerifierRunCfgAt V p (t + 1)).stk := by
    rw [tmVerifierWindowMicroStacks]
    calc
      tmVerifierWindowActionsApplyStacks (w.actions.take w.actions.length)
          (tmVerifierRunCfgAt V p t).stk =
          tmVerifierWindowActionsApplyStacks w.actions (tmVerifierRunCfgAt V p t).stk := by
            rw [List.take_length]
      _ = (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
          (tmVerifierRunCfgAt V p t).stk).stk := hAgree.2.2
      _ = (tmVerifierRunCfgAt V p (t + 1)).stk := by rw [hSucc]
  intro k
  rw [tmVerifierSelectedWindowFixedRunStacks_at_succ,
    tmVerifierSelectedWindowFixedRunStacks_at_micro V p ht w w.actions.length]
  exact congrFun hFinal.symm k

/-! ### Fixed selected-window boundary and action satisfaction -/

theorem tmVerifierWindowFixedStackBoundaryCNFAt_satisfies_stackFamilyAssignment_of_stack_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hStart :
      ∀ k : tmVerifierStackIndex V,
        stkAt (tmVerifierFixedMicroTime V p t 0) k = stkAt t k)
    (hFinal :
      ∀ k : tmVerifierStackIndex V,
        stkAt (t + 1) k =
          stkAt (tmVerifierFixedMicroTime V p t w.actions.length) k) :
    CNF.Satisfies (tmVerifierWindowFixedStackBoundaryCNFAt V p t l s w)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  rw [tmVerifierWindowFixedStackBoundaryCNFAt, CNF.satisfies_append]
  constructor
  · exact tmVerifierFrameAllStacksCNFBetween_satisfies_of_eval_eq V p t
      (tmVerifierFixedMicroTime V p t 0)
      (tmVerifierWindowFixedAntecedents V p t l s w)
      (tmVerifierStackFamilyAssignment V p stkAt) (by
        intro k _hk cell _hcell choice _hchoice
        exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
          V p stkAt t (tmVerifierFixedMicroTime V p t 0) k cell choice (hStart k))
  · exact tmVerifierFrameAllStacksCNFBetween_satisfies_of_eval_eq V p
      (tmVerifierFixedMicroTime V p t w.actions.length) (t + 1)
      (tmVerifierWindowFixedAntecedents V p t l s w)
      (tmVerifierStackFamilyAssignment V p stkAt) (by
        intro k _hk cell _hcell choice _hchoice
        exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
          V p stkAt (tmVerifierFixedMicroTime V p t w.actions.length) (t + 1) k
          cell choice (hFinal k))

theorem tmVerifierSelectedWindowFixedRunStacks_boundary_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V)
    (ht : t < tmVerifierTimeBound V p)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hMatch : tmVerifierWindowActionsMatchStacks w.actions (tmVerifierRunCfgAt V p t).stk)
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s) :
    CNF.Satisfies (tmVerifierWindowFixedStackBoundaryCNFAt V p t l s w)
      (tmVerifierStackFamilyAssignment V p
        (tmVerifierSelectedWindowFixedRunStacks V p t w)) := by
  exact
    tmVerifierWindowFixedStackBoundaryCNFAt_satisfies_stackFamilyAssignment_of_stack_eq V p
      t l s w (tmVerifierSelectedWindowFixedRunStacks V p t w)
      (tmVerifierSelectedWindowFixedRunStacks_micro_start_eq_macro V p ht w)
      (tmVerifierSelectedWindowFixedRunStacks_final_eq_macro_succ V p t l s w ht hw hMatch
        hl hs)

theorem TMVerifierStackActionReadAtomTrue.of_fixedReadGuardAt_true
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {p : L.Instance.Carrier × V.Cert.Carrier}
    {t actionIdx : Nat} {act : TMVerifierStackAction V} {a : Assignment}
    (hGuards : ∀ g ∈ act.fixedReadGuardAt p t actionIdx, g.eval a = true) :
    TMVerifierStackActionReadAtomTrue (tmVerifierFixedMicroTime V p t actionIdx) a act := by
  cases act with
  | push raw =>
      simp [TMVerifierStackActionReadAtomTrue]
  | peek k choice =>
      exact hGuards
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
          (tmVerifierFixedMicroTime V p t actionIdx) 0 choice)
        (by simp [TMVerifierStackAction.fixedReadGuardAt])
  | pop k choice =>
      exact hGuards
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
          (tmVerifierFixedMicroTime V p t actionIdx) 0 choice)
        (by simp [TMVerifierStackAction.fixedReadGuardAt])
  | load =>
      simp [TMVerifierStackActionReadAtomTrue]
  | branch tag =>
      simp [TMVerifierStackActionReadAtomTrue]

theorem tmVerifierWindowFixedStackActionCNFAt_satisfies_active_applyStacks_of_readGuards_stkAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (antecedents : List Literal)
    (hStack :
      ∀ micro : Nat,
        stkAt (tmVerifierFixedMicroTime V p t micro) =
          tmVerifierWindowMicroStacks V p t w micro)
    (hGuards :
      ∀ g ∈ tmVerifierWindowFixedActionReadGuards p t w,
        g.eval (tmVerifierStackFamilyAssignment V p stkAt) = true) :
    CNF.Satisfies
      (tmVerifierWindowFixedStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
        p t w antecedents)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro c hc
  rw [tmVerifierWindowFixedStackActionCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨entry, hentry, hc⟩
  have hApplyBase :=
    tmVerifierWindowMicroStacks_apply_succ_of_zipIdx_mem V p t w entry hentry
  have hApply :
      stkAt (tmVerifierFixedMicroTime V p t (entry.2 + 1)) =
        tmVerifierStackActionApplyStacks entry.1
          (stkAt (tmVerifierFixedMicroTime V p t entry.2)) := by
    rw [hStack (entry.2 + 1), hStack entry.2]
    exact hApplyBase
  have hAction :=
    tmVerifierStackActionCNFBetween_satisfies_active_applyStacks V p stkAt
      (tmVerifierFixedMicroTime V p t entry.2)
      (tmVerifierFixedMicroTime V p t (entry.2 + 1))
      antecedents entry.1 hApply
      (TMVerifierStackActionReadAtomTrue.of_fixedReadGuardAt_true (by
        intro g hg
        exact hGuards g (by
          rw [tmVerifierWindowFixedActionReadGuards, tmVerifierWindowFixedActionReadGuardsFrom]
          exact List.mem_flatMap.mpr ⟨entry, hentry, hg⟩)))
  exact hAction c hc

theorem tmVerifierSelectedWindowFixedRunStacks_actionCNF_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V)
    (ht : t < tmVerifierTimeBound V p)
    (antecedents : List Literal)
    (hGuards :
      ∀ g ∈ tmVerifierWindowFixedActionReadGuards p t w,
        g.eval
          (tmVerifierStackFamilyAssignment V p
            (tmVerifierSelectedWindowFixedRunStacks V p t w)) = true) :
    CNF.Satisfies
      (tmVerifierWindowFixedStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
        p t w antecedents)
      (tmVerifierStackFamilyAssignment V p
        (tmVerifierSelectedWindowFixedRunStacks V p t w)) := by
  exact
    tmVerifierWindowFixedStackActionCNFAt_satisfies_active_applyStacks_of_readGuards_stkAt
      V p t w (tmVerifierSelectedWindowFixedRunStacks V p t w) antecedents
      (fun micro => tmVerifierSelectedWindowFixedRunStacks_at_micro V p ht w micro)
      hGuards

theorem tmVerifierSelectedWindowFixedRunStacks_transitionWindow_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V)
    (ht : t < tmVerifierTimeBound V p)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hMatch : tmVerifierWindowActionsMatchStacks w.actions (tmVerifierRunCfgAt V p t).stk)
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s)
    (hGuards :
      ∀ g ∈ tmVerifierWindowFixedActionReadGuards p t w,
        g.eval
          (tmVerifierStackFamilyAssignment V p
            (tmVerifierSelectedWindowFixedRunStacks V p t w)) = true) :
    CNF.Satisfies
      (tmVerifierWindowFixedControlCNFAt V p t l s w ++
        tmVerifierWindowFixedStackBoundaryCNFAt V p t l s w ++
          tmVerifierWindowFixedStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
            p t w (tmVerifierWindowFixedAntecedents V p t l s w))
      (tmVerifierStackFamilyAssignment V p
        (tmVerifierSelectedWindowFixedRunStacks V p t w)) := by
  rw [CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    constructor
    · intro clause hclause
      have hAgree :=
        tmVerifierStmtWindowsAt_stepAux_agrees V t ((tmVerifierTM V).m l) s
          (tmVerifierRunCfgAt V p t).stk hw hMatch
      have hSucc := tmVerifierRunCfgAt_succ_of_label_some V p t hl hs
      have hNextLabel :
          w.nextLabel = (tmVerifierRunCfgAt V p (t + 1)).l := by
        rw [hAgree.1, hSucc]
      have hNextState :
          w.nextState = (tmVerifierRunCfgAt V p (t + 1)).var := by
        rw [hAgree.2.1, hSucc]
      have hClause :
          clause =
              tmVerifierImplicationClause (tmVerifierWindowFixedAntecedents V p t l s w)
                (tmVerifierLabelAtom V (t + 1) w.nextLabel) ∨
            clause =
              tmVerifierImplicationClause (tmVerifierWindowFixedAntecedents V p t l s w)
                (tmVerifierStateAtom V (t + 1) w.nextState) := by
        simpa [tmVerifierWindowFixedControlCNFAt] using hclause
      rcases hClause with rfl | rfl
      · exact tmVerifierImplicationClause_satisfies_of_conclusion
          (tmVerifierWindowFixedAntecedents V p t l s w)
          (tmVerifierLabelAtom V (t + 1) w.nextLabel)
          (tmVerifierStackFamilyAssignment V p
            (tmVerifierSelectedWindowFixedRunStacks V p t w)) (by
            rw [tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary]
            rw [tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff]
            exact hNextLabel)
      · exact tmVerifierImplicationClause_satisfies_of_conclusion
          (tmVerifierWindowFixedAntecedents V p t l s w)
          (tmVerifierStateAtom V (t + 1) w.nextState)
          (tmVerifierStackFamilyAssignment V p
            (tmVerifierSelectedWindowFixedRunStacks V p t w)) (by
            rw [tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary]
            rw [tmVerifierStateAtom_eval_controlBoundaryAssignment_iff]
            exact hNextState)
    · exact tmVerifierSelectedWindowFixedRunStacks_boundary_satisfies V p t l s w
        ht hw hMatch hl hs
  · exact tmVerifierSelectedWindowFixedRunStacks_actionCNF_satisfies V p t w
      ht (tmVerifierWindowFixedAntecedents V p t l s w) hGuards

theorem tmVerifierStmtWindowsAt_exists_selected_window_fixedTransitionWindow
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    {t : Nat} (ht : t < tmVerifierTimeBound V p)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s) :
    ∃ w : TMVerifierStmtWindow V,
      w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s ∧
        CNF.Satisfies
          (tmVerifierWindowFixedControlCNFAt V p t l s w ++
            tmVerifierWindowFixedStackBoundaryCNFAt V p t l s w ++
              tmVerifierWindowFixedStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
                p t w (tmVerifierWindowFixedAntecedents V p t l s w))
          (tmVerifierStackFamilyAssignment V p
            (tmVerifierSelectedWindowFixedRunStacks V p t w)) ∧
          tmVerifierWindowActionsMatchStacks w.actions (tmVerifierRunCfgAt V p t).stk := by
  rcases tmVerifierStmtWindowsAt_exists_true_actionReadGuards_topStack V p t l s with
    ⟨w, hw, hguardsMicro, hmatch⟩
  have hguardsFixed :
      ∀ g ∈ tmVerifierWindowFixedActionReadGuards p t w,
        g.eval
          (tmVerifierStackFamilyAssignment V p
            (tmVerifierSelectedWindowFixedRunStacks V p t w)) = true := by
    intro g hg
    rw [tmVerifierWindowFixedActionReadGuards, tmVerifierWindowFixedActionReadGuardsFrom]
      at hg
    rcases List.mem_flatMap.mp hg with ⟨entry, hentry, hg⟩
    rcases entry with ⟨act, idx⟩
    have hTimeStack :
        tmVerifierSelectedWindowFixedRunStacks V p t w
            (tmVerifierFixedMicroTime V p t idx) =
          tmVerifierWindowMicroStacks V p t w idx :=
      tmVerifierSelectedWindowFixedRunStacks_at_micro V p ht w idx
    let localStacks := fun u => tmVerifierWindowMicroStacks V p t w ((Nat.unpair u).2)
    cases act with
    | push raw =>
        simp [TMVerifierStackAction.fixedReadGuardAt] at hg
    | peek k choice =>
        have hg' :
            g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
              (tmVerifierFixedMicroTime V p t idx) 0 choice := by
          simpa [TMVerifierStackAction.fixedReadGuardAt] using hg
        subst g
        have hLocalGuard :
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                (tmVerifierMicroTime t idx) 0 choice).eval
              (tmVerifierStackFamilyAssignment V p localStacks) = true := by
          have hmem :
              TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                  (tmVerifierMicroTime t idx) 0 choice ∈
                tmVerifierWindowActionReadGuards t w := by
            rw [tmVerifierWindowActionReadGuards, tmVerifierWindowActionReadGuardsFrom]
            exact List.mem_flatMap.mpr ⟨(TMVerifierStackAction.peek k choice, idx),
              hentry, by simp [TMVerifierStackAction.readGuardAt]⟩
          simpa [tmVerifierWindowMicroStackFamilyAssignment, localStacks] using
            hguardsMicro _ hmem
        have hLocalStack :
            localStacks (tmVerifierMicroTime t idx) k =
              tmVerifierWindowMicroStacks V p t w idx k := by
          simp [localStacks]
        have hEvalEq :=
          TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_times_stack_eq
            V p localStacks (tmVerifierSelectedWindowFixedRunStacks V p t w)
            (tmVerifierMicroTime t idx) (tmVerifierFixedMicroTime V p t idx) k 0 choice
            ((hLocalStack.trans (congrFun hTimeStack k).symm))
        exact hEvalEq.symm.trans (by simpa [localStacks] using hLocalGuard)
    | pop k choice =>
        have hg' :
            g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
              (tmVerifierFixedMicroTime V p t idx) 0 choice := by
          simpa [TMVerifierStackAction.fixedReadGuardAt] using hg
        subst g
        have hLocalGuard :
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                (tmVerifierMicroTime t idx) 0 choice).eval
              (tmVerifierStackFamilyAssignment V p localStacks) = true := by
          have hmem :
              TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                  (tmVerifierMicroTime t idx) 0 choice ∈
                tmVerifierWindowActionReadGuards t w := by
            rw [tmVerifierWindowActionReadGuards, tmVerifierWindowActionReadGuardsFrom]
            exact List.mem_flatMap.mpr ⟨(TMVerifierStackAction.pop k choice, idx),
              hentry, by simp [TMVerifierStackAction.readGuardAt]⟩
          simpa [tmVerifierWindowMicroStackFamilyAssignment, localStacks] using
            hguardsMicro _ hmem
        have hLocalStack :
            localStacks (tmVerifierMicroTime t idx) k =
              tmVerifierWindowMicroStacks V p t w idx k := by
          simp [localStacks]
        have hEvalEq :=
          TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_times_stack_eq
            V p localStacks (tmVerifierSelectedWindowFixedRunStacks V p t w)
            (tmVerifierMicroTime t idx) (tmVerifierFixedMicroTime V p t idx) k 0 choice
            ((hLocalStack.trans (congrFun hTimeStack k).symm))
        exact hEvalEq.symm.trans (by simpa [localStacks] using hLocalGuard)
    | load =>
        simp [TMVerifierStackAction.fixedReadGuardAt] at hg
    | branch tag =>
        simp [TMVerifierStackAction.fixedReadGuardAt] at hg
  exact ⟨w, hw,
    tmVerifierSelectedWindowFixedRunStacks_transitionWindow_satisfies V p t l s w ht hw
      hmatch hl hs hguardsFixed,
    hmatch⟩

end SAT
end ComplexityReduction
