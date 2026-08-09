/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyWindowUniqueness

/-!
Aggregate accepted-run satisfaction for the x-only Cook-Levin tableau.
-/

namespace ComplexityReduction
namespace SAT

theorem tmVerifierXOnlyTransitionFixedWindowStackCNFAt_satisfies_current_label_state
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hl : (tmVerifierRunCfgAt V (x, c) t).l = some l)
    (hs : (tmVerifierRunCfgAt V (x, c) t).var = s)
    (hCurrent :
      ∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies
            (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V x t l s w ++
              tmVerifierXOnlyWindowFixedStackActionCNFAt V B x t w
                (tmVerifierXOnlyWindowFixedAntecedents V x t l s w))
            (tmVerifierStackFamilyAssignment V (x, c) stkAt)) :
    CNF.Satisfies (tmVerifierXOnlyTransitionFixedWindowStackCNFAt V B x t)
      (tmVerifierStackFamilyAssignment V (x, c) stkAt) := by
  intro clause hclause
  rw [tmVerifierXOnlyTransitionFixedWindowStackCNFAt] at hclause
  rcases List.mem_flatMap.mp hclause with ⟨l', _hl', hclause⟩
  rcases List.mem_flatMap.mp hclause with ⟨s', _hs', hclause⟩
  rcases List.mem_flatMap.mp hclause with ⟨w, hw, hclause⟩
  by_cases hLabelEq : l' = l
  · subst l'
    by_cases hStateEq : s' = s
    · subst s'
      exact hCurrent w hw clause hclause
    · have hFalse :
        (tmVerifierStateAtom V t s').eval
            (tmVerifierStackFamilyAssignment V (x, c) stkAt) = false := by
        exact tmVerifierStateAtom_eval_stackFamilyAssignment_false_of_ne V (x, c) stkAt t s'
          (by
            intro h
            exact hStateEq (by simpa [hs] using h))
      exact tmVerifierXOnlyWindowFixedStackCNF_satisfies_of_false_antecedent V B x t
        l s' w (tmVerifierStackFamilyAssignment V (x, c) stkAt)
        (tmVerifierXOnlyWindowFixedAntecedents_state_mem V x t l s' w) hFalse clause
        hclause
  · have hFalse :
      (tmVerifierLabelAtom V t (some l')).eval
          (tmVerifierStackFamilyAssignment V (x, c) stkAt) = false := by
      exact tmVerifierLabelAtom_eval_stackFamilyAssignment_false_of_ne V (x, c) stkAt t
        (some l') (by
          intro h
          exact hLabelEq (Option.some.inj (by simpa [hl] using h)))
    exact tmVerifierXOnlyWindowFixedStackCNF_satisfies_of_false_antecedent V B x t
      l' s' w (tmVerifierStackFamilyAssignment V (x, c) stkAt)
      (tmVerifierXOnlyWindowFixedAntecedents_label_mem V x t l' s' w) hFalse clause
      hclause

theorem tmVerifierXOnlyTransitionFixedControlCNFAt_satisfies_current_label_state
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hl : (tmVerifierRunCfgAt V (x, c) t).l = some l)
    (hs : (tmVerifierRunCfgAt V (x, c) t).var = s)
    (hCurrent :
      ∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies (tmVerifierXOnlyWindowFixedControlCNFAt V x t l s w)
            (tmVerifierStackFamilyAssignment V (x, c) stkAt)) :
    CNF.Satisfies (tmVerifierXOnlyTransitionFixedControlCNFAt V x t)
      (tmVerifierStackFamilyAssignment V (x, c) stkAt) := by
  intro clause hclause
  rw [tmVerifierXOnlyTransitionFixedControlCNFAt] at hclause
  rcases List.mem_flatMap.mp hclause with ⟨l', _hl', hclause⟩
  rcases List.mem_flatMap.mp hclause with ⟨s', _hs', hclause⟩
  rcases List.mem_flatMap.mp hclause with ⟨w, hw, hclause⟩
  by_cases hLabelEq : l' = l
  · subst l'
    by_cases hStateEq : s' = s
    · subst s'
      exact hCurrent w hw clause hclause
    · have hFalse :
        (tmVerifierStateAtom V t s').eval
            (tmVerifierStackFamilyAssignment V (x, c) stkAt) = false := by
        exact tmVerifierStateAtom_eval_stackFamilyAssignment_false_of_ne V (x, c) stkAt t s'
          (by
            intro h
            exact hStateEq (by simpa [hs] using h))
      exact tmVerifierXOnlyWindowFixedControlCNFAt_satisfies_of_false_antecedent V x t
        l s' w (tmVerifierStackFamilyAssignment V (x, c) stkAt)
        (tmVerifierXOnlyWindowFixedAntecedents_state_mem V x t l s' w) hFalse clause
        hclause
  · have hFalse :
      (tmVerifierLabelAtom V t (some l')).eval
          (tmVerifierStackFamilyAssignment V (x, c) stkAt) = false := by
      exact tmVerifierLabelAtom_eval_stackFamilyAssignment_false_of_ne V (x, c) stkAt t
        (some l') (by
          intro h
          exact hLabelEq (Option.some.inj (by simpa [hl] using h)))
    exact tmVerifierXOnlyWindowFixedControlCNFAt_satisfies_of_false_antecedent V x t
      l' s' w (tmVerifierStackFamilyAssignment V (x, c) stkAt)
      (tmVerifierXOnlyWindowFixedAntecedents_label_mem V x t l' s' w) hFalse clause
      hclause

theorem tmVerifierXOnlyHaltedRowsCNFAt_satisfies_of_nonhalting_label
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (t : Nat)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    {l : (tmVerifierTM V).Λ}
    (hl : (tmVerifierRunCfgAt V (x, c) t).l = some l) :
    CNF.Satisfies (tmVerifierXOnlyHaltedRowsCNFAt V x t)
      (tmVerifierStackFamilyAssignment V (x, c) stkAt) := by
  intro clause hclause
  rw [tmVerifierXOnlyHaltedRowsCNFAt] at hclause
  rcases List.mem_flatMap.mp hclause with ⟨s, _hs, hclause⟩
  let antecedents := tmVerifierHaltedRowAntecedents V t s
  have hFalse :
      (tmVerifierLabelAtom V t none).eval
          (tmVerifierStackFamilyAssignment V (x, c) stkAt) = false := by
    exact tmVerifierLabelAtom_eval_stackFamilyAssignment_false_of_ne V (x, c) stkAt t none
      (by
        intro h
        simp [hl] at h)
  have hmem : tmVerifierLabelAtom V t none ∈ antecedents := by
    simp [antecedents, tmVerifierHaltedRowAntecedents]
  rw [tmVerifierXOnlyHaltedRowCNFAt] at hclause
  have hSatisfies :
      CNF.Satisfies
        ([tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) none),
          tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) s)] ++
            tmVerifierXOnlyFrameAllStacksCNFBetween V x t (t + 1) antecedents)
        (tmVerifierStackFamilyAssignment V (x, c) stkAt) := by
    rw [CNF.satisfies_append]
    constructor
    · intro c0 hc0
      have hc0' :
          c0 = tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) none) ∨
            c0 = tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) s) := by
        simpa using hc0
      rcases hc0' with rfl | rfl
      · exact tmVerifierImplicationClause_satisfies_of_false_antecedent antecedents
          (tmVerifierLabelAtom V (t + 1) none) (tmVerifierLabelAtom V t none)
          (tmVerifierStackFamilyAssignment V (x, c) stkAt) hmem hFalse
      · exact tmVerifierImplicationClause_satisfies_of_false_antecedent antecedents
          (tmVerifierStateAtom V (t + 1) s) (tmVerifierLabelAtom V t none)
          (tmVerifierStackFamilyAssignment V (x, c) stkAt) hmem hFalse
    · exact tmVerifierXOnlyFrameAllStacksCNFBetween_satisfies_of_false_antecedent V x t
        (t + 1) antecedents (tmVerifierStackFamilyAssignment V (x, c) stkAt) hmem hFalse
  exact hSatisfies clause hclause

theorem tmVerifierXOnlyAcceptedRunGlobalStacks_sameControl_current
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hOut : tmVerifierOutputsBoolInTime V (x, c) true)
    {t : Nat} (ht : t < tmVerifierXOnlyTimeBound V x)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    (hl : (tmVerifierRunCfgAt V (x, c) t).l = some l)
    (hs : (tmVerifierRunCfgAt V (x, c) t).var = s) :
    (∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies (tmVerifierXOnlyWindowFixedControlCNFAt V x t l s w)
            (tmVerifierXOnlyAcceptedRunAssignment V x c)) ∧
      (∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies
            (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V x t l s w ++
              tmVerifierXOnlyWindowFixedStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
                x t w (tmVerifierXOnlyWindowFixedAntecedents V x t l s w))
            (tmVerifierXOnlyAcceptedRunAssignment V x c)) := by
  by_cases htFixed : t < tmVerifierTimeBound V (x, c)
  · let selected := tmVerifierRunSelectedWindow V (x, c) t
    have hwSelected : selected ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s := by
      simpa [selected] using tmVerifierRunSelectedWindow_mem V (x, c) (t := t) hl hs
    have hSelectedMatch :
        tmVerifierWindowActionsMatchStacks selected.actions (tmVerifierRunCfgAt V (x, c) t).stk := by
      classical
      have hspec :=
        Classical.choose_spec
          (tmVerifierStmtWindowsAt_exists_true_actionReadGuards_topStack V (x, c) t l
            (tmVerifierRunCfgAt V (x, c) t).var)
      simpa [selected, tmVerifierRunSelectedWindow, hl, hs] using hspec.2.2
    have hSelectedGuards :
        ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuards x t selected,
          g.eval (tmVerifierXOnlyAcceptedRunAssignment V x c) = true := by
      simpa [selected] using
        tmVerifierRunSelectedWindow_xOnlyFixedGuards_satisfies_acceptedRunGlobalStacks V x c
          htFixed hl hs
    have hDomains :
        ∀ w : TMVerifierStmtWindow V,
          w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
            ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx →
              ∀ k : tmVerifierStackIndex V,
                CNF.Satisfies
                  (tmVerifierXOnlyStackCellDomainsCNFAt V x
                    (tmVerifierXOnlyFixedMicroTime V x t entry.2) k)
                  (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
      intro _w _hw entry _hentry k
      simpa [tmVerifierXOnlyAcceptedRunAssignment] using
        tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_stackFamilyAssignment V (x, c)
          (tmVerifierXOnlyAcceptedRunGlobalStacks V x c)
          (tmVerifierXOnlyFixedMicroTime V x t entry.2)
          (tmVerifierXOnlyAcceptedRunGlobalStacks_fixedMicro_stacksActive_any V x c
            t entry.2) k x
    have hSelectedStackEq :
        ∀ micro : Nat,
          tmVerifierXOnlyAcceptedRunGlobalStacks V x c (tmVerifierXOnlyFixedMicroTime V x t micro) =
            tmVerifierWindowMicroStacks V (x, c) t selected micro := by
      intro micro
      simpa [selected] using tmVerifierXOnlyAcceptedRunGlobalStacks_at_fixed_micro V x c t micro
    have hSelectedBoundary :
        CNF.Satisfies (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V x t l s selected)
          (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
      simpa [tmVerifierXOnlyAcceptedRunAssignment] using
        tmVerifierXOnlyWindowFixedStackBoundaryCNFAt_satisfies_stackFamilyAssignment_of_stack_eq
          V (x, c) x t l s selected (tmVerifierXOnlyAcceptedRunGlobalStacks V x c)
          (by
            intro k
            rw [hSelectedStackEq 0, tmVerifierXOnlyAcceptedRunGlobalStacks_at_macro V x c
              (Nat.le_of_lt ht)]
            simp [tmVerifierWindowMicroStacks, tmVerifierWindowActionsApplyStacks, selected])
          (by
            intro k
            rw [tmVerifierXOnlyAcceptedRunGlobalStacks_at_macro V x c (Nat.succ_le_of_lt ht),
              hSelectedStackEq selected.actions.length]
            have hFinal :=
              tmVerifierSelectedWindowFixedRunStacks_final_eq_macro_succ V (x, c) t l s
                selected htFixed hwSelected hSelectedMatch hl hs k
            simpa [tmVerifierSelectedWindowFixedRunStacks_at_succ V (x, c) t selected,
              tmVerifierSelectedWindowFixedRunStacks_at_micro V (x, c) htFixed selected
                selected.actions.length] using hFinal)
    have hSelectedAction :
        CNF.Satisfies
          (tmVerifierXOnlyWindowFixedStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
            x t selected (tmVerifierXOnlyWindowFixedAntecedents V x t l s selected))
          (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
      simpa [tmVerifierXOnlyAcceptedRunAssignment] using
        tmVerifierXOnlyWindowFixedStackActionCNFAt_satisfies_active_applyStacks_of_readGuards_stkAt
          V (x, c) x t selected (tmVerifierXOnlyAcceptedRunGlobalStacks V x c)
          (tmVerifierXOnlyWindowFixedAntecedents V x t l s selected)
          hSelectedStackEq (by simpa [tmVerifierXOnlyAcceptedRunAssignment] using hSelectedGuards)
    have hSelectedStack :
        CNF.Satisfies
          (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V x t l s selected ++
            tmVerifierXOnlyWindowFixedStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
              x t selected (tmVerifierXOnlyWindowFixedAntecedents V x t l s selected))
          (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
      exact (CNF.satisfies_append
        (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V x t l s selected)
        (tmVerifierXOnlyWindowFixedStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
          x t selected (tmVerifierXOnlyWindowFixedAntecedents V x t l s selected))
        (tmVerifierXOnlyAcceptedRunAssignment V x c)).2
        ⟨hSelectedBoundary, hSelectedAction⟩
    have hSelectedControl :
        CNF.Satisfies (tmVerifierXOnlyWindowFixedControlCNFAt V x t l s selected)
          (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
      intro clause hclause
      have hAgree :=
        tmVerifierStmtWindowsAt_stepAux_agrees V t ((tmVerifierTM V).m l) s
          (tmVerifierRunCfgAt V (x, c) t).stk hwSelected hSelectedMatch
      have hSucc := tmVerifierRunCfgAt_succ_of_label_some V (x, c) t hl hs
      have hNextLabel : selected.nextLabel = (tmVerifierRunCfgAt V (x, c) (t + 1)).l := by
        rw [hAgree.1, hSucc]
      have hNextState : selected.nextState = (tmVerifierRunCfgAt V (x, c) (t + 1)).var := by
        rw [hAgree.2.1, hSucc]
      have hClause :
          clause =
              tmVerifierImplicationClause (tmVerifierXOnlyWindowFixedAntecedents V x t l s selected)
                (tmVerifierLabelAtom V (t + 1) selected.nextLabel) ∨
            clause =
              tmVerifierImplicationClause (tmVerifierXOnlyWindowFixedAntecedents V x t l s selected)
                (tmVerifierStateAtom V (t + 1) selected.nextState) := by
        simpa [tmVerifierXOnlyWindowFixedControlCNFAt] using hclause
      rcases hClause with rfl | rfl
      · exact tmVerifierImplicationClause_satisfies_of_conclusion
          (tmVerifierXOnlyWindowFixedAntecedents V x t l s selected)
          (tmVerifierLabelAtom V (t + 1) selected.nextLabel)
          (tmVerifierXOnlyAcceptedRunAssignment V x c) (by
            rw [tmVerifierXOnlyAcceptedRunAssignment]
            rw [tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary]
            rw [tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff]
            exact hNextLabel)
      · exact tmVerifierImplicationClause_satisfies_of_conclusion
          (tmVerifierXOnlyWindowFixedAntecedents V x t l s selected)
          (tmVerifierStateAtom V (t + 1) selected.nextState)
          (tmVerifierXOnlyAcceptedRunAssignment V x c) (by
            rw [tmVerifierXOnlyAcceptedRunAssignment]
            rw [tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary]
            rw [tmVerifierStateAtom_eval_controlBoundaryAssignment_iff]
            exact hNextState)
    constructor
    · intro w hw
      by_cases hAll : ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuards x t w,
          g.eval (tmVerifierXOnlyAcceptedRunAssignment V x c) = true
      · have hEq :
          selected = w :=
          tmVerifierStmtWindowsAt_unique_of_true_xOnlyFixedActionReadGuards V x t
            ((tmVerifierTM V).m l) s (tmVerifierXOnlyAcceptedRunAssignment V x c)
            hDomains hwSelected hw hSelectedGuards hAll
        simpa [hEq] using hSelectedControl
      · push Not at hAll
        rcases hAll with ⟨bad, hbadMem, hbadNotTrue⟩
        have hbadFalse : bad.eval (tmVerifierXOnlyAcceptedRunAssignment V x c) = false := by
          cases hEval : bad.eval (tmVerifierXOnlyAcceptedRunAssignment V x c) <;>
            simp [hEval] at hbadNotTrue ⊢
        exact tmVerifierXOnlyWindowFixedControlCNFAt_satisfies_of_false_antecedent V x t
          l s w (tmVerifierXOnlyAcceptedRunAssignment V x c)
          (tmVerifierXOnlyWindowFixedAntecedents_fixedGuard_mem V x t l s w hbadMem)
          hbadFalse
    · intro w hw
      by_cases hAll : ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuards x t w,
          g.eval (tmVerifierXOnlyAcceptedRunAssignment V x c) = true
      · have hEq :
          selected = w :=
          tmVerifierStmtWindowsAt_unique_of_true_xOnlyFixedActionReadGuards V x t
            ((tmVerifierTM V).m l) s (tmVerifierXOnlyAcceptedRunAssignment V x c)
            hDomains hwSelected hw hSelectedGuards hAll
        simpa [hEq] using hSelectedStack
      · push Not at hAll
        rcases hAll with ⟨bad, hbadMem, hbadNotTrue⟩
        have hbadFalse : bad.eval (tmVerifierXOnlyAcceptedRunAssignment V x c) = false := by
          cases hEval : bad.eval (tmVerifierXOnlyAcceptedRunAssignment V x c) <;>
            simp [hEval] at hbadNotTrue ⊢
        exact tmVerifierXOnlyWindowFixedStackCNF_satisfies_of_false_antecedent V
          (tmVerifierActivePushPayloadBoundary V) x t l s w
          (tmVerifierXOnlyAcceptedRunAssignment V x c)
          (tmVerifierXOnlyWindowFixedAntecedents_fixedGuard_mem V x t l s w hbadMem)
          hbadFalse
  · have hcfg := tmVerifierRunCfgAt_of_outputs_true_ge_timeBound V (x, c) hOut
      (Nat.le_of_not_gt htFixed)
    rw [hcfg] at hl
    simp [tmVerifierOutputCfg, Turing.haltList] at hl

theorem tmVerifierXOnlyHaltedRowCNFAt_satisfies_acceptedRun
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hOut : tmVerifierOutputsBoolInTime V (x, c) true)
    {t : Nat} (ht : t < tmVerifierXOnlyTimeBound V x)
    (s : (tmVerifierTM V).σ)
    (hLabel : (tmVerifierRunCfgAt V (x, c) t).l = none)
    (hs : (tmVerifierRunCfgAt V (x, c) t).var = s) :
    CNF.Satisfies (tmVerifierXOnlyHaltedRowCNFAt V x t s)
      (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
  let a := tmVerifierXOnlyAcceptedRunAssignment V x c
  have htSuccX : t + 1 ≤ tmVerifierXOnlyTimeBound V x := Nat.succ_le_of_lt ht
  have hCfgT :
      tmVerifierRunCfgAt V (x, c) t = tmVerifierOutputCfg V true := by
    by_cases htFixed : t < tmVerifierTimeBound V (x, c)
    · exact tmVerifierRunCfgAt_of_label_none_outputs_true V (x, c) (Nat.le_of_lt htFixed)
        hOut hLabel
    · exact tmVerifierRunCfgAt_of_outputs_true_ge_timeBound V (x, c) hOut
        (Nat.le_of_not_gt htFixed)
  have hCfgSucc :
      tmVerifierRunCfgAt V (x, c) (t + 1) = tmVerifierOutputCfg V true := by
    by_cases htFixed : t < tmVerifierTimeBound V (x, c)
    · have htSuccFixed : t + 1 ≤ tmVerifierTimeBound V (x, c) := Nat.succ_le_of_lt htFixed
      have hLabelSucc : (tmVerifierRunCfgAt V (x, c) (t + 1)).l = none := by
        rw [tmVerifierRunCfgAt, Function.iterate_succ_apply']
        cases hrun :
            (flip bind (tmVerifierTM V).step)^[t]
              (some (tmVerifierInitialCfg V (x, c))) with
        | none =>
            rfl
        | some cfg =>
            have hcfg : tmVerifierRunCfgAt V (x, c) t = cfg := by
              rw [tmVerifierRunCfgAt, hrun]
            have hcfgLabel : cfg.l = none := by
              simpa [hcfg] using hLabel
            have hstep : (tmVerifierTM V).step cfg = none := by
              rcases cfg with ⟨label, state, stk⟩
              cases label with
              | none =>
                  rfl
              | some l =>
                  simp at hcfgLabel
            change (match (tmVerifierTM V).step cfg with
              | some cfg => cfg
              | none => tmVerifierOutputCfg V true).l = none
            rw [hstep]
            simp [tmVerifierOutputCfg, Turing.haltList]
      exact tmVerifierRunCfgAt_of_label_none_outputs_true V (x, c) htSuccFixed hOut
        hLabelSucc
    · exact tmVerifierRunCfgAt_of_outputs_true_ge_timeBound V (x, c) hOut
        (by omega)
  have hState : s = (tmVerifierOutputCfg V true).var := by
    rw [← hs, hCfgT]
  rw [tmVerifierXOnlyHaltedRowCNFAt]
  let antecedents := tmVerifierHaltedRowAntecedents V t s
  change CNF.Satisfies
    ([tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) none),
      tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) s)] ++
        tmVerifierXOnlyFrameAllStacksCNFBetween V x t (t + 1) antecedents) a
  rw [CNF.satisfies_append]
  constructor
  · intro clause hclause
    have hclause' :
        clause = tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) none) ∨
          clause = tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) s) := by
      simpa using hclause
    rcases hclause' with rfl | rfl
    · exact tmVerifierImplicationClause_satisfies_of_conclusion antecedents
        (tmVerifierLabelAtom V (t + 1) none) a (by
          dsimp [a]
          rw [tmVerifierXOnlyAcceptedRunAssignment]
          rw [tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary]
          rw [tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff]
          rw [hCfgSucc]
          simp [tmVerifierOutputCfg, Turing.haltList])
    · exact tmVerifierImplicationClause_satisfies_of_conclusion antecedents
        (tmVerifierStateAtom V (t + 1) s) a (by
          dsimp [a]
          rw [tmVerifierXOnlyAcceptedRunAssignment]
          rw [tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary]
          rw [tmVerifierStateAtom_eval_controlBoundaryAssignment_iff]
          rw [hState, hCfgSucc])
  · exact tmVerifierXOnlyFrameAllStacksCNFBetween_satisfies_of_eval_eq V (x, c) x t
      (t + 1) antecedents (tmVerifierXOnlyAcceptedRunGlobalStacks V x c) (by
        intro k _hk cell _hcell choice _hchoice
        have hStack :
            tmVerifierXOnlyAcceptedRunGlobalStacks V x c (t + 1) k =
              tmVerifierXOnlyAcceptedRunGlobalStacks V x c t k := by
          rw [tmVerifierXOnlyAcceptedRunGlobalStacks_at_macro V x c htSuccX,
            tmVerifierXOnlyAcceptedRunGlobalStacks_at_macro V x c (Nat.le_of_lt ht),
            hCfgT, hCfgSucc]
        exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
          V (x, c) (tmVerifierXOnlyAcceptedRunGlobalStacks V x c) t (t + 1) k cell choice
          hStack)

theorem tmVerifierXOnlyHaltedRowsCNFAt_satisfies_acceptedRun
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hOut : tmVerifierOutputsBoolInTime V (x, c) true)
    {t : Nat} (ht : t < tmVerifierXOnlyTimeBound V x)
    (hLabel : (tmVerifierRunCfgAt V (x, c) t).l = none) :
    CNF.Satisfies (tmVerifierXOnlyHaltedRowsCNFAt V x t)
      (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
  intro clause hclause
  rw [tmVerifierXOnlyHaltedRowsCNFAt] at hclause
  rcases List.mem_flatMap.mp hclause with ⟨s, _hsMem, hclause⟩
  by_cases hs : (tmVerifierRunCfgAt V (x, c) t).var = s
  · exact tmVerifierXOnlyHaltedRowCNFAt_satisfies_acceptedRun V x c hOut ht s
      hLabel hs clause hclause
  · have hFalse :
        (tmVerifierStateAtom V t s).eval (tmVerifierXOnlyAcceptedRunAssignment V x c) =
          false := by
      rw [tmVerifierXOnlyAcceptedRunAssignment]
      exact tmVerifierStateAtom_eval_stackFamilyAssignment_false_of_ne V (x, c)
        (tmVerifierXOnlyAcceptedRunGlobalStacks V x c) t s (by
          intro h
          exact hs h.symm)
    let antecedents := tmVerifierHaltedRowAntecedents V t s
    rw [tmVerifierXOnlyHaltedRowCNFAt] at hclause
    have hmem : tmVerifierStateAtom V t s ∈ antecedents := by
      simp [antecedents, tmVerifierHaltedRowAntecedents]
    have hSatisfies :
        CNF.Satisfies (tmVerifierXOnlyHaltedRowCNFAt V x t s)
          (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
      rw [tmVerifierXOnlyHaltedRowCNFAt]
      change CNF.Satisfies
        ([tmVerifierImplicationClause antecedents (tmVerifierLabelAtom V (t + 1) none),
          tmVerifierImplicationClause antecedents (tmVerifierStateAtom V (t + 1) s)] ++
            tmVerifierXOnlyFrameAllStacksCNFBetween V x t (t + 1) antecedents)
          (tmVerifierXOnlyAcceptedRunAssignment V x c)
      rw [CNF.satisfies_append]
      constructor
      · intro c0 hc0
        have hc0' :
            c0 = tmVerifierImplicationClause antecedents
                (tmVerifierLabelAtom V (t + 1) none) ∨
              c0 = tmVerifierImplicationClause antecedents
                (tmVerifierStateAtom V (t + 1) s) := by
          simpa using hc0
        rcases hc0' with rfl | rfl
        · exact tmVerifierImplicationClause_satisfies_of_false_antecedent antecedents
            (tmVerifierLabelAtom V (t + 1) none) (tmVerifierStateAtom V t s)
            (tmVerifierXOnlyAcceptedRunAssignment V x c) hmem hFalse
        · exact tmVerifierImplicationClause_satisfies_of_false_antecedent antecedents
            (tmVerifierStateAtom V (t + 1) s) (tmVerifierStateAtom V t s)
            (tmVerifierXOnlyAcceptedRunAssignment V x c) hmem hFalse
      · exact tmVerifierXOnlyFrameAllStacksCNFBetween_satisfies_of_false_antecedent V x t
          (t + 1) antecedents (tmVerifierXOnlyAcceptedRunAssignment V x c) hmem hFalse
    exact hSatisfies clause hclause

theorem tmVerifierXOnlyTransitionFixedRowCNFAt_satisfies_current_label_state
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hl : (tmVerifierRunCfgAt V (x, c) t).l = some l)
    (hs : (tmVerifierRunCfgAt V (x, c) t).var = s)
    (hControlCurrent :
      ∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies (tmVerifierXOnlyWindowFixedControlCNFAt V x t l s w)
            (tmVerifierStackFamilyAssignment V (x, c) stkAt))
    (hStackCurrent :
      ∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies
            (tmVerifierXOnlyWindowFixedStackBoundaryCNFAt V x t l s w ++
              tmVerifierXOnlyWindowFixedStackActionCNFAt V B x t w
                (tmVerifierXOnlyWindowFixedAntecedents V x t l s w))
            (tmVerifierStackFamilyAssignment V (x, c) stkAt)) :
    CNF.Satisfies (tmVerifierXOnlyTransitionFixedRowCNFAt V B x t)
      (tmVerifierStackFamilyAssignment V (x, c) stkAt) := by
  rw [tmVerifierXOnlyTransitionFixedRowCNFAt, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    exact ⟨tmVerifierXOnlyTransitionFixedControlCNFAt_satisfies_current_label_state V
        x c t l s stkAt hl hs hControlCurrent,
      tmVerifierXOnlyTransitionFixedWindowStackCNFAt_satisfies_current_label_state V
        B x c t l s stkAt hl hs hStackCurrent⟩
  · exact tmVerifierXOnlyHaltedRowsCNFAt_satisfies_of_nonhalting_label V x c t stkAt hl

theorem tmVerifierXOnlyTransitionFixedRowCNFAt_satisfies_acceptedRun
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hOut : tmVerifierOutputsBoolInTime V (x, c) true)
    {t : Nat} (ht : t < tmVerifierXOnlyTimeBound V x) :
    CNF.Satisfies (tmVerifierXOnlyTransitionFixedRowCNFAt V
        (tmVerifierActivePushPayloadBoundary V) x t)
      (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
  cases hLabel : (tmVerifierRunCfgAt V (x, c) t).l with
  | some l =>
      let s := (tmVerifierRunCfgAt V (x, c) t).var
      have hCurrent :=
        tmVerifierXOnlyAcceptedRunGlobalStacks_sameControl_current V x c hOut ht hLabel rfl
      simpa [tmVerifierXOnlyAcceptedRunAssignment] using
        tmVerifierXOnlyTransitionFixedRowCNFAt_satisfies_current_label_state V
          (tmVerifierActivePushPayloadBoundary V) x c t l s
          (tmVerifierXOnlyAcceptedRunGlobalStacks V x c) hLabel rfl hCurrent.1 hCurrent.2
  | none =>
      rw [tmVerifierXOnlyTransitionFixedRowCNFAt, CNF.satisfies_append]
      constructor
      · rw [CNF.satisfies_append]
        constructor
        · intro c0 hc0
          rw [tmVerifierXOnlyTransitionFixedControlCNFAt] at hc0
          rcases List.mem_flatMap.mp hc0 with ⟨l, _hl, hc0⟩
          rcases List.mem_flatMap.mp hc0 with ⟨s, _hs, hc0⟩
          rcases List.mem_flatMap.mp hc0 with ⟨w, _hw, hc0⟩
          have hFalse :
              (tmVerifierLabelAtom V t (some l)).eval
                  (tmVerifierXOnlyAcceptedRunAssignment V x c) = false := by
            rw [tmVerifierXOnlyAcceptedRunAssignment]
            exact tmVerifierLabelAtom_eval_stackFamilyAssignment_false_of_ne V (x, c)
              (tmVerifierXOnlyAcceptedRunGlobalStacks V x c) t (some l) (by
                intro h
                simp [hLabel] at h)
          exact tmVerifierXOnlyWindowFixedControlCNFAt_satisfies_of_false_antecedent V x t
            l s w (tmVerifierXOnlyAcceptedRunAssignment V x c)
            (tmVerifierXOnlyWindowFixedAntecedents_label_mem V x t l s w) hFalse c0 hc0
        · intro c0 hc0
          rw [tmVerifierXOnlyTransitionFixedWindowStackCNFAt] at hc0
          rcases List.mem_flatMap.mp hc0 with ⟨l, _hl, hc0⟩
          rcases List.mem_flatMap.mp hc0 with ⟨s, _hs, hc0⟩
          rcases List.mem_flatMap.mp hc0 with ⟨w, _hw, hc0⟩
          have hFalse :
              (tmVerifierLabelAtom V t (some l)).eval
                  (tmVerifierXOnlyAcceptedRunAssignment V x c) = false := by
            rw [tmVerifierXOnlyAcceptedRunAssignment]
            exact tmVerifierLabelAtom_eval_stackFamilyAssignment_false_of_ne V (x, c)
              (tmVerifierXOnlyAcceptedRunGlobalStacks V x c) t (some l) (by
                intro h
                simp [hLabel] at h)
          exact tmVerifierXOnlyWindowFixedStackCNF_satisfies_of_false_antecedent V
            (tmVerifierActivePushPayloadBoundary V) x t l s w
            (tmVerifierXOnlyAcceptedRunAssignment V x c)
            (tmVerifierXOnlyWindowFixedAntecedents_label_mem V x t l s w) hFalse c0 hc0
      · exact tmVerifierXOnlyHaltedRowsCNFAt_satisfies_acceptedRun V x c hOut ht hLabel

theorem tmVerifierXOnlyTransitionFixedRowsCNF_satisfies_acceptedRun
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hOut : tmVerifierOutputsBoolInTime V (x, c) true) :
    CNF.Satisfies (tmVerifierXOnlyTransitionFixedRowsCNF V
        (tmVerifierActivePushPayloadBoundary V) x)
      (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
  intro clause hclause
  rw [tmVerifierXOnlyTransitionFixedRowsCNF] at hclause
  rcases List.mem_flatMap.mp hclause with ⟨t, ht, hclause⟩
  have htLt : t < tmVerifierXOnlyTimeBound V x := by
    simpa [tmVerifierXOnlyTransitionTimeRange, List.mem_range] using ht
  exact tmVerifierXOnlyTransitionFixedRowCNFAt_satisfies_acceptedRun V x c hOut htLt
    clause hclause

theorem tmVerifierXOnlyGlobalTableauCNF_satisfies_acceptedRun
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (x : L.Instance.Carrier) (c : V.Cert.Carrier)
    (hSize : V.Cert.inputSize c ≤ tmVerifierCertificateSizeBound V x)
    (hOut : tmVerifierOutputsBoolInTime V (x, c) true) :
    CNF.Satisfies (tmVerifierXOnlyGlobalTableauCNF V
        (tmVerifierActivePushPayloadBoundary V) x)
      (tmVerifierXOnlyAcceptedRunAssignment V x c) := by
  intro clause hclause
  rw [tmVerifierXOnlyGlobalTableauCNF] at hclause
  rcases List.mem_flatMap.mp hclause with ⟨block, hblock, hclause⟩
  rw [tmVerifierXOnlyGlobalTableauBlocks] at hblock
  simp only [List.mem_cons, List.not_mem_nil] at hblock
  rcases hblock with hblock | hblock | hblock | hblock | hblock | hblock | hblock
  · subst block
    exact tmVerifierXOnlyControlDomainRowsCNF_satisfies_acceptedRun V x c clause hclause
  · subst block
    exact tmVerifierXOnlyInitialControlCNF_satisfies_acceptedRun V x c clause hclause
  · subst block
    exact tmVerifierXOnlyInitialStackCNF_satisfies_acceptedRun V x c hSize clause hclause
  · subst block
    exact tmVerifierXOnlyStackWellFormedRowsCNF_satisfies_acceptedRun V x c hSize
      clause hclause
  · subst block
    exact tmVerifierXOnlyTransitionFixedMicroDomainRowsCNF_satisfies_acceptedRun V x c
      hSize hOut clause hclause
  · subst block
    exact tmVerifierXOnlyTransitionFixedRowsCNF_satisfies_acceptedRun V x c hOut clause hclause
  · rcases hblock with hblock | hfalse
    · subst block
      exact tmVerifierXOnlyEndpointCNF_satisfies_acceptedRun_of_outputs_true V x c hSize hOut
        clause hclause
    · cases hfalse

end SAT
end ComplexityReduction
