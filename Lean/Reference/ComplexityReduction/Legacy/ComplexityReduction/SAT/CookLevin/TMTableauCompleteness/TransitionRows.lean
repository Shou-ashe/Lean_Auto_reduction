/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.ActionTrace

namespace ComplexityReduction
namespace SAT

/-! ### Selected transition-window completeness helpers -/

theorem tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (label : Option (tmVerifierTM V).Λ) :
    (tmVerifierLabelAtom V t label).eval (tmVerifierStackFamilyAssignment V p stkAt) =
      (tmVerifierLabelAtom V t label).eval (tmVerifierControlBoundaryAssignment V p) := by
  classical
  change tmVerifierStackFamilyAssignment V p stkAt (tmVerifierLabelAtom V t label).var =
    tmVerifierControlBoundaryAssignment V p (tmVerifierLabelAtom V t label).var
  have hNoSelectedSymbol :
      ¬ ∃ u k cell, ∃ hcell : cell < (stkAt u k).length,
        (tmVerifierLabelAtom V t label).var =
          (tmVerifierStackSymbolAtom V u k cell
            (tmVerifierActiveStackSymbolPayload V k ((stkAt u k)[cell]'hcell))).var := by
    rintro ⟨u, k, cell, hcell, h⟩
    exact tmVerifierStackSymbolAtom_var_ne_labelAtom_var V u t k cell
      (tmVerifierActiveStackSymbolPayload V k ((stkAt u k)[cell]'hcell)) label h.symm
  have hNoSelectedEmpty :
      ¬ ∃ u k cell, ∃ hcell : cell < (stkAt u k).length,
        (tmVerifierLabelAtom V t label).var =
          (tmVerifierStackEmptyAtom V u k cell).var := by
    rintro ⟨u, k, cell, _hcell, h⟩
    exact tmVerifierStackEmptyAtom_var_ne_labelAtom_var V u t k cell label h.symm
  have hNoAnyEmpty :
      ¬ ∃ u k cell,
        (tmVerifierLabelAtom V t label).var = (tmVerifierStackEmptyAtom V u k cell).var := by
    rintro ⟨u, k, cell, h⟩
    exact tmVerifierStackEmptyAtom_var_ne_labelAtom_var V u t k cell label h.symm
  have hNoAnySymbol :
      ¬ ∃ u k cell payload,
        (tmVerifierLabelAtom V t label).var =
          (tmVerifierStackSymbolAtom V u k cell payload).var := by
    rintro ⟨u, k, cell, payload, h⟩
    exact tmVerifierStackSymbolAtom_var_ne_labelAtom_var V u t k cell payload label h.symm
  rw [tmVerifierStackFamilyAssignment, if_neg hNoSelectedSymbol, if_neg hNoSelectedEmpty,
    if_neg hNoAnyEmpty, if_neg hNoAnySymbol]

theorem tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (t : Nat) (state : (tmVerifierTM V).σ) :
    (tmVerifierStateAtom V t state).eval (tmVerifierStackFamilyAssignment V p stkAt) =
      (tmVerifierStateAtom V t state).eval (tmVerifierControlBoundaryAssignment V p) := by
  classical
  change tmVerifierStackFamilyAssignment V p stkAt (tmVerifierStateAtom V t state).var =
    tmVerifierControlBoundaryAssignment V p (tmVerifierStateAtom V t state).var
  have hNoSelectedSymbol :
      ¬ ∃ u k cell, ∃ hcell : cell < (stkAt u k).length,
        (tmVerifierStateAtom V t state).var =
          (tmVerifierStackSymbolAtom V u k cell
            (tmVerifierActiveStackSymbolPayload V k ((stkAt u k)[cell]'hcell))).var := by
    rintro ⟨u, k, cell, hcell, h⟩
    exact tmVerifierStackSymbolAtom_var_ne_stateAtom_var V u t k cell
      (tmVerifierActiveStackSymbolPayload V k ((stkAt u k)[cell]'hcell)) state h.symm
  have hNoSelectedEmpty :
      ¬ ∃ u k cell, ∃ hcell : cell < (stkAt u k).length,
        (tmVerifierStateAtom V t state).var =
          (tmVerifierStackEmptyAtom V u k cell).var := by
    rintro ⟨u, k, cell, _hcell, h⟩
    exact tmVerifierStackEmptyAtom_var_ne_stateAtom_var V u t k cell state h.symm
  have hNoAnyEmpty :
      ¬ ∃ u k cell,
        (tmVerifierStateAtom V t state).var = (tmVerifierStackEmptyAtom V u k cell).var := by
    rintro ⟨u, k, cell, h⟩
    exact tmVerifierStackEmptyAtom_var_ne_stateAtom_var V u t k cell state h.symm
  have hNoAnySymbol :
      ¬ ∃ u k cell payload,
        (tmVerifierStateAtom V t state).var =
          (tmVerifierStackSymbolAtom V u k cell payload).var := by
    rintro ⟨u, k, cell, payload, h⟩
    exact tmVerifierStackSymbolAtom_var_ne_stateAtom_var V u t k cell payload state h.symm
  rw [tmVerifierStackFamilyAssignment, if_neg hNoSelectedSymbol, if_neg hNoSelectedEmpty,
    if_neg hNoAnyEmpty, if_neg hNoAnySymbol]

theorem tmVerifierRunCfgAt_succ_of_label_some
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s) :
    tmVerifierRunCfgAt V p (t + 1) =
      Turing.TM2.stepAux ((tmVerifierTM V).m l) s (tmVerifierRunCfgAt V p t).stk := by
  cases hrun :
      (flip bind (tmVerifierTM V).step)^[t] (some (tmVerifierInitialCfg V p)) with
  | none =>
      have _hrun' :
          (flip Option.bind (Turing.TM2.step (tmVerifierTM V).m))^[t]
              (some (tmVerifierInitialCfg V p)) = none := by
        simp [Turing.FinTM2.step] at hrun
        exact hrun
      have hcfg : tmVerifierRunCfgAt V p t = tmVerifierOutputCfg V true := by
        rw [tmVerifierRunCfgAt, hrun]
      exact False.elim (by
        simp [hcfg, tmVerifierOutputCfg, Turing.haltList] at hl)
  | some cfg =>
      rcases cfg with ⟨label, state, stk⟩
      cases label with
      | none =>
          have _hrun' :
              (flip Option.bind (Turing.TM2.step (tmVerifierTM V).m))^[t]
                  (some (tmVerifierInitialCfg V p)) =
                some { l := none, var := state, stk := stk } := by
            simp [Turing.FinTM2.step] at hrun
            exact hrun
          have hcfg :
              tmVerifierRunCfgAt V p t = { l := none, var := state, stk := stk } := by
            rw [tmVerifierRunCfgAt, hrun]
          exact False.elim (by simp [hcfg] at hl)
      | some label =>
          have hrun' :
              (flip Option.bind (Turing.TM2.step (tmVerifierTM V).m))^[t]
                  (some (tmVerifierInitialCfg V p)) =
                some { l := some label, var := state, stk := stk } := by
            simpa [Turing.FinTM2.step] using hrun
          have hcfg :
              tmVerifierRunCfgAt V p t = { l := some label, var := state, stk := stk } := by
            rw [tmVerifierRunCfgAt, hrun]
          have hl' : label = l := by simpa [hcfg] using hl
          have hs' : state = s := by simpa [hcfg] using hs
          subst l
          subst s
          rw [hcfg]
          rw [tmVerifierRunCfgAt, Function.iterate_succ_apply', hrun]
          change
            (match
                (tmVerifierTM V).step { l := some label, var := state, stk := stk } with
              | some cfg => cfg
              | none => tmVerifierOutputCfg V true) =
              Turing.TM2.stepAux ((tmVerifierTM V).m label) state stk
          simp [Turing.FinTM2.step, Turing.TM2.step]

theorem tmVerifierWindowControlCNFAt_satisfies_run_selected
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hMatch : tmVerifierWindowActionsMatchStacks w.actions (tmVerifierRunCfgAt V p t).stk)
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s) :
    CNF.Satisfies (tmVerifierWindowControlCNFAt V t l s w)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
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
  intro clause hclause
  have hClause :
      clause =
          tmVerifierImplicationClause (tmVerifierWindowAntecedents V t l s w)
            (tmVerifierLabelAtom V (t + 1) w.nextLabel) ∨
        clause =
          tmVerifierImplicationClause (tmVerifierWindowAntecedents V t l s w)
            (tmVerifierStateAtom V (t + 1) w.nextState) := by
    simpa [tmVerifierWindowControlCNFAt] using hclause
  rcases hClause with rfl | rfl
  · exact tmVerifierImplicationClause_satisfies_of_conclusion
      (tmVerifierWindowAntecedents V t l s w)
      (tmVerifierLabelAtom V (t + 1) w.nextLabel)
      (tmVerifierStackFamilyAssignment V p stkAt) (by
        rw [tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary]
        rw [tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff]
        exact hNextLabel)
  · exact tmVerifierImplicationClause_satisfies_of_conclusion
      (tmVerifierWindowAntecedents V t l s w)
      (tmVerifierStateAtom V (t + 1) w.nextState)
      (tmVerifierStackFamilyAssignment V p stkAt) (by
        rw [tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary]
        rw [tmVerifierStateAtom_eval_controlBoundaryAssignment_iff]
        exact hNextState)

theorem tmVerifierWindowControlCNFAt_satisfies_run_selected_microAssignment
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hMatch : tmVerifierWindowActionsMatchStacks w.actions (tmVerifierRunCfgAt V p t).stk)
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s) :
    CNF.Satisfies (tmVerifierWindowControlCNFAt V t l s w)
      (tmVerifierWindowMicroStackFamilyAssignment V p t w) := by
  simpa [tmVerifierWindowMicroStackFamilyAssignment] using
    tmVerifierWindowControlCNFAt_satisfies_run_selected V p t l s w
      (fun u => tmVerifierWindowMicroStacks V p t w ((Nat.unpair u).2))
      hw hMatch hl hs

theorem tmVerifierWindowStackActionCNFAt_satisfies_active_applyStacks_of_readGuards_stkAt
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (antecedents : List Literal)
    (hStack :
      ∀ micro : Nat,
        stkAt (tmVerifierMicroTime t micro) = tmVerifierWindowMicroStacks V p t w micro)
    (hGuards :
      ∀ g ∈ tmVerifierWindowActionReadGuards t w,
        g.eval (tmVerifierStackFamilyAssignment V p stkAt) = true) :
    CNF.Satisfies
      (tmVerifierWindowStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
        p t w antecedents)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  apply tmVerifierWindowStackActionCNFAt_satisfies_of_actions
  intro entry hentry
  have hApplyBase :=
    tmVerifierWindowMicroStacks_apply_succ_of_zipIdx_mem V p t w entry hentry
  have hApply :
      stkAt (tmVerifierMicroTime t (entry.2 + 1)) =
        tmVerifierStackActionApplyStacks entry.1 (stkAt (tmVerifierMicroTime t entry.2)) := by
    rw [hStack (entry.2 + 1), hStack entry.2]
    exact hApplyBase
  exact
    tmVerifierStackActionCNFBetween_satisfies_active_applyStacks V p stkAt
      (tmVerifierMicroTime t entry.2) (tmVerifierMicroTime t (entry.2 + 1))
      antecedents entry.1 hApply
      (TMVerifierStackActionReadAtomTrue.of_readGuardAt_true (by
        intro g hg
        exact hGuards g (by
          rw [tmVerifierWindowActionReadGuards, tmVerifierWindowActionReadGuardsFrom]
          exact List.mem_flatMap.mpr ⟨entry, hentry, hg⟩)))

theorem TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_time_stack_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (stkAt₁ stkAt₂ :
      Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (time : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k)
    (hStack : stkAt₁ time k = stkAt₂ time k) :
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) time cell choice).eval
        (tmVerifierStackFamilyAssignment V p stkAt₁) =
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) time cell choice).eval
        (tmVerifierStackFamilyAssignment V p stkAt₂) := by
  cases choice with
  | empty =>
      by_cases hcell₁ : cell < (stkAt₁ time k).length
      · have hcell₂ : cell < (stkAt₂ time k).length := by simpa [hStack] using hcell₁
        simp [TMVerifierStackReadChoice.atomAt,
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_selected V p stkAt₁ time k
            hcell₁,
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_selected V p stkAt₂ time k
            hcell₂]
      · have hcell₂ : ¬ cell < (stkAt₂ time k).length := by simpa [hStack] using hcell₁
        simp [TMVerifierStackReadChoice.atomAt,
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt₁
            (u := time) (j := k) (cell := cell) hcell₁,
          tmVerifierStackEmptyAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt₂
            (u := time) (j := k) (cell := cell) hcell₂]
  | symbol payload symbol =>
      by_cases hcell₁ : cell < (stkAt₁ time k).length
      · have hcell₂ : cell < (stkAt₂ time k).length := by simpa [hStack] using hcell₁
        have hget :
            ((stkAt₂ time k)[cell]'hcell₂) = ((stkAt₁ time k)[cell]'hcell₁) := by
          simp [hStack]
        by_cases hp :
            payload = tmVerifierActiveStackSymbolPayload V k ((stkAt₁ time k)[cell]'hcell₁)
        · have hp₂ :
            payload =
              tmVerifierActiveStackSymbolPayload V k ((stkAt₂ time k)[cell]'hcell₂) := by
            simpa [hget] using hp
          simp [TMVerifierStackReadChoice.atomAt,
            tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_selected_payload V p stkAt₁
              time k hcell₁ hp,
            tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_selected_payload V p stkAt₂
              time k hcell₂ hp₂]
        · have hp₂ :
            payload ≠
              tmVerifierActiveStackSymbolPayload V k ((stkAt₂ time k)[cell]'hcell₂) := by
            simpa [hget] using hp
          simp [TMVerifierStackReadChoice.atomAt,
            tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_selected_ne_payload V p
              stkAt₁ time k hcell₁ hp,
            tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_selected_ne_payload V p
              stkAt₂ time k hcell₂ hp₂]
      · have hcell₂ : ¬ cell < (stkAt₂ time k).length := by simpa [hStack] using hcell₁
        simp [TMVerifierStackReadChoice.atomAt,
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt₁
            (u := time) (j := k) (cell := cell) (payload := payload) hcell₁,
          tmVerifierStackSymbolAtom_eval_stackFamilyAssignment_of_not_selected V p stkAt₂
            (u := time) (j := k) (cell := cell) (payload := payload) hcell₂]

noncomputable def tmVerifierSelectedWindowRunStacks
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
      tmVerifierWindowMicroStacks V p t w ((Nat.unpair u).2)

theorem tmVerifierSelectedWindowRunStacks_at_start
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) :
    tmVerifierSelectedWindowRunStacks V p t w t = (tmVerifierRunCfgAt V p t).stk := by
  simp [tmVerifierSelectedWindowRunStacks]

theorem tmVerifierSelectedWindowRunStacks_at_succ
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) :
    tmVerifierSelectedWindowRunStacks V p t w (t + 1) =
      (tmVerifierRunCfgAt V p (t + 1)).stk := by
  by_cases hEq : t + 1 = t
  · omega
  · simp [tmVerifierSelectedWindowRunStacks]

theorem tmVerifierSelectedWindowRunStacks_at_micro
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) (micro : Nat) :
    tmVerifierSelectedWindowRunStacks V p t w (tmVerifierMicroTime t micro) =
      tmVerifierWindowMicroStacks V p t w micro := by
  have hUnpair : (Nat.unpair (tmVerifierMicroTime t micro)).2 = micro := by
    simp
  simp [tmVerifierSelectedWindowRunStacks, hUnpair]

theorem tmVerifierSelectedWindowRunStacks_micro_start_eq_macro
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) :
    ∀ k : tmVerifierStackIndex V,
      tmVerifierSelectedWindowRunStacks V p t w (tmVerifierMicroTime t 0) k =
        tmVerifierSelectedWindowRunStacks V p t w t k := by
  intro k
  rw [tmVerifierSelectedWindowRunStacks_at_micro V p t w 0,
    tmVerifierSelectedWindowRunStacks_at_start]
  simp [tmVerifierWindowMicroStacks, tmVerifierWindowActionsApplyStacks]

theorem tmVerifierSelectedWindowRunStacks_final_eq_macro_succ
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hMatch : tmVerifierWindowActionsMatchStacks w.actions (tmVerifierRunCfgAt V p t).stk)
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s) :
    ∀ k : tmVerifierStackIndex V,
      tmVerifierSelectedWindowRunStacks V p t w (t + 1) k =
        tmVerifierSelectedWindowRunStacks V p t w
          (tmVerifierMicroTime t w.actions.length) k := by
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
  rw [tmVerifierSelectedWindowRunStacks_at_succ,
    tmVerifierSelectedWindowRunStacks_at_micro V p t w w.actions.length]
  exact congrFun hFinal.symm k

theorem tmVerifierWindowStackBoundaryCNFAt_satisfies_stackFamilyAssignment_of_stack_eq
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hStart :
      ∀ k : tmVerifierStackIndex V,
        stkAt (tmVerifierMicroTime t 0) k = stkAt t k)
    (hFinal :
      ∀ k : tmVerifierStackIndex V,
        stkAt (t + 1) k = stkAt (tmVerifierMicroTime t w.actions.length) k) :
    CNF.Satisfies (tmVerifierWindowStackBoundaryCNFAt V p t l s w)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  rw [tmVerifierWindowStackBoundaryCNFAt, CNF.satisfies_append]
  constructor
  · exact tmVerifierFrameAllStacksCNFBetween_satisfies_of_eval_eq V p t
      (tmVerifierMicroTime t 0) (tmVerifierWindowAntecedents V t l s w)
      (tmVerifierStackFamilyAssignment V p stkAt) (by
        intro k _hk cell _hcell choice _hchoice
        exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
          V p stkAt t (tmVerifierMicroTime t 0) k cell choice (hStart k))
  · exact tmVerifierFrameAllStacksCNFBetween_satisfies_of_eval_eq V p
      (tmVerifierMicroTime t w.actions.length) (t + 1)
      (tmVerifierWindowAntecedents V t l s w)
      (tmVerifierStackFamilyAssignment V p stkAt) (by
        intro k _hk cell _hcell choice _hchoice
        exact TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_stack_eq
          V p stkAt (tmVerifierMicroTime t w.actions.length) (t + 1) k cell choice
          (hFinal k))

theorem tmVerifierSelectedWindowRunStacks_boundary_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hMatch : tmVerifierWindowActionsMatchStacks w.actions (tmVerifierRunCfgAt V p t).stk)
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s) :
    CNF.Satisfies (tmVerifierWindowStackBoundaryCNFAt V p t l s w)
      (tmVerifierStackFamilyAssignment V p (tmVerifierSelectedWindowRunStacks V p t w)) := by
  exact tmVerifierWindowStackBoundaryCNFAt_satisfies_stackFamilyAssignment_of_stack_eq V p
    t l s w (tmVerifierSelectedWindowRunStacks V p t w)
    (tmVerifierSelectedWindowRunStacks_micro_start_eq_macro V p t w)
    (tmVerifierSelectedWindowRunStacks_final_eq_macro_succ V p t l s w hw hMatch hl hs)

theorem tmVerifierSelectedWindowRunStacks_actionCNF_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V)
    (antecedents : List Literal)
    (hGuards :
      ∀ g ∈ tmVerifierWindowActionReadGuards t w,
        g.eval
          (tmVerifierStackFamilyAssignment V p (tmVerifierSelectedWindowRunStacks V p t w)) =
          true) :
    CNF.Satisfies
      (tmVerifierWindowStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
        p t w antecedents)
      (tmVerifierStackFamilyAssignment V p (tmVerifierSelectedWindowRunStacks V p t w)) := by
  exact tmVerifierWindowStackActionCNFAt_satisfies_active_applyStacks_of_readGuards_stkAt V
    p t w (tmVerifierSelectedWindowRunStacks V p t w) antecedents
    (fun micro =>
      tmVerifierSelectedWindowRunStacks_at_micro V p t w micro)
    hGuards

theorem tmVerifierSelectedWindowRunStacks_transitionWindow_satisfies
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hMatch : tmVerifierWindowActionsMatchStacks w.actions (tmVerifierRunCfgAt V p t).stk)
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s)
    (hGuards :
      ∀ g ∈ tmVerifierWindowActionReadGuards t w,
        g.eval
          (tmVerifierStackFamilyAssignment V p (tmVerifierSelectedWindowRunStacks V p t w)) =
          true) :
    CNF.Satisfies
      (tmVerifierWindowControlCNFAt V t l s w ++
        tmVerifierWindowStackBoundaryCNFAt V p t l s w ++
          tmVerifierWindowStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
            p t w (tmVerifierWindowAntecedents V t l s w))
      (tmVerifierStackFamilyAssignment V p (tmVerifierSelectedWindowRunStacks V p t w)) := by
  rw [CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    constructor
    · exact tmVerifierWindowControlCNFAt_satisfies_run_selected V p t l s w
        (tmVerifierSelectedWindowRunStacks V p t w) hw hMatch hl hs
    · exact tmVerifierSelectedWindowRunStacks_boundary_satisfies V p t l s w
        hw hMatch hl hs
  · exact tmVerifierSelectedWindowRunStacks_actionCNF_satisfies V p t w
      (tmVerifierWindowAntecedents V t l s w) hGuards

theorem tmVerifierImplicationClause_satisfies_of_false_antecedent_append
    (antecedents suffix : List Literal) (conclusion ant : Literal) (a : Assignment)
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    Clause.Satisfies (tmVerifierImplicationClause (antecedents ++ suffix) conclusion) a :=
  tmVerifierImplicationClause_satisfies_of_false_antecedent (antecedents ++ suffix)
    conclusion ant a (List.mem_append.mpr (Or.inl hmem)) hAnt

theorem tmVerifierWindowControlCNFAt_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    {ant : Literal}
    (hmem : ant ∈ tmVerifierWindowAntecedents V t l s w)
    (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierWindowControlCNFAt V t l s w) a := by
  intro c hc
  have hc' :
      c =
          tmVerifierImplicationClause (tmVerifierWindowAntecedents V t l s w)
            (tmVerifierLabelAtom V (t + 1) w.nextLabel) ∨
        c =
          tmVerifierImplicationClause (tmVerifierWindowAntecedents V t l s w)
            (tmVerifierStateAtom V (t + 1) w.nextState) := by
    simpa [tmVerifierWindowControlCNFAt] using hc
  rcases hc' with rfl | rfl
  · exact tmVerifierImplicationClause_satisfies_of_false_antecedent
      (tmVerifierWindowAntecedents V t l s w)
      (tmVerifierLabelAtom V (t + 1) w.nextLabel) ant a hmem hAnt
  · exact tmVerifierImplicationClause_satisfies_of_false_antecedent
      (tmVerifierWindowAntecedents V t l s w)
      (tmVerifierStateAtom V (t + 1) w.nextState) ant a hmem hAnt

theorem tmVerifierFrameChoiceCNFBetween_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (choice : TMVerifierStackReadChoice V k) (antecedents : List Literal)
    (a : Assignment) {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierFrameChoiceCNFBetween V tin tout k cell choice antecedents)
      a := by
  intro c hc
  have hc' :
      c = tmVerifierFrameForwardClause V tin tout k cell choice antecedents ∨
        c = tmVerifierFrameBackwardClause V tin tout k cell choice antecedents := by
    simpa [tmVerifierFrameChoiceCNFBetween] using hc
  rcases hc' with rfl | rfl
  · exact tmVerifierImplicationClause_satisfies_of_false_antecedent_append antecedents
      [TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice]
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice) ant a hmem
      hAnt
  · exact tmVerifierImplicationClause_satisfies_of_false_antecedent_append antecedents
      [TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice]
      (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice) ant a hmem
      hAnt

theorem tmVerifierFrameCellCNFBetween_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment) {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierFrameCellCNFBetween V tin tout k cell antecedents) a := by
  intro c hc
  rw [tmVerifierFrameCellCNFBetween] at hc
  rcases List.mem_flatMap.mp hc with ⟨choice, _hchoice, hc⟩
  exact tmVerifierFrameChoiceCNFBetween_satisfies_of_false_antecedent V tin tout k cell
    choice antecedents a hmem hAnt c hc

theorem tmVerifierFrameStackCNFBetween_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (antecedents : List Literal)
    (a : Assignment) {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierFrameStackCNFBetween V p tin tout k antecedents) a := by
  intro c hc
  rw [tmVerifierFrameStackCNFBetween] at hc
  rcases List.mem_flatMap.mp hc with ⟨cell, _hcell, hc⟩
  exact tmVerifierFrameCellCNFBetween_satisfies_of_false_antecedent V tin tout k cell
    antecedents a hmem hAnt c hc

theorem tmVerifierFrameAllStacksCNFBetween_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (antecedents : List Literal) (a : Assignment)
    {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierFrameAllStacksCNFBetween V p tin tout antecedents) a := by
  intro c hc
  rw [tmVerifierFrameAllStacksCNFBetween] at hc
  rcases List.mem_flatMap.mp hc with ⟨k, _hk, hc⟩
  exact tmVerifierFrameStackCNFBetween_satisfies_of_false_antecedent V p tin tout k
    antecedents a hmem hAnt c hc

theorem tmVerifierPushTopCNF_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (tout : Nat) (raw : TMVerifierStackSymbol V) (antecedents : List Literal)
    (a : Assignment) {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierPushTopCNF V B tout raw antecedents) a := by
  intro c hc
  have hc' :
      c = tmVerifierImplicationClause antecedents
        (tmVerifierStackSymbolAtom V tout raw.stack 0 (B.payload raw)) := by
    simpa [tmVerifierPushTopCNF] using hc
  subst c
  exact tmVerifierImplicationClause_satisfies_of_false_antecedent antecedents
    (tmVerifierStackSymbolAtom V tout raw.stack 0 (B.payload raw)) ant a hmem hAnt

theorem tmVerifierPushShiftCellCNF_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment) {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierPushShiftCellCNF V tin tout k cell antecedents) a := by
  intro c hc
  rw [tmVerifierPushShiftCellCNF] at hc
  rcases List.mem_map.mp hc with ⟨choice, _hchoice, rfl⟩
  exact tmVerifierImplicationClause_satisfies_of_false_antecedent_append antecedents
    [TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin cell choice]
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout (cell + 1) choice) ant a
    hmem hAnt

theorem tmVerifierPopShiftCellCNF_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (tin tout : Nat) (k : tmVerifierStackIndex V) (cell : Nat)
    (antecedents : List Literal) (a : Assignment) {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierPopShiftCellCNF V tin tout k cell antecedents) a := by
  intro c hc
  rw [tmVerifierPopShiftCellCNF] at hc
  rcases List.mem_map.mp hc with ⟨choice, _hchoice, rfl⟩
  exact tmVerifierImplicationClause_satisfies_of_false_antecedent_append antecedents
    [TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin (cell + 1) choice]
    (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tout cell choice) ant a hmem
    hAnt

theorem tmVerifierPushActionCNFBetween_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (raw : TMVerifierStackSymbol V) (antecedents : List Literal) (a : Assignment)
    {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierPushActionCNFBetween V B p tin tout raw antecedents) a := by
  rw [tmVerifierPushActionCNFBetween, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    constructor
    · exact tmVerifierPushTopCNF_satisfies_of_false_antecedent V B tout raw
        antecedents a hmem hAnt
    · intro c hc
      rcases List.mem_flatMap.mp hc with ⟨cell, _hcell, hc⟩
      exact tmVerifierPushShiftCellCNF_satisfies_of_false_antecedent V tin tout
        raw.stack cell antecedents a hmem hAnt c hc
  · intro c hc
    rcases List.mem_flatMap.mp hc with ⟨k, _hk, hc⟩
    exact tmVerifierFrameStackCNFBetween_satisfies_of_false_antecedent V p tin tout k
      antecedents a hmem hAnt c hc

theorem tmVerifierPopActionCNFBetween_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (k : tmVerifierStackIndex V) (antecedents : List Literal) (a : Assignment)
    {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierPopActionCNFBetween V p tin tout k antecedents) a := by
  rw [tmVerifierPopActionCNFBetween, CNF.satisfies_append]
  constructor
  · intro c hc
    rcases List.mem_flatMap.mp hc with ⟨cell, _hcell, hc⟩
    exact tmVerifierPopShiftCellCNF_satisfies_of_false_antecedent V tin tout k cell
      antecedents a hmem hAnt c hc
  · intro c hc
    rcases List.mem_flatMap.mp hc with ⟨j, _hj, hc⟩
    exact tmVerifierFrameStackCNFBetween_satisfies_of_false_antecedent V p tin tout j
      antecedents a hmem hAnt c hc

theorem tmVerifierPreserveAllStacksActionCNFBetween_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (tin tout : Nat) (antecedents : List Literal) (a : Assignment)
    {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierPreserveAllStacksActionCNFBetween V p tin tout antecedents)
      a := by
  simpa [tmVerifierPreserveAllStacksActionCNFBetween] using
    tmVerifierFrameAllStacksCNFBetween_satisfies_of_false_antecedent V p tin tout
      antecedents a hmem hAnt

theorem tmVerifierStackActionEffectCNFBetween_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (antecedents : List Literal) (act : TMVerifierStackAction V) (a : Assignment)
    {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierStackActionEffectCNFBetween V B p tin tout antecedents act)
      a := by
  cases act with
  | push raw =>
      exact tmVerifierPushActionCNFBetween_satisfies_of_false_antecedent V B p tin tout
        raw antecedents a hmem hAnt
  | pop k choice =>
      exact tmVerifierPopActionCNFBetween_satisfies_of_false_antecedent V p tin tout k
        antecedents a hmem hAnt
  | peek k choice =>
      exact tmVerifierPreserveAllStacksActionCNFBetween_satisfies_of_false_antecedent V p
        tin tout antecedents a hmem hAnt
  | load =>
      exact tmVerifierPreserveAllStacksActionCNFBetween_satisfies_of_false_antecedent V p
        tin tout antecedents a hmem hAnt
  | branch tag =>
      exact tmVerifierPreserveAllStacksActionCNFBetween_satisfies_of_false_antecedent V p
        tin tout antecedents a hmem hAnt

theorem tmVerifierStackActionReadCNFAt_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (tin : Nat) (antecedents : List Literal) (act : TMVerifierStackAction V)
    (a : Assignment) {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierStackActionReadCNFAt tin antecedents act) a := by
  cases act with
  | push raw =>
      simp [tmVerifierStackActionReadCNFAt]
  | peek k choice =>
      intro c hc
      have hc' :
          c = tmVerifierImplicationClause antecedents
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin 0 choice) := by
        simpa [tmVerifierStackActionReadCNFAt] using hc
      subst c
      exact tmVerifierImplicationClause_satisfies_of_false_antecedent antecedents
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin 0 choice) ant a hmem hAnt
  | pop k choice =>
      intro c hc
      have hc' :
          c = tmVerifierImplicationClause antecedents
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin 0 choice) := by
        simpa [tmVerifierStackActionReadCNFAt] using hc
      subst c
      exact tmVerifierImplicationClause_satisfies_of_false_antecedent antecedents
        (TMVerifierStackReadChoice.atomAt (V := V) (k := k) tin 0 choice) ant a hmem hAnt
  | load =>
      simp [tmVerifierStackActionReadCNFAt]
  | branch tag =>
      simp [tmVerifierStackActionReadCNFAt]

theorem tmVerifierStackActionCNFBetween_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (tin tout : Nat)
    (antecedents : List Literal) (act : TMVerifierStackAction V) (a : Assignment)
    {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierStackActionCNFBetween V B p tin tout antecedents act) a := by
  rw [tmVerifierStackActionCNFBetween, CNF.satisfies_append]
  exact ⟨tmVerifierStackActionEffectCNFBetween_satisfies_of_false_antecedent V B p tin
      tout antecedents act a hmem hAnt,
    tmVerifierStackActionReadCNFAt_satisfies_of_false_antecedent tin antecedents act a
      hmem hAnt⟩

theorem tmVerifierWindowStackActionCNFAt_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal) (a : Assignment)
    {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierWindowStackActionCNFAt V B p t w antecedents) a := by
  apply tmVerifierWindowStackActionCNFAt_satisfies_of_actions
  intro entry _hentry
  exact tmVerifierStackActionCNFBetween_satisfies_of_false_antecedent V B p
    (tmVerifierMicroTime t entry.2) (tmVerifierMicroTime t (entry.2 + 1))
    antecedents entry.1 a hmem hAnt

theorem tmVerifierWindowStackBoundaryCNFAt_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment) {ant : Literal}
    (hmem : ant ∈ tmVerifierWindowAntecedents V t l s w)
    (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierWindowStackBoundaryCNFAt V p t l s w) a := by
  rw [tmVerifierWindowStackBoundaryCNFAt, CNF.satisfies_append]
  constructor
  · exact tmVerifierFrameAllStacksCNFBetween_satisfies_of_false_antecedent V p t
      (tmVerifierMicroTime t 0) (tmVerifierWindowAntecedents V t l s w) a hmem hAnt
  · exact tmVerifierFrameAllStacksCNFBetween_satisfies_of_false_antecedent V p
      (tmVerifierMicroTime t w.actions.length) (t + 1)
      (tmVerifierWindowAntecedents V t l s w) a hmem hAnt

theorem tmVerifierWindowTransitionCNF_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment) {ant : Literal}
    (hmem : ant ∈ tmVerifierWindowAntecedents V t l s w)
    (hAnt : ant.eval a = false) :
    CNF.Satisfies
      (tmVerifierWindowControlCNFAt V t l s w ++
        tmVerifierWindowStackBoundaryCNFAt V p t l s w ++
          tmVerifierWindowStackActionCNFAt V B p t w
            (tmVerifierWindowAntecedents V t l s w)) a := by
  rw [CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    exact ⟨tmVerifierWindowControlCNFAt_satisfies_of_false_antecedent V t l s w a
        hmem hAnt,
      tmVerifierWindowStackBoundaryCNFAt_satisfies_of_false_antecedent V p t l s w a
        hmem hAnt⟩
  · exact tmVerifierWindowStackActionCNFAt_satisfies_of_false_antecedent V B p t w
      (tmVerifierWindowAntecedents V t l s w) a hmem hAnt

theorem tmVerifierStmtWindowsAt_exists_selected_window_transitionWindow
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s) :
    ∃ w : TMVerifierStmtWindow V,
      w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s ∧
        CNF.Satisfies
          (tmVerifierWindowControlCNFAt V t l s w ++
            tmVerifierWindowStackBoundaryCNFAt V p t l s w ++
              tmVerifierWindowStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
                p t w (tmVerifierWindowAntecedents V t l s w))
          (tmVerifierStackFamilyAssignment V p (tmVerifierSelectedWindowRunStacks V p t w)) ∧
          tmVerifierWindowActionsMatchStacks w.actions (tmVerifierRunCfgAt V p t).stk := by
  rcases tmVerifierStmtWindowsAt_exists_true_actionReadGuards_topStack V p t l s with
    ⟨w, hw, hguardsMicro, hmatch⟩
  have hguardsMixed :
      ∀ g ∈ tmVerifierWindowActionReadGuards t w,
        g.eval
          (tmVerifierStackFamilyAssignment V p (tmVerifierSelectedWindowRunStacks V p t w)) =
          true := by
    intro g hg
    have hguardsBase := hguardsMicro g hg
    rw [tmVerifierWindowMicroStackFamilyAssignment] at hguardsBase
    rw [tmVerifierWindowActionReadGuards] at hg
    rcases List.mem_flatMap.mp hg with ⟨entry, hentry, hg⟩
    rcases entry with ⟨act, idx⟩
    have hTimeStack :
        tmVerifierSelectedWindowRunStacks V p t w (tmVerifierMicroTime t idx) =
          tmVerifierWindowMicroStacks V p t w idx :=
      tmVerifierSelectedWindowRunStacks_at_micro V p t w idx
    let microStacks := fun u => tmVerifierWindowMicroStacks V p t w (Nat.unpair u).2
    cases act with
    | push raw =>
        simp [TMVerifierStackAction.readGuardAt] at hg
    | peek k choice =>
        have hg' :
            g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
              (tmVerifierMicroTime t idx) 0 choice := by
          simpa [TMVerifierStackAction.readGuardAt] using hg
        subst g
        have hUnpair :
            (Nat.unpair (tmVerifierMicroTime t idx)).2 = idx := by
          simp
        have hBaseStack :
            microStacks (tmVerifierMicroTime t idx) k =
              tmVerifierWindowMicroStacks V p t w idx k := by
          simp [microStacks, hUnpair]
        have hEvalEq :=
          TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_time_stack_eq
            V p (tmVerifierSelectedWindowRunStacks V p t w) microStacks
            (tmVerifierMicroTime t idx) k 0 choice
            ((congrFun hTimeStack k).trans hBaseStack.symm)
        exact
          hEvalEq.trans (by simpa [microStacks] using hguardsBase)
    | pop k choice =>
        have hg' :
            g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
              (tmVerifierMicroTime t idx) 0 choice := by
          simpa [TMVerifierStackAction.readGuardAt] using hg
        subst g
        have hUnpair :
            (Nat.unpair (tmVerifierMicroTime t idx)).2 = idx := by
          simp
        have hBaseStack :
            microStacks (tmVerifierMicroTime t idx) k =
              tmVerifierWindowMicroStacks V p t w idx k := by
          simp [microStacks, hUnpair]
        have hEvalEq :=
          TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_time_stack_eq
            V p (tmVerifierSelectedWindowRunStacks V p t w) microStacks
            (tmVerifierMicroTime t idx) k 0 choice
            ((congrFun hTimeStack k).trans hBaseStack.symm)
        exact
          hEvalEq.trans (by simpa [microStacks] using hguardsBase)
    | load =>
        simp [TMVerifierStackAction.readGuardAt] at hg
    | branch tag =>
        simp [TMVerifierStackAction.readGuardAt] at hg
  exact ⟨w, hw,
    tmVerifierSelectedWindowRunStacks_transitionWindow_satisfies V p t l s w hw hmatch
      hl hs hguardsMixed,
    hmatch⟩

end SAT
end ComplexityReduction
