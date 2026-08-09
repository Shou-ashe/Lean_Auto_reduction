/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.GlobalAcceptedRun
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.TransitionRowsAggregation

/-!
Transition-row aggregation for fixed-pair global micro rows.

This mirrors the local transition-row aggregation lemmas, but every action
micro row is named by `tmVerifierFixedMicroTime V p t micro`.
-/

namespace ComplexityReduction
namespace SAT

/-! ### False-antecedent helpers for fixed stack rows -/

theorem tmVerifierWindowFixedStackActionCNFAt_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal) (a : Assignment)
    {ant : Literal}
    (hmem : ant ∈ antecedents) (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierWindowFixedStackActionCNFAt V B p t w antecedents) a := by
  intro c hc
  rw [tmVerifierWindowFixedStackActionCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨entry, _hentry, hc⟩
  exact tmVerifierStackActionCNFBetween_satisfies_of_false_antecedent V B p
    (tmVerifierFixedMicroTime V p t entry.2)
    (tmVerifierFixedMicroTime V p t (entry.2 + 1))
    antecedents entry.1 a hmem hAnt c hc

theorem tmVerifierWindowFixedStackBoundaryCNFAt_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment) {ant : Literal}
    (hmem : ant ∈ tmVerifierWindowFixedAntecedents V p t l s w)
    (hAnt : ant.eval a = false) :
    CNF.Satisfies (tmVerifierWindowFixedStackBoundaryCNFAt V p t l s w) a := by
  rw [tmVerifierWindowFixedStackBoundaryCNFAt, CNF.satisfies_append]
  constructor
  · exact tmVerifierFrameAllStacksCNFBetween_satisfies_of_false_antecedent V p t
      (tmVerifierFixedMicroTime V p t 0) (tmVerifierWindowFixedAntecedents V p t l s w)
      a hmem hAnt
  · exact tmVerifierFrameAllStacksCNFBetween_satisfies_of_false_antecedent V p
      (tmVerifierFixedMicroTime V p t w.actions.length) (t + 1)
      (tmVerifierWindowFixedAntecedents V p t l s w) a hmem hAnt

theorem tmVerifierWindowFixedStackCNF_satisfies_of_false_antecedent
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment) {ant : Literal}
    (hmem : ant ∈ tmVerifierWindowFixedAntecedents V p t l s w)
    (hAnt : ant.eval a = false) :
    CNF.Satisfies
      (tmVerifierWindowFixedStackBoundaryCNFAt V p t l s w ++
        tmVerifierWindowFixedStackActionCNFAt V B p t w
          (tmVerifierWindowFixedAntecedents V p t l s w)) a := by
  rw [CNF.satisfies_append]
  exact ⟨tmVerifierWindowFixedStackBoundaryCNFAt_satisfies_of_false_antecedent V p t
      l s w a hmem hAnt,
    tmVerifierWindowFixedStackActionCNFAt_satisfies_of_false_antecedent V B p t w
      (tmVerifierWindowFixedAntecedents V p t l s w) a hmem hAnt⟩

/-! ### Aggregation outside the active control row -/

theorem tmVerifierTransitionFixedWindowStackCNFAt_satisfies_current_label_state
    {L : EncodedDecisionProblem} (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s)
    (hCurrent :
      ∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies
            (tmVerifierWindowFixedStackBoundaryCNFAt V p t l s w ++
              tmVerifierWindowFixedStackActionCNFAt V B p t w
                (tmVerifierWindowFixedAntecedents V p t l s w))
            (tmVerifierStackFamilyAssignment V p stkAt)) :
    CNF.Satisfies (tmVerifierTransitionFixedWindowStackCNFAt V B p t)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro c hc
  rw [tmVerifierTransitionFixedWindowStackCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨l', _hl', hc⟩
  rcases List.mem_flatMap.mp hc with ⟨s', _hs', hc⟩
  rcases List.mem_flatMap.mp hc with ⟨w, hw, hc⟩
  by_cases hLabelEq : l' = l
  · subst l'
    by_cases hStateEq : s' = s
    · subst s'
      exact hCurrent w hw c hc
    · have hFalse :
          (tmVerifierStateAtom V t s').eval
              (tmVerifierStackFamilyAssignment V p stkAt) = false := by
        exact tmVerifierStateAtom_eval_stackFamilyAssignment_false_of_ne V p stkAt t s'
          (by
            intro h
            exact hStateEq (by simpa [hs] using h))
      exact tmVerifierWindowFixedStackCNF_satisfies_of_false_antecedent V B p t l s' w
        (tmVerifierStackFamilyAssignment V p stkAt)
        (tmVerifierWindowFixedAntecedents_state_mem V p t l s' w) hFalse c hc
  · have hFalse :
        (tmVerifierLabelAtom V t (some l')).eval
            (tmVerifierStackFamilyAssignment V p stkAt) = false := by
      exact tmVerifierLabelAtom_eval_stackFamilyAssignment_false_of_ne V p stkAt t
        (some l') (by
          intro h
          exact hLabelEq (Option.some.inj (by simpa [hl] using h)))
    exact tmVerifierWindowFixedStackCNF_satisfies_of_false_antecedent V B p t l' s' w
      (tmVerifierStackFamilyAssignment V p stkAt)
      (tmVerifierWindowFixedAntecedents_label_mem V p t l' s' w) hFalse c hc

theorem tmVerifierTransitionFixedControlCNFAt_satisfies_current_label_state
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s)
    (hControlCurrent :
      ∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies (tmVerifierWindowFixedControlCNFAt V p t l s w)
            (tmVerifierStackFamilyAssignment V p stkAt)) :
    CNF.Satisfies (tmVerifierTransitionFixedControlCNFAt V p t)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  intro c hc
  rw [tmVerifierTransitionFixedControlCNFAt] at hc
  rcases List.mem_flatMap.mp hc with ⟨l', _hl', hc⟩
  rcases List.mem_flatMap.mp hc with ⟨s', _hs', hc⟩
  rcases List.mem_flatMap.mp hc with ⟨w, hw, hc⟩
  by_cases hLabelEq : l' = l
  · subst l'
    by_cases hStateEq : s' = s
    · subst s'
      exact hControlCurrent w hw c hc
    · have hFalse :
          (tmVerifierStateAtom V t s').eval
              (tmVerifierStackFamilyAssignment V p stkAt) = false := by
        exact tmVerifierStateAtom_eval_stackFamilyAssignment_false_of_ne V p stkAt t s'
          (by
            intro h
            exact hStateEq (by simpa [hs] using h))
      exact tmVerifierWindowFixedControlCNFAt_satisfies_of_false_antecedent V p t l s' w
        (tmVerifierStackFamilyAssignment V p stkAt)
        (tmVerifierWindowFixedAntecedents_state_mem V p t l s' w) hFalse c hc
  · have hFalse :
        (tmVerifierLabelAtom V t (some l')).eval
            (tmVerifierStackFamilyAssignment V p stkAt) = false := by
      exact tmVerifierLabelAtom_eval_stackFamilyAssignment_false_of_ne V p stkAt t
        (some l') (by
          intro h
          exact hLabelEq (Option.some.inj (by simpa [hl] using h)))
    exact tmVerifierWindowFixedControlCNFAt_satisfies_of_false_antecedent V p t l' s' w
      (tmVerifierStackFamilyAssignment V p stkAt)
      (tmVerifierWindowFixedAntecedents_label_mem V p t l' s' w) hFalse c hc

theorem tmVerifierTransitionFixedRowCNFAt_satisfies_current_label_state
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (stkAt : Nat → ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s)
    (hControlCurrent :
      ∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies (tmVerifierWindowFixedControlCNFAt V p t l s w)
            (tmVerifierStackFamilyAssignment V p stkAt))
    (hStackCurrent :
      ∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies
            (tmVerifierWindowFixedStackBoundaryCNFAt V p t l s w ++
              tmVerifierWindowFixedStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
                p t w (tmVerifierWindowFixedAntecedents V p t l s w))
            (tmVerifierStackFamilyAssignment V p stkAt)) :
    CNF.Satisfies (tmVerifierTransitionFixedRowCNFAt V
        (tmVerifierActivePushPayloadBoundary V) p t)
      (tmVerifierStackFamilyAssignment V p stkAt) := by
  rw [tmVerifierTransitionFixedRowCNFAt, CNF.satisfies_append]
  constructor
  · rw [CNF.satisfies_append]
    exact ⟨tmVerifierTransitionFixedControlCNFAt_satisfies_current_label_state V p t l s
        stkAt hl hs hControlCurrent,
      tmVerifierTransitionFixedWindowStackCNFAt_satisfies_current_label_state V
        (tmVerifierActivePushPayloadBoundary V) p t l s stkAt hl hs hStackCurrent⟩
  · exact tmVerifierHaltedRowsCNFAt_satisfies_of_nonhalting_label V p t stkAt hl

/-! ### Fixed same-control generated-window aggregation -/

theorem tmVerifierWindowFixedActionReadGuardsFrom_cons_of_fixedReadGuardAt_nil
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (p : L.Instance.Carrier × V.Cert.Carrier) (t idx : Nat)
    (act : TMVerifierStackAction V) (actions : List (TMVerifierStackAction V))
    (hRead : act.fixedReadGuardAt p t idx = []) :
    tmVerifierWindowFixedActionReadGuardsFrom p t (act :: actions) idx =
      tmVerifierWindowFixedActionReadGuardsFrom p t actions (idx + 1) := by
  simp [tmVerifierWindowFixedActionReadGuardsFrom, hRead]

theorem tmVerifierStmtWindowsAt_unique_of_true_fixedActionReadGuardsFrom
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stmt : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ)
    (idx : Nat) (a : Assignment)
    (hDomains :
      ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t stmt s →
        ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx idx →
          ∀ k : tmVerifierStackIndex V,
            CNF.Satisfies
              (tmVerifierStackCellDomainsCNFAt V p
                (tmVerifierFixedMicroTime V p t entry.2) k)
              a)
    {w₁ w₂ : TMVerifierStmtWindow V}
    (hw₁ : w₁ ∈ tmVerifierStmtWindowsAt V t stmt s)
    (hw₂ : w₂ ∈ tmVerifierStmtWindowsAt V t stmt s)
    (hGuards₁ :
      ∀ g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t w₁.actions idx,
        g.eval a = true)
    (hGuards₂ :
      ∀ g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t w₂.actions idx,
        g.eval a = true) :
    w₁ = w₂ := by
  induction stmt generalizing s idx w₁ w₂ with
  | push k f q ih =>
      let act : TMVerifierStackAction V :=
        TMVerifierStackAction.push (V := V) { stack := k, symbol := f s }
      rcases List.mem_map.mp hw₁ with ⟨tail₁, htail₁, rfl⟩
      rcases List.mem_map.mp hw₂ with ⟨tail₂, htail₂, rfl⟩
      have hTailDomains :
          ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t q s →
            ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx (idx + 1) →
              ∀ j : tmVerifierStackIndex V,
                CNF.Satisfies
                  (tmVerifierStackCellDomainsCNFAt V p
                    (tmVerifierFixedMicroTime V p t entry.2) j) a := by
        intro w hw entry hentry j
        exact hDomains (TMVerifierStmtWindow.consAction act w)
          (List.mem_map.mpr ⟨w, hw, rfl⟩) entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
      have hTailGuards₁ :
          ∀ g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t tail₁.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        have hEq :
            tmVerifierWindowFixedActionReadGuardsFrom p t
                (TMVerifierStmtWindow.consAction act tail₁).actions idx =
              tmVerifierWindowFixedActionReadGuardsFrom p t tail₁.actions (idx + 1) := by
          exact tmVerifierWindowFixedActionReadGuardsFrom_cons_of_fixedReadGuardAt_nil
            p t idx act tail₁.actions (by simp [act, TMVerifierStackAction.fixedReadGuardAt])
        exact hGuards₁ g (by simpa [hEq] using hg)
      have hTailGuards₂ :
          ∀ g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t tail₂.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        have hEq :
            tmVerifierWindowFixedActionReadGuardsFrom p t
                (TMVerifierStmtWindow.consAction act tail₂).actions idx =
              tmVerifierWindowFixedActionReadGuardsFrom p t tail₂.actions (idx + 1) := by
          exact tmVerifierWindowFixedActionReadGuardsFrom_cons_of_fixedReadGuardAt_nil
            p t idx act tail₂.actions (by simp [act, TMVerifierStackAction.fixedReadGuardAt])
        exact hGuards₂ g (by simpa [hEq] using hg)
      have hTail := ih s (idx + 1) hTailDomains htail₁ htail₂
        hTailGuards₁ hTailGuards₂
      subst tail₂
      rfl
  | peek k f q ih =>
      rcases List.mem_flatMap.mp hw₁ with ⟨choice₁, hchoice₁, hmem₁⟩
      rcases List.mem_map.mp hmem₁ with ⟨tail₁, htail₁, rfl⟩
      rcases List.mem_flatMap.mp hw₂ with ⟨choice₂, hchoice₂, hmem₂⟩
      rcases List.mem_map.mp hmem₂ with ⟨tail₂, htail₂, rfl⟩
      let act₁ : TMVerifierStackAction V := TMVerifierStackAction.peek (V := V) k choice₁
      have hHead₁ :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
            (tmVerifierFixedMicroTime V p t idx) 0 choice₁).eval a = true := by
        exact hGuards₁ _ (by
          simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.fixedReadGuardAt])
      have hHead₂ :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
            (tmVerifierFixedMicroTime V p t idx) 0 choice₂).eval a = true := by
        exact hGuards₂ _ (by
          simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.fixedReadGuardAt])
      have hEntry₁ :
          (act₁, idx) ∈
            (TMVerifierStmtWindow.consAction act₁
              (TMVerifierStmtWindow.consGuard
                (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice₁)
                tail₁)).actions.zipIdx idx := by
        simp [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard]
      have hDomain :
          CNF.Satisfies
            (tmVerifierStackCellDomainsCNFAt V p (tmVerifierFixedMicroTime V p t idx) k)
            a :=
        hDomains
          (TMVerifierStmtWindow.consAction act₁
            (TMVerifierStmtWindow.consGuard
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice₁)
              tail₁))
          (List.mem_flatMap.mpr
            ⟨choice₁, hchoice₁, List.mem_map.mpr ⟨tail₁, htail₁, rfl⟩⟩)
          (act₁, idx) hEntry₁ k
      have hChoiceEq : choice₁ = choice₂ :=
        tmVerifierStackCellDomainsCNFAt_satisfies_choice_eq V p
          (tmVerifierFixedMicroTime V p t idx) k 0 a hDomain
          (tmVerifierCellRange_zero_mem V p) choice₁ choice₂ hchoice₁ hchoice₂
          hHead₁ hHead₂
      subst choice₂
      have hTailDomains :
          ∀ w : TMVerifierStmtWindow V,
            w ∈ tmVerifierStmtWindowsAt V t q (f s choice₁.toOption) →
              ∀ entry : TMVerifierStackAction V × Nat,
                entry ∈ w.actions.zipIdx (idx + 1) →
                ∀ j : tmVerifierStackIndex V,
                  CNF.Satisfies
                    (tmVerifierStackCellDomainsCNFAt V p
                      (tmVerifierFixedMicroTime V p t entry.2) j) a := by
        intro w hw entry hentry j
        let parent : TMVerifierStmtWindow V :=
          TMVerifierStmtWindow.consAction act₁
            (TMVerifierStmtWindow.consGuard
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice₁) w)
        have hparent :
            parent ∈ tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.peek k f q) s :=
          List.mem_flatMap.mpr
            ⟨choice₁, hchoice₁, List.mem_map.mpr ⟨w, hw, by simp [parent, act₁]⟩⟩
        exact hDomains parent hparent entry (by
          simpa [parent, act₁, TMVerifierStmtWindow.consAction,
            TMVerifierStmtWindow.consGuard] using Or.inr hentry) j
      have hTailGuards₁ :
          ∀ g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t tail₁.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₁ g (by
          have hmem :
              g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                    (tmVerifierFixedMicroTime V p t idx) 0 choice₁ ∨
                g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t tail₁.actions
                  (idx + 1) := Or.inr hg
          simpa [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.fixedReadGuardAt] using hmem)
      have hTailGuards₂ :
          ∀ g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t tail₂.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₂ g (by
          have hmem :
              g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                    (tmVerifierFixedMicroTime V p t idx) 0 choice₁ ∨
                g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t tail₂.actions
                  (idx + 1) := Or.inr hg
          simpa [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.fixedReadGuardAt] using hmem)
      have hTail := ih (f s choice₁.toOption) (idx + 1) hTailDomains
        htail₁ htail₂ hTailGuards₁ hTailGuards₂
      subst tail₂
      rfl
  | pop k f q ih =>
      rcases List.mem_flatMap.mp hw₁ with ⟨choice₁, hchoice₁, hmem₁⟩
      rcases List.mem_map.mp hmem₁ with ⟨tail₁, htail₁, rfl⟩
      rcases List.mem_flatMap.mp hw₂ with ⟨choice₂, hchoice₂, hmem₂⟩
      rcases List.mem_map.mp hmem₂ with ⟨tail₂, htail₂, rfl⟩
      let act₁ : TMVerifierStackAction V := TMVerifierStackAction.pop (V := V) k choice₁
      have hHead₁ :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
            (tmVerifierFixedMicroTime V p t idx) 0 choice₁).eval a = true := by
        exact hGuards₁ _ (by
          simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.fixedReadGuardAt])
      have hHead₂ :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
            (tmVerifierFixedMicroTime V p t idx) 0 choice₂).eval a = true := by
        exact hGuards₂ _ (by
          simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.fixedReadGuardAt])
      have hEntry₁ :
          (act₁, idx) ∈
            (TMVerifierStmtWindow.consAction act₁
              (TMVerifierStmtWindow.consGuard
                (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice₁)
                tail₁)).actions.zipIdx idx := by
        simp [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard]
      have hDomain :
          CNF.Satisfies
            (tmVerifierStackCellDomainsCNFAt V p (tmVerifierFixedMicroTime V p t idx) k)
            a :=
        hDomains
          (TMVerifierStmtWindow.consAction act₁
            (TMVerifierStmtWindow.consGuard
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice₁)
              tail₁))
          (List.mem_flatMap.mpr
            ⟨choice₁, hchoice₁, List.mem_map.mpr ⟨tail₁, htail₁, rfl⟩⟩)
          (act₁, idx) hEntry₁ k
      have hChoiceEq : choice₁ = choice₂ :=
        tmVerifierStackCellDomainsCNFAt_satisfies_choice_eq V p
          (tmVerifierFixedMicroTime V p t idx) k 0 a hDomain
          (tmVerifierCellRange_zero_mem V p) choice₁ choice₂ hchoice₁ hchoice₂
          hHead₁ hHead₂
      subst choice₂
      have hTailDomains :
          ∀ w : TMVerifierStmtWindow V,
            w ∈ tmVerifierStmtWindowsAt V t q (f s choice₁.toOption) →
              ∀ entry : TMVerifierStackAction V × Nat,
                entry ∈ w.actions.zipIdx (idx + 1) →
                ∀ j : tmVerifierStackIndex V,
                  CNF.Satisfies
                    (tmVerifierStackCellDomainsCNFAt V p
                      (tmVerifierFixedMicroTime V p t entry.2) j) a := by
        intro w hw entry hentry j
        let parent : TMVerifierStmtWindow V :=
          TMVerifierStmtWindow.consAction act₁
            (TMVerifierStmtWindow.consGuard
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice₁) w)
        have hparent :
            parent ∈ tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.pop k f q) s :=
          List.mem_flatMap.mpr
            ⟨choice₁, hchoice₁, List.mem_map.mpr ⟨w, hw, by simp [parent, act₁]⟩⟩
        exact hDomains parent hparent entry (by
          simpa [parent, act₁, TMVerifierStmtWindow.consAction,
            TMVerifierStmtWindow.consGuard] using Or.inr hentry) j
      have hTailGuards₁ :
          ∀ g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t tail₁.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₁ g (by
          have hmem :
              g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                    (tmVerifierFixedMicroTime V p t idx) 0 choice₁ ∨
                g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t tail₁.actions
                  (idx + 1) := Or.inr hg
          simpa [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.fixedReadGuardAt] using hmem)
      have hTailGuards₂ :
          ∀ g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t tail₂.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₂ g (by
          have hmem :
              g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                    (tmVerifierFixedMicroTime V p t idx) 0 choice₁ ∨
                g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t tail₂.actions
                  (idx + 1) := Or.inr hg
          simpa [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.fixedReadGuardAt] using hmem)
      have hTail := ih (f s choice₁.toOption) (idx + 1) hTailDomains
        htail₁ htail₂ hTailGuards₁ hTailGuards₂
      subst tail₂
      rfl
  | load f q ih =>
      let act : TMVerifierStackAction V := TMVerifierStackAction.load (V := V)
      rcases List.mem_map.mp hw₁ with ⟨tail₁, htail₁, rfl⟩
      rcases List.mem_map.mp hw₂ with ⟨tail₂, htail₂, rfl⟩
      have hTailDomains :
          ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t q (f s) →
            ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx (idx + 1) →
              ∀ j : tmVerifierStackIndex V,
                CNF.Satisfies
                  (tmVerifierStackCellDomainsCNFAt V p
                    (tmVerifierFixedMicroTime V p t entry.2) j) a := by
        intro w hw entry hentry j
        exact hDomains (TMVerifierStmtWindow.consAction act w)
          (List.mem_map.mpr ⟨w, hw, rfl⟩) entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
      have hTailGuards₁ :
          ∀ g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t tail₁.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₁ g (by
          simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.fixedReadGuardAt] using hg)
      have hTailGuards₂ :
          ∀ g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t tail₂.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₂ g (by
          simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.fixedReadGuardAt] using hg)
      have hTail := ih (f s) (idx + 1) hTailDomains htail₁ htail₂
        hTailGuards₁ hTailGuards₂
      subst tail₂
      rfl
  | branch f q₁ q₂ ih₁ ih₂ =>
      by_cases hBranch : f s
      · let act : TMVerifierStackAction V :=
          TMVerifierStackAction.branch (V := V) TMVerifierStmtTag.branchTrue
        simp [tmVerifierStmtWindowsAt, hBranch] at hw₁ hw₂
        rcases hw₁ with ⟨tail₁, htail₁, rfl⟩
        rcases hw₂ with ⟨tail₂, htail₂, rfl⟩
        have hTailDomains :
            ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t q₁ s →
              ∀ entry : TMVerifierStackAction V × Nat,
                entry ∈ w.actions.zipIdx (idx + 1) →
                ∀ j : tmVerifierStackIndex V,
                  CNF.Satisfies
                    (tmVerifierStackCellDomainsCNFAt V p
                      (tmVerifierFixedMicroTime V p t entry.2) j) a := by
          intro w hw entry hentry j
          have hparent :
              TMVerifierStmtWindow.consAction act w ∈
                tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.branch f q₁ q₂) s := by
            simp [tmVerifierStmtWindowsAt, hBranch, act]
            exact ⟨w, hw, rfl⟩
          exact hDomains (TMVerifierStmtWindow.consAction act w) hparent entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
        have hTailGuards₁ :
            ∀ g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t tail₁.actions (idx + 1),
              g.eval a = true := by
          intro g hg
          have hEq :
              tmVerifierWindowFixedActionReadGuardsFrom p t
                  (TMVerifierStmtWindow.consAction act tail₁).actions idx =
                tmVerifierWindowFixedActionReadGuardsFrom p t tail₁.actions (idx + 1) := by
            exact tmVerifierWindowFixedActionReadGuardsFrom_cons_of_fixedReadGuardAt_nil
              p t idx act tail₁.actions
              (by simp [act, TMVerifierStackAction.fixedReadGuardAt])
          exact hGuards₁ g (by simpa [hEq] using hg)
        have hTailGuards₂ :
            ∀ g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t tail₂.actions (idx + 1),
              g.eval a = true := by
          intro g hg
          have hEq :
              tmVerifierWindowFixedActionReadGuardsFrom p t
                  (TMVerifierStmtWindow.consAction act tail₂).actions idx =
                tmVerifierWindowFixedActionReadGuardsFrom p t tail₂.actions (idx + 1) := by
            exact tmVerifierWindowFixedActionReadGuardsFrom_cons_of_fixedReadGuardAt_nil
              p t idx act tail₂.actions
              (by simp [act, TMVerifierStackAction.fixedReadGuardAt])
          exact hGuards₂ g (by simpa [hEq] using hg)
        have hTail := ih₁ s (idx + 1) hTailDomains htail₁ htail₂
          hTailGuards₁ hTailGuards₂
        subst tail₂
        rfl
      · let act : TMVerifierStackAction V :=
          TMVerifierStackAction.branch (V := V) TMVerifierStmtTag.branchFalse
        simp [tmVerifierStmtWindowsAt, hBranch] at hw₁ hw₂
        rcases hw₁ with ⟨tail₁, htail₁, rfl⟩
        rcases hw₂ with ⟨tail₂, htail₂, rfl⟩
        have hTailDomains :
            ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t q₂ s →
              ∀ entry : TMVerifierStackAction V × Nat,
                entry ∈ w.actions.zipIdx (idx + 1) →
                ∀ j : tmVerifierStackIndex V,
                  CNF.Satisfies
                    (tmVerifierStackCellDomainsCNFAt V p
                      (tmVerifierFixedMicroTime V p t entry.2) j) a := by
          intro w hw entry hentry j
          have hparent :
              TMVerifierStmtWindow.consAction act w ∈
                tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.branch f q₁ q₂) s := by
            simp [tmVerifierStmtWindowsAt, hBranch, act]
            exact ⟨w, hw, rfl⟩
          exact hDomains (TMVerifierStmtWindow.consAction act w) hparent entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
        have hTailGuards₁ :
            ∀ g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t tail₁.actions (idx + 1),
              g.eval a = true := by
          intro g hg
          have hEq :
              tmVerifierWindowFixedActionReadGuardsFrom p t
                  (TMVerifierStmtWindow.consAction act tail₁).actions idx =
                tmVerifierWindowFixedActionReadGuardsFrom p t tail₁.actions (idx + 1) := by
            exact tmVerifierWindowFixedActionReadGuardsFrom_cons_of_fixedReadGuardAt_nil
              p t idx act tail₁.actions
              (by simp [act, TMVerifierStackAction.fixedReadGuardAt])
          exact hGuards₁ g (by simpa [hEq] using hg)
        have hTailGuards₂ :
            ∀ g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t tail₂.actions (idx + 1),
              g.eval a = true := by
          intro g hg
          have hEq :
              tmVerifierWindowFixedActionReadGuardsFrom p t
                  (TMVerifierStmtWindow.consAction act tail₂).actions idx =
                tmVerifierWindowFixedActionReadGuardsFrom p t tail₂.actions (idx + 1) := by
            exact tmVerifierWindowFixedActionReadGuardsFrom_cons_of_fixedReadGuardAt_nil
              p t idx act tail₂.actions
              (by simp [act, TMVerifierStackAction.fixedReadGuardAt])
          exact hGuards₂ g (by simpa [hEq] using hg)
        have hTail := ih₂ s (idx + 1) hTailDomains htail₁ htail₂
          hTailGuards₁ hTailGuards₂
        subst tail₂
        rfl
  | goto f =>
      simp [tmVerifierStmtWindowsAt] at hw₁ hw₂
      subst w₁
      subst w₂
      rfl
  | halt =>
      simp [tmVerifierStmtWindowsAt] at hw₁ hw₂
      subst w₁
      subst w₂
      rfl

theorem tmVerifierStmtWindowsAt_unique_of_true_fixedActionReadGuards
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stmt : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ)
    (a : Assignment)
    (hDomains :
      ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t stmt s →
        ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx →
          ∀ k : tmVerifierStackIndex V,
            CNF.Satisfies
              (tmVerifierStackCellDomainsCNFAt V p
                (tmVerifierFixedMicroTime V p t entry.2) k)
              a)
    {w₁ w₂ : TMVerifierStmtWindow V}
    (hw₁ : w₁ ∈ tmVerifierStmtWindowsAt V t stmt s)
    (hw₂ : w₂ ∈ tmVerifierStmtWindowsAt V t stmt s)
    (hGuards₁ : ∀ g ∈ tmVerifierWindowFixedActionReadGuards p t w₁, g.eval a = true)
    (hGuards₂ : ∀ g ∈ tmVerifierWindowFixedActionReadGuards p t w₂, g.eval a = true) :
    w₁ = w₂ := by
  simpa [tmVerifierWindowFixedActionReadGuards] using
    tmVerifierStmtWindowsAt_unique_of_true_fixedActionReadGuardsFrom V p t stmt s 0 a
      hDomains hw₁ hw₂ hGuards₁ hGuards₂

/-! ### Accepted-run global assignment for nonhalted transition rows -/

theorem tmVerifierRunSelectedWindow_fixedGuards_satisfies_acceptedRunGlobalStacks
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    {t : Nat} (_ht : t < tmVerifierTimeBound V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s) :
    ∀ g ∈ tmVerifierWindowFixedActionReadGuards p t (tmVerifierRunSelectedWindow V p t),
      g.eval
        (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)) =
        true := by
  classical
  have hspec :=
    Classical.choose_spec
      (tmVerifierStmtWindowsAt_exists_true_actionReadGuards_topStack V p t l
        (tmVerifierRunCfgAt V p t).var)
  have hguardsMicro := hspec.2.1
  intro g hg
  rw [tmVerifierWindowFixedActionReadGuards, tmVerifierWindowFixedActionReadGuardsFrom] at hg
  rcases List.mem_flatMap.mp hg with ⟨entry, hentry, hg⟩
  rcases entry with ⟨act, idx⟩
  let w := tmVerifierRunSelectedWindow V p t
  let localStacks := fun u => tmVerifierWindowMicroStacks V p t w ((Nat.unpair u).2)
  have hGlobalStack :
      tmVerifierAcceptedRunGlobalStacks V p (tmVerifierFixedMicroTime V p t idx) =
        tmVerifierWindowMicroStacks V p t w idx := by
    simpa [w] using tmVerifierAcceptedRunGlobalStacks_at_fixed_micro V p t idx
  have hLocalStack :
      localStacks (tmVerifierMicroTime t idx) =
        tmVerifierWindowMicroStacks V p t w idx := by
    simp [localStacks]
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
        have hmemChoose :
            TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                (tmVerifierMicroTime t idx) 0 choice ∈
              tmVerifierWindowActionReadGuards t
                (Classical.choose
                  (tmVerifierStmtWindowsAt_exists_true_actionReadGuards_topStack V p t l
                    (tmVerifierRunCfgAt V p t).var)) := by
          simpa [w, tmVerifierRunSelectedWindow, hl] using hmem
        simpa [tmVerifierRunSelectedWindow, hl, hs, w, localStacks,
          tmVerifierWindowMicroStackFamilyAssignment] using hguardsMicro _ hmemChoose
      have hStack :
          localStacks (tmVerifierMicroTime t idx) k =
            tmVerifierAcceptedRunGlobalStacks V p (tmVerifierFixedMicroTime V p t idx) k :=
        (congrFun hLocalStack k).trans (congrFun hGlobalStack k).symm
      have hEvalEq :=
        TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_times_stack_eq
          V p localStacks (tmVerifierAcceptedRunGlobalStacks V p)
          (tmVerifierMicroTime t idx) (tmVerifierFixedMicroTime V p t idx) k 0 choice
          hStack
      exact hEvalEq.symm.trans hLocalGuard
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
        have hmemChoose :
            TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                (tmVerifierMicroTime t idx) 0 choice ∈
              tmVerifierWindowActionReadGuards t
                (Classical.choose
                  (tmVerifierStmtWindowsAt_exists_true_actionReadGuards_topStack V p t l
                    (tmVerifierRunCfgAt V p t).var)) := by
          simpa [w, tmVerifierRunSelectedWindow, hl] using hmem
        simpa [tmVerifierRunSelectedWindow, hl, hs, w, localStacks,
          tmVerifierWindowMicroStackFamilyAssignment] using hguardsMicro _ hmemChoose
      have hStack :
          localStacks (tmVerifierMicroTime t idx) k =
            tmVerifierAcceptedRunGlobalStacks V p (tmVerifierFixedMicroTime V p t idx) k :=
        (congrFun hLocalStack k).trans (congrFun hGlobalStack k).symm
      have hEvalEq :=
        TMVerifierStackReadChoice.atomAt_eval_stackFamilyAssignment_eq_of_times_stack_eq
          V p localStacks (tmVerifierAcceptedRunGlobalStacks V p)
          (tmVerifierMicroTime t idx) (tmVerifierFixedMicroTime V p t idx) k 0 choice
          hStack
      exact hEvalEq.symm.trans hLocalGuard
  | load =>
      simp [TMVerifierStackAction.fixedReadGuardAt] at hg
  | branch tag =>
      simp [TMVerifierStackAction.fixedReadGuardAt] at hg

theorem tmVerifierAcceptedRunGlobalStacks_sameControl_current
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    {t : Nat} (ht : t < tmVerifierTimeBound V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s) :
    (∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies (tmVerifierWindowFixedControlCNFAt V p t l s w)
            (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p))) ∧
      (∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies
            (tmVerifierWindowFixedStackBoundaryCNFAt V p t l s w ++
              tmVerifierWindowFixedStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
                p t w (tmVerifierWindowFixedAntecedents V p t l s w))
            (tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p))) := by
  let a := tmVerifierStackFamilyAssignment V p (tmVerifierAcceptedRunGlobalStacks V p)
  let selected := tmVerifierRunSelectedWindow V p t
  have hwSelected : selected ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s := by
    simpa [selected] using tmVerifierRunSelectedWindow_mem V p (t := t) hl hs
  have hSelectedMatch :
      tmVerifierWindowActionsMatchStacks selected.actions (tmVerifierRunCfgAt V p t).stk := by
    classical
    have hspec :=
      Classical.choose_spec
        (tmVerifierStmtWindowsAt_exists_true_actionReadGuards_topStack V p t l
          (tmVerifierRunCfgAt V p t).var)
    simpa [selected, tmVerifierRunSelectedWindow, hl, hs] using hspec.2.2
  have hSelectedGuards :
      ∀ g ∈ tmVerifierWindowFixedActionReadGuards p t selected, g.eval a = true := by
    simpa [a, selected] using
      tmVerifierRunSelectedWindow_fixedGuards_satisfies_acceptedRunGlobalStacks V p ht hl hs
  have hDomains :
      ∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx →
            ∀ k : tmVerifierStackIndex V,
              CNF.Satisfies
                (tmVerifierStackCellDomainsCNFAt V p
                  (tmVerifierFixedMicroTime V p t entry.2) k) a := by
    intro _w _hw entry _hentry k
    exact tmVerifierStackCellDomainsCNFAt_satisfies_stackFamilyAssignment V p
      (tmVerifierAcceptedRunGlobalStacks V p)
      (tmVerifierFixedMicroTime V p t entry.2)
      (tmVerifierAcceptedRunGlobalStacks_fixedMicro_stacksActive_any V p t entry.2) k
  have hSelectedStackEq :
      ∀ micro : Nat,
        tmVerifierAcceptedRunGlobalStacks V p (tmVerifierFixedMicroTime V p t micro) =
          tmVerifierWindowMicroStacks V p t selected micro := by
    intro micro
    simpa [selected] using tmVerifierAcceptedRunGlobalStacks_at_fixed_micro V p t micro
  have hSelectedBoundary :
      CNF.Satisfies (tmVerifierWindowFixedStackBoundaryCNFAt V p t l s selected) a := by
    exact
      tmVerifierWindowFixedStackBoundaryCNFAt_satisfies_stackFamilyAssignment_of_stack_eq V p
        t l s selected (tmVerifierAcceptedRunGlobalStacks V p)
        (by
          intro k
          rw [hSelectedStackEq 0, tmVerifierAcceptedRunGlobalStacks_at_macro V p
            (Nat.le_of_lt ht)]
          simp [tmVerifierWindowMicroStacks, tmVerifierWindowActionsApplyStacks, selected])
        (by
          intro k
          rw [tmVerifierAcceptedRunGlobalStacks_at_macro V p (Nat.succ_le_of_lt ht),
            hSelectedStackEq selected.actions.length]
          have hFinal :=
            tmVerifierSelectedWindowFixedRunStacks_final_eq_macro_succ V p t l s selected
              ht hwSelected hSelectedMatch hl hs k
          simpa [tmVerifierSelectedWindowFixedRunStacks_at_succ V p t selected,
            tmVerifierSelectedWindowFixedRunStacks_at_micro V p ht selected
              selected.actions.length] using hFinal)
  have hSelectedAction :
      CNF.Satisfies
        (tmVerifierWindowFixedStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
          p t selected (tmVerifierWindowFixedAntecedents V p t l s selected)) a := by
    exact
      tmVerifierWindowFixedStackActionCNFAt_satisfies_active_applyStacks_of_readGuards_stkAt
        V p t selected (tmVerifierAcceptedRunGlobalStacks V p)
        (tmVerifierWindowFixedAntecedents V p t l s selected)
        hSelectedStackEq (by simpa [a] using hSelectedGuards)
  have hSelectedStack :
      CNF.Satisfies
        (tmVerifierWindowFixedStackBoundaryCNFAt V p t l s selected ++
          tmVerifierWindowFixedStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
            p t selected (tmVerifierWindowFixedAntecedents V p t l s selected)) a := by
    exact (CNF.satisfies_append
      (tmVerifierWindowFixedStackBoundaryCNFAt V p t l s selected)
      (tmVerifierWindowFixedStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
        p t selected (tmVerifierWindowFixedAntecedents V p t l s selected)) a).2
      ⟨hSelectedBoundary, hSelectedAction⟩
  have hSelectedControl :
      CNF.Satisfies (tmVerifierWindowFixedControlCNFAt V p t l s selected) a := by
    intro clause hclause
    have hAgree :=
      tmVerifierStmtWindowsAt_stepAux_agrees V t ((tmVerifierTM V).m l) s
        (tmVerifierRunCfgAt V p t).stk hwSelected hSelectedMatch
    have hSucc := tmVerifierRunCfgAt_succ_of_label_some V p t hl hs
    have hNextLabel :
        selected.nextLabel = (tmVerifierRunCfgAt V p (t + 1)).l := by
      rw [hAgree.1, hSucc]
    have hNextState :
        selected.nextState = (tmVerifierRunCfgAt V p (t + 1)).var := by
      rw [hAgree.2.1, hSucc]
    have hClause :
        clause =
            tmVerifierImplicationClause (tmVerifierWindowFixedAntecedents V p t l s selected)
              (tmVerifierLabelAtom V (t + 1) selected.nextLabel) ∨
          clause =
            tmVerifierImplicationClause (tmVerifierWindowFixedAntecedents V p t l s selected)
              (tmVerifierStateAtom V (t + 1) selected.nextState) := by
      simpa [tmVerifierWindowFixedControlCNFAt] using hclause
    rcases hClause with rfl | rfl
    · exact tmVerifierImplicationClause_satisfies_of_conclusion
        (tmVerifierWindowFixedAntecedents V p t l s selected)
        (tmVerifierLabelAtom V (t + 1) selected.nextLabel) a (by
          rw [tmVerifierLabelAtom_eval_stackFamilyAssignment_controlBoundary]
          rw [tmVerifierLabelAtom_eval_controlBoundaryAssignment_iff]
          exact hNextLabel)
    · exact tmVerifierImplicationClause_satisfies_of_conclusion
        (tmVerifierWindowFixedAntecedents V p t l s selected)
        (tmVerifierStateAtom V (t + 1) selected.nextState) a (by
          rw [tmVerifierStateAtom_eval_stackFamilyAssignment_controlBoundary]
          rw [tmVerifierStateAtom_eval_controlBoundaryAssignment_iff]
          exact hNextState)
  constructor
  · intro w hw
    by_cases hAll : ∀ g ∈ tmVerifierWindowFixedActionReadGuards p t w, g.eval a = true
    · have hEq :
          selected = w :=
        tmVerifierStmtWindowsAt_unique_of_true_fixedActionReadGuards V p t
          ((tmVerifierTM V).m l) s a hDomains hwSelected hw hSelectedGuards hAll
      simpa [hEq] using hSelectedControl
    · push Not at hAll
      rcases hAll with ⟨bad, hbadMem, hbadNotTrue⟩
      have hbadFalse : bad.eval a = false := by
        cases hEval : bad.eval a <;> simp [hEval] at hbadNotTrue ⊢
      exact tmVerifierWindowFixedControlCNFAt_satisfies_of_false_antecedent V p t l s w
        a (tmVerifierWindowFixedAntecedents_fixedGuard_mem V p t l s w hbadMem)
        hbadFalse
  · intro w hw
    by_cases hAll : ∀ g ∈ tmVerifierWindowFixedActionReadGuards p t w, g.eval a = true
    · have hEq :
          selected = w :=
        tmVerifierStmtWindowsAt_unique_of_true_fixedActionReadGuards V p t
          ((tmVerifierTM V).m l) s a hDomains hwSelected hw hSelectedGuards hAll
      simpa [hEq] using hSelectedStack
    · push Not at hAll
      rcases hAll with ⟨bad, hbadMem, hbadNotTrue⟩
      have hbadFalse : bad.eval a = false := by
        cases hEval : bad.eval a <;> simp [hEval] at hbadNotTrue ⊢
      exact tmVerifierWindowFixedStackCNF_satisfies_of_false_antecedent V
        (tmVerifierActivePushPayloadBoundary V) p t l s w a
        (tmVerifierWindowFixedAntecedents_fixedGuard_mem V p t l s w hbadMem) hbadFalse

end SAT
end ComplexityReduction
