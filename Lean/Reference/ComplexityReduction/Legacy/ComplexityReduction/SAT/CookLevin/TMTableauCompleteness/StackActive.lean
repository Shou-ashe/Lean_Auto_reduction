/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.StackBoundary

namespace ComplexityReduction
namespace SAT

/-! ### Active-symbol invariant for concrete accepting-run stk -/

def tmVerifierStackListActive
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (k : tmVerifierStackIndex V) (xs : List ((tmVerifierTM V).Γ k)) : Prop :=
  ∀ (cell : Nat) (s : (tmVerifierTM V).Γ k),
    xs[cell]? = some s → tmVerifierStackSymbolActive V k s

def tmVerifierStacksActive
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)) : Prop :=
  ∀ k, tmVerifierStackListActive V k (stk k)

def tmVerifierCfgStacksActive
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (cfg : (tmVerifierTM V).Cfg) : Prop :=
  tmVerifierStacksActive V cfg.stk

theorem tmVerifierStackSymbolActive_of_controlPush
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (raw : TMVerifierStackSymbol V) (hraw : raw ∈ tmVerifierControlPushSymbols V) :
    tmVerifierStackSymbolActive V raw.stack raw.symbol := by
  rcases tmVerifierActiveStackSymbols_push_cover V raw hraw with
    ⟨named, hNamed, hStack, hSymbol⟩
  exact ⟨named, hNamed, hStack, hSymbol⟩

theorem tmVerifierStackListActive_tail
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V} {xs : List ((tmVerifierTM V).Γ k)}
    (hxs : tmVerifierStackListActive V k xs) :
    tmVerifierStackListActive V k xs.tail := by
  unfold tmVerifierStackListActive at hxs ⊢
  intro cell s hget
  cases xs with
  | nil =>
      simp at hget
  | cons head tail =>
      exact hxs (cell + 1) s (by simpa using hget)

theorem tmVerifierStackListActive_cons
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {k : tmVerifierStackIndex V} {s : (tmVerifierTM V).Γ k}
    {xs : List ((tmVerifierTM V).Γ k)}
    (hs : tmVerifierStackSymbolActive V k s)
    (hxs : tmVerifierStackListActive V k xs) :
    tmVerifierStackListActive V k (s :: xs) := by
  unfold tmVerifierStackListActive at hxs ⊢
  intro cell symbol hget
  cases cell with
  | zero =>
      simp at hget
      cases hget
      exact hs
  | succ cell =>
      exact hxs cell symbol (by simpa using hget)

theorem tmVerifierStacksActive_push
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)}
    (hstk : tmVerifierStacksActive V stk)
    (raw : TMVerifierStackSymbol V) (hraw : raw ∈ tmVerifierControlPushSymbols V) :
    tmVerifierStacksActive V
      (Function.update stk raw.stack (raw.symbol :: stk raw.stack)) := by
  unfold tmVerifierStacksActive
  intro k
  unfold tmVerifierStackListActive
  intro cell s hget
  by_cases hk : k = raw.stack
  · subst k
    have hActiveHead := tmVerifierStackSymbolActive_of_controlPush V raw hraw
    exact
      tmVerifierStackListActive_cons hActiveHead (hstk raw.stack) cell s
        (by simpa [Function.update] using hget)
  · exact hstk k cell s (by simpa [Function.update, hk] using hget)

theorem tmVerifierStacksActive_pop
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)}
    (hstk : tmVerifierStacksActive V stk) (k : tmVerifierStackIndex V) :
    tmVerifierStacksActive V (Function.update stk k (stk k).tail) := by
  unfold tmVerifierStacksActive
  intro j
  unfold tmVerifierStackListActive
  intro cell s hget
  by_cases hjk : j = k
  · subst j
    exact
      tmVerifierStackListActive_tail (hstk k) cell s
        (by simpa [Function.update] using hget)
  · exact hstk j cell s (by simpa [Function.update, hjk] using hget)

def tmVerifierStackActionPushCount
    {L : EncodedDecisionProblem} {V : TMVerifier L} :
    TMVerifierStackAction V → Nat
  | TMVerifierStackAction.push _ => 1
  | _ => 0

def tmVerifierStackActionsPushCount
    {L : EncodedDecisionProblem} {V : TMVerifier L} :
    List (TMVerifierStackAction V) → Nat
  | [] => 0
  | act :: rest =>
      tmVerifierStackActionPushCount act + tmVerifierStackActionsPushCount rest

theorem tmVerifierStackActionsPushCount_take_le
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (actions : List (TMVerifierStackAction V)) (n : Nat) :
    tmVerifierStackActionsPushCount (actions.take n) ≤
      tmVerifierStackActionsPushCount actions := by
  induction actions generalizing n with
  | nil =>
      simp [tmVerifierStackActionsPushCount]
  | cons act rest ih =>
      cases n with
      | zero =>
          simp [tmVerifierStackActionsPushCount]
      | succ n =>
          simp [tmVerifierStackActionsPushCount]
          exact ih n

theorem tmVerifierStackActionApplyStacks_stacksActive
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)}
    (act : TMVerifierStackAction V)
    (hstk : tmVerifierStacksActive V stk)
    (hPush : TMVerifierStackActionPushSymbolMem (V := V) act) :
    tmVerifierStacksActive V (tmVerifierStackActionApplyStacks act stk) := by
  cases act with
  | push raw =>
      exact tmVerifierStacksActive_push hstk raw (by
        simpa [TMVerifierStackActionPushSymbolMem] using hPush)
  | pop k choice =>
      exact tmVerifierStacksActive_pop hstk k
  | peek k choice =>
      simpa [tmVerifierStackActionApplyStacks] using hstk
  | load =>
      simpa [tmVerifierStackActionApplyStacks] using hstk
  | branch tag =>
      simpa [tmVerifierStackActionApplyStacks] using hstk

theorem tmVerifierWindowActionsApplyStacks_stacksActive
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (actions : List (TMVerifierStackAction V))
    {stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)}
    (hstk : tmVerifierStacksActive V stk)
    (hPush : ∀ act, act ∈ actions → TMVerifierStackActionPushSymbolMem (V := V) act) :
    tmVerifierStacksActive V (tmVerifierWindowActionsApplyStacks actions stk) := by
  induction actions generalizing stk with
  | nil =>
      simpa [tmVerifierWindowActionsApplyStacks] using hstk
  | cons act rest ih =>
      have hHead :
          tmVerifierStacksActive V (tmVerifierStackActionApplyStacks act stk) :=
        tmVerifierStackActionApplyStacks_stacksActive act hstk (hPush act (by simp))
      exact ih hHead (by
        intro tailAct htail
        exact hPush tailAct (by simp [htail]))

theorem tmVerifierStackActionApplyStacks_length_le
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (act : TMVerifierStackAction V)
    (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (k : tmVerifierStackIndex V) :
    (tmVerifierStackActionApplyStacks act stk k).length ≤
      (stk k).length + tmVerifierStackActionPushCount act := by
  cases act with
  | push raw =>
      by_cases hk : k = raw.stack
      · subst k
        simp [tmVerifierStackActionApplyStacks, tmVerifierStackActionPushCount,
          Function.update]
      · simp [tmVerifierStackActionApplyStacks, tmVerifierStackActionPushCount,
          Function.update, hk]
  | pop stack choice =>
      by_cases hk : k = stack
      · subst k
        simp [tmVerifierStackActionApplyStacks, tmVerifierStackActionPushCount,
          Function.update]
      · simp [tmVerifierStackActionApplyStacks, tmVerifierStackActionPushCount,
          Function.update, hk]
  | peek stack choice =>
      simp [tmVerifierStackActionApplyStacks, tmVerifierStackActionPushCount]
  | load =>
      simp [tmVerifierStackActionApplyStacks, tmVerifierStackActionPushCount]
  | branch tag =>
      simp [tmVerifierStackActionApplyStacks, tmVerifierStackActionPushCount]

theorem tmVerifierWindowActionsApplyStacks_length_le
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (actions : List (TMVerifierStackAction V))
    (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (k : tmVerifierStackIndex V) :
    (tmVerifierWindowActionsApplyStacks actions stk k).length ≤
      (stk k).length + tmVerifierStackActionsPushCount actions := by
  induction actions generalizing stk with
  | nil =>
      simp [tmVerifierWindowActionsApplyStacks, tmVerifierStackActionsPushCount]
  | cons act rest ih =>
      have hTail := ih (tmVerifierStackActionApplyStacks act stk)
      have hHead := tmVerifierStackActionApplyStacks_length_le act stk k
      calc
        (tmVerifierWindowActionsApplyStacks (act :: rest) stk k).length
            ≤ (tmVerifierStackActionApplyStacks act stk k).length +
                tmVerifierStackActionsPushCount rest := by
              simpa [tmVerifierWindowActionsApplyStacks] using hTail
        _ ≤ ((stk k).length + tmVerifierStackActionPushCount act) +
                tmVerifierStackActionsPushCount rest := by
              exact Nat.add_le_add_right hHead _
        _ = (stk k).length + tmVerifierStackActionsPushCount (act :: rest) := by
              simp [tmVerifierStackActionsPushCount, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm]

theorem tmVerifierStmtWindowsAt_actions_pushCount_le_stmtPushCount
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat)
    (stmt : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ)
    {w : TMVerifierStmtWindow V}
    (hw : w ∈ tmVerifierStmtWindowsAt V t stmt s) :
    tmVerifierStackActionsPushCount w.actions ≤ TM2Programs.stmtPushCount stmt := by
  induction stmt generalizing s w with
  | push k f q ih =>
      rcases List.mem_map.mp hw with ⟨w₀, hw₀, rfl⟩
      have hTail := ih s hw₀
      simp [TMVerifierStmtWindow.consAction, tmVerifierStackActionsPushCount,
        tmVerifierStackActionPushCount, TM2Programs.stmtPushCount]
      omega
  | peek k f q ih =>
      rcases List.mem_flatMap.mp hw with ⟨choice, _hchoice, hmem⟩
      rcases List.mem_map.mp hmem with ⟨w₀, hw₀, rfl⟩
      have hTail := ih (f s choice.toOption) hw₀
      simpa [TMVerifierStmtWindow.consAction, tmVerifierStackActionsPushCount,
        tmVerifierStackActionPushCount, TM2Programs.stmtPushCount] using hTail
  | pop k f q ih =>
      rcases List.mem_flatMap.mp hw with ⟨choice, _hchoice, hmem⟩
      rcases List.mem_map.mp hmem with ⟨w₀, hw₀, rfl⟩
      have hTail := ih (f s choice.toOption) hw₀
      simpa [TMVerifierStmtWindow.consAction, tmVerifierStackActionsPushCount,
        tmVerifierStackActionPushCount, TM2Programs.stmtPushCount] using hTail
  | load f q ih =>
      rcases List.mem_map.mp hw with ⟨w₀, hw₀, rfl⟩
      have hTail := ih (f s) hw₀
      simpa [TMVerifierStmtWindow.consAction, tmVerifierStackActionsPushCount,
        tmVerifierStackActionPushCount, TM2Programs.stmtPushCount] using hTail
  | branch f q₁ q₂ ih₁ ih₂ =>
      by_cases hBranch : f s
      · simp [tmVerifierStmtWindowsAt, hBranch] at hw
        rcases hw with ⟨w₀, hw₀, rfl⟩
        have hTail := ih₁ s hw₀
        have hMax :
            TM2Programs.stmtPushCount q₁ ≤
              max (TM2Programs.stmtPushCount q₁) (TM2Programs.stmtPushCount q₂) :=
          Nat.le_max_left _ _
        simpa [TMVerifierStmtWindow.consAction, tmVerifierStackActionsPushCount,
          tmVerifierStackActionPushCount, TM2Programs.stmtPushCount, hBranch] using
          hTail.trans hMax
      · simp [tmVerifierStmtWindowsAt, hBranch] at hw
        rcases hw with ⟨w₀, hw₀, rfl⟩
        have hTail := ih₂ s hw₀
        have hMax :
            TM2Programs.stmtPushCount q₂ ≤
              max (TM2Programs.stmtPushCount q₁) (TM2Programs.stmtPushCount q₂) :=
          Nat.le_max_right _ _
        simpa [TMVerifierStmtWindow.consAction, tmVerifierStackActionsPushCount,
          tmVerifierStackActionPushCount, TM2Programs.stmtPushCount, hBranch] using
          hTail.trans hMax
  | goto f =>
      simp [tmVerifierStmtWindowsAt] at hw
      subst w
      simp [tmVerifierStackActionsPushCount, TM2Programs.stmtPushCount]
  | halt =>
      simp [tmVerifierStmtWindowsAt] at hw
      subst w
      simp [tmVerifierStackActionsPushCount, TM2Programs.stmtPushCount]

theorem tmVerifierStepAux_stacksActive
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (stmt : (tmVerifierTM V).Stmt) (state : (tmVerifierTM V).σ)
    (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    (hstk : tmVerifierStacksActive V stk)
    (hStmt :
      ∀ raw, raw ∈ tmVerifierStmtPushSymbols V stmt →
        raw ∈ tmVerifierControlPushSymbols V) :
    tmVerifierCfgStacksActive V (Turing.TM2.stepAux stmt state stk) := by
  induction stmt generalizing state stk with
  | push k f q ih =>
      have hRaw :
          ({ stack := k, symbol := f state } : TMVerifierStackSymbol V) ∈
            tmVerifierControlPushSymbols V :=
        hStmt ({ stack := k, symbol := f state } : TMVerifierStackSymbol V)
          (tmVerifierStmtPushSymbols_push_mem V k f q state)
      have hstk' :
          tmVerifierStacksActive V
            (Function.update stk k (f state :: stk k)) :=
        tmVerifierStacksActive_push hstk
          ({ stack := k, symbol := f state } : TMVerifierStackSymbol V) hRaw
      have hTail :
          ∀ raw, raw ∈ tmVerifierStmtPushSymbols V q →
            raw ∈ tmVerifierControlPushSymbols V := by
        intro raw hraw
        exact hStmt raw (by simp [tmVerifierStmtPushSymbols, hraw])
      simpa [Turing.TM2.stepAux] using
        ih state (Function.update stk k (f state :: stk k)) hstk' hTail
  | peek k f q ih =>
      have hTail :
          ∀ raw, raw ∈ tmVerifierStmtPushSymbols V q →
            raw ∈ tmVerifierControlPushSymbols V := by
        intro raw hraw
        exact hStmt raw (by simpa [tmVerifierStmtPushSymbols] using hraw)
      simpa [Turing.TM2.stepAux] using ih (f state (stk k).head?) stk hstk hTail
  | pop k f q ih =>
      have hTail :
          ∀ raw, raw ∈ tmVerifierStmtPushSymbols V q →
            raw ∈ tmVerifierControlPushSymbols V := by
        intro raw hraw
        exact hStmt raw (by simpa [tmVerifierStmtPushSymbols] using hraw)
      have hstk' : tmVerifierStacksActive V (Function.update stk k (stk k).tail) :=
        tmVerifierStacksActive_pop hstk k
      simpa [Turing.TM2.stepAux] using
        ih (f state (stk k).head?) (Function.update stk k (stk k).tail) hstk' hTail
  | load f q ih =>
      have hTail :
          ∀ raw, raw ∈ tmVerifierStmtPushSymbols V q →
            raw ∈ tmVerifierControlPushSymbols V := by
        intro raw hraw
        exact hStmt raw (by simpa [tmVerifierStmtPushSymbols] using hraw)
      simpa [Turing.TM2.stepAux] using ih (f state) stk hstk hTail
  | branch f q₁ q₂ ih₁ ih₂ =>
      by_cases hBranch : f state
      · have hTail :
            ∀ raw, raw ∈ tmVerifierStmtPushSymbols V q₁ →
              raw ∈ tmVerifierControlPushSymbols V := by
          intro raw hraw
          exact hStmt raw (by simp [tmVerifierStmtPushSymbols, hraw])
        simpa [Turing.TM2.stepAux, hBranch] using ih₁ state stk hstk hTail
      · have hTail :
            ∀ raw, raw ∈ tmVerifierStmtPushSymbols V q₂ →
              raw ∈ tmVerifierControlPushSymbols V := by
          intro raw hraw
          exact hStmt raw (by simp [tmVerifierStmtPushSymbols, hraw])
        simpa [Turing.TM2.stepAux, hBranch] using ih₂ state stk hstk hTail
  | goto f =>
      simpa [tmVerifierCfgStacksActive, Turing.TM2.stepAux] using hstk
  | halt =>
      simpa [tmVerifierCfgStacksActive, Turing.TM2.stepAux] using hstk

theorem tmVerifierStep_stacksActive
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {cfg cfg' : (tmVerifierTM V).Cfg}
    (hstep : (tmVerifierTM V).step cfg = some cfg')
    (hcfg : tmVerifierCfgStacksActive V cfg) :
    tmVerifierCfgStacksActive V cfg' := by
  rcases cfg with ⟨label, state, stk⟩
  cases label with
  | none =>
      simp [Turing.FinTM2.step, Turing.TM2.step] at hstep
  | some label =>
      have hAux :
          tmVerifierCfgStacksActive V
            (Turing.TM2.stepAux ((tmVerifierTM V).m label) state stk) :=
        tmVerifierStepAux_stacksActive V ((tmVerifierTM V).m label) state stk hcfg
          (fun raw hraw => tmVerifierControlPushSymbols_label_mem V label raw hraw)
      have hcfg' :
          cfg' = Turing.TM2.stepAux ((tmVerifierTM V).m label) state stk := by
        have hSome :
            some cfg' = some (Turing.TM2.stepAux ((tmVerifierTM V).m label) state stk) := by
          simpa [Turing.FinTM2.step, Turing.TM2.step] using hstep.symm
        cases hSome
        rfl
      subst cfg'
      exact hAux

theorem tmVerifierInitialCfg_stacksActive
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) :
    tmVerifierCfgStacksActive V (tmVerifierInitialCfg V p) := by
  unfold tmVerifierCfgStacksActive tmVerifierStacksActive tmVerifierStackListActive
  intro k cell s hget
  by_cases hk : k = (tmVerifierTM V).k₀
  · subst k
    exact tmVerifierStackSymbolActive_input V s
  · have hEmpty := tmVerifierInitialCfg_noninput_stack_empty V p k hk
    rw [hEmpty] at hget
    simp at hget

theorem tmVerifierOutputCfg_stacksActive
    {L : EncodedDecisionProblem} (V : TMVerifier L) (b : Bool) :
    tmVerifierCfgStacksActive V (tmVerifierOutputCfg V b) := by
  unfold tmVerifierCfgStacksActive tmVerifierStacksActive tmVerifierStackListActive
  intro k cell s hget
  by_cases hk : k = (tmVerifierTM V).k₁
  · subst k
    exact tmVerifierStackSymbolActive_output V s
  · have hEmpty := tmVerifierOutputCfg_nonoutput_stack_empty V b k hk
    rw [hEmpty] at hget
    simp at hget

theorem optionBindIterate_preserves_some_eq
    {σ : Type} (f : σ → Option σ) (P : σ → Prop) {init : σ}
    (hinit : P init)
    (hstep : ∀ {a b : σ}, f a = some b → P a → P b) :
    ∀ (t : Nat) {x : σ}, (flip bind f)^[t] (some init) = some x → P x := by
  intro t
  induction t with
  | zero =>
      intro x hx
      cases hx
      exact hinit
  | succ t ih =>
      intro x hx
      rw [Function.iterate_succ_apply'] at hx
      cases hprev : (flip bind f)^[t] (some init) with
      | none =>
        rw [hprev] at hx
        change Option.bind (none : Option σ) f = some x at hx
        simp at hx
      | some a =>
        have ha : P a := ih hprev
        cases hnext : f a with
        | none =>
            rw [hprev] at hx
            change Option.bind (some a) f = some x at hx
            have hx' : f a = some x := by
              simpa using hx
            rw [hnext] at hx'
            simp at hx'
        | some b =>
            rw [hprev] at hx
            change Option.bind (some a) f = some x at hx
            have hx' : f a = some x := by
              simpa using hx
            rw [hnext] at hx'
            cases hx'
            exact hstep hnext ha

theorem optionBindIterate_preserves_some
    {σ : Type} (f : σ → Option σ) (P : σ → Prop) {init : σ}
    (hinit : P init)
    (hstep : ∀ {a b : σ}, f a = some b → P a → P b) (t : Nat) :
    match (flip bind f)^[t] (some init) with
    | some x => P x
    | none => True := by
  cases hrun : (flip bind f)^[t] (some init) with
  | none =>
      trivial
  | some x =>
      simpa using optionBindIterate_preserves_some_eq f P hinit hstep t hrun

theorem tmVerifierRunOption_stacksActive
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) :
    match (flip bind (tmVerifierTM V).step)^[t] (some (tmVerifierInitialCfg V p)) with
    | some cfg => tmVerifierCfgStacksActive V cfg
    | none => True := by
  cases hrun : (flip bind (tmVerifierTM V).step)^[t] (some (tmVerifierInitialCfg V p)) with
  | none =>
      trivial
  | some cfg =>
      exact
        optionBindIterate_preserves_some_eq (tmVerifierTM V).step
          (tmVerifierCfgStacksActive V) (tmVerifierInitialCfg_stacksActive V p)
          (fun hstep hcfg => tmVerifierStep_stacksActive V hstep hcfg) t hrun

theorem tmVerifierRunCfgAt_stacksActive
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat) :
    tmVerifierCfgStacksActive V (tmVerifierRunCfgAt V p t) := by
  unfold tmVerifierRunCfgAt
  cases hopt :
      (flip bind (tmVerifierTM V).step)^[t] (some (tmVerifierInitialCfg V p)) with
  | none =>
      simpa using tmVerifierOutputCfg_stacksActive V true
  | some cfg =>
      exact
        optionBindIterate_preserves_some_eq (tmVerifierTM V).step
          (tmVerifierCfgStacksActive V) (tmVerifierInitialCfg_stacksActive V p)
          (fun hstep hcfg => tmVerifierStep_stacksActive V hstep hcfg) t hopt

theorem tmVerifierRunStackSymbolActive
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (k : tmVerifierStackIndex V) (cell : Nat) (s : (tmVerifierTM V).Γ k)
    (hget : ((tmVerifierRunCfgAt V p t).stk k)[cell]? = some s) :
    tmVerifierStackSymbolActive V k s :=
  (tmVerifierRunCfgAt_stacksActive V p t) k cell s hget

end SAT
end ComplexityReduction
