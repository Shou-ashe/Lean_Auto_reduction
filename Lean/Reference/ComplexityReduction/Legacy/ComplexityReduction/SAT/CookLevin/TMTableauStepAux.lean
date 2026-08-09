/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauGuardSelection

/-!
Operational alignment for statement windows.

`TMTransitionWindows` recursively enumerates finite execution windows for one
`TM2.Stmt`.  This file proves the purely operational part of that enumeration:
if the recorded `peek`/`pop` choices agree with the current stack heads along
the recorded action trace, then the window's next control row and final stacks
are exactly the result of mathlib's `Turing.TM2.stepAux`.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Action traces over concrete TM2 stacks -/

/-- Apply the stack effect of one recorded window action to concrete TM2 stacks. -/
noncomputable def tmVerifierStackActionApplyStacks {L : EncodedDecisionProblem}
    {V : TMVerifier L} :
    TMVerifierStackAction V →
      (∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)) →
        (∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
  | TMVerifierStackAction.push raw, stk =>
      Function.update stk raw.stack (raw.symbol :: stk raw.stack)
  | TMVerifierStackAction.peek _ _, stk => stk
  | TMVerifierStackAction.pop k _, stk =>
      Function.update stk k (stk k).tail
  | TMVerifierStackAction.load, stk => stk
  | TMVerifierStackAction.branch _, stk => stk

/-- The read-side condition for one recorded action at the current concrete stacks. -/
noncomputable def tmVerifierStackActionReadsCurrent {L : EncodedDecisionProblem}
    {V : TMVerifier L}
    (act : TMVerifierStackAction V)
    (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)) : Prop :=
  match act with
  | TMVerifierStackAction.peek k choice => choice.toOption = (stk k).head?
  | TMVerifierStackAction.pop k choice => choice.toOption = (stk k).head?
  | _ => True

/-- Apply a recorded action trace to concrete TM2 stacks. -/
noncomputable def tmVerifierWindowActionsApplyStacks {L : EncodedDecisionProblem}
    {V : TMVerifier L} :
    List (TMVerifierStackAction V) →
      (∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)) →
        (∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
  | [], stk => stk
  | act :: rest, stk =>
      tmVerifierWindowActionsApplyStacks rest
        (tmVerifierStackActionApplyStacks act stk)

/--
The recorded action trace reads the current concrete stack heads at each
`peek`/`pop`, after applying all previous recorded stack effects.
-/
noncomputable def tmVerifierWindowActionsMatchStacks {L : EncodedDecisionProblem}
    {V : TMVerifier L} :
    List (TMVerifierStackAction V) →
      (∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)) → Prop
  | [], _ => True
  | act :: rest, stk =>
      tmVerifierStackActionReadsCurrent act stk ∧
        tmVerifierWindowActionsMatchStacks rest
          (tmVerifierStackActionApplyStacks act stk)

theorem tmVerifierWindowActionsMatchStacks_cons_tail
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {act : TMVerifierStackAction V} {rest : List (TMVerifierStackAction V)}
    {stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)}
    (h : tmVerifierWindowActionsMatchStacks (act :: rest) stk) :
    tmVerifierWindowActionsMatchStacks rest
      (tmVerifierStackActionApplyStacks act stk) :=
  h.2

/-! ### Statement-window agreement with `TM2.stepAux` -/

theorem tmVerifierStmtWindowsAt_stepAux_agrees
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (t : Nat)
    (stmt : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ)
    (stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k))
    {w : TMVerifierStmtWindow V}
    (hw : w ∈ tmVerifierStmtWindowsAt V t stmt s)
    (hMatch : tmVerifierWindowActionsMatchStacks w.actions stk) :
    w.nextLabel = (Turing.TM2.stepAux stmt s stk).l ∧
      w.nextState = (Turing.TM2.stepAux stmt s stk).var ∧
        tmVerifierWindowActionsApplyStacks w.actions stk =
          (Turing.TM2.stepAux stmt s stk).stk := by
  induction stmt generalizing s stk w with
  | push k f q ih =>
      rcases List.mem_map.mp hw with ⟨w₀, hw₀, rfl⟩
      have hTail :
          tmVerifierWindowActionsMatchStacks w₀.actions
            (Function.update stk k (f s :: stk k)) := by
        simpa [TMVerifierStmtWindow.consAction, tmVerifierWindowActionsMatchStacks,
          tmVerifierStackActionReadsCurrent, tmVerifierStackActionApplyStacks] using hMatch.2
      have hIH := ih s (Function.update stk k (f s :: stk k)) hw₀ hTail
      simpa [tmVerifierStmtWindowsAt, TMVerifierStmtWindow.consAction,
        tmVerifierWindowActionsApplyStacks, tmVerifierStackActionApplyStacks,
        Turing.TM2.stepAux] using hIH
  | peek k f q ih =>
      rcases List.mem_flatMap.mp hw with ⟨choice, _hchoice, hmem⟩
      rcases List.mem_map.mp hmem with ⟨w₀, hw₀, rfl⟩
      have hRead : choice.toOption = (stk k).head? := by
        simpa [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
          tmVerifierWindowActionsMatchStacks, tmVerifierStackActionReadsCurrent]
          using hMatch.1
      have hTail : tmVerifierWindowActionsMatchStacks w₀.actions stk := by
        simpa [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
          tmVerifierWindowActionsMatchStacks, tmVerifierStackActionApplyStacks]
          using hMatch.2
      have hIH := ih (f s choice.toOption) stk hw₀ hTail
      simpa [tmVerifierStmtWindowsAt, TMVerifierStmtWindow.consAction,
        TMVerifierStmtWindow.consGuard, tmVerifierWindowActionsApplyStacks,
        tmVerifierStackActionApplyStacks, Turing.TM2.stepAux, hRead] using hIH
  | pop k f q ih =>
      rcases List.mem_flatMap.mp hw with ⟨choice, _hchoice, hmem⟩
      rcases List.mem_map.mp hmem with ⟨w₀, hw₀, rfl⟩
      have hRead : choice.toOption = (stk k).head? := by
        simpa [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
          tmVerifierWindowActionsMatchStacks, tmVerifierStackActionReadsCurrent]
          using hMatch.1
      have hTail :
          tmVerifierWindowActionsMatchStacks w₀.actions
            (Function.update stk k (stk k).tail) := by
        simpa [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
          tmVerifierWindowActionsMatchStacks, tmVerifierStackActionApplyStacks]
          using hMatch.2
      have hIH := ih (f s choice.toOption)
        (Function.update stk k (stk k).tail) hw₀ hTail
      simpa [tmVerifierStmtWindowsAt, TMVerifierStmtWindow.consAction,
        TMVerifierStmtWindow.consGuard, tmVerifierWindowActionsApplyStacks,
        tmVerifierStackActionApplyStacks, Turing.TM2.stepAux, hRead] using hIH
  | load f q ih =>
      rcases List.mem_map.mp hw with ⟨w₀, hw₀, rfl⟩
      have hTail : tmVerifierWindowActionsMatchStacks w₀.actions stk := by
        simpa [TMVerifierStmtWindow.consAction, tmVerifierWindowActionsMatchStacks,
          tmVerifierStackActionReadsCurrent, tmVerifierStackActionApplyStacks] using hMatch.2
      have hIH := ih (f s) stk hw₀ hTail
      simpa [tmVerifierStmtWindowsAt, TMVerifierStmtWindow.consAction,
        tmVerifierWindowActionsApplyStacks, tmVerifierStackActionApplyStacks,
        Turing.TM2.stepAux] using hIH
  | branch f q₁ q₂ ih₁ ih₂ =>
      by_cases hBranch : f s
      · simp [tmVerifierStmtWindowsAt, hBranch] at hw
        rcases hw with ⟨w₀, hw₀, rfl⟩
        have hTail : tmVerifierWindowActionsMatchStacks w₀.actions stk := by
          simpa [TMVerifierStmtWindow.consAction, tmVerifierWindowActionsMatchStacks,
            tmVerifierStackActionReadsCurrent, tmVerifierStackActionApplyStacks] using hMatch.2
        have hIH := ih₁ s stk hw₀ hTail
        simpa [tmVerifierStmtWindowsAt, hBranch, TMVerifierStmtWindow.consAction,
          tmVerifierWindowActionsApplyStacks, tmVerifierStackActionApplyStacks,
          Turing.TM2.stepAux] using hIH
      · simp [tmVerifierStmtWindowsAt, hBranch] at hw
        rcases hw with ⟨w₀, hw₀, rfl⟩
        have hTail : tmVerifierWindowActionsMatchStacks w₀.actions stk := by
          simpa [TMVerifierStmtWindow.consAction, tmVerifierWindowActionsMatchStacks,
            tmVerifierStackActionReadsCurrent, tmVerifierStackActionApplyStacks] using hMatch.2
        have hIH := ih₂ s stk hw₀ hTail
        simpa [tmVerifierStmtWindowsAt, hBranch, TMVerifierStmtWindow.consAction,
          tmVerifierWindowActionsApplyStacks, tmVerifierStackActionApplyStacks,
          Turing.TM2.stepAux] using hIH
  | goto f =>
      simp [tmVerifierStmtWindowsAt] at hw
      subst w
      simp [tmVerifierWindowActionsApplyStacks, Turing.TM2.stepAux]
  | halt =>
      simp [tmVerifierStmtWindowsAt] at hw
      subst w
      simp [tmVerifierWindowActionsApplyStacks, Turing.TM2.stepAux]

theorem TMVerifierWindowRowFiniteEffect.stepAux_next_control
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {p : L.Instance.Carrier × V.Cert.Carrier} {t : Nat}
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V} {a : Assignment}
    {hDomains : TMVerifierWindowActionDomainEvidence V p t w a}
    {stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)}
    (hEff : TMVerifierWindowRowFiniteEffect V B p t l s w a hDomains)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hMatch : tmVerifierWindowActionsMatchStacks w.actions stk) :
    (tmVerifierLabelAtom V (t + 1)
        (Turing.TM2.stepAux ((tmVerifierTM V).m l) s stk).l).eval a = true ∧
      (tmVerifierStateAtom V (t + 1)
        (Turing.TM2.stepAux ((tmVerifierTM V).m l) s stk).var).eval a = true ∧
        tmVerifierWindowActionsApplyStacks w.actions stk =
          (Turing.TM2.stepAux ((tmVerifierTM V).m l) s stk).stk := by
  have hStep := tmVerifierStmtWindowsAt_stepAux_agrees V t ((tmVerifierTM V).m l) s
    stk hw hMatch
  rcases hEff with ⟨hLabel, hState, _hActions⟩
  exact ⟨by simpa [hStep.1] using hLabel,
    by simpa [hStep.2.1] using hState,
    hStep.2.2⟩

namespace TMVerifierFixedPairTableauEvidence

theorem transitionWindowFiniteStepAuxControl
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hLabel :
      (E.controlRow t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)).label =
        some l)
    (hState :
      (E.controlRow t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)).state = s)
    (hGuards : ∀ g ∈ tmVerifierWindowActionReadGuards t w, g.eval a = true)
    {stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)}
    (hMatch : tmVerifierWindowActionsMatchStacks w.actions stk) :
    (tmVerifierLabelAtom V (t + 1)
        (Turing.TM2.stepAux ((tmVerifierTM V).m l) s stk).l).eval a = true ∧
      (tmVerifierStateAtom V (t + 1)
        (Turing.TM2.stepAux ((tmVerifierTM V).m l) s stk).var).eval a = true ∧
        tmVerifierWindowActionsApplyStacks w.actions stk =
          (Turing.TM2.stepAux ((tmVerifierTM V).m l) s stk).stk :=
  (E.transitionWindowFiniteRowEffect ht hl hs hw hLabel hState hGuards).stepAux_next_control
    hw hMatch

end TMVerifierFixedPairTableauEvidence

namespace TMVerifierXOnlyTableauSeed

theorem transitionWindowFiniteStepAuxControl
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, wSeed.cert))
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hLabel :
      (wSeed.fixedPairEvidence.controlRow t
        (tmVerifierTransitionTimeRange_mem_tableauTimeRange V (x, wSeed.cert) ht)).label =
        some l)
    (hState :
      (wSeed.fixedPairEvidence.controlRow t
        (tmVerifierTransitionTimeRange_mem_tableauTimeRange V (x, wSeed.cert) ht)).state = s)
    (hGuards : ∀ g ∈ tmVerifierWindowActionReadGuards t w, g.eval a = true)
    {stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)}
    (hMatch : tmVerifierWindowActionsMatchStacks w.actions stk) :
    (tmVerifierLabelAtom V (t + 1)
        (Turing.TM2.stepAux ((tmVerifierTM V).m l) s stk).l).eval a = true ∧
      (tmVerifierStateAtom V (t + 1)
        (Turing.TM2.stepAux ((tmVerifierTM V).m l) s stk).var).eval a = true ∧
        tmVerifierWindowActionsApplyStacks w.actions stk =
          (Turing.TM2.stepAux ((tmVerifierTM V).m l) s stk).stk :=
  wSeed.fixedPairEvidence.transitionWindowFiniteStepAuxControl ht hl hs hw hLabel hState
    hGuards hMatch

end TMVerifierXOnlyTableauSeed

end SAT
end ComplexityReduction
