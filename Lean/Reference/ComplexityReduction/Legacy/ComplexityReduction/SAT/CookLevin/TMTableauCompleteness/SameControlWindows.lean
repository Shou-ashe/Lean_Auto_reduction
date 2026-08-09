/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMStackChoiceUniqueness
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.TransitionRowsAggregation

namespace ComplexityReduction
namespace SAT

/-! ### Same-control generated-window aggregation -/

theorem tmVerifierWindowActionReadGuardsFrom_cons_of_readGuardAt_nil
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (t idx : Nat) (act : TMVerifierStackAction V)
    (actions : List (TMVerifierStackAction V))
    (hRead : act.readGuardAt t idx = []) :
    tmVerifierWindowActionReadGuardsFrom t (act :: actions) idx =
      tmVerifierWindowActionReadGuardsFrom t actions (idx + 1) := by
  simp [tmVerifierWindowActionReadGuardsFrom, hRead]

theorem tmVerifierStmtWindowsAt_unique_of_true_actionReadGuardsFrom
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stmt : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ)
    (idx : Nat) (a : Assignment)
    (hDomains :
      ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t stmt s →
        ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx idx →
          ∀ k : tmVerifierStackIndex V,
            CNF.Satisfies
              (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t entry.2) k)
              a)
    {w₁ w₂ : TMVerifierStmtWindow V}
    (hw₁ : w₁ ∈ tmVerifierStmtWindowsAt V t stmt s)
    (hw₂ : w₂ ∈ tmVerifierStmtWindowsAt V t stmt s)
    (hGuards₁ :
      ∀ g ∈ tmVerifierWindowActionReadGuardsFrom t w₁.actions idx, g.eval a = true)
    (hGuards₂ :
      ∀ g ∈ tmVerifierWindowActionReadGuardsFrom t w₂.actions idx, g.eval a = true) :
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
                    (tmVerifierMicroTime t entry.2) j) a := by
        intro w hw entry hentry j
        exact hDomains (TMVerifierStmtWindow.consAction act w)
          (List.mem_map.mpr ⟨w, hw, rfl⟩) entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
      have hTailGuards₁ :
          ∀ g ∈ tmVerifierWindowActionReadGuardsFrom t tail₁.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        have hEq :
            tmVerifierWindowActionReadGuardsFrom t
                (TMVerifierStmtWindow.consAction act tail₁).actions idx =
              tmVerifierWindowActionReadGuardsFrom t tail₁.actions (idx + 1) := by
          exact tmVerifierWindowActionReadGuardsFrom_cons_of_readGuardAt_nil t idx act
            tail₁.actions (by simp [act, TMVerifierStackAction.readGuardAt])
        exact hGuards₁ g (by simpa [hEq] using hg)
      have hTailGuards₂ :
          ∀ g ∈ tmVerifierWindowActionReadGuardsFrom t tail₂.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        have hEq :
            tmVerifierWindowActionReadGuardsFrom t
                (TMVerifierStmtWindow.consAction act tail₂).actions idx =
              tmVerifierWindowActionReadGuardsFrom t tail₂.actions (idx + 1) := by
          exact tmVerifierWindowActionReadGuardsFrom_cons_of_readGuardAt_nil t idx act
            tail₂.actions (by simp [act, TMVerifierStackAction.readGuardAt])
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
      let act₂ : TMVerifierStackAction V := TMVerifierStackAction.peek (V := V) k choice₂
      have hHead₁ :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
            (tmVerifierMicroTime t idx) 0 choice₁).eval a = true := by
        exact hGuards₁ _ (by
          simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierWindowActionReadGuardsFrom, TMVerifierStackAction.readGuardAt])
      have hHead₂ :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
            (tmVerifierMicroTime t idx) 0 choice₂).eval a = true := by
        exact hGuards₂ _ (by
          simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierWindowActionReadGuardsFrom, TMVerifierStackAction.readGuardAt])
      have hEntry₁ :
          (act₁, idx) ∈
            (TMVerifierStmtWindow.consAction act₁
              (TMVerifierStmtWindow.consGuard
                (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice₁)
                tail₁)).actions.zipIdx idx := by
        simp [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard]
      have hDomain :
          CNF.Satisfies
            (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t idx) k) a :=
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
          (tmVerifierMicroTime t idx) k 0 a hDomain
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
                      (tmVerifierMicroTime t entry.2) j) a := by
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
          ∀ g ∈ tmVerifierWindowActionReadGuardsFrom t tail₁.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₁ g (by
          have hmem :
              g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                    (tmVerifierMicroTime t idx) 0 choice₁ ∨
                g ∈ tmVerifierWindowActionReadGuardsFrom t tail₁.actions (idx + 1) :=
            Or.inr hg
          simpa [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierWindowActionReadGuardsFrom, TMVerifierStackAction.readGuardAt] using hmem)
      have hTailGuards₂ :
          ∀ g ∈ tmVerifierWindowActionReadGuardsFrom t tail₂.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₂ g (by
          have hmem :
              g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                    (tmVerifierMicroTime t idx) 0 choice₁ ∨
                g ∈ tmVerifierWindowActionReadGuardsFrom t tail₂.actions (idx + 1) :=
            Or.inr hg
          simpa [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierWindowActionReadGuardsFrom, TMVerifierStackAction.readGuardAt] using hmem)
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
      let act₂ : TMVerifierStackAction V := TMVerifierStackAction.pop (V := V) k choice₂
      have hHead₁ :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
            (tmVerifierMicroTime t idx) 0 choice₁).eval a = true := by
        exact hGuards₁ _ (by
          simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierWindowActionReadGuardsFrom, TMVerifierStackAction.readGuardAt])
      have hHead₂ :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
            (tmVerifierMicroTime t idx) 0 choice₂).eval a = true := by
        exact hGuards₂ _ (by
          simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierWindowActionReadGuardsFrom, TMVerifierStackAction.readGuardAt])
      have hEntry₁ :
          (act₁, idx) ∈
            (TMVerifierStmtWindow.consAction act₁
              (TMVerifierStmtWindow.consGuard
                (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice₁)
                tail₁)).actions.zipIdx idx := by
        simp [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard]
      have hDomain :
          CNF.Satisfies
            (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t idx) k) a :=
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
          (tmVerifierMicroTime t idx) k 0 a hDomain
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
                      (tmVerifierMicroTime t entry.2) j) a := by
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
          ∀ g ∈ tmVerifierWindowActionReadGuardsFrom t tail₁.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₁ g (by
          have hmem :
              g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                    (tmVerifierMicroTime t idx) 0 choice₁ ∨
                g ∈ tmVerifierWindowActionReadGuardsFrom t tail₁.actions (idx + 1) :=
            Or.inr hg
          simpa [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierWindowActionReadGuardsFrom, TMVerifierStackAction.readGuardAt] using hmem)
      have hTailGuards₂ :
          ∀ g ∈ tmVerifierWindowActionReadGuardsFrom t tail₂.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₂ g (by
          have hmem :
              g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                    (tmVerifierMicroTime t idx) 0 choice₁ ∨
                g ∈ tmVerifierWindowActionReadGuardsFrom t tail₂.actions (idx + 1) :=
            Or.inr hg
          simpa [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierWindowActionReadGuardsFrom, TMVerifierStackAction.readGuardAt] using hmem)
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
                    (tmVerifierMicroTime t entry.2) j) a := by
        intro w hw entry hentry j
        exact hDomains (TMVerifierStmtWindow.consAction act w)
          (List.mem_map.mpr ⟨w, hw, rfl⟩) entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
      have hTailGuards₁ :
          ∀ g ∈ tmVerifierWindowActionReadGuardsFrom t tail₁.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₁ g (by
          simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowActionReadGuardsFrom,
            TMVerifierStackAction.readGuardAt] using hg)
      have hTailGuards₂ :
          ∀ g ∈ tmVerifierWindowActionReadGuardsFrom t tail₂.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₂ g (by
          simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowActionReadGuardsFrom,
            TMVerifierStackAction.readGuardAt] using hg)
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
                      (tmVerifierMicroTime t entry.2) j) a := by
          intro w hw entry hentry j
          have hparent :
              TMVerifierStmtWindow.consAction act w ∈
                tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.branch f q₁ q₂) s := by
            simp [tmVerifierStmtWindowsAt, hBranch, act]
            exact ⟨w, hw, rfl⟩
          exact hDomains (TMVerifierStmtWindow.consAction act w) hparent entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
        have hTailGuards₁ :
            ∀ g ∈ tmVerifierWindowActionReadGuardsFrom t tail₁.actions (idx + 1),
              g.eval a = true := by
          intro g hg
          have hEq :
              tmVerifierWindowActionReadGuardsFrom t
                  (TMVerifierStmtWindow.consAction act tail₁).actions idx =
                tmVerifierWindowActionReadGuardsFrom t tail₁.actions (idx + 1) := by
            exact tmVerifierWindowActionReadGuardsFrom_cons_of_readGuardAt_nil t idx act
              tail₁.actions (by simp [act, TMVerifierStackAction.readGuardAt])
          exact hGuards₁ g (by simpa [hEq] using hg)
        have hTailGuards₂ :
            ∀ g ∈ tmVerifierWindowActionReadGuardsFrom t tail₂.actions (idx + 1),
              g.eval a = true := by
          intro g hg
          have hEq :
              tmVerifierWindowActionReadGuardsFrom t
                  (TMVerifierStmtWindow.consAction act tail₂).actions idx =
                tmVerifierWindowActionReadGuardsFrom t tail₂.actions (idx + 1) := by
            exact tmVerifierWindowActionReadGuardsFrom_cons_of_readGuardAt_nil t idx act
              tail₂.actions (by simp [act, TMVerifierStackAction.readGuardAt])
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
                      (tmVerifierMicroTime t entry.2) j) a := by
          intro w hw entry hentry j
          have hparent :
              TMVerifierStmtWindow.consAction act w ∈
                tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.branch f q₁ q₂) s := by
            simp [tmVerifierStmtWindowsAt, hBranch, act]
            exact ⟨w, hw, rfl⟩
          exact hDomains (TMVerifierStmtWindow.consAction act w) hparent entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
        have hTailGuards₁ :
            ∀ g ∈ tmVerifierWindowActionReadGuardsFrom t tail₁.actions (idx + 1),
              g.eval a = true := by
          intro g hg
          have hEq :
              tmVerifierWindowActionReadGuardsFrom t
                  (TMVerifierStmtWindow.consAction act tail₁).actions idx =
                tmVerifierWindowActionReadGuardsFrom t tail₁.actions (idx + 1) := by
            exact tmVerifierWindowActionReadGuardsFrom_cons_of_readGuardAt_nil t idx act
              tail₁.actions (by simp [act, TMVerifierStackAction.readGuardAt])
          exact hGuards₁ g (by simpa [hEq] using hg)
        have hTailGuards₂ :
            ∀ g ∈ tmVerifierWindowActionReadGuardsFrom t tail₂.actions (idx + 1),
              g.eval a = true := by
          intro g hg
          have hEq :
              tmVerifierWindowActionReadGuardsFrom t
                  (TMVerifierStmtWindow.consAction act tail₂).actions idx =
                tmVerifierWindowActionReadGuardsFrom t tail₂.actions (idx + 1) := by
            exact tmVerifierWindowActionReadGuardsFrom_cons_of_readGuardAt_nil t idx act
              tail₂.actions (by simp [act, TMVerifierStackAction.readGuardAt])
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

theorem tmVerifierStmtWindowsAt_unique_of_true_actionReadGuards
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (stmt : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ)
    (a : Assignment)
    (hDomains :
      ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t stmt s →
        ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx →
          ∀ k : tmVerifierStackIndex V,
            CNF.Satisfies
              (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t entry.2) k)
              a)
    {w₁ w₂ : TMVerifierStmtWindow V}
    (hw₁ : w₁ ∈ tmVerifierStmtWindowsAt V t stmt s)
    (hw₂ : w₂ ∈ tmVerifierStmtWindowsAt V t stmt s)
    (hGuards₁ : ∀ g ∈ tmVerifierWindowActionReadGuards t w₁, g.eval a = true)
    (hGuards₂ : ∀ g ∈ tmVerifierWindowActionReadGuards t w₂, g.eval a = true) :
    w₁ = w₂ := by
  simpa [tmVerifierWindowActionReadGuards] using
    tmVerifierStmtWindowsAt_unique_of_true_actionReadGuardsFrom V p t stmt s 0 a
      hDomains hw₁ hw₂ hGuards₁ hGuards₂

theorem tmVerifierSelectedWindowRunStacks_sameControl_current
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (selected : TMVerifierStmtWindow V)
    (hwSelected : selected ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hGuardsSelected :
      ∀ g ∈ tmVerifierWindowActionReadGuards t selected,
        g.eval
          (tmVerifierStackFamilyAssignment V p
            (tmVerifierSelectedWindowRunStacks V p t selected)) = true)
    (hSelected :
      CNF.Satisfies
        (tmVerifierWindowControlCNFAt V t l s selected ++
          tmVerifierWindowStackBoundaryCNFAt V p t l s selected ++
            tmVerifierWindowStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
              p t selected (tmVerifierWindowAntecedents V t l s selected))
        (tmVerifierStackFamilyAssignment V p
          (tmVerifierSelectedWindowRunStacks V p t selected))) :
    (∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies (tmVerifierWindowControlCNFAt V t l s w)
            (tmVerifierStackFamilyAssignment V p
              (tmVerifierSelectedWindowRunStacks V p t selected))) ∧
      (∀ w : TMVerifierStmtWindow V,
        w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
          CNF.Satisfies
            (tmVerifierWindowStackBoundaryCNFAt V p t l s w ++
              tmVerifierWindowStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
                p t w (tmVerifierWindowAntecedents V t l s w))
            (tmVerifierStackFamilyAssignment V p
              (tmVerifierSelectedWindowRunStacks V p t selected))) := by
  let a :=
    tmVerifierStackFamilyAssignment V p
      (tmVerifierSelectedWindowRunStacks V p t selected)
  have hDomains :
      ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s →
        ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx →
          ∀ k : tmVerifierStackIndex V,
            CNF.Satisfies
              (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t entry.2) k)
              a := by
    intro _w _hw entry _hentry k
    exact tmVerifierStackCellDomainsCNFAt_satisfies_stackFamilyAssignment V p
      (tmVerifierSelectedWindowRunStacks V p t selected) (tmVerifierMicroTime t entry.2)
      (by
        rw [tmVerifierSelectedWindowRunStacks_at_micro V p t selected entry.2]
        exact tmVerifierWindowMicroStacks_stacksActive V p t hwSelected entry.2)
      k
  have hSelectedOuter :
      CNF.Satisfies
        ((tmVerifierWindowControlCNFAt V t l s selected ++
            tmVerifierWindowStackBoundaryCNFAt V p t l s selected) ++
          tmVerifierWindowStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
            p t selected (tmVerifierWindowAntecedents V t l s selected)) a := by
    simpa [a] using hSelected
  have hSelectedSplit :=
    (CNF.satisfies_append
      (tmVerifierWindowControlCNFAt V t l s selected ++
        tmVerifierWindowStackBoundaryCNFAt V p t l s selected)
      (tmVerifierWindowStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
        p t selected (tmVerifierWindowAntecedents V t l s selected)) a).1 hSelectedOuter
  have hSelectedControlBoundary :=
    (CNF.satisfies_append
      (tmVerifierWindowControlCNFAt V t l s selected)
      (tmVerifierWindowStackBoundaryCNFAt V p t l s selected) a).1 hSelectedSplit.1
  have hSelectedStack :
      CNF.Satisfies
        (tmVerifierWindowStackBoundaryCNFAt V p t l s selected ++
          tmVerifierWindowStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
            p t selected (tmVerifierWindowAntecedents V t l s selected)) a := by
    exact (CNF.satisfies_append
      (tmVerifierWindowStackBoundaryCNFAt V p t l s selected)
      (tmVerifierWindowStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
        p t selected (tmVerifierWindowAntecedents V t l s selected)) a).2
      ⟨hSelectedControlBoundary.2, hSelectedSplit.2⟩
  constructor
  · intro w hw
    by_cases hAll :
        ∀ g ∈ tmVerifierWindowActionReadGuards t w, g.eval a = true
    · have hEq :
          selected = w :=
        tmVerifierStmtWindowsAt_unique_of_true_actionReadGuards V p t
          ((tmVerifierTM V).m l) s a hDomains hwSelected hw
          (by simpa [a] using hGuardsSelected) hAll
      simpa [a, hEq] using hSelectedControlBoundary.1
    · push Not at hAll
      rcases hAll with ⟨bad, hbadMem, hbadNotTrue⟩
      have hbadFalse : bad.eval a = false := by
        cases hEval : bad.eval a <;> simp [hEval] at hbadNotTrue ⊢
      have hmemAnt : bad ∈ tmVerifierWindowAntecedents V t l s w := by
        rw [tmVerifierWindowAntecedents]
        exact List.mem_append.mpr (Or.inr hbadMem)
      exact tmVerifierWindowControlCNFAt_satisfies_of_false_antecedent V t l s w a
        hmemAnt hbadFalse
  · intro w hw
    by_cases hAll :
        ∀ g ∈ tmVerifierWindowActionReadGuards t w, g.eval a = true
    · have hEq :
          selected = w :=
        tmVerifierStmtWindowsAt_unique_of_true_actionReadGuards V p t
          ((tmVerifierTM V).m l) s a hDomains hwSelected hw
          (by simpa [a] using hGuardsSelected) hAll
      simpa [a, hEq] using hSelectedStack
    · push Not at hAll
      rcases hAll with ⟨bad, hbadMem, hbadNotTrue⟩
      have hbadFalse : bad.eval a = false := by
        cases hEval : bad.eval a <;> simp [hEval] at hbadNotTrue ⊢
      have hmemAnt : bad ∈ tmVerifierWindowAntecedents V t l s w := by
        rw [tmVerifierWindowAntecedents]
        exact List.mem_append.mpr (Or.inr hbadMem)
      exact tmVerifierWindowStackCNF_satisfies_of_false_antecedent V
        (tmVerifierActivePushPayloadBoundary V) p t l s w a hmemAnt hbadFalse

theorem tmVerifierTransitionRowCNFAt_satisfies_sameControl_selected
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (selected : TMVerifierStmtWindow V)
    (hl : (tmVerifierRunCfgAt V p t).l = some l)
    (hs : (tmVerifierRunCfgAt V p t).var = s)
    (hwSelected : selected ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hGuardsSelected :
      ∀ g ∈ tmVerifierWindowActionReadGuards t selected,
        g.eval
          (tmVerifierStackFamilyAssignment V p
            (tmVerifierSelectedWindowRunStacks V p t selected)) = true)
    (hSelected :
      CNF.Satisfies
        (tmVerifierWindowControlCNFAt V t l s selected ++
          tmVerifierWindowStackBoundaryCNFAt V p t l s selected ++
            tmVerifierWindowStackActionCNFAt V (tmVerifierActivePushPayloadBoundary V)
              p t selected (tmVerifierWindowAntecedents V t l s selected))
        (tmVerifierStackFamilyAssignment V p
          (tmVerifierSelectedWindowRunStacks V p t selected))) :
    CNF.Satisfies
      (tmVerifierTransitionRowCNFAt V (tmVerifierActivePushPayloadBoundary V) p t)
      (tmVerifierStackFamilyAssignment V p
          (tmVerifierSelectedWindowRunStacks V p t selected)) := by
  have hCurrent :=
    tmVerifierSelectedWindowRunStacks_sameControl_current V p t l s selected
      hwSelected hGuardsSelected hSelected
  exact tmVerifierTransitionRowCNFAt_satisfies_current_label_state V p t l s
    (tmVerifierSelectedWindowRunStacks V p t selected) hl hs hCurrent.1 hCurrent.2

end SAT
end ComplexityReduction
