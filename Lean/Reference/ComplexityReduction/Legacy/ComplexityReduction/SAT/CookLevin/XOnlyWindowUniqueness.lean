/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyTransitionAccepted
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyStackDecoder

/-!
Uniqueness for generated statement windows selected by x-only fixed read guards.
-/

namespace ComplexityReduction
namespace SAT

theorem tmVerifierXOnlyWindowFixedActionReadGuardsFrom_cons_of_xOnlyFixedReadGuardAt_nil
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    (x : L.Instance.Carrier) (t idx : Nat)
    (act : TMVerifierStackAction V) (actions : List (TMVerifierStackAction V))
    (hRead : act.xOnlyFixedReadGuardAt x t idx = []) :
    tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t (act :: actions) idx =
      tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t actions (idx + 1) := by
  simp [tmVerifierXOnlyWindowFixedActionReadGuardsFrom, hRead]

theorem tmVerifierStmtWindowsAt_unique_of_true_xOnlyFixedActionReadGuardsFrom
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (t : Nat) (stmt : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ)
    (idx : Nat) (a : Assignment)
    (hDomains :
      ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t stmt s →
        ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx idx →
          ∀ k : tmVerifierStackIndex V,
            CNF.Satisfies
              (tmVerifierXOnlyStackCellDomainsCNFAt V x
                (tmVerifierXOnlyFixedMicroTime V x t entry.2) k)
              a)
    {w₁ w₂ : TMVerifierStmtWindow V}
    (hw₁ : w₁ ∈ tmVerifierStmtWindowsAt V t stmt s)
    (hw₂ : w₂ ∈ tmVerifierStmtWindowsAt V t stmt s)
    (hGuards₁ :
      ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t w₁.actions idx,
        g.eval a = true)
    (hGuards₂ :
      ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t w₂.actions idx,
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
                  (tmVerifierXOnlyStackCellDomainsCNFAt V x
                    (tmVerifierXOnlyFixedMicroTime V x t entry.2) j) a := by
        intro w hw entry hentry j
        exact hDomains (TMVerifierStmtWindow.consAction act w)
          (List.mem_map.mpr ⟨w, hw, rfl⟩) entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
      have hTailGuards₁ :
          ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₁.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        have hEq :
            tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t
                (TMVerifierStmtWindow.consAction act tail₁).actions idx =
              tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₁.actions (idx + 1) := by
          exact tmVerifierXOnlyWindowFixedActionReadGuardsFrom_cons_of_xOnlyFixedReadGuardAt_nil
            x t idx act tail₁.actions (by simp [act, TMVerifierStackAction.xOnlyFixedReadGuardAt])
        exact hGuards₁ g (by simpa [hEq] using hg)
      have hTailGuards₂ :
          ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₂.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        have hEq :
            tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t
                (TMVerifierStmtWindow.consAction act tail₂).actions idx =
              tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₂.actions (idx + 1) := by
          exact tmVerifierXOnlyWindowFixedActionReadGuardsFrom_cons_of_xOnlyFixedReadGuardAt_nil
            x t idx act tail₂.actions (by simp [act, TMVerifierStackAction.xOnlyFixedReadGuardAt])
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
            (tmVerifierXOnlyFixedMicroTime V x t idx) 0 choice₁).eval a = true := by
        exact hGuards₁ _ (by
          simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierXOnlyWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.xOnlyFixedReadGuardAt])
      have hHead₂ :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
            (tmVerifierXOnlyFixedMicroTime V x t idx) 0 choice₂).eval a = true := by
        exact hGuards₂ _ (by
          simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierXOnlyWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.xOnlyFixedReadGuardAt])
      have hEntry₁ :
          (act₁, idx) ∈
            (TMVerifierStmtWindow.consAction act₁
              (TMVerifierStmtWindow.consGuard
                (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice₁)
                tail₁)).actions.zipIdx idx := by
        simp [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard]
      have hDomain :
          CNF.Satisfies
            (tmVerifierXOnlyStackCellDomainsCNFAt V x
              (tmVerifierXOnlyFixedMicroTime V x t idx) k)
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
        tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x
          (tmVerifierXOnlyFixedMicroTime V x t idx) k 0 a hDomain
          (tmVerifierXOnlyCellRange_zero_mem V x) choice₁ choice₂ hchoice₁ hchoice₂
          hHead₁ hHead₂
      subst choice₂
      have hTailDomains :
          ∀ w : TMVerifierStmtWindow V,
            w ∈ tmVerifierStmtWindowsAt V t q (f s choice₁.toOption) →
              ∀ entry : TMVerifierStackAction V × Nat,
                entry ∈ w.actions.zipIdx (idx + 1) →
                ∀ j : tmVerifierStackIndex V,
                  CNF.Satisfies
                    (tmVerifierXOnlyStackCellDomainsCNFAt V x
                      (tmVerifierXOnlyFixedMicroTime V x t entry.2) j) a := by
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
          ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₁.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₁ g (by
          have hmem :
              g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                    (tmVerifierXOnlyFixedMicroTime V x t idx) 0 choice₁ ∨
                g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₁.actions
                  (idx + 1) := Or.inr hg
          simpa [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierXOnlyWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.xOnlyFixedReadGuardAt] using hmem)
      have hTailGuards₂ :
          ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₂.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₂ g (by
          have hmem :
              g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                    (tmVerifierXOnlyFixedMicroTime V x t idx) 0 choice₁ ∨
                g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₂.actions
                  (idx + 1) := Or.inr hg
          simpa [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierXOnlyWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.xOnlyFixedReadGuardAt] using hmem)
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
            (tmVerifierXOnlyFixedMicroTime V x t idx) 0 choice₁).eval a = true := by
        exact hGuards₁ _ (by
          simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierXOnlyWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.xOnlyFixedReadGuardAt])
      have hHead₂ :
          (TMVerifierStackReadChoice.atomAt (V := V) (k := k)
            (tmVerifierXOnlyFixedMicroTime V x t idx) 0 choice₂).eval a = true := by
        exact hGuards₂ _ (by
          simp [TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierXOnlyWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.xOnlyFixedReadGuardAt])
      have hEntry₁ :
          (act₁, idx) ∈
            (TMVerifierStmtWindow.consAction act₁
              (TMVerifierStmtWindow.consGuard
                (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice₁)
                tail₁)).actions.zipIdx idx := by
        simp [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard]
      have hDomain :
          CNF.Satisfies
            (tmVerifierXOnlyStackCellDomainsCNFAt V x
              (tmVerifierXOnlyFixedMicroTime V x t idx) k)
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
        tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x
          (tmVerifierXOnlyFixedMicroTime V x t idx) k 0 a hDomain
          (tmVerifierXOnlyCellRange_zero_mem V x) choice₁ choice₂ hchoice₁ hchoice₂
          hHead₁ hHead₂
      subst choice₂
      have hTailDomains :
          ∀ w : TMVerifierStmtWindow V,
            w ∈ tmVerifierStmtWindowsAt V t q (f s choice₁.toOption) →
              ∀ entry : TMVerifierStackAction V × Nat,
                entry ∈ w.actions.zipIdx (idx + 1) →
                ∀ j : tmVerifierStackIndex V,
                  CNF.Satisfies
                    (tmVerifierXOnlyStackCellDomainsCNFAt V x
                      (tmVerifierXOnlyFixedMicroTime V x t entry.2) j) a := by
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
          ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₁.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₁ g (by
          have hmem :
              g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                    (tmVerifierXOnlyFixedMicroTime V x t idx) 0 choice₁ ∨
                g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₁.actions
                  (idx + 1) := Or.inr hg
          simpa [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierXOnlyWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.xOnlyFixedReadGuardAt] using hmem)
      have hTailGuards₂ :
          ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₂.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₂ g (by
          have hmem :
              g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                    (tmVerifierXOnlyFixedMicroTime V x t idx) 0 choice₁ ∨
                g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₂.actions
                  (idx + 1) := Or.inr hg
          simpa [act₁, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard,
            tmVerifierXOnlyWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.xOnlyFixedReadGuardAt] using hmem)
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
                  (tmVerifierXOnlyStackCellDomainsCNFAt V x
                    (tmVerifierXOnlyFixedMicroTime V x t entry.2) j) a := by
        intro w hw entry hentry j
        exact hDomains (TMVerifierStmtWindow.consAction act w)
          (List.mem_map.mpr ⟨w, hw, rfl⟩) entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
      have hTailGuards₁ :
          ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₁.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₁ g (by
          simpa [act, TMVerifierStmtWindow.consAction,
            tmVerifierXOnlyWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.xOnlyFixedReadGuardAt] using hg)
      have hTailGuards₂ :
          ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₂.actions (idx + 1),
            g.eval a = true := by
        intro g hg
        exact hGuards₂ g (by
          simpa [act, TMVerifierStmtWindow.consAction,
            tmVerifierXOnlyWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.xOnlyFixedReadGuardAt] using hg)
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
                    (tmVerifierXOnlyStackCellDomainsCNFAt V x
                      (tmVerifierXOnlyFixedMicroTime V x t entry.2) j) a := by
          intro w hw entry hentry j
          have hparent :
              TMVerifierStmtWindow.consAction act w ∈
                tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.branch f q₁ q₂) s := by
            simp [tmVerifierStmtWindowsAt, hBranch, act]
            exact ⟨w, hw, rfl⟩
          exact hDomains (TMVerifierStmtWindow.consAction act w) hparent entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
        have hTailGuards₁ :
            ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₁.actions (idx + 1),
              g.eval a = true := by
          intro g hg
          have hEq :
              tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t
                  (TMVerifierStmtWindow.consAction act tail₁).actions idx =
                tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₁.actions (idx + 1) := by
            exact tmVerifierXOnlyWindowFixedActionReadGuardsFrom_cons_of_xOnlyFixedReadGuardAt_nil
              x t idx act tail₁.actions
              (by simp [act, TMVerifierStackAction.xOnlyFixedReadGuardAt])
          exact hGuards₁ g (by simpa [hEq] using hg)
        have hTailGuards₂ :
            ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₂.actions (idx + 1),
              g.eval a = true := by
          intro g hg
          have hEq :
              tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t
                  (TMVerifierStmtWindow.consAction act tail₂).actions idx =
                tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₂.actions (idx + 1) := by
            exact tmVerifierXOnlyWindowFixedActionReadGuardsFrom_cons_of_xOnlyFixedReadGuardAt_nil
              x t idx act tail₂.actions
              (by simp [act, TMVerifierStackAction.xOnlyFixedReadGuardAt])
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
                    (tmVerifierXOnlyStackCellDomainsCNFAt V x
                      (tmVerifierXOnlyFixedMicroTime V x t entry.2) j) a := by
          intro w hw entry hentry j
          have hparent :
              TMVerifierStmtWindow.consAction act w ∈
                tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.branch f q₁ q₂) s := by
            simp [tmVerifierStmtWindowsAt, hBranch, act]
            exact ⟨w, hw, rfl⟩
          exact hDomains (TMVerifierStmtWindow.consAction act w) hparent entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
        have hTailGuards₁ :
            ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₁.actions (idx + 1),
              g.eval a = true := by
          intro g hg
          have hEq :
              tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t
                  (TMVerifierStmtWindow.consAction act tail₁).actions idx =
                tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₁.actions (idx + 1) := by
            exact tmVerifierXOnlyWindowFixedActionReadGuardsFrom_cons_of_xOnlyFixedReadGuardAt_nil
              x t idx act tail₁.actions
              (by simp [act, TMVerifierStackAction.xOnlyFixedReadGuardAt])
          exact hGuards₁ g (by simpa [hEq] using hg)
        have hTailGuards₂ :
            ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₂.actions (idx + 1),
              g.eval a = true := by
          intro g hg
          have hEq :
              tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t
                  (TMVerifierStmtWindow.consAction act tail₂).actions idx =
                tmVerifierXOnlyWindowFixedActionReadGuardsFrom x t tail₂.actions (idx + 1) := by
            exact tmVerifierXOnlyWindowFixedActionReadGuardsFrom_cons_of_xOnlyFixedReadGuardAt_nil
              x t idx act tail₂.actions
              (by simp [act, TMVerifierStackAction.xOnlyFixedReadGuardAt])
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

theorem tmVerifierStmtWindowsAt_unique_of_true_xOnlyFixedActionReadGuards
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (t : Nat) (stmt : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ)
    (a : Assignment)
    (hDomains :
      ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t stmt s →
        ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx →
          ∀ k : tmVerifierStackIndex V,
            CNF.Satisfies
              (tmVerifierXOnlyStackCellDomainsCNFAt V x
                (tmVerifierXOnlyFixedMicroTime V x t entry.2) k)
              a)
    {w₁ w₂ : TMVerifierStmtWindow V}
    (hw₁ : w₁ ∈ tmVerifierStmtWindowsAt V t stmt s)
    (hw₂ : w₂ ∈ tmVerifierStmtWindowsAt V t stmt s)
    (hGuards₁ : ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuards x t w₁, g.eval a = true)
    (hGuards₂ : ∀ g ∈ tmVerifierXOnlyWindowFixedActionReadGuards x t w₂, g.eval a = true) :
    w₁ = w₂ := by
  simpa [tmVerifierXOnlyWindowFixedActionReadGuards] using
    tmVerifierStmtWindowsAt_unique_of_true_xOnlyFixedActionReadGuardsFrom V x t stmt s 0 a
      hDomains hw₁ hw₂ hGuards₁ hGuards₂

end SAT
end ComplexityReduction
