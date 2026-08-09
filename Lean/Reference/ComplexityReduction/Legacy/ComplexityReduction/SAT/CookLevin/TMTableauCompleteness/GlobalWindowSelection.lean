/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.GlobalExtraction

/-!
Selected-window extraction for satisfied global fixed-micro tableau rows.

The row-local window-selection API is hard-wired to `tmVerifierMicroTime`.  This
file mirrors only the pieces needed for soundness of `tmVerifierGlobalTableauCNF`,
whose micro rows are named by `tmVerifierFixedMicroTime V p t micro`.
-/

namespace ComplexityReduction
namespace SAT

theorem tmVerifierStmtWindowsAt_exists_true_fixedActionReadGuardsFrom
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
              a) :
    ∃ w : TMVerifierStmtWindow V,
      w ∈ tmVerifierStmtWindowsAt V t stmt s ∧
        ∀ g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t w.actions idx,
          g.eval a = true := by
  induction stmt generalizing s idx with
  | push k f q ih =>
      let act : TMVerifierStackAction V :=
        TMVerifierStackAction.push (V := V) { stack := k, symbol := f s }
      have hTailDomains :
          ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t q s →
            ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx (idx + 1) →
              ∀ k : tmVerifierStackIndex V,
                CNF.Satisfies
                  (tmVerifierStackCellDomainsCNFAt V p
                    (tmVerifierFixedMicroTime V p t entry.2) k) a := by
        intro w hw entry hentry j
        exact hDomains (TMVerifierStmtWindow.consAction act w)
          (List.mem_map.mpr ⟨w, hw, rfl⟩) entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
      rcases ih s (idx + 1) hTailDomains with ⟨w, hw, hguards⟩
      refine ⟨TMVerifierStmtWindow.consAction act w, List.mem_map.mpr ⟨w, hw, rfl⟩, ?_⟩
      intro g hg
      exact hguards g (by
        simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowFixedActionReadGuardsFrom,
          TMVerifierStackAction.fixedReadGuardAt] using hg)
  | peek k f q ih =>
      classical
      let emptyChoice : TMVerifierStackReadChoice V k := TMVerifierStackReadChoice.empty
      rcases tmVerifierStmtWindowsAt_nonempty V t q (f s emptyChoice.toOption) with
        ⟨dummyTail, hdummyTail⟩
      let dummyWindow : TMVerifierStmtWindow V :=
        TMVerifierStmtWindow.consAction (TMVerifierStackAction.peek (V := V) k emptyChoice)
          (TMVerifierStmtWindow.consGuard
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 emptyChoice)
            dummyTail)
      have hdummyWindow :
          dummyWindow ∈ tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.peek k f q) s := by
        exact List.mem_flatMap.mpr
          ⟨emptyChoice, tmVerifierStackReadChoices_empty_mem V k,
            List.mem_map.mpr ⟨dummyTail, hdummyTail, by simp [dummyWindow]⟩⟩
      let dummyEntry : TMVerifierStackAction V × Nat :=
        (TMVerifierStackAction.peek (V := V) k emptyChoice, idx)
      have hdummyEntry : dummyEntry ∈ dummyWindow.actions.zipIdx idx := by
        simp [dummyEntry, dummyWindow, TMVerifierStmtWindow.consAction,
          TMVerifierStmtWindow.consGuard]
      let d :=
        tmVerifierDecodedStackCellOf V p (tmVerifierFixedMicroTime V p t idx) k 0 a
          (hDomains dummyWindow hdummyWindow dummyEntry hdummyEntry k)
          (tmVerifierCellRange_zero_mem V p)
      let choice : TMVerifierStackReadChoice V k := d.choice
      have hTailDomains :
          ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t q
              (f s choice.toOption) →
            ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx (idx + 1) →
              ∀ k : tmVerifierStackIndex V,
                CNF.Satisfies
                  (tmVerifierStackCellDomainsCNFAt V p
                    (tmVerifierFixedMicroTime V p t entry.2) k) a := by
        intro w hw entry hentry j
        let parent : TMVerifierStmtWindow V :=
          TMVerifierStmtWindow.consAction (TMVerifierStackAction.peek (V := V) k choice)
            (TMVerifierStmtWindow.consGuard
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice) w)
        have hparent :
            parent ∈ tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.peek k f q) s := by
          exact List.mem_flatMap.mpr
            ⟨choice, d.choice_mem, List.mem_map.mpr ⟨w, hw, by simp [parent, choice]⟩⟩
        exact hDomains parent hparent entry (by
          simpa [parent, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard]
            using Or.inr hentry) j
      rcases ih (f s choice.toOption) (idx + 1) hTailDomains with
        ⟨w, hw, hguards⟩
      let selected : TMVerifierStmtWindow V :=
        TMVerifierStmtWindow.consAction (TMVerifierStackAction.peek (V := V) k choice)
          (TMVerifierStmtWindow.consGuard
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice) w)
      refine ⟨selected, ?_, ?_⟩
      · exact List.mem_flatMap.mpr
          ⟨choice, d.choice_mem, List.mem_map.mpr ⟨w, hw, by simp [selected, choice]⟩⟩
      · intro g hg
        have hg' :
            g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                (tmVerifierFixedMicroTime V p t idx) 0 choice ∨
              g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t w.actions (idx + 1) := by
          simpa [selected, choice, TMVerifierStmtWindow.consAction,
            TMVerifierStmtWindow.consGuard, tmVerifierWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.fixedReadGuardAt] using hg
        rcases hg' with rfl | htail
        · exact d.atom_true
        · exact hguards g htail
  | pop k f q ih =>
      classical
      let emptyChoice : TMVerifierStackReadChoice V k := TMVerifierStackReadChoice.empty
      rcases tmVerifierStmtWindowsAt_nonempty V t q (f s emptyChoice.toOption) with
        ⟨dummyTail, hdummyTail⟩
      let dummyWindow : TMVerifierStmtWindow V :=
        TMVerifierStmtWindow.consAction (TMVerifierStackAction.pop (V := V) k emptyChoice)
          (TMVerifierStmtWindow.consGuard
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 emptyChoice)
            dummyTail)
      have hdummyWindow :
          dummyWindow ∈ tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.pop k f q) s := by
        exact List.mem_flatMap.mpr
          ⟨emptyChoice, tmVerifierStackReadChoices_empty_mem V k,
            List.mem_map.mpr ⟨dummyTail, hdummyTail, by simp [dummyWindow]⟩⟩
      let dummyEntry : TMVerifierStackAction V × Nat :=
        (TMVerifierStackAction.pop (V := V) k emptyChoice, idx)
      have hdummyEntry : dummyEntry ∈ dummyWindow.actions.zipIdx idx := by
        simp [dummyEntry, dummyWindow, TMVerifierStmtWindow.consAction,
          TMVerifierStmtWindow.consGuard]
      let d :=
        tmVerifierDecodedStackCellOf V p (tmVerifierFixedMicroTime V p t idx) k 0 a
          (hDomains dummyWindow hdummyWindow dummyEntry hdummyEntry k)
          (tmVerifierCellRange_zero_mem V p)
      let choice : TMVerifierStackReadChoice V k := d.choice
      have hTailDomains :
          ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t q
              (f s choice.toOption) →
            ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx (idx + 1) →
              ∀ k : tmVerifierStackIndex V,
                CNF.Satisfies
                  (tmVerifierStackCellDomainsCNFAt V p
                    (tmVerifierFixedMicroTime V p t entry.2) k) a := by
        intro w hw entry hentry j
        let parent : TMVerifierStmtWindow V :=
          TMVerifierStmtWindow.consAction (TMVerifierStackAction.pop (V := V) k choice)
            (TMVerifierStmtWindow.consGuard
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice) w)
        have hparent :
            parent ∈ tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.pop k f q) s := by
          exact List.mem_flatMap.mpr
            ⟨choice, d.choice_mem, List.mem_map.mpr ⟨w, hw, by simp [parent, choice]⟩⟩
        exact hDomains parent hparent entry (by
          simpa [parent, TMVerifierStmtWindow.consAction, TMVerifierStmtWindow.consGuard]
            using Or.inr hentry) j
      rcases ih (f s choice.toOption) (idx + 1) hTailDomains with
        ⟨w, hw, hguards⟩
      let selected : TMVerifierStmtWindow V :=
        TMVerifierStmtWindow.consAction (TMVerifierStackAction.pop (V := V) k choice)
          (TMVerifierStmtWindow.consGuard
            (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice) w)
      refine ⟨selected, ?_, ?_⟩
      · exact List.mem_flatMap.mpr
          ⟨choice, d.choice_mem, List.mem_map.mpr ⟨w, hw, by simp [selected, choice]⟩⟩
      · intro g hg
        have hg' :
            g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
                (tmVerifierFixedMicroTime V p t idx) 0 choice ∨
              g ∈ tmVerifierWindowFixedActionReadGuardsFrom p t w.actions (idx + 1) := by
          simpa [selected, choice, TMVerifierStmtWindow.consAction,
            TMVerifierStmtWindow.consGuard, tmVerifierWindowFixedActionReadGuardsFrom,
            TMVerifierStackAction.fixedReadGuardAt] using hg
        rcases hg' with rfl | htail
        · exact d.atom_true
        · exact hguards g htail
  | load f q ih =>
      let act : TMVerifierStackAction V := TMVerifierStackAction.load (V := V)
      have hTailDomains :
          ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t q (f s) →
            ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx (idx + 1) →
              ∀ k : tmVerifierStackIndex V,
                CNF.Satisfies
                  (tmVerifierStackCellDomainsCNFAt V p
                    (tmVerifierFixedMicroTime V p t entry.2) k) a := by
        intro w hw entry hentry j
        exact hDomains (TMVerifierStmtWindow.consAction act w)
          (List.mem_map.mpr ⟨w, hw, rfl⟩) entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
      rcases ih (f s) (idx + 1) hTailDomains with ⟨w, hw, hguards⟩
      refine ⟨TMVerifierStmtWindow.consAction act w, List.mem_map.mpr ⟨w, hw, rfl⟩, ?_⟩
      intro g hg
      exact hguards g (by
        simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowFixedActionReadGuardsFrom,
          TMVerifierStackAction.fixedReadGuardAt] using hg)
  | branch f q₁ q₂ ih₁ ih₂ =>
      by_cases hBranch : f s
      · let act : TMVerifierStackAction V :=
          TMVerifierStackAction.branch (V := V) TMVerifierStmtTag.branchTrue
        have hTailDomains :
            ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t q₁ s →
              ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx (idx + 1) →
                ∀ k : tmVerifierStackIndex V,
                  CNF.Satisfies
                    (tmVerifierStackCellDomainsCNFAt V p
                      (tmVerifierFixedMicroTime V p t entry.2) k) a := by
          intro w hw entry hentry j
          have hparent :
              TMVerifierStmtWindow.consAction act w ∈
                tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.branch f q₁ q₂) s := by
            simp [tmVerifierStmtWindowsAt, hBranch, act]
            exact ⟨w, hw, rfl⟩
          exact hDomains (TMVerifierStmtWindow.consAction act w) hparent entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
        rcases ih₁ s (idx + 1) hTailDomains with ⟨w, hw, hguards⟩
        refine ⟨TMVerifierStmtWindow.consAction act w, ?_, ?_⟩
        · simp [tmVerifierStmtWindowsAt, hBranch, act]
          exact ⟨w, hw, rfl⟩
        · intro g hg
          exact hguards g (by
            simpa [act, TMVerifierStmtWindow.consAction,
              tmVerifierWindowFixedActionReadGuardsFrom,
              TMVerifierStackAction.fixedReadGuardAt] using hg)
      · let act : TMVerifierStackAction V :=
          TMVerifierStackAction.branch (V := V) TMVerifierStmtTag.branchFalse
        have hTailDomains :
            ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t q₂ s →
              ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx (idx + 1) →
                ∀ k : tmVerifierStackIndex V,
                  CNF.Satisfies
                    (tmVerifierStackCellDomainsCNFAt V p
                      (tmVerifierFixedMicroTime V p t entry.2) k) a := by
          intro w hw entry hentry j
          have hparent :
              TMVerifierStmtWindow.consAction act w ∈
                tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.branch f q₁ q₂) s := by
            simp [tmVerifierStmtWindowsAt, hBranch, act]
            exact ⟨w, hw, rfl⟩
          exact hDomains (TMVerifierStmtWindow.consAction act w) hparent entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
        rcases ih₂ s (idx + 1) hTailDomains with ⟨w, hw, hguards⟩
        refine ⟨TMVerifierStmtWindow.consAction act w, ?_, ?_⟩
        · simp [tmVerifierStmtWindowsAt, hBranch, act]
          exact ⟨w, hw, rfl⟩
        · intro g hg
          exact hguards g (by
            simpa [act, TMVerifierStmtWindow.consAction,
              tmVerifierWindowFixedActionReadGuardsFrom,
              TMVerifierStackAction.fixedReadGuardAt] using hg)
  | goto f =>
      refine ⟨{ guards := [], actions := [], nextLabel := some (f s), nextState := s },
        by simp [tmVerifierStmtWindowsAt], ?_⟩
      intro g hg
      simp [tmVerifierWindowFixedActionReadGuardsFrom] at hg
  | halt =>
      refine ⟨{ guards := [], actions := [], nextLabel := none, nextState := s },
        by simp [tmVerifierStmtWindowsAt], ?_⟩
      intro g hg
      simp [tmVerifierWindowFixedActionReadGuardsFrom] at hg

theorem tmVerifierStmtWindowsAt_exists_true_fixedActionReadGuards
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
              a) :
    ∃ w : TMVerifierStmtWindow V,
      w ∈ tmVerifierStmtWindowsAt V t stmt s ∧
        ∀ g ∈ tmVerifierWindowFixedActionReadGuards p t w, g.eval a = true := by
  simpa [tmVerifierWindowFixedActionReadGuards] using
    tmVerifierStmtWindowsAt_exists_true_fixedActionReadGuardsFrom V p t stmt s 0 a hDomains

end SAT
end ComplexityReduction
