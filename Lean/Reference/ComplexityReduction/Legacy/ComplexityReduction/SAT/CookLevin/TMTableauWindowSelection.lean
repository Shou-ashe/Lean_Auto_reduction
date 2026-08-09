/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauStackLists

/-!
Selected statement windows from decoded micro-domain rows.

The aggregate transition row enumerates every finite statement window.  For
`peek`/`pop`, the active window is the one whose recorded read choices are the
true choices selected by the corresponding input micro-row stack domains.  This
file proves that such a window exists and packages the result for fixed-pair and
x-only tableau evidence.
-/

namespace ComplexityReduction
namespace SAT

theorem tmVerifierStmtWindowsAt_nonempty
    {L : EncodedDecisionProblem} (V : TMVerifier L) (t : Nat)
    (stmt : (tmVerifierTM V).Stmt) (s : (tmVerifierTM V).σ) :
    ∃ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t stmt s := by
  induction stmt generalizing s with
  | push k f q ih =>
      rcases ih s with ⟨w, hw⟩
      exact ⟨TMVerifierStmtWindow.consAction
        (TMVerifierStackAction.push (V := V) { stack := k, symbol := f s }) w,
        List.mem_map.mpr ⟨w, hw, rfl⟩⟩
  | peek k f q ih =>
      let choice : TMVerifierStackReadChoice V k := TMVerifierStackReadChoice.empty
      rcases ih (f s choice.toOption) with ⟨w, hw⟩
      exact
        ⟨TMVerifierStmtWindow.consAction (TMVerifierStackAction.peek (V := V) k choice)
            (TMVerifierStmtWindow.consGuard
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice) w),
          List.mem_flatMap.mpr
            ⟨choice, tmVerifierStackReadChoices_empty_mem V k,
              List.mem_map.mpr ⟨w, hw, rfl⟩⟩⟩
  | pop k f q ih =>
      let choice : TMVerifierStackReadChoice V k := TMVerifierStackReadChoice.empty
      rcases ih (f s choice.toOption) with ⟨w, hw⟩
      exact
        ⟨TMVerifierStmtWindow.consAction (TMVerifierStackAction.pop (V := V) k choice)
            (TMVerifierStmtWindow.consGuard
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice) w),
          List.mem_flatMap.mpr
            ⟨choice, tmVerifierStackReadChoices_empty_mem V k,
              List.mem_map.mpr ⟨w, hw, rfl⟩⟩⟩
  | load f q ih =>
      rcases ih (f s) with ⟨w, hw⟩
      exact ⟨TMVerifierStmtWindow.consAction (TMVerifierStackAction.load (V := V)) w,
        List.mem_map.mpr ⟨w, hw, rfl⟩⟩
  | branch f q₁ q₂ ih₁ ih₂ =>
      by_cases hBranch : f s
      · rcases ih₁ s with ⟨w, hw⟩
        exact
          ⟨TMVerifierStmtWindow.consAction
              (TMVerifierStackAction.branch (V := V) TMVerifierStmtTag.branchTrue) w,
            by
              simp [tmVerifierStmtWindowsAt, hBranch]
              exact ⟨w, hw, rfl⟩⟩
      · rcases ih₂ s with ⟨w, hw⟩
        exact
          ⟨TMVerifierStmtWindow.consAction
              (TMVerifierStackAction.branch (V := V) TMVerifierStmtTag.branchFalse) w,
            by
              simp [tmVerifierStmtWindowsAt, hBranch]
              exact ⟨w, hw, rfl⟩⟩
  | goto f =>
      exact ⟨{ guards := [], actions := [], nextLabel := some (f s), nextState := s }, by
        simp [tmVerifierStmtWindowsAt]⟩
  | halt =>
      exact ⟨{ guards := [], actions := [], nextLabel := none, nextState := s }, by
        simp [tmVerifierStmtWindowsAt]⟩

theorem tmVerifierStmtWindowsAt_exists_true_actionReadGuardsFrom
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
              a) :
    ∃ w : TMVerifierStmtWindow V,
      w ∈ tmVerifierStmtWindowsAt V t stmt s ∧
        ∀ g ∈ tmVerifierWindowActionReadGuardsFrom t w.actions idx, g.eval a = true := by
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
                    (tmVerifierMicroTime t entry.2) k) a := by
        intro w hw entry hentry j
        exact hDomains (TMVerifierStmtWindow.consAction act w)
          (List.mem_map.mpr ⟨w, hw, rfl⟩) entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
      rcases ih s (idx + 1) hTailDomains with ⟨w, hw, hguards⟩
      refine ⟨TMVerifierStmtWindow.consAction act w, List.mem_map.mpr ⟨w, hw, rfl⟩, ?_⟩
      intro g hg
      exact hguards g (by
        simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowActionReadGuardsFrom,
          TMVerifierStackAction.readGuardAt] using hg)
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
      have hdummyWindow : dummyWindow ∈
          tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.peek k f q) s := by
        exact List.mem_flatMap.mpr
          ⟨emptyChoice, tmVerifierStackReadChoices_empty_mem V k,
            List.mem_map.mpr ⟨dummyTail, hdummyTail, by simp [dummyWindow]⟩⟩
      let dummyEntry : TMVerifierStackAction V × Nat :=
        (TMVerifierStackAction.peek (V := V) k emptyChoice, idx)
      have hdummyEntry : dummyEntry ∈ dummyWindow.actions.zipIdx idx := by
        simp [dummyEntry, dummyWindow, TMVerifierStmtWindow.consAction,
          TMVerifierStmtWindow.consGuard]
      let d :=
        tmVerifierDecodedStackCellOf V p (tmVerifierMicroTime t idx) k 0 a
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
                    (tmVerifierMicroTime t entry.2) k) a := by
        intro w hw entry hentry j
        let parent : TMVerifierStmtWindow V :=
          TMVerifierStmtWindow.consAction (TMVerifierStackAction.peek (V := V) k choice)
            (TMVerifierStmtWindow.consGuard
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice) w)
        have hparent : parent ∈
            tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.peek k f q) s := by
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
                (tmVerifierMicroTime t idx) 0 choice ∨
              g ∈ tmVerifierWindowActionReadGuardsFrom t w.actions (idx + 1) := by
          simpa [selected, choice, TMVerifierStmtWindow.consAction,
            TMVerifierStmtWindow.consGuard, tmVerifierWindowActionReadGuardsFrom,
            TMVerifierStackAction.readGuardAt] using hg
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
      have hdummyWindow : dummyWindow ∈
          tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.pop k f q) s := by
        exact List.mem_flatMap.mpr
          ⟨emptyChoice, tmVerifierStackReadChoices_empty_mem V k,
            List.mem_map.mpr ⟨dummyTail, hdummyTail, by simp [dummyWindow]⟩⟩
      let dummyEntry : TMVerifierStackAction V × Nat :=
        (TMVerifierStackAction.pop (V := V) k emptyChoice, idx)
      have hdummyEntry : dummyEntry ∈ dummyWindow.actions.zipIdx idx := by
        simp [dummyEntry, dummyWindow, TMVerifierStmtWindow.consAction,
          TMVerifierStmtWindow.consGuard]
      let d :=
        tmVerifierDecodedStackCellOf V p (tmVerifierMicroTime t idx) k 0 a
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
                    (tmVerifierMicroTime t entry.2) k) a := by
        intro w hw entry hentry j
        let parent : TMVerifierStmtWindow V :=
          TMVerifierStmtWindow.consAction (TMVerifierStackAction.pop (V := V) k choice)
            (TMVerifierStmtWindow.consGuard
              (TMVerifierStackReadChoice.atomAt (V := V) (k := k) t 0 choice) w)
        have hparent : parent ∈
            tmVerifierStmtWindowsAt V t (Turing.TM2.Stmt.pop k f q) s := by
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
                (tmVerifierMicroTime t idx) 0 choice ∨
              g ∈ tmVerifierWindowActionReadGuardsFrom t w.actions (idx + 1) := by
          simpa [selected, choice, TMVerifierStmtWindow.consAction,
            TMVerifierStmtWindow.consGuard, tmVerifierWindowActionReadGuardsFrom,
            TMVerifierStackAction.readGuardAt] using hg
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
                    (tmVerifierMicroTime t entry.2) k) a := by
        intro w hw entry hentry j
        exact hDomains (TMVerifierStmtWindow.consAction act w)
          (List.mem_map.mpr ⟨w, hw, rfl⟩) entry (by
            simpa [act, TMVerifierStmtWindow.consAction] using Or.inr hentry) j
      rcases ih (f s) (idx + 1) hTailDomains with ⟨w, hw, hguards⟩
      refine ⟨TMVerifierStmtWindow.consAction act w, List.mem_map.mpr ⟨w, hw, rfl⟩, ?_⟩
      intro g hg
      exact hguards g (by
        simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowActionReadGuardsFrom,
          TMVerifierStackAction.readGuardAt] using hg)
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
                      (tmVerifierMicroTime t entry.2) k) a := by
          intro w hw entry hentry j
          have hparent : TMVerifierStmtWindow.consAction act w ∈
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
            simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowActionReadGuardsFrom,
              TMVerifierStackAction.readGuardAt] using hg)
      · let act : TMVerifierStackAction V :=
          TMVerifierStackAction.branch (V := V) TMVerifierStmtTag.branchFalse
        have hTailDomains :
            ∀ w : TMVerifierStmtWindow V, w ∈ tmVerifierStmtWindowsAt V t q₂ s →
              ∀ entry : TMVerifierStackAction V × Nat, entry ∈ w.actions.zipIdx (idx + 1) →
                ∀ k : tmVerifierStackIndex V,
                  CNF.Satisfies
                    (tmVerifierStackCellDomainsCNFAt V p
                      (tmVerifierMicroTime t entry.2) k) a := by
          intro w hw entry hentry j
          have hparent : TMVerifierStmtWindow.consAction act w ∈
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
            simpa [act, TMVerifierStmtWindow.consAction, tmVerifierWindowActionReadGuardsFrom,
              TMVerifierStackAction.readGuardAt] using hg)
  | goto f =>
      refine ⟨{ guards := [], actions := [], nextLabel := some (f s), nextState := s },
        by simp [tmVerifierStmtWindowsAt], ?_⟩
      intro g hg
      simp [tmVerifierWindowActionReadGuardsFrom] at hg
  | halt =>
      refine ⟨{ guards := [], actions := [], nextLabel := none, nextState := s },
        by simp [tmVerifierStmtWindowsAt], ?_⟩
      intro g hg
      simp [tmVerifierWindowActionReadGuardsFrom] at hg

theorem tmVerifierStmtWindowsAt_exists_true_actionReadGuards
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
              a) :
    ∃ w : TMVerifierStmtWindow V,
      w ∈ tmVerifierStmtWindowsAt V t stmt s ∧
        ∀ g ∈ tmVerifierWindowActionReadGuards t w, g.eval a = true := by
  simpa [tmVerifierWindowActionReadGuards] using
    tmVerifierStmtWindowsAt_exists_true_actionReadGuardsFrom V p t stmt s 0 a hDomains

namespace TMVerifierFixedPairTableauEvidence

theorem exists_transitionWindowReadGuards
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V) :
    ∃ w : TMVerifierStmtWindow V,
      w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s ∧
        ∀ g ∈ tmVerifierWindowActionReadGuards t w, g.eval a = true := by
  refine tmVerifierStmtWindowsAt_exists_true_actionReadGuards V p t
    ((tmVerifierTM V).m l) s a ?_
  intro w hw entry hentry k
  have hWindow :
      CNF.Satisfies (tmVerifierWindowMicroDomainCNFAt V p t w) a :=
    tmVerifierTransitionMicroDomainCNFAt_satisfies_window V p t l s w a
      (E.transitionMicroDomainRow t ht) hl hs hw
  exact tmVerifierWindowMicroDomainCNFAt_satisfies_domain_of_microTime V p t w
    entry.2 a hWindow
    (tmVerifierWindowActionMicroTimeRange_mem_microTimeRange V w
      (tmVerifierWindowActionMicroTimeRange_input_mem V w entry hentry))
    k

theorem exists_transitionWindowFiniteStepAuxMacroRow
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hLabel :
      (E.controlRow t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)).label =
        some l)
    (hState :
      (E.controlRow t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)).state = s) :
    ∃ w : TMVerifierStmtWindow V,
      w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s ∧
        (tmVerifierLabelAtom V (t + 1)
            (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
              (fun k => tmVerifierDecodedStackList V p t k a
                (E.transitionStackCellDomainsAt ht k))).l).eval a = true ∧
          (tmVerifierStateAtom V (t + 1)
            (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
              (fun k => tmVerifierDecodedStackList V p t k a
                (E.transitionStackCellDomainsAt ht k))).var).eval a = true ∧
            (fun k => tmVerifierDecodedStackList V p (t + 1) k a
              (E.stackCellDomainsAt (t + 1)
                (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V p ht) k)) =
              (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
                (fun k => tmVerifierDecodedStackList V p t k a
                  (E.transitionStackCellDomainsAt ht k))).stk := by
  rcases E.exists_transitionWindowReadGuards ht hl hs with ⟨w, hw, hGuards⟩
  exact ⟨w, hw,
    E.transitionWindowFiniteStepAuxMacroRow ht hl hs hw hLabel hState hGuards⟩

end TMVerifierFixedPairTableauEvidence

namespace TMVerifierXOnlyTableauSeed

theorem exists_transitionWindowReadGuards
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, wSeed.cert))
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V) :
    ∃ w : TMVerifierStmtWindow V,
      w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s ∧
        ∀ g ∈ tmVerifierWindowActionReadGuards t w, g.eval a = true :=
  wSeed.fixedPairEvidence.exists_transitionWindowReadGuards ht hl hs

theorem exists_transitionWindowFiniteStepAuxMacroRow
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, wSeed.cert))
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hLabel :
      (wSeed.fixedPairEvidence.controlRow t
        (tmVerifierTransitionTimeRange_mem_tableauTimeRange V (x, wSeed.cert) ht)).label =
        some l)
    (hState :
      (wSeed.fixedPairEvidence.controlRow t
        (tmVerifierTransitionTimeRange_mem_tableauTimeRange V (x, wSeed.cert) ht)).state = s) :
    ∃ w : TMVerifierStmtWindow V,
      w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s ∧
        (tmVerifierLabelAtom V (t + 1)
            (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
              (fun k => tmVerifierDecodedStackList V (x, wSeed.cert) t k a
                (wSeed.fixedPairEvidence.transitionStackCellDomainsAt ht k))).l).eval a =
            true ∧
          (tmVerifierStateAtom V (t + 1)
            (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
              (fun k => tmVerifierDecodedStackList V (x, wSeed.cert) t k a
                (wSeed.fixedPairEvidence.transitionStackCellDomainsAt ht k))).var).eval a =
            true ∧
            (fun k => tmVerifierDecodedStackList V (x, wSeed.cert) (t + 1) k a
              (wSeed.fixedPairEvidence.stackCellDomainsAt (t + 1)
                (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V (x, wSeed.cert) ht)
                k)) =
              (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
                (fun k => tmVerifierDecodedStackList V (x, wSeed.cert) t k a
                  (wSeed.fixedPairEvidence.transitionStackCellDomainsAt ht k))).stk :=
  wSeed.fixedPairEvidence.exists_transitionWindowFiniteStepAuxMacroRow ht hl hs hLabel hState

end TMVerifierXOnlyTableauSeed

end SAT
end ComplexityReduction
