/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.GlobalMacroSteps

/-!
Decoded macro-step soundness for global fixed-micro tableaux.

`GlobalMacroSteps` supplies the fixed-micro finite action semantics.  This file
packages those finite stack effects as the actual adjacent `Turing.TM2.step`
equality between decoded macro rows.
-/

namespace ComplexityReduction
namespace SAT

theorem TMVerifierWindowFixedRowFiniteEffect.stepAux_next_control
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {p : L.Instance.Carrier × V.Cert.Carrier}
    {t : Nat} {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V} {a : Assignment}
    {hDomains : TMVerifierWindowFixedActionDomainEvidence V p t w a}
    {stk : ∀ k : tmVerifierStackIndex V, List ((tmVerifierTM V).Γ k)}
    (hEff : TMVerifierWindowFixedRowFiniteEffect V B p t l s w a hDomains)
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
  exact ⟨by simpa [hStep.1] using hEff.1,
    by simpa [hStep.2.1] using hEff.2.1,
    hStep.2.2⟩

theorem tmVerifierWindowFixedActionsApplyStacks_eq_decodedStackListsFrom
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (antecedents : List Literal) (a : Assignment)
    (actions : List (TMVerifierStackAction V)) (idx : Nat)
    (hStart :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierFixedMicroTime V p t idx) k) a)
    (hStartWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackWellFormedCNFAt V p (tmVerifierFixedMicroTime V p t idx) k) a)
    (hFinal :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p
            (tmVerifierFixedMicroTime V p t (idx + actions.length)) k) a)
    (hDomains :
      ∀ entry, entry ∈ actions.zipIdx idx →
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierStackCellDomainsCNFAt V p
              (tmVerifierFixedMicroTime V p t entry.2) k) a) ∧
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierStackCellDomainsCNFAt V p
              (tmVerifierFixedMicroTime V p t (entry.2 + 1)) k) a))
    (hWF :
      ∀ entry, entry ∈ actions.zipIdx idx →
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierStackWellFormedCNFAt V p
              (tmVerifierFixedMicroTime V p t entry.2) k) a) ∧
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierStackWellFormedCNFAt V p
              (tmVerifierFixedMicroTime V p t (entry.2 + 1)) k) a))
    (hEffects :
      ∀ entry, ∀ hentry : entry ∈ actions.zipIdx idx,
        TMVerifierStackActionFixedBoundaryEffect V B p t entry.2 antecedents a
          (hDomains entry hentry).1 (hDomains entry hentry).2 entry.1)
    (hPush :
      ∀ entry, ∀ _hentry : entry ∈ actions.zipIdx idx,
        TMVerifierStackActionPushSymbolMem (V := V) entry.1) :
    tmVerifierWindowActionsApplyStacks actions
      (fun k => tmVerifierDecodedStackList V p (tmVerifierFixedMicroTime V p t idx) k a
        (hStart k)) =
      (fun k => tmVerifierDecodedStackList V p
        (tmVerifierFixedMicroTime V p t (idx + actions.length)) k a (hFinal k)) := by
  induction actions generalizing idx hStart hStartWF with
  | nil =>
      funext k
      simp [tmVerifierWindowActionsApplyStacks,
        tmVerifierDecodedStackList_eq_of_domain_proofs V p
          (tmVerifierFixedMicroTime V p t idx) k a (hStart k) (hFinal k)]
  | cons act rest ih =>
      let entry : TMVerifierStackAction V × Nat := (act, idx)
      have hentry : entry ∈ (act :: rest).zipIdx idx := by
        simp [entry]
      let hHeadDomains := hDomains entry hentry
      let hHeadWF := hWF entry hentry
      let startStacks :=
        fun k => tmVerifierDecodedStackList V p (tmVerifierFixedMicroTime V p t idx) k a
          (hStart k)
      let headInputStacks :=
        fun k => tmVerifierDecodedStackList V p (tmVerifierFixedMicroTime V p t idx) k a
          (hHeadDomains.1 k)
      let headOutputStacks :=
        fun k => tmVerifierDecodedStackList V p (tmVerifierFixedMicroTime V p t (idx + 1)) k
          a (hHeadDomains.2 k)
      have hInputEq : headInputStacks = startStacks := by
        funext k
        exact tmVerifierDecodedStackList_eq_of_domain_proofs V p
          (tmVerifierFixedMicroTime V p t idx) k a (hHeadDomains.1 k) (hStart k)
      have hStep :
          headOutputStacks =
            tmVerifierStackActionApplyStacks act headInputStacks :=
        (hEffects entry hentry).decodedStackLists_eq_apply (hPush entry hentry)
          hHeadWF.1 hHeadWF.2
      have hApplyEq :
          tmVerifierStackActionApplyStacks act startStacks = headOutputStacks := by
        rw [← hInputEq]
        exact hStep.symm
      have hFinalTail :
          ∀ k : tmVerifierStackIndex V,
            CNF.Satisfies
              (tmVerifierStackCellDomainsCNFAt V p
                (tmVerifierFixedMicroTime V p t ((idx + 1) + rest.length)) k) a := by
        intro k
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hFinal k
      have hTail :=
        ih (idx := idx + 1) (hStart := hHeadDomains.2) (hStartWF := hHeadWF.2)
          (hFinal := hFinalTail)
          (fun tailEntry htail => hDomains tailEntry (by simp [htail]))
          (fun tailEntry htail => hWF tailEntry (by simp [htail]))
          (fun tailEntry htail => hEffects tailEntry (by simp [htail]))
          (fun tailEntry htail => hPush tailEntry (by simp [htail]))
      calc
        tmVerifierWindowActionsApplyStacks (act :: rest) startStacks =
            tmVerifierWindowActionsApplyStacks rest headOutputStacks := by
          simp [tmVerifierWindowActionsApplyStacks, hApplyEq]
        _ = (fun k => tmVerifierDecodedStackList V p
              (tmVerifierFixedMicroTime V p t ((idx + 1) + rest.length)) k a
              (hFinalTail k)) := hTail
        _ = (fun k => tmVerifierDecodedStackList V p
              (tmVerifierFixedMicroTime V p t (idx + (act :: rest).length)) k a
              (hFinal k)) := by
          have hTime : (idx + 1) + rest.length = idx + (act :: rest).length := by
            simp [Nat.add_assoc, Nat.add_comm]
          funext k
          exact tmVerifierDecodedStackList_eq_of_time_eq V p (by rw [hTime]) k a
            (hFinalTail k) (hFinal k)

theorem TMVerifierWindowFixedRowFiniteEffect.actionsApply_eq_decodedFinalFrom
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {p : L.Instance.Carrier × V.Cert.Carrier}
    {t : Nat} {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V} {a : Assignment}
    {hDomains : TMVerifierWindowFixedActionDomainEvidence V p t w a}
    (hEff : TMVerifierWindowFixedRowFiniteEffect V B p t l s w a hDomains)
    (hWF : TMVerifierWindowFixedActionWellFormedEvidence V p t w a)
    (hPush :
      ∀ entry, ∀ _hentry : entry ∈ w.actions.zipIdx,
        TMVerifierStackActionPushSymbolMem (V := V) entry.1)
    (hStart :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierFixedMicroTime V p t 0) k)
          a)
    (hStartWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackWellFormedCNFAt V p (tmVerifierFixedMicroTime V p t 0) k)
          a)
    (hFinal :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p
            (tmVerifierFixedMicroTime V p t w.actions.length) k) a) :
    tmVerifierWindowActionsApplyStacks w.actions
      (fun k => tmVerifierDecodedStackList V p (tmVerifierFixedMicroTime V p t 0) k a
        (hStart k)) =
      (fun k => tmVerifierDecodedStackList V p
        (tmVerifierFixedMicroTime V p t w.actions.length) k a (hFinal k)) :=
  have hFinal0 :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p
            (tmVerifierFixedMicroTime V p t (0 + w.actions.length)) k) a := by
    intro k
    simpa using hFinal k
  have hCore :=
    tmVerifierWindowFixedActionsApplyStacks_eq_decodedStackListsFrom V B p t
      (tmVerifierWindowFixedAntecedents V p t l s w) a w.actions 0
      hStart hStartWF hFinal0 hDomains hWF hEff.2.2 hPush
  calc
    tmVerifierWindowActionsApplyStacks w.actions
        (fun k => tmVerifierDecodedStackList V p (tmVerifierFixedMicroTime V p t 0) k a
          (hStart k)) =
        (fun k => tmVerifierDecodedStackList V p
          (tmVerifierFixedMicroTime V p t (0 + w.actions.length)) k a (hFinal0 k)) := hCore
    _ = (fun k => tmVerifierDecodedStackList V p
          (tmVerifierFixedMicroTime V p t w.actions.length) k a (hFinal k)) := by
        funext k
        exact tmVerifierDecodedStackList_eq_of_time_eq V p (by simp) k a
          (hFinal0 k) (hFinal k)

namespace TMVerifierGlobalTableauEvidence

theorem transitionWindowInputStackLists_eq_windowStart
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
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
    (hGuards : ∀ g ∈ tmVerifierWindowFixedActionReadGuards p t w, g.eval a = true) :
    (fun k => tmVerifierDecodedStackList V p (tmVerifierFixedMicroTime V p t 0) k a
      (E.windowStartDomain ht hl hs hw k)) =
      (fun k => tmVerifierDecodedStackList V p t k a
        (E.transitionStackCellDomainsAt ht k)) := by
  have hBoundary :
      CNF.Satisfies (tmVerifierWindowFixedStackBoundaryCNFAt V p t l s w) a :=
    tmVerifierTransitionFixedRowCNFAt_satisfies_window_boundary V B p t l s w a
      (E.transitionFixedRow t ht) hl hs hw
  have hAntecedents := E.windowAntecedents_true ht hLabel hState hGuards
  funext k
  exact TMVerifierDecodedFramePrefixEffect.decodedStackList_eq
    (tmVerifierWindowFixedStackBoundaryCNFAt_satisfies_input_frame V p t l s w a
      hBoundary hAntecedents k (E.transitionStackCellDomainsAt ht k)
      (E.windowStartDomain ht hl hs hw k))

theorem transitionWindowOutputStackLists_eq_windowFinal
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
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
    (hGuards : ∀ g ∈ tmVerifierWindowFixedActionReadGuards p t w, g.eval a = true) :
    (fun k => tmVerifierDecodedStackList V p (t + 1) k a
      (E.stackCellDomainsAt (t + 1)
        (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V p ht) k)) =
      (fun k => tmVerifierDecodedStackList V p
        (tmVerifierFixedMicroTime V p t w.actions.length) k a
        (E.windowFinalDomain ht hl hs hw k)) := by
  have hBoundary :
      CNF.Satisfies (tmVerifierWindowFixedStackBoundaryCNFAt V p t l s w) a :=
    tmVerifierTransitionFixedRowCNFAt_satisfies_window_boundary V B p t l s w a
      (E.transitionFixedRow t ht) hl hs hw
  have hAntecedents := E.windowAntecedents_true ht hLabel hState hGuards
  funext k
  exact TMVerifierDecodedFramePrefixEffect.decodedStackList_eq
    (tmVerifierWindowFixedStackBoundaryCNFAt_satisfies_output_frame V p t l s w a
      hBoundary hAntecedents k (E.windowFinalDomain ht hl hs hw k)
      (E.stackCellDomainsAt (t + 1)
        (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V p ht) k))

theorem transitionWindowActionsApply_eq_windowFinal
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
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
    (hGuards : ∀ g ∈ tmVerifierWindowFixedActionReadGuards p t w, g.eval a = true) :
    tmVerifierWindowActionsApplyStacks w.actions
      (fun k => tmVerifierDecodedStackList V p (tmVerifierFixedMicroTime V p t 0) k a
        (E.windowStartDomain ht hl hs hw k)) =
      (fun k => tmVerifierDecodedStackList V p (tmVerifierFixedMicroTime V p t w.actions.length)
        k a (E.windowFinalDomain ht hl hs hw k)) := by
  have hEff := E.transitionWindowFiniteRowEffect ht hl hs hw hLabel hState hGuards
  have hPush :
      ∀ entry, ∀ _hentry : entry ∈ w.actions.zipIdx,
        TMVerifierStackActionPushSymbolMem (V := V) entry.1 := by
    intro entry hentry
    exact tmVerifierStmtWindowsAt_zipIdx_action_pushSymbolMem_of_label V t l s hw entry hentry
  exact TMVerifierWindowFixedRowFiniteEffect.actionsApply_eq_decodedFinalFrom hEff
    (E.windowActionWellFormedEvidence ht hl hs hw) hPush
    (E.windowStartDomain ht hl hs hw) (E.windowStartWellFormed ht hl hs hw)
    (E.windowFinalDomain ht hl hs hw)

theorem transitionWindowFiniteStepAuxMacroRow
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
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
    (hGuards : ∀ g ∈ tmVerifierWindowFixedActionReadGuards p t w, g.eval a = true) :
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
  let macroStacks :=
    fun k => tmVerifierDecodedStackList V p t k a (E.transitionStackCellDomainsAt ht k)
  let startStacks :=
    fun k => tmVerifierDecodedStackList V p (tmVerifierFixedMicroTime V p t 0) k a
      (E.windowStartDomain ht hl hs hw k)
  let finalStacks :=
    fun k => tmVerifierDecodedStackList V p (tmVerifierFixedMicroTime V p t w.actions.length)
      k a (E.windowFinalDomain ht hl hs hw k)
  let outStacks :=
    fun k => tmVerifierDecodedStackList V p (t + 1) k a
      (E.stackCellDomainsAt (t + 1)
        (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V p ht) k)
  have hInput : startStacks = macroStacks :=
    E.transitionWindowInputStackLists_eq_windowStart ht hl hs hw hLabel hState hGuards
  have hOutput : outStacks = finalStacks :=
    E.transitionWindowOutputStackLists_eq_windowFinal ht hl hs hw hLabel hState hGuards
  have hApply : tmVerifierWindowActionsApplyStacks w.actions startStacks = finalStacks :=
    E.transitionWindowActionsApply_eq_windowFinal ht hl hs hw hLabel hState hGuards
  have hEff := E.transitionWindowFiniteRowEffect ht hl hs hw hLabel hState hGuards
  have hStep :=
    hEff.stepAux_next_control hw
      (E.transitionWindowActionsMatchDecodedStackListsFrom ht hl hs hw hLabel hState hGuards)
  refine ⟨?_, ?_, ?_⟩
  · simpa [macroStacks, startStacks, hInput] using hStep.1
  · simpa [macroStacks, startStacks, hInput] using hStep.2.1
  · calc
      outStacks = finalStacks := hOutput
      _ = tmVerifierWindowActionsApplyStacks w.actions startStacks := hApply.symm
      _ = (Turing.TM2.stepAux ((tmVerifierTM V).m l) s startStacks).stk := hStep.2.2
      _ = (Turing.TM2.stepAux ((tmVerifierTM V).m l) s macroStacks).stk := by
        simp [hInput]

theorem exists_transitionWindowFiniteStepAuxMacroRow
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
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
  exact ⟨w, hw, E.transitionWindowFiniteStepAuxMacroRow ht hl hs hw hLabel hState hGuards⟩

theorem transitionDecodedCfg_step
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ}
    (hLabel :
      (E.controlRow t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)).label =
        some l) :
    (tmVerifierTM V).step
        (E.decodedCfg t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)) =
      some
        (E.decodedCfg (t + 1)
          (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V p ht)) := by
  let ht0 := tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht
  let ht1 := tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V p ht
  let row := E.controlRow t ht0
  let l0 : (tmVerifierTM V).Λ := l
  let s0 : (tmVerifierTM V).σ := row.state
  have hs0 : s0 ∈ tmVerifierStateList V := by
    classical
    simp [tmVerifierStateList]
  have hl0 : l0 ∈ tmVerifierLabelList V := by
    classical
    simp [tmVerifierLabelList]
  have hState : row.state = s0 := rfl
  rcases E.exists_transitionWindowFiniteStepAuxMacroRow ht hl0 hs0 hLabel hState with
    ⟨w, hw, hStep⟩
  let cfg : (tmVerifierTM V).Cfg :=
    Turing.TM2.stepAux ((tmVerifierTM V).m l0) s0
      (fun k => tmVerifierDecodedStackList V p t k a
        (E.transitionStackCellDomainsAt ht k))
  have hNextLabel :
      (E.controlRow (t + 1) ht1).label = cfg.l := by
    exact tmVerifierControlDomainCNFAt_satisfies_label_eq V (t + 1) a
      (E.controlDomainRow (t + 1) ht1)
      (E.controlRow (t + 1) ht1).label_true (by simpa [cfg] using hStep.1)
  have hNextState :
      (E.controlRow (t + 1) ht1).state = cfg.var := by
    exact tmVerifierControlDomainCNFAt_satisfies_state_eq V (t + 1) a
      (E.controlDomainRow (t + 1) ht1)
      (E.controlRow (t + 1) ht1).state_true (by simpa [cfg] using hStep.2.1)
  have hStacks :
      (fun k => tmVerifierDecodedStackList V p (t + 1) k a
        (E.stackCellDomainsAt (t + 1) ht1 k)) = cfg.stk := by
    simpa [cfg] using hStep.2.2
  have hCfg : cfg = E.decodedCfg (t + 1) ht1 := by
    rcases cfg with ⟨cl, cv, cs⟩
    simp [TMVerifierGlobalTableauEvidence.decodedCfg] at hNextLabel hNextState hStacks ⊢
    rw [← hNextLabel, ← hNextState, ← hStacks]
  have hInputStacks :
      (fun k => tmVerifierDecodedStackList V p t k a (E.stackCellDomainsAt t ht0 k)) =
        (fun k => tmVerifierDecodedStackList V p t k a
          (E.transitionStackCellDomainsAt ht k)) := by
    funext k
    exact tmVerifierDecodedStackList_eq_of_domain_proofs V p t k a
      (E.stackCellDomainsAt t ht0 k) (E.transitionStackCellDomainsAt ht k)
  have hStepAuxInput :
      Turing.TM2.stepAux ((tmVerifierTM V).m l0) s0
          (fun k => tmVerifierDecodedStackList V p t k a
            (E.stackCellDomainsAt t ht0 k)) =
        cfg := by
    exact congrArg (Turing.TM2.stepAux ((tmVerifierTM V).m l0) s0) hInputStacks
  have hLeft :
      (tmVerifierTM V).step (E.decodedCfg t ht0) = some cfg := by
    have hExpand :
        (tmVerifierTM V).step (E.decodedCfg t ht0) =
          some (Turing.TM2.stepAux ((tmVerifierTM V).m l0) s0
            (fun k => tmVerifierDecodedStackList V p t k a
              (E.stackCellDomainsAt t ht0 k))) := by
      simp [TMVerifierGlobalTableauEvidence.decodedCfg, Turing.FinTM2.step, Turing.TM2.step,
        row, l0, s0, hLabel, hState]
    exact hExpand.trans (congrArg some hStepAuxInput)
  exact hLeft.trans (congrArg some hCfg)

theorem transitionDecodedCfg_stepOption
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p) :
    (tmVerifierTM V).step
        (E.decodedCfg t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)) =
      Option.bind
        (E.controlRow t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)).label
        (fun _ =>
          some
            (E.decodedCfg (t + 1)
              (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V p ht))) := by
  let ht0 := tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht
  cases hLabel : (E.controlRow t ht0).label with
  | none =>
      have hStepNone :
          (tmVerifierTM V).step (E.decodedCfg t ht0) = none := by
        change Turing.TM2.step (tmVerifierTM V).m
          { l := (E.controlRow t ht0).label
            var := (E.controlRow t ht0).state
            stk := fun k =>
              tmVerifierDecodedStackList V p t k a (E.stackCellDomainsAt t ht0 k) } = none
        rw [hLabel]
        rfl
      rw [hStepNone]
      rfl
  | some l =>
      simpa [hLabel] using E.transitionDecodedCfg_step ht hLabel

end TMVerifierGlobalTableauEvidence

namespace TMVerifierXOnlyGlobalTableauSeed

theorem transitionDecodedCfg_step
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyGlobalTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, wSeed.cert))
    {l : (tmVerifierTM V).Λ}
    (hLabel :
      (wSeed.globalEvidence.controlRow t
        (tmVerifierTransitionTimeRange_mem_tableauTimeRange V (x, wSeed.cert) ht)).label =
        some l) :
    (tmVerifierTM V).step
        (wSeed.decodedCfg t
          (tmVerifierTransitionTimeRange_mem_tableauTimeRange V (x, wSeed.cert) ht)) =
      some
        (wSeed.decodedCfg (t + 1)
          (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V (x, wSeed.cert) ht)) :=
  wSeed.globalEvidence.transitionDecodedCfg_step ht hLabel

theorem transitionDecodedCfg_stepOption
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyGlobalTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, wSeed.cert)) :
    (tmVerifierTM V).step
        (wSeed.decodedCfg t
          (tmVerifierTransitionTimeRange_mem_tableauTimeRange V (x, wSeed.cert) ht)) =
      Option.bind
        (wSeed.globalEvidence.controlRow t
          (tmVerifierTransitionTimeRange_mem_tableauTimeRange V (x, wSeed.cert) ht)).label
        (fun _ =>
          some
            (wSeed.decodedCfg (t + 1)
              (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V (x, wSeed.cert) ht))) :=
  wSeed.globalEvidence.transitionDecodedCfg_stepOption ht

end TMVerifierXOnlyGlobalTableauSeed

end SAT
end ComplexityReduction
