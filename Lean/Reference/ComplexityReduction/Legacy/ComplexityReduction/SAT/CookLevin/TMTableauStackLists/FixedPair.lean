/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauStackLists.WindowEffects

namespace ComplexityReduction
namespace SAT

namespace TMVerifierFixedPairTableauEvidence

theorem transitionWindowFiniteReadsCurrent
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
    (entry : TMVerifierStackAction V × Nat) (hentry : entry ∈ w.actions.zipIdx) :
    tmVerifierStackActionReadsCurrent entry.1
      (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t entry.2) k a
        (((E.windowActionDomainEvidence ht hl hs hw) entry hentry).1 k)) :=
  TMVerifierWindowStackReadsFinite.action_reads_decodedStackList
    (E.transitionWindowFiniteReads ht hl hs hw hLabel hState hGuards) entry hentry

theorem transitionWindowActionsMatchDecodedStackListsFrom
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
    (hStart :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t 0) k)
          a)
    (hStartWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t 0) k)
          a) :
    tmVerifierWindowActionsMatchStacks w.actions
      (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t 0) k a
        (hStart k)) := by
  have hEff := E.transitionWindowFiniteRowEffect ht hl hs hw hLabel hState hGuards
  exact TMVerifierWindowRowFiniteEffect.actionsMatch_decodedStackListsFrom hEff
      (E.transitionWindowFiniteReads ht hl hs hw hLabel hState hGuards)
      (E.windowActionWellFormedEvidence ht hl hs hw)
      (fun entry hentry =>
        tmVerifierStmtWindowsAt_zipIdx_action_pushSymbolMem_of_label V t l s hw entry hentry)
      hStart hStartWF

theorem transitionWindowFiniteStepAuxControlFromDecodedStackLists
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
    (hStart :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t 0) k)
          a)
    (hStartWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t 0) k)
          a) :
    (tmVerifierLabelAtom V (t + 1)
        (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
          (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t 0) k a
            (hStart k))).l).eval a = true ∧
      (tmVerifierStateAtom V (t + 1)
        (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
          (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t 0) k a
            (hStart k))).var).eval a = true ∧
        tmVerifierWindowActionsApplyStacks w.actions
          (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t 0) k a
            (hStart k)) =
          (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
            (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t 0) k a
              (hStart k))).stk :=
  E.transitionWindowFiniteStepAuxControl ht hl hs hw hLabel hState hGuards
    (E.transitionWindowActionsMatchDecodedStackListsFrom ht hl hs hw hLabel hState hGuards
      hStart hStartWF)

theorem transitionWindowInputStackLists_eq_windowStart
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
    (hGuards : ∀ g ∈ tmVerifierWindowActionReadGuards t w, g.eval a = true) :
    (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t 0) k a
      (E.windowStartDomain ht hl hs hw k)) =
      (fun k => tmVerifierDecodedStackList V p t k a
        (E.transitionStackCellDomainsAt ht k)) := by
  have hBoundary :
      CNF.Satisfies (tmVerifierWindowStackBoundaryCNFAt V p t l s w) a :=
    tmVerifierTransitionRowCNFAt_satisfies_window_boundary V B p t l s w a
      (E.transitionRow t ht) hl hs hw
  have hAntecedents := E.windowAntecedents_true ht hLabel hState hGuards
  funext k
  exact TMVerifierDecodedFramePrefixEffect.decodedStackList_eq
    (tmVerifierWindowStackBoundaryCNFAt_satisfies_input_frame V p t l s w a
      hBoundary hAntecedents k (E.transitionStackCellDomainsAt ht k)
      (E.windowStartDomain ht hl hs hw k))

theorem transitionWindowOutputStackLists_eq_windowFinal
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
    (hGuards : ∀ g ∈ tmVerifierWindowActionReadGuards t w, g.eval a = true) :
    (fun k => tmVerifierDecodedStackList V p (t + 1) k a
      (E.stackCellDomainsAt (t + 1)
        (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V p ht) k)) =
      (fun k => tmVerifierDecodedStackList V p
        (tmVerifierMicroTime t w.actions.length) k a
        (E.windowFinalDomain ht hl hs hw k)) := by
  have hBoundary :
      CNF.Satisfies (tmVerifierWindowStackBoundaryCNFAt V p t l s w) a :=
    tmVerifierTransitionRowCNFAt_satisfies_window_boundary V B p t l s w a
      (E.transitionRow t ht) hl hs hw
  have hAntecedents := E.windowAntecedents_true ht hLabel hState hGuards
  funext k
  exact TMVerifierDecodedFramePrefixEffect.decodedStackList_eq
    (tmVerifierWindowStackBoundaryCNFAt_satisfies_output_frame V p t l s w a
      hBoundary hAntecedents k (E.windowFinalDomain ht hl hs hw k)
      (E.stackCellDomainsAt (t + 1)
        (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V p ht) k))

theorem transitionWindowActionsApply_eq_windowFinal
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
    (hGuards : ∀ g ∈ tmVerifierWindowActionReadGuards t w, g.eval a = true) :
    tmVerifierWindowActionsApplyStacks w.actions
      (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t 0) k a
        (E.windowStartDomain ht hl hs hw k)) =
      (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t w.actions.length) k a
        (E.windowFinalDomain ht hl hs hw k)) := by
  have hEff := E.transitionWindowFiniteRowEffect ht hl hs hw hLabel hState hGuards
  exact TMVerifierWindowRowFiniteEffect.actionsApply_eq_decodedFinalFrom hEff
    (E.windowActionWellFormedEvidence ht hl hs hw)
    (fun entry hentry =>
      tmVerifierStmtWindowsAt_zipIdx_action_pushSymbolMem_of_label V t l s hw entry hentry)
    (E.windowStartDomain ht hl hs hw)
    (E.windowStartWellFormed ht hl hs hw)
    (E.windowFinalDomain ht hl hs hw)

theorem transitionWindowFiniteStepAuxMacroRow
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
    (hGuards : ∀ g ∈ tmVerifierWindowActionReadGuards t w, g.eval a = true) :
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
    fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t 0) k a
      (E.windowStartDomain ht hl hs hw k)
  let finalStacks :=
    fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t w.actions.length) k a
      (E.windowFinalDomain ht hl hs hw k)
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
  have hStep :=
    E.transitionWindowFiniteStepAuxControlFromDecodedStackLists ht hl hs hw hLabel hState hGuards
      (E.windowStartDomain ht hl hs hw) (E.windowStartWellFormed ht hl hs hw)
  refine ⟨?_, ?_, ?_⟩
  · simpa [macroStacks, startStacks, hInput] using hStep.1
  · simpa [macroStacks, startStacks, hInput] using hStep.2.1
  · calc
      outStacks = finalStacks := hOutput
      _ = tmVerifierWindowActionsApplyStacks w.actions startStacks := hApply.symm
      _ = (Turing.TM2.stepAux ((tmVerifierTM V).m l) s startStacks).stk := hStep.2.2
      _ = (Turing.TM2.stepAux ((tmVerifierTM V).m l) s macroStacks).stk := by
        simp [hInput]

end TMVerifierFixedPairTableauEvidence

end SAT
end ComplexityReduction
