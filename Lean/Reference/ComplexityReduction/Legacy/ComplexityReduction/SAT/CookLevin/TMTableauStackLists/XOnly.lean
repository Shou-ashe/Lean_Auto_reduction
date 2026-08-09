/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauStackLists.FixedPair

namespace ComplexityReduction
namespace SAT

namespace TMVerifierXOnlyTableauSeed

theorem transitionWindowFiniteReadsCurrent
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
    (entry : TMVerifierStackAction V × Nat) (hentry : entry ∈ w.actions.zipIdx) :
    tmVerifierStackActionReadsCurrent entry.1
      (fun k => tmVerifierDecodedStackList V (x, wSeed.cert)
        (tmVerifierMicroTime t entry.2) k a
        (((wSeed.windowActionDomainEvidence ht hl hs hw) entry hentry).1 k)) :=
  TMVerifierWindowStackReadsFinite.action_reads_decodedStackList
    (wSeed.transitionWindowFiniteReads ht hl hs hw hLabel hState hGuards) entry hentry

theorem transitionWindowActionsMatchDecodedStackListsFrom
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
    (hStart :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V (x, wSeed.cert) (tmVerifierMicroTime t 0) k)
          a)
    (hStartWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackWellFormedCNFAt V (x, wSeed.cert) (tmVerifierMicroTime t 0) k)
          a) :
    tmVerifierWindowActionsMatchStacks w.actions
      (fun k => tmVerifierDecodedStackList V (x, wSeed.cert) (tmVerifierMicroTime t 0) k a
        (hStart k)) :=
  wSeed.fixedPairEvidence.transitionWindowActionsMatchDecodedStackListsFrom ht hl hs hw hLabel
    hState hGuards hStart hStartWF

theorem transitionWindowFiniteStepAuxControlFromDecodedStackLists
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
    (hStart :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V (x, wSeed.cert) (tmVerifierMicroTime t 0) k)
          a)
    (hStartWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackWellFormedCNFAt V (x, wSeed.cert) (tmVerifierMicroTime t 0) k)
          a) :
    (tmVerifierLabelAtom V (t + 1)
        (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
          (fun k => tmVerifierDecodedStackList V (x, wSeed.cert) (tmVerifierMicroTime t 0)
            k a (hStart k))).l).eval a = true ∧
      (tmVerifierStateAtom V (t + 1)
        (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
          (fun k => tmVerifierDecodedStackList V (x, wSeed.cert) (tmVerifierMicroTime t 0)
            k a (hStart k))).var).eval a = true ∧
        tmVerifierWindowActionsApplyStacks w.actions
          (fun k => tmVerifierDecodedStackList V (x, wSeed.cert) (tmVerifierMicroTime t 0)
            k a (hStart k)) =
          (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
            (fun k => tmVerifierDecodedStackList V (x, wSeed.cert) (tmVerifierMicroTime t 0)
              k a (hStart k))).stk :=
  wSeed.fixedPairEvidence.transitionWindowFiniteStepAuxControlFromDecodedStackLists ht hl hs
    hw hLabel hState hGuards hStart hStartWF

theorem transitionWindowInputStackLists_eq_windowStart
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
    (hGuards : ∀ g ∈ tmVerifierWindowActionReadGuards t w, g.eval a = true) :
    (fun k => tmVerifierDecodedStackList V (x, wSeed.cert) (tmVerifierMicroTime t 0) k a
      (wSeed.windowStartDomain ht hl hs hw k)) =
      (fun k => tmVerifierDecodedStackList V (x, wSeed.cert) t k a
        (wSeed.fixedPairEvidence.transitionStackCellDomainsAt ht k)) :=
  wSeed.fixedPairEvidence.transitionWindowInputStackLists_eq_windowStart ht hl hs hw hLabel
    hState hGuards

theorem transitionWindowOutputStackLists_eq_windowFinal
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
    (hGuards : ∀ g ∈ tmVerifierWindowActionReadGuards t w, g.eval a = true) :
    (fun k => tmVerifierDecodedStackList V (x, wSeed.cert) (t + 1) k a
      (wSeed.fixedPairEvidence.stackCellDomainsAt (t + 1)
        (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V (x, wSeed.cert) ht) k)) =
      (fun k => tmVerifierDecodedStackList V (x, wSeed.cert)
        (tmVerifierMicroTime t w.actions.length) k a
        (wSeed.windowFinalDomain ht hl hs hw k)) :=
  wSeed.fixedPairEvidence.transitionWindowOutputStackLists_eq_windowFinal ht hl hs hw hLabel
    hState hGuards

theorem transitionWindowActionsApply_eq_windowFinal
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
    (hGuards : ∀ g ∈ tmVerifierWindowActionReadGuards t w, g.eval a = true) :
    tmVerifierWindowActionsApplyStacks w.actions
      (fun k => tmVerifierDecodedStackList V (x, wSeed.cert) (tmVerifierMicroTime t 0) k a
        (wSeed.windowStartDomain ht hl hs hw k)) =
      (fun k => tmVerifierDecodedStackList V (x, wSeed.cert)
        (tmVerifierMicroTime t w.actions.length) k a
        (wSeed.windowFinalDomain ht hl hs hw k)) :=
  wSeed.fixedPairEvidence.transitionWindowActionsApply_eq_windowFinal ht hl hs hw hLabel
    hState hGuards

theorem transitionWindowFiniteStepAuxMacroRow
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
    (hGuards : ∀ g ∈ tmVerifierWindowActionReadGuards t w, g.eval a = true) :
    (tmVerifierLabelAtom V (t + 1)
        (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
          (fun k => tmVerifierDecodedStackList V (x, wSeed.cert) t k a
            (wSeed.fixedPairEvidence.transitionStackCellDomainsAt ht k))).l).eval a = true ∧
      (tmVerifierStateAtom V (t + 1)
        (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
          (fun k => tmVerifierDecodedStackList V (x, wSeed.cert) t k a
            (wSeed.fixedPairEvidence.transitionStackCellDomainsAt ht k))).var).eval a = true ∧
        (fun k => tmVerifierDecodedStackList V (x, wSeed.cert) (t + 1) k a
          (wSeed.fixedPairEvidence.stackCellDomainsAt (t + 1)
            (tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange V (x, wSeed.cert) ht)
            k)) =
          (Turing.TM2.stepAux ((tmVerifierTM V).m l) s
            (fun k => tmVerifierDecodedStackList V (x, wSeed.cert) t k a
              (wSeed.fixedPairEvidence.transitionStackCellDomainsAt ht k))).stk :=
  wSeed.fixedPairEvidence.transitionWindowFiniteStepAuxMacroRow ht hl hs hw hLabel hState
    hGuards

end TMVerifierXOnlyTableauSeed

end SAT
end ComplexityReduction
