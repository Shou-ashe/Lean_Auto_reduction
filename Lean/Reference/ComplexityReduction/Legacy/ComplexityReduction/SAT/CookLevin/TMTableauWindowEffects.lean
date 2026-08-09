/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauControlUniqueness

/-!
Selected-window antecedents from decoded tableau evidence.

This file connects decoded control rows to the aggregate transition-row effect
surface.  It still leaves micro-time stack-domain coverage explicit; the point
here is to stop re-proving the control antecedents for every later operational
alignment lemma.
-/

namespace ComplexityReduction
namespace SAT

theorem tmVerifierTransitionTimeRange_mem_tableauTimeRange
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) {t : Nat}
    (ht : t ∈ tmVerifierTransitionTimeRange V p) :
    t ∈ tmVerifierTableauTimeRange V p := by
  simp [tmVerifierTransitionTimeRange, tmVerifierTableauTimeRange] at ht ⊢
  exact Nat.le_of_lt ht

theorem tmVerifierTransitionTimeRange_succ_mem_tableauTimeRange
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    (p : L.Instance.Carrier × V.Cert.Carrier) {t : Nat}
    (ht : t ∈ tmVerifierTransitionTimeRange V p) :
    t + 1 ∈ tmVerifierTableauTimeRange V p := by
  simp [tmVerifierTransitionTimeRange, tmVerifierTableauTimeRange] at ht ⊢
  exact ht

namespace TMVerifierFixedPairTableauEvidence

theorem windowAntecedents_true {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hLabel :
      (E.controlRow t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)).label =
        some l)
    (hState :
      (E.controlRow t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)).state = s)
    (hGuards : ∀ g ∈ tmVerifierWindowActionReadGuards t w, g.eval a = true) :
    ∀ g ∈ tmVerifierWindowAntecedents V t l s w, g.eval a = true := by
  intro g hg
  have hLabelTrue :
      (tmVerifierLabelAtom V t (some l)).eval a = true := by
    simpa [hLabel] using
      (E.controlRow t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)).label_true
  have hStateTrue :
      (tmVerifierStateAtom V t s).eval a = true := by
    simpa [hState] using
      (E.controlRow t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)).state_true
  have hg' :
      g = tmVerifierLabelAtom V t (some l) ∨
        g = tmVerifierStateAtom V t s ∨ g ∈ tmVerifierWindowActionReadGuards t w := by
    simpa [tmVerifierWindowAntecedents] using hg
  rcases hg' with rfl | hRest
  · exact hLabelTrue
  · rcases hRest with rfl | hGuard
    · exact hStateTrue
    · exact hGuards g hGuard

theorem transitionWindowRowEffect {L : EncodedDecisionProblem} {V : TMVerifier L}
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
    (hDomains :
      ∀ micro (k : tmVerifierStackIndex V),
        CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t micro) k) a) :
    TMVerifierWindowRowEffect V B p t l s w a hDomains :=
  tmVerifierTransitionRowCNFAt_satisfies_window_effect V B p t l s w a
    (E.transitionRow t ht) hl hs hw hDomains
    (E.windowAntecedents_true ht hLabel hState hGuards)

end TMVerifierFixedPairTableauEvidence

namespace TMVerifierXOnlyTableauSeed

theorem transitionWindowRowEffect {L : EncodedDecisionProblem} {V : TMVerifier L}
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
    (hDomains :
      ∀ micro (k : tmVerifierStackIndex V),
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V (x, wSeed.cert) (tmVerifierMicroTime t micro) k)
          a) :
    TMVerifierWindowRowEffect V B (x, wSeed.cert) t l s w a hDomains :=
  wSeed.fixedPairEvidence.transitionWindowRowEffect ht hl hs hw hLabel hState hGuards hDomains

end TMVerifierXOnlyTableauSeed

end SAT
end ComplexityReduction
