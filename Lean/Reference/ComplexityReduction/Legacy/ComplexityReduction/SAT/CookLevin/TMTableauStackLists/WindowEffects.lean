/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauStackLists.Decoded

namespace ComplexityReduction
namespace SAT

/-! ### Read alignment as concrete stack-head matching -/

theorem TMVerifierStackActionBoundaryRead.reads_decodedStackList
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {p : L.Instance.Carrier × V.Cert.Carrier}
    {t actionIdx : Nat} {a : Assignment}
    {hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t actionIdx) k) a}
    {act : TMVerifierStackAction V}
    (hRead : TMVerifierStackActionBoundaryRead V p t actionIdx a hIn act) :
    tmVerifierStackActionReadsCurrent act
      (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t actionIdx) k a
        (hIn k)) := by
  cases act with
  | push raw =>
      simp [tmVerifierStackActionReadsCurrent]
  | peek k choice =>
      simp [TMVerifierStackActionBoundaryRead] at hRead
      simp [tmVerifierStackActionReadsCurrent, tmVerifierDecodedStackList_head?, hRead]
  | pop k choice =>
      simp [TMVerifierStackActionBoundaryRead] at hRead
      simp [tmVerifierStackActionReadsCurrent, tmVerifierDecodedStackList_head?, hRead]
  | load =>
      simp [tmVerifierStackActionReadsCurrent]
  | branch tag =>
      simp [tmVerifierStackActionReadsCurrent]

theorem TMVerifierWindowStackReadsFinite.action_reads_decodedStackList
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {p : L.Instance.Carrier × V.Cert.Carrier}
    {t : Nat} {w : TMVerifierStmtWindow V} {a : Assignment}
    {hDomains : TMVerifierWindowActionDomainEvidence V p t w a}
    (hReads : TMVerifierWindowStackReadsFinite V p t w a hDomains)
    (entry : TMVerifierStackAction V × Nat) (hentry : entry ∈ w.actions.zipIdx) :
    tmVerifierStackActionReadsCurrent entry.1
      (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t entry.2) k a
        ((hDomains entry hentry).1 k)) :=
  (hReads entry hentry).reads_decodedStackList

theorem tmVerifierOtherStacks_mem_of_ne
    {L : EncodedDecisionProblem} (V : TMVerifier L)
    {j k : tmVerifierStackIndex V} (h : j ≠ k) :
    j ∈ tmVerifierOtherStacks V k := by
  classical
  simp [tmVerifierOtherStacks, h]

theorem TMVerifierStackActionBoundaryEffect.decodedStackLists_eq_apply
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {p : L.Instance.Carrier × V.Cert.Carrier}
    {t actionIdx : Nat} {antecedents : List Literal} {a : Assignment}
    {hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t actionIdx) k) a}
    {hOut :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t (actionIdx + 1)) k)
          a}
    {act : TMVerifierStackAction V}
    (hEff :
      TMVerifierStackActionBoundaryEffect V B p t actionIdx antecedents a hIn hOut act)
    (hPush : TMVerifierStackActionPushSymbolMem (V := V) act)
    (hInWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t actionIdx) k) a)
    (hOutWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t (actionIdx + 1)) k)
          a) :
    (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t (actionIdx + 1)) k a
      (hOut k)) =
      tmVerifierStackActionApplyStacks act
        (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t actionIdx) k a
          (hIn k)) := by
  funext k
  cases act with
  | push raw =>
      have hraw : raw ∈ tmVerifierControlPushSymbols V := by
        simpa [TMVerifierStackActionPushSymbolMem] using hPush
      by_cases hk : k = raw.stack
      · subst k
        simpa [tmVerifierStackActionApplyStacks, Function.update] using
          TMVerifierDecodedPushPrefixEffect.decodedStackList_eq_cons (hEff.1 hraw)
            (hInWF raw.stack)
      · have hFrame := hEff.2 k (tmVerifierOtherStacks_mem_of_ne V hk)
        simpa [tmVerifierStackActionApplyStacks, Function.update, hk] using
          TMVerifierDecodedFramePrefixEffect.decodedStackList_eq hFrame
  | pop stack choice =>
      by_cases hk : k = stack
      · subst k
        simpa [tmVerifierStackActionApplyStacks, Function.update] using
          TMVerifierDecodedPopPrefixEffect.decodedStackList_eq_tail hEff.1
            (hInWF stack) (hOutWF stack)
      · have hFrame := hEff.2 k (tmVerifierOtherStacks_mem_of_ne V hk)
        simpa [tmVerifierStackActionApplyStacks, Function.update, hk] using
          TMVerifierDecodedFramePrefixEffect.decodedStackList_eq hFrame
  | peek stack choice =>
      have hFrame := hEff k (tmVerifierStackList_mem V k)
      simpa [tmVerifierStackActionApplyStacks] using
        TMVerifierDecodedFramePrefixEffect.decodedStackList_eq hFrame
  | load =>
      have hFrame := hEff k (tmVerifierStackList_mem V k)
      simpa [tmVerifierStackActionApplyStacks] using
        TMVerifierDecodedFramePrefixEffect.decodedStackList_eq hFrame
  | branch tag =>
      have hFrame := hEff k (tmVerifierStackList_mem V k)
      simpa [tmVerifierStackActionApplyStacks] using
        TMVerifierDecodedFramePrefixEffect.decodedStackList_eq hFrame

theorem tmVerifierWindowActionsMatchDecodedStackListsFrom
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (antecedents : List Literal) (a : Assignment)
    (actions : List (TMVerifierStackAction V)) (idx : Nat)
    (hStart :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t idx) k) a)
    (hStartWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t idx) k) a)
    (hDomains :
      ∀ entry, entry ∈ actions.zipIdx idx →
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t entry.2) k)
            a) ∧
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t (entry.2 + 1)) k)
            a))
    (hWF :
      ∀ entry, entry ∈ actions.zipIdx idx →
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t entry.2) k) a) ∧
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t (entry.2 + 1)) k)
            a))
    (hEffects :
      ∀ entry, ∀ hentry : entry ∈ actions.zipIdx idx,
        TMVerifierStackActionBoundaryEffect V B p t entry.2 antecedents a
          (hDomains entry hentry).1 (hDomains entry hentry).2 entry.1)
    (hReads :
      ∀ entry, ∀ hentry : entry ∈ actions.zipIdx idx,
        TMVerifierStackActionBoundaryRead V p t entry.2 a
          (hDomains entry hentry).1 entry.1)
    (hPush :
      ∀ entry, ∀ _hentry : entry ∈ actions.zipIdx idx,
        TMVerifierStackActionPushSymbolMem (V := V) entry.1) :
    tmVerifierWindowActionsMatchStacks actions
      (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t idx) k a
        (hStart k)) := by
  induction actions generalizing idx hStart hStartWF with
  | nil =>
      simp [tmVerifierWindowActionsMatchStacks]
  | cons act rest ih =>
      let entry : TMVerifierStackAction V × Nat := (act, idx)
      have hentry : entry ∈ (act :: rest).zipIdx idx := by
        simp [entry]
      let hHeadDomains := hDomains entry hentry
      let hHeadWF := hWF entry hentry
      let startStacks :=
        fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t idx) k a
          (hStart k)
      let headInputStacks :=
        fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t idx) k a
          (hHeadDomains.1 k)
      let headOutputStacks :=
        fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t (idx + 1)) k a
          (hHeadDomains.2 k)
      have hInputEq : headInputStacks = startStacks := by
        funext k
        exact tmVerifierDecodedStackList_eq_of_domain_proofs V p (tmVerifierMicroTime t idx)
          k a (hHeadDomains.1 k) (hStart k)
      have hReadHead :
          tmVerifierStackActionReadsCurrent act headInputStacks :=
        (hReads entry hentry).reads_decodedStackList
      have hStep :
          headOutputStacks =
            tmVerifierStackActionApplyStacks act headInputStacks :=
        (hEffects entry hentry).decodedStackLists_eq_apply (hPush entry hentry)
          hHeadWF.1 hHeadWF.2
      constructor
      · simpa [startStacks, headInputStacks, hInputEq] using hReadHead
      · have hTailMatch :
            tmVerifierWindowActionsMatchStacks rest headOutputStacks := by
          refine ih (idx := idx + 1) (hStart := hHeadDomains.2)
            (hStartWF := hHeadWF.2) ?_ ?_ ?_ ?_ ?_
          · intro tailEntry htail
            exact hDomains tailEntry (by simp [htail])
          · intro tailEntry htail
            exact hWF tailEntry (by simp [htail])
          · intro tailEntry htail
            exact hEffects tailEntry (by simp [htail])
          · intro tailEntry htail
            exact hReads tailEntry (by simp [htail])
          · intro tailEntry htail
            exact hPush tailEntry (by simp [htail])
        have hApplyEq :
            tmVerifierStackActionApplyStacks act startStacks = headOutputStacks := by
          rw [← hInputEq]
          exact hStep.symm
        simpa [tmVerifierWindowActionsMatchStacks, tmVerifierWindowActionsApplyStacks,
          startStacks, hApplyEq] using hTailMatch

theorem TMVerifierWindowStackEffectsFinite.actionsMatch_decodedStackListsFrom
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {p : L.Instance.Carrier × V.Cert.Carrier}
    {t : Nat} {w : TMVerifierStmtWindow V} {antecedents : List Literal}
    {a : Assignment}
    {hDomains : TMVerifierWindowActionDomainEvidence V p t w a}
    (hEffects : TMVerifierWindowStackEffectsFinite V B p t w antecedents a hDomains)
    (hReads : TMVerifierWindowStackReadsFinite V p t w a hDomains)
    (hWF : TMVerifierWindowActionWellFormedEvidence V p t w a)
    (hPush :
      ∀ entry, ∀ _hentry : entry ∈ w.actions.zipIdx,
        TMVerifierStackActionPushSymbolMem (V := V) entry.1)
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
        (hStart k)) :=
  tmVerifierWindowActionsMatchDecodedStackListsFrom V B p t antecedents a w.actions 0
    hStart hStartWF hDomains hWF hEffects hReads hPush

theorem tmVerifierWindowActionsApplyStacks_eq_decodedStackListsFrom
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (antecedents : List Literal) (a : Assignment)
    (actions : List (TMVerifierStackAction V)) (idx : Nat)
    (hStart :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t idx) k) a)
    (hStartWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t idx) k) a)
    (hFinal :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p
            (tmVerifierMicroTime t (idx + actions.length)) k) a)
    (hDomains :
      ∀ entry, entry ∈ actions.zipIdx idx →
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t entry.2) k)
            a) ∧
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t (entry.2 + 1)) k)
            a))
    (hWF :
      ∀ entry, entry ∈ actions.zipIdx idx →
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t entry.2) k) a) ∧
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t (entry.2 + 1)) k)
            a))
    (hEffects :
      ∀ entry, ∀ hentry : entry ∈ actions.zipIdx idx,
        TMVerifierStackActionBoundaryEffect V B p t entry.2 antecedents a
          (hDomains entry hentry).1 (hDomains entry hentry).2 entry.1)
    (hPush :
      ∀ entry, ∀ _hentry : entry ∈ actions.zipIdx idx,
        TMVerifierStackActionPushSymbolMem (V := V) entry.1) :
    tmVerifierWindowActionsApplyStacks actions
      (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t idx) k a
        (hStart k)) =
      (fun k => tmVerifierDecodedStackList V p
        (tmVerifierMicroTime t (idx + actions.length)) k a (hFinal k)) := by
  induction actions generalizing idx hStart hStartWF with
  | nil =>
      funext k
      simp [tmVerifierWindowActionsApplyStacks,
        tmVerifierDecodedStackList_eq_of_domain_proofs V p (tmVerifierMicroTime t idx) k a
          (hStart k) (hFinal k)]
  | cons act rest ih =>
      let entry : TMVerifierStackAction V × Nat := (act, idx)
      have hentry : entry ∈ (act :: rest).zipIdx idx := by
        simp [entry]
      let hHeadDomains := hDomains entry hentry
      let hHeadWF := hWF entry hentry
      let startStacks :=
        fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t idx) k a
          (hStart k)
      let headInputStacks :=
        fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t idx) k a
          (hHeadDomains.1 k)
      let headOutputStacks :=
        fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t (idx + 1)) k a
          (hHeadDomains.2 k)
      have hInputEq : headInputStacks = startStacks := by
        funext k
        exact tmVerifierDecodedStackList_eq_of_domain_proofs V p (tmVerifierMicroTime t idx)
          k a (hHeadDomains.1 k) (hStart k)
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
                (tmVerifierMicroTime t ((idx + 1) + rest.length)) k) a := by
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
              (tmVerifierMicroTime t ((idx + 1) + rest.length)) k a
              (hFinalTail k)) := hTail
        _ = (fun k => tmVerifierDecodedStackList V p
              (tmVerifierMicroTime t (idx + (act :: rest).length)) k a (hFinal k)) := by
          have hTime : (idx + 1) + rest.length = idx + (act :: rest).length := by
            simp [Nat.add_assoc, Nat.add_comm]
          funext k
          exact tmVerifierDecodedStackList_eq_of_time_eq V p
            (by rw [hTime]) k a (hFinalTail k) (hFinal k)

theorem TMVerifierWindowStackEffectsFinite.actionsApply_eq_decodedFinalFrom
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {p : L.Instance.Carrier × V.Cert.Carrier}
    {t : Nat} {w : TMVerifierStmtWindow V} {antecedents : List Literal}
    {a : Assignment}
    {hDomains : TMVerifierWindowActionDomainEvidence V p t w a}
    (hEffects : TMVerifierWindowStackEffectsFinite V B p t w antecedents a hDomains)
    (hWF : TMVerifierWindowActionWellFormedEvidence V p t w a)
    (hPush :
      ∀ entry, ∀ _hentry : entry ∈ w.actions.zipIdx,
        TMVerifierStackActionPushSymbolMem (V := V) entry.1)
    (hStart :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t 0) k)
          a)
    (hStartWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t 0) k)
          a)
    (hFinal :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t w.actions.length) k)
          a) :
    tmVerifierWindowActionsApplyStacks w.actions
      (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t 0) k a
        (hStart k)) =
      (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t w.actions.length) k a
        (hFinal k)) :=
  have hFinal0 :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t (0 + w.actions.length)) k)
          a := by
    intro k
    simpa using hFinal k
  have hCore :=
    tmVerifierWindowActionsApplyStacks_eq_decodedStackListsFrom V B p t antecedents a
      w.actions 0 hStart hStartWF hFinal0 hDomains hWF hEffects hPush
  calc
    tmVerifierWindowActionsApplyStacks w.actions
        (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t 0) k a
          (hStart k)) =
        (fun k => tmVerifierDecodedStackList V p
          (tmVerifierMicroTime t (0 + w.actions.length)) k a (hFinal0 k)) := hCore
    _ = (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t w.actions.length) k a
          (hFinal k)) := by
        funext k
        exact tmVerifierDecodedStackList_eq_of_time_eq V p (by simp) k a
          (hFinal0 k) (hFinal k)

theorem TMVerifierWindowRowFiniteEffect.actionsMatch_decodedStackListsFrom
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {p : L.Instance.Carrier × V.Cert.Carrier}
    {t : Nat} {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V} {a : Assignment}
    {hDomains : TMVerifierWindowActionDomainEvidence V p t w a}
    (hEff : TMVerifierWindowRowFiniteEffect V B p t l s w a hDomains)
    (hReads : TMVerifierWindowStackReadsFinite V p t w a hDomains)
    (hWF : TMVerifierWindowActionWellFormedEvidence V p t w a)
    (hPush :
      ∀ entry, ∀ _hentry : entry ∈ w.actions.zipIdx,
        TMVerifierStackActionPushSymbolMem (V := V) entry.1)
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
        (hStart k)) :=
  TMVerifierWindowStackEffectsFinite.actionsMatch_decodedStackListsFrom hEff.2.2
    hReads hWF hPush hStart hStartWF

theorem TMVerifierWindowRowFiniteEffect.actionsApply_eq_decodedFinalFrom
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {p : L.Instance.Carrier × V.Cert.Carrier}
    {t : Nat} {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V} {a : Assignment}
    {hDomains : TMVerifierWindowActionDomainEvidence V p t w a}
    (hEff : TMVerifierWindowRowFiniteEffect V B p t l s w a hDomains)
    (hWF : TMVerifierWindowActionWellFormedEvidence V p t w a)
    (hPush :
      ∀ entry, ∀ _hentry : entry ∈ w.actions.zipIdx,
        TMVerifierStackActionPushSymbolMem (V := V) entry.1)
    (hStart :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t 0) k)
          a)
    (hStartWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t 0) k)
          a)
    (hFinal :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t w.actions.length) k)
          a) :
    tmVerifierWindowActionsApplyStacks w.actions
      (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t 0) k a
        (hStart k)) =
      (fun k => tmVerifierDecodedStackList V p (tmVerifierMicroTime t w.actions.length) k a
        (hFinal k)) :=
  TMVerifierWindowStackEffectsFinite.actionsApply_eq_decodedFinalFrom hEff.2.2
    hWF hPush hStart hStartWF hFinal

end SAT
end ComplexityReduction
