/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyGlobalExtraction
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.XOnlyStackListEffects

/-!
Selected-window finite action semantics for x-only global tableau rows.

This is the x-only analogue of the fixed-pair `GlobalMacroSteps` layer, up to
the point where a concrete statement window and its read guards are already
chosen.
-/

namespace ComplexityReduction
namespace SAT

/-! ### X-only finite action effects -/

noncomputable def TMVerifierXOnlyWindowFixedActionDomainEvidence
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) (a : Assignment) : Prop :=
  ∀ entry, entry ∈ w.actions.zipIdx →
    (∀ k : tmVerifierStackIndex V,
      CNF.Satisfies
        (tmVerifierXOnlyStackCellDomainsCNFAt V x
          (tmVerifierXOnlyFixedMicroTime V x t entry.2) k) a) ∧
    (∀ k : tmVerifierStackIndex V,
      CNF.Satisfies
        (tmVerifierXOnlyStackCellDomainsCNFAt V x
          (tmVerifierXOnlyFixedMicroTime V x t (entry.2 + 1)) k) a)

noncomputable def TMVerifierXOnlyWindowFixedActionWellFormedEvidence
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) (a : Assignment) : Prop :=
  ∀ entry, entry ∈ w.actions.zipIdx →
    (∀ k : tmVerifierStackIndex V,
      CNF.Satisfies
        (tmVerifierXOnlyStackWellFormedCNFAt V x
          (tmVerifierXOnlyFixedMicroTime V x t entry.2) k) a) ∧
    (∀ k : tmVerifierStackIndex V,
      CNF.Satisfies
        (tmVerifierXOnlyStackWellFormedCNFAt V x
          (tmVerifierXOnlyFixedMicroTime V x t (entry.2 + 1)) k) a)

noncomputable def TMVerifierXOnlyStackActionFixedBoundaryEffect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t actionIdx : Nat)
    (_antecedents : List Literal) (a : Assignment)
    (hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackCellDomainsCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t actionIdx) k) a)
    (hOut :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackCellDomainsCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1)) k) a) :
    TMVerifierStackAction V → Prop
  | TMVerifierStackAction.push raw =>
      (∀ _hraw : raw ∈ tmVerifierControlPushSymbols V,
        TMVerifierXOnlyDecodedPushPrefixEffect V B x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
          raw a (hIn raw.stack) (hOut raw.stack)) ∧
      (∀ j, j ∈ tmVerifierOtherStacks V raw.stack →
        TMVerifierXOnlyDecodedFramePrefixEffect V x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
          j a (hIn j) (hOut j))
  | TMVerifierStackAction.pop k _ =>
      TMVerifierXOnlyDecodedPopPrefixEffect V x
        (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
        (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
        k a (hIn k) (hOut k) ∧
      (∀ j, j ∈ tmVerifierOtherStacks V k →
        TMVerifierXOnlyDecodedFramePrefixEffect V x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
          j a (hIn j) (hOut j))
  | TMVerifierStackAction.peek _ _ =>
      ∀ k, k ∈ tmVerifierStackList V →
        TMVerifierXOnlyDecodedFramePrefixEffect V x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
          k a (hIn k) (hOut k)
  | TMVerifierStackAction.load =>
      ∀ k, k ∈ tmVerifierStackList V →
        TMVerifierXOnlyDecodedFramePrefixEffect V x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
          k a (hIn k) (hOut k)
  | TMVerifierStackAction.branch _ =>
      ∀ k, k ∈ tmVerifierStackList V →
        TMVerifierXOnlyDecodedFramePrefixEffect V x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
          k a (hIn k) (hOut k)

noncomputable def TMVerifierXOnlyStackActionFixedBoundaryRead
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (t actionIdx : Nat) (a : Assignment)
    (hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackCellDomainsCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t actionIdx) k) a) :
    TMVerifierStackAction V → Prop
  | TMVerifierStackAction.peek k choice =>
      (tmVerifierXOnlyDecodedStackCellOf V x
        (tmVerifierXOnlyFixedMicroTime V x t actionIdx) k 0 a (hIn k)
        (tmVerifierXOnlyCellRange_zero_mem V x)).choice = choice
  | TMVerifierStackAction.pop k choice =>
      (tmVerifierXOnlyDecodedStackCellOf V x
        (tmVerifierXOnlyFixedMicroTime V x t actionIdx) k 0 a (hIn k)
        (tmVerifierXOnlyCellRange_zero_mem V x)).choice = choice
  | _ => True

noncomputable def TMVerifierXOnlyWindowFixedStackEffectsFinite
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal)
    (a : Assignment)
    (hDomains : TMVerifierXOnlyWindowFixedActionDomainEvidence V x t w a) : Prop :=
  ∀ entry, ∀ hentry : entry ∈ w.actions.zipIdx,
    TMVerifierXOnlyStackActionFixedBoundaryEffect V B x t entry.2 antecedents a
      (hDomains entry hentry).1 (hDomains entry hentry).2 entry.1

noncomputable def TMVerifierXOnlyWindowFixedStackReadsFinite
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (x : L.Instance.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) (a : Assignment)
    (hDomains : TMVerifierXOnlyWindowFixedActionDomainEvidence V x t w a) : Prop :=
  ∀ entry, ∀ hentry : entry ∈ w.actions.zipIdx,
    TMVerifierXOnlyStackActionFixedBoundaryRead V x t entry.2 a
      (hDomains entry hentry).1 entry.1

noncomputable def TMVerifierXOnlyWindowFixedRowFiniteEffect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (hDomains : TMVerifierXOnlyWindowFixedActionDomainEvidence V x t w a) : Prop :=
  (tmVerifierLabelAtom V (t + 1) w.nextLabel).eval a = true ∧
  (tmVerifierStateAtom V (t + 1) w.nextState).eval a = true ∧
  TMVerifierXOnlyWindowFixedStackEffectsFinite V B x t w
    (tmVerifierXOnlyWindowFixedAntecedents V x t l s w) a hDomains

theorem tmVerifierXOnlyStackActionCNFBetween_satisfies_fixed_boundary_effect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t actionIdx : Nat)
    (antecedents : List Literal) (a : Assignment)
    (act : TMVerifierStackAction V)
    (hAction :
      CNF.Satisfies
        (tmVerifierXOnlyStackActionCNFBetween V B x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
          antecedents act) a)
    (hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackCellDomainsCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t actionIdx) k) a)
    (hOut :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackCellDomainsCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1)) k) a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierXOnlyStackActionFixedBoundaryEffect V B x t actionIdx antecedents a hIn hOut
      act := by
  cases act with
  | push raw =>
      have hEffect :=
        tmVerifierXOnlyStackActionCNFBetween_satisfies_effect_cnf V B x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
          antecedents (TMVerifierStackAction.push raw) a hAction
      constructor
      · intro hraw
        exact tmVerifierXOnlyPushActionCNFBetween_decoded_prefix_effect V B x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
          raw antecedents a
          (by simpa [tmVerifierXOnlyStackActionEffectCNFBetween] using hEffect)
          (hIn raw.stack) (hOut raw.stack) hraw hAntecedents
      · intro j hj cell hcell
        exact tmVerifierXOnlyPushActionCNFBetween_decoded_other_stack_choice_eq V B x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
          raw j cell antecedents a
          (by simpa [tmVerifierXOnlyStackActionEffectCNFBetween] using hEffect)
          (hIn j) (hOut j) hj hcell hAntecedents
  | pop k choice =>
      have hEffect :=
        tmVerifierXOnlyStackActionCNFBetween_satisfies_effect_cnf V B x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
          antecedents (TMVerifierStackAction.pop k choice) a hAction
      constructor
      · exact tmVerifierXOnlyPopActionCNFBetween_decoded_prefix_effect V x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
          k antecedents a
          (by simpa [tmVerifierXOnlyStackActionEffectCNFBetween] using hEffect)
          (hIn k) (hOut k) hAntecedents
      · intro j hj cell hcell
        exact tmVerifierXOnlyPopActionCNFBetween_decoded_other_stack_choice_eq V x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
          k j cell antecedents a
          (by simpa [tmVerifierXOnlyStackActionEffectCNFBetween] using hEffect)
          (hIn j) (hOut j) hj hcell hAntecedents
  | peek k choice =>
      have hEffect :=
        tmVerifierXOnlyStackActionCNFBetween_satisfies_effect_cnf V B x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
          antecedents (TMVerifierStackAction.peek k choice) a hAction
      intro j hj
      exact tmVerifierXOnlyPreserveAllStacksActionCNFBetween_decoded_prefix_effect V x
        (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
        (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
        j antecedents a
        (by simpa [tmVerifierXOnlyStackActionEffectCNFBetween] using hEffect)
        (hIn j) (hOut j) hj hAntecedents
  | load =>
      have hEffect :=
        tmVerifierXOnlyStackActionCNFBetween_satisfies_effect_cnf V B x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
          antecedents TMVerifierStackAction.load a hAction
      intro j hj
      exact tmVerifierXOnlyPreserveAllStacksActionCNFBetween_decoded_prefix_effect V x
        (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
        (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
        j antecedents a
        (by simpa [tmVerifierXOnlyStackActionEffectCNFBetween] using hEffect)
        (hIn j) (hOut j) hj hAntecedents
  | branch tag =>
      have hEffect :=
        tmVerifierXOnlyStackActionCNFBetween_satisfies_effect_cnf V B x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
          antecedents (TMVerifierStackAction.branch tag) a hAction
      intro j hj
      exact tmVerifierXOnlyPreserveAllStacksActionCNFBetween_decoded_prefix_effect V x
        (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
        (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
        j antecedents a
        (by simpa [tmVerifierXOnlyStackActionEffectCNFBetween] using hEffect)
        (hIn j) (hOut j) hj hAntecedents

theorem tmVerifierXOnlyStackActionCNFBetween_satisfies_fixed_boundary_read
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t actionIdx : Nat)
    (antecedents : List Literal) (a : Assignment)
    (act : TMVerifierStackAction V)
    (hAction :
      CNF.Satisfies
        (tmVerifierXOnlyStackActionCNFBetween V B x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
          antecedents act) a)
    (hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackCellDomainsCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t actionIdx) k) a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hReadMem : TMVerifierStackActionReadChoiceMem (V := V) act) :
    TMVerifierXOnlyStackActionFixedBoundaryRead V x t actionIdx a hIn act := by
  cases act with
  | push raw =>
      simp [TMVerifierXOnlyStackActionFixedBoundaryRead]
  | peek k choice =>
      have hRead := tmVerifierXOnlyStackActionCNFBetween_satisfies_read V B x
        (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
        (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
        antecedents (TMVerifierStackAction.peek k choice) a hAction hAntecedents
      exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x
        (tmVerifierXOnlyFixedMicroTime V x t actionIdx) k 0 a (hIn k)
        (tmVerifierXOnlyCellRange_zero_mem V x)
        (tmVerifierXOnlyDecodedStackCellOf V x (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          k 0 a (hIn k) (tmVerifierXOnlyCellRange_zero_mem V x)).choice
        choice
        (tmVerifierXOnlyDecodedStackCellOf V x (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          k 0 a (hIn k) (tmVerifierXOnlyCellRange_zero_mem V x)).choice_mem
        (by simpa [TMVerifierStackActionReadChoiceMem] using hReadMem)
        (tmVerifierXOnlyDecodedStackCellOf V x (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          k 0 a (hIn k) (tmVerifierXOnlyCellRange_zero_mem V x)).atom_true
        (by simpa [TMVerifierStackActionReadAtomTrue] using hRead)
  | pop k choice =>
      have hRead := tmVerifierXOnlyStackActionCNFBetween_satisfies_read V B x
        (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
        (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1))
        antecedents (TMVerifierStackAction.pop k choice) a hAction hAntecedents
      exact tmVerifierXOnlyStackCellDomainsCNFAt_satisfies_choice_eq V x
        (tmVerifierXOnlyFixedMicroTime V x t actionIdx) k 0 a (hIn k)
        (tmVerifierXOnlyCellRange_zero_mem V x)
        (tmVerifierXOnlyDecodedStackCellOf V x (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          k 0 a (hIn k) (tmVerifierXOnlyCellRange_zero_mem V x)).choice
        choice
        (tmVerifierXOnlyDecodedStackCellOf V x (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          k 0 a (hIn k) (tmVerifierXOnlyCellRange_zero_mem V x)).choice_mem
        (by simpa [TMVerifierStackActionReadChoiceMem] using hReadMem)
        (tmVerifierXOnlyDecodedStackCellOf V x (tmVerifierXOnlyFixedMicroTime V x t actionIdx)
          k 0 a (hIn k) (tmVerifierXOnlyCellRange_zero_mem V x)).atom_true
        (by simpa [TMVerifierStackActionReadAtomTrue] using hRead)
  | load =>
      simp [TMVerifierXOnlyStackActionFixedBoundaryRead]
  | branch tag =>
      simp [TMVerifierXOnlyStackActionFixedBoundaryRead]

theorem TMVerifierXOnlyStackActionFixedBoundaryRead.reads_decodedStackList
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {x : L.Instance.Carrier}
    {t actionIdx : Nat} {a : Assignment}
    {hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackCellDomainsCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t actionIdx) k) a}
    {act : TMVerifierStackAction V}
    (hRead : TMVerifierXOnlyStackActionFixedBoundaryRead V x t actionIdx a hIn act) :
    tmVerifierStackActionReadsCurrent act
      (fun k => tmVerifierXOnlyDecodedStackList V x
        (tmVerifierXOnlyFixedMicroTime V x t actionIdx) k a (hIn k)) := by
  cases act with
  | push raw =>
      simp [tmVerifierStackActionReadsCurrent]
  | peek k choice =>
      simp [TMVerifierXOnlyStackActionFixedBoundaryRead] at hRead
      simp [tmVerifierStackActionReadsCurrent, tmVerifierXOnlyDecodedStackList_head?, hRead]
  | pop k choice =>
      simp [TMVerifierXOnlyStackActionFixedBoundaryRead] at hRead
      simp [tmVerifierStackActionReadsCurrent, tmVerifierXOnlyDecodedStackList_head?, hRead]
  | load =>
      simp [tmVerifierStackActionReadsCurrent]
  | branch tag =>
      simp [tmVerifierStackActionReadsCurrent]

theorem TMVerifierXOnlyStackActionFixedBoundaryEffect.decodedStackLists_eq_apply
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {x : L.Instance.Carrier}
    {t actionIdx : Nat} {antecedents : List Literal} {a : Assignment}
    {hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackCellDomainsCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t actionIdx) k) a}
    {hOut :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackCellDomainsCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1)) k) a}
    {act : TMVerifierStackAction V}
    (hEff :
      TMVerifierXOnlyStackActionFixedBoundaryEffect V B x t actionIdx antecedents a hIn hOut
        act)
    (hPush : TMVerifierStackActionPushSymbolMem (V := V) act)
    (hInWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackWellFormedCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t actionIdx) k) a)
    (hOutWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackWellFormedCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1)) k) a) :
    (fun k => tmVerifierXOnlyDecodedStackList V x
      (tmVerifierXOnlyFixedMicroTime V x t (actionIdx + 1)) k a (hOut k)) =
      tmVerifierStackActionApplyStacks act
        (fun k => tmVerifierXOnlyDecodedStackList V x
          (tmVerifierXOnlyFixedMicroTime V x t actionIdx) k a (hIn k)) := by
  funext k
  cases act with
  | push raw =>
      have hraw : raw ∈ tmVerifierControlPushSymbols V := by
        simpa [TMVerifierStackActionPushSymbolMem] using hPush
      by_cases hk : k = raw.stack
      · subst k
        simpa [tmVerifierStackActionApplyStacks, Function.update] using
          TMVerifierXOnlyDecodedPushPrefixEffect.decodedStackList_eq_cons (hEff.1 hraw)
            (hInWF raw.stack)
      · have hFrame := hEff.2 k (tmVerifierOtherStacks_mem_of_ne V hk)
        simpa [tmVerifierStackActionApplyStacks, Function.update, hk] using
          TMVerifierXOnlyDecodedFramePrefixEffect.decodedStackList_eq hFrame
  | pop stack choice =>
      by_cases hk : k = stack
      · subst k
        simpa [tmVerifierStackActionApplyStacks, Function.update] using
          TMVerifierXOnlyDecodedPopPrefixEffect.decodedStackList_eq_tail hEff.1
            (hInWF stack) (hOutWF stack)
      · have hFrame := hEff.2 k (tmVerifierOtherStacks_mem_of_ne V hk)
        simpa [tmVerifierStackActionApplyStacks, Function.update, hk] using
          TMVerifierXOnlyDecodedFramePrefixEffect.decodedStackList_eq hFrame
  | peek stack choice =>
      have hFrame := hEff k (tmVerifierStackList_mem V k)
      simpa [tmVerifierStackActionApplyStacks] using
        TMVerifierXOnlyDecodedFramePrefixEffect.decodedStackList_eq hFrame
  | load =>
      have hFrame := hEff k (tmVerifierStackList_mem V k)
      simpa [tmVerifierStackActionApplyStacks] using
        TMVerifierXOnlyDecodedFramePrefixEffect.decodedStackList_eq hFrame
  | branch tag =>
      have hFrame := hEff k (tmVerifierStackList_mem V k)
      simpa [tmVerifierStackActionApplyStacks] using
        TMVerifierXOnlyDecodedFramePrefixEffect.decodedStackList_eq hFrame

theorem tmVerifierXOnlyWindowFixedActionsApplyStacks_eq_decodedStackListsFrom
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat)
    (antecedents : List Literal) (a : Assignment)
    (actions : List (TMVerifierStackAction V)) (idx : Nat)
    (hStart :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackCellDomainsCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t idx) k) a)
    (hStartWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackWellFormedCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t idx) k) a)
    (hFinal :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackCellDomainsCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t (idx + actions.length)) k) a)
    (hDomains :
      ∀ entry, entry ∈ actions.zipIdx idx →
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierXOnlyStackCellDomainsCNFAt V x
              (tmVerifierXOnlyFixedMicroTime V x t entry.2) k) a) ∧
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierXOnlyStackCellDomainsCNFAt V x
              (tmVerifierXOnlyFixedMicroTime V x t (entry.2 + 1)) k) a))
    (hWF :
      ∀ entry, entry ∈ actions.zipIdx idx →
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierXOnlyStackWellFormedCNFAt V x
              (tmVerifierXOnlyFixedMicroTime V x t entry.2) k) a) ∧
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierXOnlyStackWellFormedCNFAt V x
              (tmVerifierXOnlyFixedMicroTime V x t (entry.2 + 1)) k) a))
    (hEffects :
      ∀ entry, ∀ hentry : entry ∈ actions.zipIdx idx,
        TMVerifierXOnlyStackActionFixedBoundaryEffect V B x t entry.2 antecedents a
          (hDomains entry hentry).1 (hDomains entry hentry).2 entry.1)
    (hPush :
      ∀ entry, ∀ _hentry : entry ∈ actions.zipIdx idx,
        TMVerifierStackActionPushSymbolMem (V := V) entry.1) :
    tmVerifierWindowActionsApplyStacks actions
      (fun k => tmVerifierXOnlyDecodedStackList V x
        (tmVerifierXOnlyFixedMicroTime V x t idx) k a (hStart k)) =
      (fun k => tmVerifierXOnlyDecodedStackList V x
        (tmVerifierXOnlyFixedMicroTime V x t (idx + actions.length)) k a (hFinal k)) := by
  induction actions generalizing idx hStart hStartWF with
  | nil =>
      funext k
      simp [tmVerifierWindowActionsApplyStacks,
        tmVerifierXOnlyDecodedStackList_eq_of_domain_proofs V x
          (tmVerifierXOnlyFixedMicroTime V x t idx) k a (hStart k) (hFinal k)]
  | cons act rest ih =>
      let entry : TMVerifierStackAction V × Nat := (act, idx)
      have hentry : entry ∈ (act :: rest).zipIdx idx := by
        simp [entry]
      let hHeadDomains := hDomains entry hentry
      let hHeadWF := hWF entry hentry
      let startStacks :=
        fun k => tmVerifierXOnlyDecodedStackList V x
          (tmVerifierXOnlyFixedMicroTime V x t idx) k a (hStart k)
      let headInputStacks :=
        fun k => tmVerifierXOnlyDecodedStackList V x
          (tmVerifierXOnlyFixedMicroTime V x t idx) k a (hHeadDomains.1 k)
      let headOutputStacks :=
        fun k => tmVerifierXOnlyDecodedStackList V x
          (tmVerifierXOnlyFixedMicroTime V x t (idx + 1)) k a (hHeadDomains.2 k)
      have hInputEq : headInputStacks = startStacks := by
        funext k
        exact tmVerifierXOnlyDecodedStackList_eq_of_domain_proofs V x
          (tmVerifierXOnlyFixedMicroTime V x t idx) k a (hHeadDomains.1 k) (hStart k)
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
              (tmVerifierXOnlyStackCellDomainsCNFAt V x
                (tmVerifierXOnlyFixedMicroTime V x t ((idx + 1) + rest.length)) k) a := by
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
        _ = (fun k => tmVerifierXOnlyDecodedStackList V x
              (tmVerifierXOnlyFixedMicroTime V x t ((idx + 1) + rest.length)) k a
              (hFinalTail k)) := hTail
        _ = (fun k => tmVerifierXOnlyDecodedStackList V x
              (tmVerifierXOnlyFixedMicroTime V x t (idx + (act :: rest).length)) k a
              (hFinal k)) := by
          have hTime : (idx + 1) + rest.length = idx + (act :: rest).length := by
            simp [Nat.add_assoc, Nat.add_comm]
          funext k
          exact tmVerifierXOnlyDecodedStackList_eq_of_time_eq V x (by rw [hTime]) k a
            (hFinalTail k) (hFinal k)

theorem TMVerifierXOnlyWindowFixedRowFiniteEffect.actionsApply_eq_decodedFinalFrom
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {x : L.Instance.Carrier}
    {t : Nat} {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V} {a : Assignment}
    {hDomains : TMVerifierXOnlyWindowFixedActionDomainEvidence V x t w a}
    (hEff : TMVerifierXOnlyWindowFixedRowFiniteEffect V B x t l s w a hDomains)
    (hWF : TMVerifierXOnlyWindowFixedActionWellFormedEvidence V x t w a)
    (hPush :
      ∀ entry, ∀ _hentry : entry ∈ w.actions.zipIdx,
        TMVerifierStackActionPushSymbolMem (V := V) entry.1)
    (hStart :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackCellDomainsCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t 0) k) a)
    (hStartWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackWellFormedCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t 0) k) a)
    (hFinal :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackCellDomainsCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t w.actions.length) k) a) :
    tmVerifierWindowActionsApplyStacks w.actions
      (fun k => tmVerifierXOnlyDecodedStackList V x
        (tmVerifierXOnlyFixedMicroTime V x t 0) k a (hStart k)) =
      (fun k => tmVerifierXOnlyDecodedStackList V x
        (tmVerifierXOnlyFixedMicroTime V x t w.actions.length) k a (hFinal k)) :=
  have hFinal0 :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackCellDomainsCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t (0 + w.actions.length)) k) a := by
    intro k
    simpa using hFinal k
  have hCore :=
    tmVerifierXOnlyWindowFixedActionsApplyStacks_eq_decodedStackListsFrom V B x t
      (tmVerifierXOnlyWindowFixedAntecedents V x t l s w) a w.actions 0
      hStart hStartWF hFinal0 hDomains hWF hEff.2.2 hPush
  calc
    tmVerifierWindowActionsApplyStacks w.actions
        (fun k => tmVerifierXOnlyDecodedStackList V x
          (tmVerifierXOnlyFixedMicroTime V x t 0) k a (hStart k)) =
        (fun k => tmVerifierXOnlyDecodedStackList V x
          (tmVerifierXOnlyFixedMicroTime V x t (0 + w.actions.length)) k a
          (hFinal0 k)) := hCore
    _ = (fun k => tmVerifierXOnlyDecodedStackList V x
          (tmVerifierXOnlyFixedMicroTime V x t w.actions.length) k a (hFinal k)) := by
        funext k
        exact tmVerifierXOnlyDecodedStackList_eq_of_time_eq V x (by simp) k a
          (hFinal0 k) (hFinal k)

theorem tmVerifierXOnlyWindowFixedActionsMatchDecodedStackListsFrom
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (x : L.Instance.Carrier) (t : Nat)
    (antecedents : List Literal) (a : Assignment)
    (actions : List (TMVerifierStackAction V)) (idx : Nat)
    (hStart :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackCellDomainsCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t idx) k) a)
    (hStartWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackWellFormedCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t idx) k) a)
    (hDomains :
      ∀ entry, entry ∈ actions.zipIdx idx →
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierXOnlyStackCellDomainsCNFAt V x
              (tmVerifierXOnlyFixedMicroTime V x t entry.2) k) a) ∧
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierXOnlyStackCellDomainsCNFAt V x
              (tmVerifierXOnlyFixedMicroTime V x t (entry.2 + 1)) k) a))
    (hWF :
      ∀ entry, entry ∈ actions.zipIdx idx →
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierXOnlyStackWellFormedCNFAt V x
              (tmVerifierXOnlyFixedMicroTime V x t entry.2) k) a) ∧
        (∀ k : tmVerifierStackIndex V,
          CNF.Satisfies
            (tmVerifierXOnlyStackWellFormedCNFAt V x
              (tmVerifierXOnlyFixedMicroTime V x t (entry.2 + 1)) k) a))
    (hEffects :
      ∀ entry, ∀ hentry : entry ∈ actions.zipIdx idx,
        TMVerifierXOnlyStackActionFixedBoundaryEffect V B x t entry.2 antecedents a
          (hDomains entry hentry).1 (hDomains entry hentry).2 entry.1)
    (hReads :
      ∀ entry, ∀ hentry : entry ∈ actions.zipIdx idx,
        TMVerifierXOnlyStackActionFixedBoundaryRead V x t entry.2 a
          (hDomains entry hentry).1 entry.1)
    (hPush :
      ∀ entry, ∀ _hentry : entry ∈ actions.zipIdx idx,
        TMVerifierStackActionPushSymbolMem (V := V) entry.1) :
    tmVerifierWindowActionsMatchStacks actions
      (fun k => tmVerifierXOnlyDecodedStackList V x
        (tmVerifierXOnlyFixedMicroTime V x t idx) k a (hStart k)) := by
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
        fun k => tmVerifierXOnlyDecodedStackList V x
          (tmVerifierXOnlyFixedMicroTime V x t idx) k a (hStart k)
      let headInputStacks :=
        fun k => tmVerifierXOnlyDecodedStackList V x
          (tmVerifierXOnlyFixedMicroTime V x t idx) k a (hHeadDomains.1 k)
      let headOutputStacks :=
        fun k => tmVerifierXOnlyDecodedStackList V x
          (tmVerifierXOnlyFixedMicroTime V x t (idx + 1)) k a (hHeadDomains.2 k)
      have hInputEq : headInputStacks = startStacks := by
        funext k
        exact tmVerifierXOnlyDecodedStackList_eq_of_domain_proofs V x
          (tmVerifierXOnlyFixedMicroTime V x t idx) k a (hHeadDomains.1 k) (hStart k)
      have hReadHead : tmVerifierStackActionReadsCurrent act headInputStacks :=
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

theorem TMVerifierXOnlyWindowFixedRowFiniteEffect.actionsMatch_decodedStackListsFrom
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {x : L.Instance.Carrier}
    {t : Nat} {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V} {a : Assignment}
    {hDomains : TMVerifierXOnlyWindowFixedActionDomainEvidence V x t w a}
    (hEff : TMVerifierXOnlyWindowFixedRowFiniteEffect V B x t l s w a hDomains)
    (hReads : TMVerifierXOnlyWindowFixedStackReadsFinite V x t w a hDomains)
    (hWF : TMVerifierXOnlyWindowFixedActionWellFormedEvidence V x t w a)
    (hPush :
      ∀ entry, ∀ _hentry : entry ∈ w.actions.zipIdx,
        TMVerifierStackActionPushSymbolMem (V := V) entry.1)
    (hStart :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackCellDomainsCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t 0) k) a)
    (hStartWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierXOnlyStackWellFormedCNFAt V x
            (tmVerifierXOnlyFixedMicroTime V x t 0) k) a) :
    tmVerifierWindowActionsMatchStacks w.actions
      (fun k => tmVerifierXOnlyDecodedStackList V x
        (tmVerifierXOnlyFixedMicroTime V x t 0) k a (hStart k)) :=
  tmVerifierXOnlyWindowFixedActionsMatchDecodedStackListsFrom V B x t
    (tmVerifierXOnlyWindowFixedAntecedents V x t l s w) a w.actions 0 hStart hStartWF
    hDomains hWF hEff.2.2 hReads hPush

end SAT
end ComplexityReduction
