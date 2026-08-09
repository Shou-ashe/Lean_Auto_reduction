/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.GlobalExtraction
import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauCompleteness.GlobalWindowSelection

/-!
Macro-step soundness for satisfied global fixed-micro tableau rows.

This is the fixed-micro analogue of `TMTableauMacroSteps`: a satisfied global
transition row with a nonhalting decoded label forces the decoded macro
configuration at `t` to take one real `Turing.TM2.step` to the decoded macro
configuration at `t + 1`.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Fixed-micro finite action effects -/

noncomputable def TMVerifierWindowFixedActionDomainEvidence
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) (a : Assignment) : Prop :=
  ∀ entry, entry ∈ w.actions.zipIdx →
    (∀ k : tmVerifierStackIndex V,
      CNF.Satisfies
        (tmVerifierStackCellDomainsCNFAt V p
          (tmVerifierFixedMicroTime V p t entry.2) k) a) ∧
    (∀ k : tmVerifierStackIndex V,
      CNF.Satisfies
        (tmVerifierStackCellDomainsCNFAt V p
          (tmVerifierFixedMicroTime V p t (entry.2 + 1)) k) a)

noncomputable def TMVerifierWindowFixedActionWellFormedEvidence
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) (a : Assignment) : Prop :=
  ∀ entry, entry ∈ w.actions.zipIdx →
    (∀ k : tmVerifierStackIndex V,
      CNF.Satisfies
        (tmVerifierStackWellFormedCNFAt V p
          (tmVerifierFixedMicroTime V p t entry.2) k) a) ∧
    (∀ k : tmVerifierStackIndex V,
      CNF.Satisfies
        (tmVerifierStackWellFormedCNFAt V p
          (tmVerifierFixedMicroTime V p t (entry.2 + 1)) k) a)

noncomputable def TMVerifierStackActionFixedBoundaryEffect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t actionIdx : Nat)
    (_antecedents : List Literal) (a : Assignment)
    (hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p
            (tmVerifierFixedMicroTime V p t actionIdx) k) a)
    (hOut :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p
            (tmVerifierFixedMicroTime V p t (actionIdx + 1)) k) a) :
    TMVerifierStackAction V → Prop
  | TMVerifierStackAction.push raw =>
      (∀ _hraw : raw ∈ tmVerifierControlPushSymbols V,
        TMVerifierDecodedPushPrefixEffect V B p
          (tmVerifierFixedMicroTime V p t actionIdx)
          (tmVerifierFixedMicroTime V p t (actionIdx + 1))
          raw a (hIn raw.stack) (hOut raw.stack)) ∧
      (∀ j, j ∈ tmVerifierOtherStacks V raw.stack →
        TMVerifierDecodedFramePrefixEffect V p
          (tmVerifierFixedMicroTime V p t actionIdx)
          (tmVerifierFixedMicroTime V p t (actionIdx + 1))
          j a (hIn j) (hOut j))
  | TMVerifierStackAction.pop k _ =>
      TMVerifierDecodedPopPrefixEffect V p
        (tmVerifierFixedMicroTime V p t actionIdx)
        (tmVerifierFixedMicroTime V p t (actionIdx + 1))
        k a (hIn k) (hOut k) ∧
      (∀ j, j ∈ tmVerifierOtherStacks V k →
        TMVerifierDecodedFramePrefixEffect V p
          (tmVerifierFixedMicroTime V p t actionIdx)
          (tmVerifierFixedMicroTime V p t (actionIdx + 1))
          j a (hIn j) (hOut j))
  | TMVerifierStackAction.peek _ _ =>
      ∀ k, k ∈ tmVerifierStackList V →
        TMVerifierDecodedFramePrefixEffect V p
          (tmVerifierFixedMicroTime V p t actionIdx)
          (tmVerifierFixedMicroTime V p t (actionIdx + 1))
          k a (hIn k) (hOut k)
  | TMVerifierStackAction.load =>
      ∀ k, k ∈ tmVerifierStackList V →
        TMVerifierDecodedFramePrefixEffect V p
          (tmVerifierFixedMicroTime V p t actionIdx)
          (tmVerifierFixedMicroTime V p t (actionIdx + 1))
          k a (hIn k) (hOut k)
  | TMVerifierStackAction.branch _ =>
      ∀ k, k ∈ tmVerifierStackList V →
        TMVerifierDecodedFramePrefixEffect V p
          (tmVerifierFixedMicroTime V p t actionIdx)
          (tmVerifierFixedMicroTime V p t (actionIdx + 1))
          k a (hIn k) (hOut k)

noncomputable def TMVerifierStackActionFixedBoundaryRead
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t actionIdx : Nat) (a : Assignment)
    (hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p
            (tmVerifierFixedMicroTime V p t actionIdx) k) a) :
    TMVerifierStackAction V → Prop
  | TMVerifierStackAction.peek k choice =>
      (tmVerifierDecodedStackCellOf V p (tmVerifierFixedMicroTime V p t actionIdx) k 0
        a (hIn k) (tmVerifierCellRange_zero_mem V p)).choice = choice
  | TMVerifierStackAction.pop k choice =>
      (tmVerifierDecodedStackCellOf V p (tmVerifierFixedMicroTime V p t actionIdx) k 0
        a (hIn k) (tmVerifierCellRange_zero_mem V p)).choice = choice
  | _ => True

noncomputable def TMVerifierWindowFixedStackEffectsFinite
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal)
    (a : Assignment)
    (hDomains : TMVerifierWindowFixedActionDomainEvidence V p t w a) : Prop :=
  ∀ entry, ∀ hentry : entry ∈ w.actions.zipIdx,
    TMVerifierStackActionFixedBoundaryEffect V B p t entry.2 antecedents a
      (hDomains entry hentry).1 (hDomains entry hentry).2 entry.1

noncomputable def TMVerifierWindowFixedStackReadsFinite
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) (a : Assignment)
    (hDomains : TMVerifierWindowFixedActionDomainEvidence V p t w a) : Prop :=
  ∀ entry, ∀ hentry : entry ∈ w.actions.zipIdx,
    TMVerifierStackActionFixedBoundaryRead V p t entry.2 a
      (hDomains entry hentry).1 entry.1

noncomputable def TMVerifierWindowFixedRowFiniteEffect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (hDomains : TMVerifierWindowFixedActionDomainEvidence V p t w a) : Prop :=
  (tmVerifierLabelAtom V (t + 1) w.nextLabel).eval a = true ∧
  (tmVerifierStateAtom V (t + 1) w.nextState).eval a = true ∧
  TMVerifierWindowFixedStackEffectsFinite V B p t w
    (tmVerifierWindowFixedAntecedents V p t l s w) a hDomains

theorem tmVerifierStackActionCNFBetween_satisfies_fixed_boundary_effect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t actionIdx : Nat)
    (antecedents : List Literal) (a : Assignment)
    (act : TMVerifierStackAction V)
    (hAction :
      CNF.Satisfies
        (tmVerifierStackActionCNFBetween V B p
          (tmVerifierFixedMicroTime V p t actionIdx)
          (tmVerifierFixedMicroTime V p t (actionIdx + 1))
          antecedents act) a)
    (hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p
            (tmVerifierFixedMicroTime V p t actionIdx) k) a)
    (hOut :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p
            (tmVerifierFixedMicroTime V p t (actionIdx + 1)) k) a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierStackActionFixedBoundaryEffect V B p t actionIdx antecedents a hIn hOut act := by
  cases act with
  | push raw =>
      have hEffect :=
        tmVerifierStackActionCNFBetween_satisfies_effect_cnf V B p
          (tmVerifierFixedMicroTime V p t actionIdx)
          (tmVerifierFixedMicroTime V p t (actionIdx + 1))
          antecedents (TMVerifierStackAction.push raw) a hAction
      constructor
      · intro hraw
        exact tmVerifierPushActionCNFBetween_decoded_prefix_effect V B p
          (tmVerifierFixedMicroTime V p t actionIdx)
          (tmVerifierFixedMicroTime V p t (actionIdx + 1))
          raw antecedents a
          (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
          (hIn raw.stack) (hOut raw.stack) hraw hAntecedents
      · intro j hj cell hcell
        exact tmVerifierPushActionCNFBetween_decoded_other_stack_choice_eq V B p
          (tmVerifierFixedMicroTime V p t actionIdx)
          (tmVerifierFixedMicroTime V p t (actionIdx + 1))
          raw j cell antecedents a
          (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
          (hIn j) (hOut j) hj hcell hAntecedents
  | pop k choice =>
      have hEffect :=
        tmVerifierStackActionCNFBetween_satisfies_effect_cnf V B p
          (tmVerifierFixedMicroTime V p t actionIdx)
          (tmVerifierFixedMicroTime V p t (actionIdx + 1))
          antecedents (TMVerifierStackAction.pop k choice) a hAction
      constructor
      · exact tmVerifierPopActionCNFBetween_decoded_prefix_effect V p
          (tmVerifierFixedMicroTime V p t actionIdx)
          (tmVerifierFixedMicroTime V p t (actionIdx + 1))
          k antecedents a
          (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
          (hIn k) (hOut k) hAntecedents
      · intro j hj cell hcell
        exact tmVerifierPopActionCNFBetween_decoded_other_stack_choice_eq V p
          (tmVerifierFixedMicroTime V p t actionIdx)
          (tmVerifierFixedMicroTime V p t (actionIdx + 1))
          k j cell antecedents a
          (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
          (hIn j) (hOut j) hj hcell hAntecedents
  | peek k choice =>
      have hEffect :=
        tmVerifierStackActionCNFBetween_satisfies_effect_cnf V B p
          (tmVerifierFixedMicroTime V p t actionIdx)
          (tmVerifierFixedMicroTime V p t (actionIdx + 1))
          antecedents (TMVerifierStackAction.peek k choice) a hAction
      intro j hj
      exact tmVerifierPreserveAllStacksActionCNFBetween_decoded_prefix_effect V p
        (tmVerifierFixedMicroTime V p t actionIdx)
        (tmVerifierFixedMicroTime V p t (actionIdx + 1))
        j antecedents a
        (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
        (hIn j) (hOut j) hj hAntecedents
  | load =>
      have hEffect :=
        tmVerifierStackActionCNFBetween_satisfies_effect_cnf V B p
          (tmVerifierFixedMicroTime V p t actionIdx)
          (tmVerifierFixedMicroTime V p t (actionIdx + 1))
          antecedents TMVerifierStackAction.load a hAction
      intro j hj
      exact tmVerifierPreserveAllStacksActionCNFBetween_decoded_prefix_effect V p
        (tmVerifierFixedMicroTime V p t actionIdx)
        (tmVerifierFixedMicroTime V p t (actionIdx + 1))
        j antecedents a
        (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
        (hIn j) (hOut j) hj hAntecedents
  | branch tag =>
      have hEffect :=
        tmVerifierStackActionCNFBetween_satisfies_effect_cnf V B p
          (tmVerifierFixedMicroTime V p t actionIdx)
          (tmVerifierFixedMicroTime V p t (actionIdx + 1))
          antecedents (TMVerifierStackAction.branch tag) a hAction
      intro j hj
      exact tmVerifierPreserveAllStacksActionCNFBetween_decoded_prefix_effect V p
        (tmVerifierFixedMicroTime V p t actionIdx)
        (tmVerifierFixedMicroTime V p t (actionIdx + 1))
        j antecedents a
        (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
        (hIn j) (hOut j) hj hAntecedents

theorem tmVerifierStackActionCNFBetween_satisfies_fixed_boundary_read
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t actionIdx : Nat)
    (antecedents : List Literal) (a : Assignment)
    (act : TMVerifierStackAction V)
    (hAction :
      CNF.Satisfies
        (tmVerifierStackActionCNFBetween V B p
          (tmVerifierFixedMicroTime V p t actionIdx)
          (tmVerifierFixedMicroTime V p t (actionIdx + 1))
          antecedents act) a)
    (hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p
            (tmVerifierFixedMicroTime V p t actionIdx) k) a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hReadMem : TMVerifierStackActionReadChoiceMem (V := V) act) :
    TMVerifierStackActionFixedBoundaryRead V p t actionIdx a hIn act := by
  cases act with
  | push raw =>
      simp [TMVerifierStackActionFixedBoundaryRead]
  | peek k choice =>
      have hRead := tmVerifierStackActionCNFBetween_satisfies_read V B p
        (tmVerifierFixedMicroTime V p t actionIdx)
        (tmVerifierFixedMicroTime V p t (actionIdx + 1))
        antecedents (TMVerifierStackAction.peek k choice) a hAction hAntecedents
      exact tmVerifierStackCellDomainsCNFAt_satisfies_choice_eq V p
        (tmVerifierFixedMicroTime V p t actionIdx) k 0 a (hIn k)
        (tmVerifierCellRange_zero_mem V p)
        (tmVerifierDecodedStackCellOf V p (tmVerifierFixedMicroTime V p t actionIdx) k 0
          a (hIn k) (tmVerifierCellRange_zero_mem V p)).choice
        choice
        (tmVerifierDecodedStackCellOf V p (tmVerifierFixedMicroTime V p t actionIdx) k 0
          a (hIn k) (tmVerifierCellRange_zero_mem V p)).choice_mem
        (by simpa [TMVerifierStackActionReadChoiceMem] using hReadMem)
        (tmVerifierDecodedStackCellOf V p (tmVerifierFixedMicroTime V p t actionIdx) k 0
          a (hIn k) (tmVerifierCellRange_zero_mem V p)).atom_true
        (by simpa [TMVerifierStackActionReadAtomTrue] using hRead)
  | pop k choice =>
      have hRead := tmVerifierStackActionCNFBetween_satisfies_read V B p
        (tmVerifierFixedMicroTime V p t actionIdx)
        (tmVerifierFixedMicroTime V p t (actionIdx + 1))
        antecedents (TMVerifierStackAction.pop k choice) a hAction hAntecedents
      exact tmVerifierStackCellDomainsCNFAt_satisfies_choice_eq V p
        (tmVerifierFixedMicroTime V p t actionIdx) k 0 a (hIn k)
        (tmVerifierCellRange_zero_mem V p)
        (tmVerifierDecodedStackCellOf V p (tmVerifierFixedMicroTime V p t actionIdx) k 0
          a (hIn k) (tmVerifierCellRange_zero_mem V p)).choice
        choice
        (tmVerifierDecodedStackCellOf V p (tmVerifierFixedMicroTime V p t actionIdx) k 0
          a (hIn k) (tmVerifierCellRange_zero_mem V p)).choice_mem
        (by simpa [TMVerifierStackActionReadChoiceMem] using hReadMem)
        (tmVerifierDecodedStackCellOf V p (tmVerifierFixedMicroTime V p t actionIdx) k 0
          a (hIn k) (tmVerifierCellRange_zero_mem V p)).atom_true
        (by simpa [TMVerifierStackActionReadAtomTrue] using hRead)
  | load =>
      simp [TMVerifierStackActionFixedBoundaryRead]
  | branch tag =>
      simp [TMVerifierStackActionFixedBoundaryRead]

theorem TMVerifierStackActionFixedBoundaryRead.reads_decodedStackList
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {p : L.Instance.Carrier × V.Cert.Carrier}
    {t actionIdx : Nat} {a : Assignment}
    {hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p
            (tmVerifierFixedMicroTime V p t actionIdx) k) a}
    {act : TMVerifierStackAction V}
    (hRead : TMVerifierStackActionFixedBoundaryRead V p t actionIdx a hIn act) :
    tmVerifierStackActionReadsCurrent act
      (fun k => tmVerifierDecodedStackList V p (tmVerifierFixedMicroTime V p t actionIdx) k
        a (hIn k)) := by
  cases act with
  | push raw =>
      simp [tmVerifierStackActionReadsCurrent]
  | peek k choice =>
      simp [TMVerifierStackActionFixedBoundaryRead] at hRead
      simp [tmVerifierStackActionReadsCurrent, tmVerifierDecodedStackList_head?, hRead]
  | pop k choice =>
      simp [TMVerifierStackActionFixedBoundaryRead] at hRead
      simp [tmVerifierStackActionReadsCurrent, tmVerifierDecodedStackList_head?, hRead]
  | load =>
      simp [tmVerifierStackActionReadsCurrent]
  | branch tag =>
      simp [tmVerifierStackActionReadsCurrent]

theorem TMVerifierStackActionFixedBoundaryEffect.decodedStackLists_eq_apply
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {p : L.Instance.Carrier × V.Cert.Carrier}
    {t actionIdx : Nat} {antecedents : List Literal} {a : Assignment}
    {hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p
            (tmVerifierFixedMicroTime V p t actionIdx) k) a}
    {hOut :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p
            (tmVerifierFixedMicroTime V p t (actionIdx + 1)) k) a}
    {act : TMVerifierStackAction V}
    (hEff :
      TMVerifierStackActionFixedBoundaryEffect V B p t actionIdx antecedents a hIn hOut act)
    (hPush : TMVerifierStackActionPushSymbolMem (V := V) act)
    (hInWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackWellFormedCNFAt V p
            (tmVerifierFixedMicroTime V p t actionIdx) k) a)
    (hOutWF :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackWellFormedCNFAt V p
            (tmVerifierFixedMicroTime V p t (actionIdx + 1)) k) a) :
    (fun k => tmVerifierDecodedStackList V p
      (tmVerifierFixedMicroTime V p t (actionIdx + 1)) k a (hOut k)) =
      tmVerifierStackActionApplyStacks act
        (fun k => tmVerifierDecodedStackList V p
          (tmVerifierFixedMicroTime V p t actionIdx) k a (hIn k)) := by
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

theorem tmVerifierWindowFixedActionsMatchDecodedStackListsFrom
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
    (hReads :
      ∀ entry, ∀ hentry : entry ∈ actions.zipIdx idx,
        TMVerifierStackActionFixedBoundaryRead V p t entry.2 a
          (hDomains entry hentry).1 entry.1)
    (hPush :
      ∀ entry, ∀ _hentry : entry ∈ actions.zipIdx idx,
        TMVerifierStackActionPushSymbolMem (V := V) entry.1) :
    tmVerifierWindowActionsMatchStacks actions
      (fun k => tmVerifierDecodedStackList V p (tmVerifierFixedMicroTime V p t idx) k a
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

theorem TMVerifierWindowFixedRowFiniteEffect.actionsMatch_decodedStackListsFrom
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {B : TMVerifierPushPayloadBoundary V}
    {p : L.Instance.Carrier × V.Cert.Carrier}
    {t : Nat} {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V} {a : Assignment}
    {hDomains : TMVerifierWindowFixedActionDomainEvidence V p t w a}
    (hEff : TMVerifierWindowFixedRowFiniteEffect V B p t l s w a hDomains)
    (hReads : TMVerifierWindowFixedStackReadsFinite V p t w a hDomains)
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
          a) :
    tmVerifierWindowActionsMatchStacks w.actions
      (fun k => tmVerifierDecodedStackList V p (tmVerifierFixedMicroTime V p t 0) k a
        (hStart k)) :=
  tmVerifierWindowFixedActionsMatchDecodedStackListsFrom V B p t
    (tmVerifierWindowFixedAntecedents V p t l s w) a w.actions 0 hStart hStartWF
    hDomains hWF hEff.2.2 hReads hPush

/-! ### Fixed-micro tableau evidence helpers -/

namespace TMVerifierGlobalTableauEvidence

theorem windowActionDomainEvidence
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    TMVerifierWindowFixedActionDomainEvidence V p t w a := by
  intro entry hentry
  have hWindow :
      CNF.Satisfies (tmVerifierWindowFixedMicroDomainCNFAt V p t w) a :=
    tmVerifierTransitionFixedMicroDomainCNFAt_satisfies_window V p t l s w a
      (E.transitionFixedMicroDomainRow t ht) hl hs hw
  constructor
  · intro k
    exact tmVerifierWindowFixedMicroDomainCNFAt_satisfies_domain V p t w entry.2 a
      hWindow (tmVerifierWindowActionMicroTimeRange_input_mem V w entry hentry) k
  · intro k
    exact tmVerifierWindowFixedMicroDomainCNFAt_satisfies_domain V p t w (entry.2 + 1) a
      hWindow (tmVerifierWindowActionMicroTimeRange_output_mem V w entry hentry) k

theorem windowActionWellFormedEvidence
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    TMVerifierWindowFixedActionWellFormedEvidence V p t w a := by
  intro entry hentry
  have hWindow :
      CNF.Satisfies (tmVerifierWindowFixedMicroDomainCNFAt V p t w) a :=
    tmVerifierTransitionFixedMicroDomainCNFAt_satisfies_window V p t l s w a
      (E.transitionFixedMicroDomainRow t ht) hl hs hw
  constructor
  · intro k
    exact tmVerifierWindowFixedMicroDomainCNFAt_satisfies_wellFormed_of_microTime V p t w
      entry.2 a hWindow
      (tmVerifierWindowActionMicroTimeRange_mem_microTimeRange V w
        (tmVerifierWindowActionMicroTimeRange_input_mem V w entry hentry)) k
  · intro k
    exact tmVerifierWindowFixedMicroDomainCNFAt_satisfies_wellFormed_of_microTime V p t w
      (entry.2 + 1) a hWindow
      (tmVerifierWindowActionMicroTimeRange_mem_microTimeRange V w
        (tmVerifierWindowActionMicroTimeRange_output_mem V w entry hentry)) k

theorem windowStartDomain
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierStackCellDomainsCNFAt V p (tmVerifierFixedMicroTime V p t 0) k) a := by
  have hWindow :
      CNF.Satisfies (tmVerifierWindowFixedMicroDomainCNFAt V p t w) a :=
    tmVerifierTransitionFixedMicroDomainCNFAt_satisfies_window V p t l s w a
      (E.transitionFixedMicroDomainRow t ht) hl hs hw
  exact tmVerifierWindowFixedMicroDomainCNFAt_satisfies_domain_of_microTime V p t w 0 a
    hWindow (tmVerifierWindowMicroTimeRange_zero_mem V w) k

theorem windowStartWellFormed
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierStackWellFormedCNFAt V p (tmVerifierFixedMicroTime V p t 0) k) a := by
  have hWindow :
      CNF.Satisfies (tmVerifierWindowFixedMicroDomainCNFAt V p t w) a :=
    tmVerifierTransitionFixedMicroDomainCNFAt_satisfies_window V p t l s w a
      (E.transitionFixedMicroDomainRow t ht) hl hs hw
  exact tmVerifierWindowFixedMicroDomainCNFAt_satisfies_wellFormed_of_microTime V p t w 0 a
    hWindow (tmVerifierWindowMicroTimeRange_zero_mem V w) k

theorem windowFinalDomain
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierStackCellDomainsCNFAt V p
        (tmVerifierFixedMicroTime V p t w.actions.length) k) a := by
  have hWindow :
      CNF.Satisfies (tmVerifierWindowFixedMicroDomainCNFAt V p t w) a :=
    tmVerifierTransitionFixedMicroDomainCNFAt_satisfies_window V p t l s w a
      (E.transitionFixedMicroDomainRow t ht) hl hs hw
  exact tmVerifierWindowFixedMicroDomainCNFAt_satisfies_domain_of_microTime V p t w
    w.actions.length a hWindow (tmVerifierWindowMicroTimeRange_final_mem V w) k

theorem windowAntecedents_true
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hLabel :
      (E.controlRow t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)).label =
        some l)
    (hState :
      (E.controlRow t (tmVerifierTransitionTimeRange_mem_tableauTimeRange V p ht)).state = s)
    (hGuards : ∀ g ∈ tmVerifierWindowFixedActionReadGuards p t w, g.eval a = true) :
    ∀ g ∈ tmVerifierWindowFixedAntecedents V p t l s w, g.eval a = true := by
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
        g = tmVerifierStateAtom V t s ∨
          g ∈ tmVerifierWindowFixedActionReadGuards p t w := by
    simpa [tmVerifierWindowFixedAntecedents] using hg
  rcases hg' with rfl | hRest
  · exact hLabelTrue
  · rcases hRest with rfl | hGuard
    · exact hStateTrue
    · exact hGuards g hGuard

theorem transitionWindowFiniteRowEffect
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
    TMVerifierWindowFixedRowFiniteEffect V B p t l s w a
      (E.windowActionDomainEvidence ht hl hs hw) := by
  let antecedents := tmVerifierWindowFixedAntecedents V p t l s w
  have hRow := E.transitionFixedRow t ht
  have hControl :
      CNF.Satisfies (tmVerifierWindowFixedControlCNFAt V p t l s w) a := by
    have hsplit := (CNF.satisfies_append
      (tmVerifierTransitionFixedControlCNFAt V p t)
      (tmVerifierTransitionFixedWindowStackCNFAt V B p t ++
        tmVerifierHaltedRowsCNFAt V p t) a).1
        (by simpa [tmVerifierTransitionFixedRowCNFAt] using hRow)
    intro c hc
    exact hsplit.1 c (by
      rw [tmVerifierTransitionFixedControlCNFAt]
      exact List.mem_flatMap.mpr
        ⟨l, hl, List.mem_flatMap.mpr ⟨s, hs, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩⟩)
  have hNextControl :
      (tmVerifierLabelAtom V (t + 1) w.nextLabel).eval a = true ∧
        (tmVerifierStateAtom V (t + 1) w.nextState).eval a = true := by
    have hAntecedents := E.windowAntecedents_true ht hLabel hState hGuards
    let antecedents := tmVerifierWindowFixedAntecedents V p t l s w
    have hLabelCNF :
        CNF.Satisfies
          [tmVerifierImplicationClause antecedents
            (tmVerifierLabelAtom V (t + 1) w.nextLabel)] a := by
      intro c hc
      have hc' :
          c = tmVerifierImplicationClause antecedents
            (tmVerifierLabelAtom V (t + 1) w.nextLabel) := by
        simpa using hc
      subst c
      exact hControl _ (by simp [tmVerifierWindowFixedControlCNFAt, antecedents])
    have hStateCNF :
        CNF.Satisfies
          [tmVerifierImplicationClause antecedents
            (tmVerifierStateAtom V (t + 1) w.nextState)] a := by
      intro c hc
      have hc' :
          c = tmVerifierImplicationClause antecedents
            (tmVerifierStateAtom V (t + 1) w.nextState) := by
        simpa using hc
      subst c
      exact hControl _ (by simp [tmVerifierWindowFixedControlCNFAt, antecedents])
    constructor
    · exact tmVerifierImplicationClause_satisfies_of_antecedents antecedents
        (tmVerifierLabelAtom V (t + 1) w.nextLabel) a hLabelCNF (by
          simpa [antecedents] using hAntecedents)
    · exact tmVerifierImplicationClause_satisfies_of_antecedents antecedents
        (tmVerifierStateAtom V (t + 1) w.nextState) a hStateCNF (by
          simpa [antecedents] using hAntecedents)
  have hStack :
      CNF.Satisfies
        (tmVerifierWindowFixedStackActionCNFAt V B p t w
          (tmVerifierWindowFixedAntecedents V p t l s w)) a := by
    have hsplit := (CNF.satisfies_append
      (tmVerifierTransitionFixedControlCNFAt V p t)
      (tmVerifierTransitionFixedWindowStackCNFAt V B p t ++
        tmVerifierHaltedRowsCNFAt V p t) a).1
        (by simpa [tmVerifierTransitionFixedRowCNFAt] using hRow)
    have hstack := (CNF.satisfies_append
      (tmVerifierTransitionFixedWindowStackCNFAt V B p t)
      (tmVerifierHaltedRowsCNFAt V p t) a).1 hsplit.2 |>.1
    exact tmVerifierTransitionFixedWindowStackCNFAt_satisfies_window V B p t l s w a
      hstack hl hs hw
  refine ⟨hNextControl.1, hNextControl.2, ?_⟩
  intro entry hentry
  have hAction :
      CNF.Satisfies
        (tmVerifierStackActionCNFBetween V B p
          (tmVerifierFixedMicroTime V p t entry.2)
          (tmVerifierFixedMicroTime V p t (entry.2 + 1))
          (tmVerifierWindowFixedAntecedents V p t l s w) entry.1) a :=
    tmVerifierWindowFixedStackActionCNFAt_satisfies_action V B p t w
      (tmVerifierWindowFixedAntecedents V p t l s w) a hStack entry hentry
  exact tmVerifierStackActionCNFBetween_satisfies_fixed_boundary_effect V B p t entry.2
    (tmVerifierWindowFixedAntecedents V p t l s w) a entry.1 hAction
    ((E.windowActionDomainEvidence ht hl hs hw) entry hentry).1
    ((E.windowActionDomainEvidence ht hl hs hw) entry hentry).2
    (E.windowAntecedents_true ht hLabel hState hGuards)

theorem transitionWindowFiniteReads
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
    TMVerifierWindowFixedStackReadsFinite V p t w a
      (E.windowActionDomainEvidence ht hl hs hw) := by
  let antecedents := tmVerifierWindowFixedAntecedents V p t l s w
  have hRow := E.transitionFixedRow t ht
  have hStack :
      CNF.Satisfies
        (tmVerifierWindowFixedStackActionCNFAt V B p t w
          (tmVerifierWindowFixedAntecedents V p t l s w)) a := by
    have hsplit := (CNF.satisfies_append
      (tmVerifierTransitionFixedControlCNFAt V p t)
      (tmVerifierTransitionFixedWindowStackCNFAt V B p t ++
        tmVerifierHaltedRowsCNFAt V p t) a).1
        (by simpa [tmVerifierTransitionFixedRowCNFAt] using hRow)
    have hstack := (CNF.satisfies_append
      (tmVerifierTransitionFixedWindowStackCNFAt V B p t)
      (tmVerifierHaltedRowsCNFAt V p t) a).1 hsplit.2 |>.1
    exact tmVerifierTransitionFixedWindowStackCNFAt_satisfies_window V B p t l s w a
      hstack hl hs hw
  intro entry hentry
  have hAction :
      CNF.Satisfies
        (tmVerifierStackActionCNFBetween V B p
          (tmVerifierFixedMicroTime V p t entry.2)
          (tmVerifierFixedMicroTime V p t (entry.2 + 1))
          (tmVerifierWindowFixedAntecedents V p t l s w) entry.1) a :=
    tmVerifierWindowFixedStackActionCNFAt_satisfies_action V B p t w
      (tmVerifierWindowFixedAntecedents V p t l s w) a hStack entry hentry
  exact tmVerifierStackActionCNFBetween_satisfies_fixed_boundary_read V B p t entry.2
    (tmVerifierWindowFixedAntecedents V p t l s w) a entry.1 hAction
    ((E.windowActionDomainEvidence ht hl hs hw) entry hentry).1
    (E.windowAntecedents_true ht hLabel hState hGuards)
    (tmVerifierStmtWindowsAt_zipIdx_action_readChoiceMem V t ((tmVerifierTM V).m l) s hw
      entry hentry)

theorem exists_transitionWindowReadGuards
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierGlobalTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V) :
    ∃ w : TMVerifierStmtWindow V,
      w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s ∧
        ∀ g ∈ tmVerifierWindowFixedActionReadGuards p t w, g.eval a = true := by
  refine tmVerifierStmtWindowsAt_exists_true_fixedActionReadGuards V p t
    ((tmVerifierTM V).m l) s a ?_
  intro w hw entry hentry k
  exact ((E.windowActionDomainEvidence ht hl hs hw) entry hentry).1 k

/-! ### Fixed-micro decoded stack-list propagation -/

theorem transitionWindowActionsMatchDecodedStackListsFrom
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
    tmVerifierWindowActionsMatchStacks w.actions
      (fun k => tmVerifierDecodedStackList V p (tmVerifierFixedMicroTime V p t 0) k a
        (E.windowStartDomain ht hl hs hw k)) := by
  have hEff := E.transitionWindowFiniteRowEffect ht hl hs hw hLabel hState hGuards
  have hPush :
      ∀ entry, ∀ _hentry : entry ∈ w.actions.zipIdx,
        TMVerifierStackActionPushSymbolMem (V := V) entry.1 := by
    intro entry hentry
    exact tmVerifierStmtWindowsAt_zipIdx_action_pushSymbolMem_of_label V t l s hw entry hentry
  exact TMVerifierWindowFixedRowFiniteEffect.actionsMatch_decodedStackListsFrom hEff
    (E.transitionWindowFiniteReads ht hl hs hw hLabel hState hGuards)
    (E.windowActionWellFormedEvidence ht hl hs hw) hPush
    (E.windowStartDomain ht hl hs hw) (E.windowStartWellFormed ht hl hs hw)

end TMVerifierGlobalTableauEvidence

end SAT
end ComplexityReduction
