/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ComplexityReduction.Legacy.ComplexityReduction.SAT.CookLevin.TMTableauWindowEffects

/-!
Finite micro-time stack-domain coverage for selected transition windows.

`TMTransitionRowSemantics` keeps a convenient row-effect boundary whose domain
hypothesis ranges over every natural micro index.  A finite CNF tableau can only
provide the action input/output micro rows it actually emits.  This file exposes
that finite boundary and proves that the aggregate tableau now supplies it for a
selected window.
-/

namespace ComplexityReduction
namespace SAT

/-! ### Finite-domain primitive action effects -/

noncomputable def TMVerifierStackActionBoundaryEffect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t actionIdx : Nat)
    (_antecedents : List Literal) (a : Assignment)
    (hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t actionIdx) k) a)
    (hOut :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t (actionIdx + 1)) k)
          a) :
    TMVerifierStackAction V → Prop
  | TMVerifierStackAction.push raw =>
      (∀ _hraw : raw ∈ tmVerifierControlPushSymbols V,
        TMVerifierDecodedPushPrefixEffect V B p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          raw a (hIn raw.stack) (hOut raw.stack)) ∧
      (∀ j, j ∈ tmVerifierOtherStacks V raw.stack →
        TMVerifierDecodedFramePrefixEffect V p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          j a (hIn j) (hOut j))
  | TMVerifierStackAction.pop k _ =>
      TMVerifierDecodedPopPrefixEffect V p
        (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
        k a (hIn k) (hOut k) ∧
      (∀ j, j ∈ tmVerifierOtherStacks V k →
        TMVerifierDecodedFramePrefixEffect V p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          j a (hIn j) (hOut j))
  | TMVerifierStackAction.peek _ _ =>
      ∀ k, k ∈ tmVerifierStackList V →
        TMVerifierDecodedFramePrefixEffect V p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          k a (hIn k) (hOut k)
  | TMVerifierStackAction.load =>
      ∀ k, k ∈ tmVerifierStackList V →
        TMVerifierDecodedFramePrefixEffect V p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          k a (hIn k) (hOut k)
  | TMVerifierStackAction.branch _ =>
      ∀ k, k ∈ tmVerifierStackList V →
        TMVerifierDecodedFramePrefixEffect V p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          k a (hIn k) (hOut k)

theorem tmVerifierStackActionEffectCNFBetween_satisfies_boundary_effect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t actionIdx : Nat)
    (antecedents : List Literal) (a : Assignment)
    (act : TMVerifierStackAction V)
    (hEffect :
      CNF.Satisfies
        (tmVerifierStackActionEffectCNFBetween V B p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          antecedents act) a)
    (hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t actionIdx) k) a)
    (hOut :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t (actionIdx + 1)) k)
          a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierStackActionBoundaryEffect V B p t actionIdx antecedents a hIn hOut act := by
  cases act with
  | push raw =>
      constructor
      · intro hraw
        exact tmVerifierPushActionCNFBetween_decoded_prefix_effect V B p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          raw antecedents a (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
          (hIn raw.stack) (hOut raw.stack) hraw hAntecedents
      · intro j hj cell hcell
        exact tmVerifierPushActionCNFBetween_decoded_other_stack_choice_eq V B p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          raw j cell antecedents a (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
          (hIn j) (hOut j) hj hcell hAntecedents
  | pop k choice =>
      constructor
      · exact tmVerifierPopActionCNFBetween_decoded_prefix_effect V p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          k antecedents a (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
          (hIn k) (hOut k) hAntecedents
      · intro j hj cell hcell
        exact tmVerifierPopActionCNFBetween_decoded_other_stack_choice_eq V p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          k j cell antecedents a (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
          (hIn j) (hOut j) hj hcell hAntecedents
  | peek k choice =>
      intro j hj
      exact tmVerifierPreserveAllStacksActionCNFBetween_decoded_prefix_effect V p
        (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
        j antecedents a (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
        (hIn j) (hOut j) hj hAntecedents
  | load =>
      intro j hj
      exact tmVerifierPreserveAllStacksActionCNFBetween_decoded_prefix_effect V p
        (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
        j antecedents a (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
        (hIn j) (hOut j) hj hAntecedents
  | branch tag =>
      intro j hj
      exact tmVerifierPreserveAllStacksActionCNFBetween_decoded_prefix_effect V p
        (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
        j antecedents a (by simpa [tmVerifierStackActionEffectCNFBetween] using hEffect)
        (hIn j) (hOut j) hj hAntecedents

theorem tmVerifierStackActionCNFBetween_satisfies_boundary_effect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t actionIdx : Nat)
    (antecedents : List Literal) (a : Assignment)
    (act : TMVerifierStackAction V)
    (hAction :
      CNF.Satisfies
        (tmVerifierStackActionCNFBetween V B p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          antecedents act) a)
    (hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t actionIdx) k) a)
    (hOut :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t (actionIdx + 1)) k)
          a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierStackActionBoundaryEffect V B p t actionIdx antecedents a hIn hOut act :=
  tmVerifierStackActionEffectCNFBetween_satisfies_boundary_effect V B p t actionIdx
    antecedents a act
    (tmVerifierStackActionCNFBetween_satisfies_effect_cnf V B p
      (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
      antecedents act a hAction)
    hIn hOut hAntecedents

/-! ### Finite-domain action read alignment -/

noncomputable def TMVerifierStackActionBoundaryRead
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t actionIdx : Nat) (a : Assignment)
    (hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t actionIdx) k) a) :
    TMVerifierStackAction V → Prop
  | TMVerifierStackAction.peek k choice =>
      (tmVerifierDecodedStackCellOf V p (tmVerifierMicroTime t actionIdx) k 0 a (hIn k)
          (tmVerifierCellRange_zero_mem V p)).choice = choice
  | TMVerifierStackAction.pop k choice =>
      (tmVerifierDecodedStackCellOf V p (tmVerifierMicroTime t actionIdx) k 0 a (hIn k)
          (tmVerifierCellRange_zero_mem V p)).choice = choice
  | _ => True

theorem tmVerifierStackActionCNFBetween_satisfies_boundary_read
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t actionIdx : Nat)
    (antecedents : List Literal) (a : Assignment)
    (act : TMVerifierStackAction V)
    (hAction :
      CNF.Satisfies
        (tmVerifierStackActionCNFBetween V B p
          (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
          antecedents act) a)
    (hIn :
      ∀ k : tmVerifierStackIndex V,
        CNF.Satisfies
          (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t actionIdx) k) a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hReadMem : TMVerifierStackActionReadChoiceMem (V := V) act) :
    TMVerifierStackActionBoundaryRead V p t actionIdx a hIn act := by
  cases act with
  | push raw =>
      simp [TMVerifierStackActionBoundaryRead]
  | peek k choice =>
      have hRead := tmVerifierStackActionCNFBetween_satisfies_read V B p
        (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
        antecedents (TMVerifierStackAction.peek k choice) a hAction hAntecedents
      exact tmVerifierStackCellDomainsCNFAt_satisfies_choice_eq V p
        (tmVerifierMicroTime t actionIdx) k 0 a (hIn k)
        (tmVerifierCellRange_zero_mem V p)
        (tmVerifierDecodedStackCellOf V p (tmVerifierMicroTime t actionIdx) k 0 a (hIn k)
          (tmVerifierCellRange_zero_mem V p)).choice
        choice
        (tmVerifierDecodedStackCellOf V p (tmVerifierMicroTime t actionIdx) k 0 a (hIn k)
          (tmVerifierCellRange_zero_mem V p)).choice_mem
        (by simpa [TMVerifierStackActionReadChoiceMem] using hReadMem)
        (tmVerifierDecodedStackCellOf V p (tmVerifierMicroTime t actionIdx) k 0 a (hIn k)
          (tmVerifierCellRange_zero_mem V p)).atom_true
        (by simpa [TMVerifierStackActionReadAtomTrue] using hRead)
  | pop k choice =>
      have hRead := tmVerifierStackActionCNFBetween_satisfies_read V B p
        (tmVerifierMicroTime t actionIdx) (tmVerifierMicroTime t (actionIdx + 1))
        antecedents (TMVerifierStackAction.pop k choice) a hAction hAntecedents
      exact tmVerifierStackCellDomainsCNFAt_satisfies_choice_eq V p
        (tmVerifierMicroTime t actionIdx) k 0 a (hIn k)
        (tmVerifierCellRange_zero_mem V p)
        (tmVerifierDecodedStackCellOf V p (tmVerifierMicroTime t actionIdx) k 0 a (hIn k)
          (tmVerifierCellRange_zero_mem V p)).choice
        choice
        (tmVerifierDecodedStackCellOf V p (tmVerifierMicroTime t actionIdx) k 0 a (hIn k)
          (tmVerifierCellRange_zero_mem V p)).choice_mem
        (by simpa [TMVerifierStackActionReadChoiceMem] using hReadMem)
        (tmVerifierDecodedStackCellOf V p (tmVerifierMicroTime t actionIdx) k 0 a (hIn k)
          (tmVerifierCellRange_zero_mem V p)).atom_true
        (by simpa [TMVerifierStackActionReadAtomTrue] using hRead)
  | load =>
      simp [TMVerifierStackActionBoundaryRead]
  | branch tag =>
      simp [TMVerifierStackActionBoundaryRead]

/-! ### Finite-domain window row effects -/

noncomputable def TMVerifierWindowActionDomainEvidence
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) (a : Assignment) : Prop :=
  ∀ entry, entry ∈ w.actions.zipIdx →
    (∀ k : tmVerifierStackIndex V,
      CNF.Satisfies
        (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t entry.2) k) a) ∧
    (∀ k : tmVerifierStackIndex V,
      CNF.Satisfies
        (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t (entry.2 + 1)) k) a)

noncomputable def TMVerifierWindowActionWellFormedEvidence
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) (a : Assignment) : Prop :=
  ∀ entry, entry ∈ w.actions.zipIdx →
    (∀ k : tmVerifierStackIndex V,
      CNF.Satisfies
        (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t entry.2) k) a) ∧
    (∀ k : tmVerifierStackIndex V,
      CNF.Satisfies
        (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t (entry.2 + 1)) k) a)

theorem TMVerifierWindowActionWellFormedEvidence.toDomainEvidence
    {L : EncodedDecisionProblem}
    {V : TMVerifier L} {p : L.Instance.Carrier × V.Cert.Carrier}
    {t : Nat} {w : TMVerifierStmtWindow V} {a : Assignment}
    (hWF : TMVerifierWindowActionWellFormedEvidence V p t w a) :
    TMVerifierWindowActionDomainEvidence V p t w a := by
  intro entry hentry
  constructor
  · intro k
    exact tmVerifierStackWellFormedCNFAt_satisfies_domains V p
      (tmVerifierMicroTime t entry.2) k a ((hWF entry hentry).1 k)
  · intro k
    exact tmVerifierStackWellFormedCNFAt_satisfies_domains V p
      (tmVerifierMicroTime t (entry.2 + 1)) k a ((hWF entry hentry).2 k)

noncomputable def TMVerifierWindowStackEffectsFinite
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal)
    (a : Assignment)
    (hDomains : TMVerifierWindowActionDomainEvidence V p t w a) :
  Prop :=
  ∀ entry, ∀ hentry : entry ∈ w.actions.zipIdx,
    TMVerifierStackActionBoundaryEffect V B p t entry.2 antecedents a
      (hDomains entry hentry).1 (hDomains entry hentry).2 entry.1

noncomputable def TMVerifierWindowStackReadsFinite
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (p : L.Instance.Carrier × V.Cert.Carrier)
    (t : Nat) (w : TMVerifierStmtWindow V) (a : Assignment)
    (hDomains : TMVerifierWindowActionDomainEvidence V p t w a) :
    Prop :=
  ∀ entry, ∀ hentry : entry ∈ w.actions.zipIdx,
    TMVerifierStackActionBoundaryRead V p t entry.2 a
      (hDomains entry hentry).1 entry.1

theorem tmVerifierWindowStackActionCNFAt_satisfies_finite_effects
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal)
    (a : Assignment)
    (h :
      CNF.Satisfies (tmVerifierWindowStackActionCNFAt V B p t w antecedents) a)
    (hDomains : TMVerifierWindowActionDomainEvidence V p t w a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    TMVerifierWindowStackEffectsFinite V B p t w antecedents a hDomains := by
  intro entry hentry
  exact tmVerifierStackActionCNFBetween_satisfies_boundary_effect V B p t entry.2
    antecedents a entry.1
    (tmVerifierWindowStackActionCNFAt_satisfies_action V B p t w antecedents a h entry
      hentry)
    (hDomains entry hentry).1 (hDomains entry hentry).2 hAntecedents

theorem tmVerifierWindowStackActionCNFAt_satisfies_finite_reads
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal)
    (a : Assignment)
    (h :
      CNF.Satisfies (tmVerifierWindowStackActionCNFAt V B p t w antecedents) a)
    (hDomains : TMVerifierWindowActionDomainEvidence V p t w a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true)
    (hReadMem :
      ∀ entry, ∀ _hentry : entry ∈ w.actions.zipIdx,
        TMVerifierStackActionReadChoiceMem (V := V) entry.1) :
    TMVerifierWindowStackReadsFinite V p t w a hDomains := by
  intro entry hentry
  exact tmVerifierStackActionCNFBetween_satisfies_boundary_read V B p t entry.2
    antecedents a entry.1
    (tmVerifierWindowStackActionCNFAt_satisfies_action V B p t w antecedents a h entry
      hentry)
    (hDomains entry hentry).1 hAntecedents (hReadMem entry hentry)

theorem TMVerifierStackActionReadAtomTrue.readGuardAt
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {t actionIdx : Nat} {act : TMVerifierStackAction V} {a : Assignment}
    (hRead : TMVerifierStackActionReadAtomTrue (tmVerifierMicroTime t actionIdx) a act) :
    ∀ g ∈ act.readGuardAt t actionIdx, g.eval a = true := by
  intro g hg
  cases act with
  | push raw =>
      simp [TMVerifierStackAction.readGuardAt] at hg
  | peek k choice =>
      have hg' :
          g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
            (tmVerifierMicroTime t actionIdx) 0 choice := by
        simpa [TMVerifierStackAction.readGuardAt] using hg
      simpa [hg', TMVerifierStackActionReadAtomTrue] using hRead
  | pop k choice =>
      have hg' :
          g = TMVerifierStackReadChoice.atomAt (V := V) (k := k)
            (tmVerifierMicroTime t actionIdx) 0 choice := by
        simpa [TMVerifierStackAction.readGuardAt] using hg
      simpa [hg', TMVerifierStackActionReadAtomTrue] using hRead
  | load =>
      simp [TMVerifierStackAction.readGuardAt] at hg
  | branch tag =>
      simp [TMVerifierStackAction.readGuardAt] at hg

theorem tmVerifierWindowStackActionCNFAt_satisfies_readGuards
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (w : TMVerifierStmtWindow V) (antecedents : List Literal)
    (a : Assignment)
    (h :
      CNF.Satisfies (tmVerifierWindowStackActionCNFAt V B p t w antecedents) a)
    (hAntecedents : ∀ l ∈ antecedents, l.eval a = true) :
    ∀ g ∈ tmVerifierWindowActionReadGuards t w, g.eval a = true := by
  intro g hg
  rw [tmVerifierWindowActionReadGuards, tmVerifierWindowActionReadGuardsFrom] at hg
  rcases List.mem_flatMap.mp hg with ⟨entry, hentry, hgEntry⟩
  have hAction :
      CNF.Satisfies
        (tmVerifierStackActionCNFBetween V B p
          (tmVerifierMicroTime t entry.2) (tmVerifierMicroTime t (entry.2 + 1))
          antecedents entry.1) a :=
    tmVerifierWindowStackActionCNFAt_satisfies_action V B p t w antecedents a h entry
      hentry
  exact TMVerifierStackActionReadAtomTrue.readGuardAt
    (tmVerifierStackActionCNFBetween_satisfies_read V B p
      (tmVerifierMicroTime t entry.2) (tmVerifierMicroTime t (entry.2 + 1))
      antecedents entry.1 a hAction hAntecedents) g hgEntry

noncomputable def TMVerifierWindowRowFiniteEffect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (hDomains : TMVerifierWindowActionDomainEvidence V p t w a) :
    Prop :=
  (tmVerifierLabelAtom V (t + 1) w.nextLabel).eval a = true ∧
  (tmVerifierStateAtom V (t + 1) w.nextState).eval a = true ∧
  TMVerifierWindowStackEffectsFinite V B p t w
    (tmVerifierWindowAntecedents V t l s w) a hDomains

theorem tmVerifierTransitionWindowCNFAt_satisfies_finite_effect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionWindowCNFAt V B p t l s w) a)
    (hDomains : TMVerifierWindowActionDomainEvidence V p t w a)
    (hAntecedents :
      ∀ g ∈ tmVerifierWindowAntecedents V t l s w, g.eval a = true) :
    TMVerifierWindowRowFiniteEffect V B p t l s w a hDomains := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierWindowControlCNFAt V t l s w)
    (tmVerifierWindowStackActionCNFAt V B p t w (tmVerifierWindowAntecedents V t l s w))
    a).1 (by simpa [tmVerifierTransitionWindowCNFAt] using h)
  have hControl :=
    tmVerifierWindowControlCNFAt_satisfies_next_control V t l s w a hsplit.1
      hAntecedents
  exact ⟨hControl.1, hControl.2,
    tmVerifierWindowStackActionCNFAt_satisfies_finite_effects V B p t w
      (tmVerifierWindowAntecedents V t l s w) a hsplit.2 hDomains hAntecedents⟩

theorem tmVerifierTransitionWindowCNFAt_satisfies_finite_reads
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionWindowCNFAt V B p t l s w) a)
    (hDomains : TMVerifierWindowActionDomainEvidence V p t w a)
    (hAntecedents :
      ∀ g ∈ tmVerifierWindowAntecedents V t l s w, g.eval a = true)
    (hReadMem :
      ∀ entry, ∀ _hentry : entry ∈ w.actions.zipIdx,
        TMVerifierStackActionReadChoiceMem (V := V) entry.1) :
    TMVerifierWindowStackReadsFinite V p t w a hDomains := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierWindowControlCNFAt V t l s w)
    (tmVerifierWindowStackActionCNFAt V B p t w (tmVerifierWindowAntecedents V t l s w))
    a).1 (by simpa [tmVerifierTransitionWindowCNFAt] using h)
  exact tmVerifierWindowStackActionCNFAt_satisfies_finite_reads V B p t w
    (tmVerifierWindowAntecedents V t l s w) a hsplit.2 hDomains hAntecedents hReadMem

theorem tmVerifierTransitionRowCNFAt_satisfies_window_finite_effect
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionRowCNFAt V B p t) a)
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hDomains : TMVerifierWindowActionDomainEvidence V p t w a)
    (hAntecedents :
      ∀ g ∈ tmVerifierWindowAntecedents V t l s w, g.eval a = true) :
    TMVerifierWindowRowFiniteEffect V B p t l s w a hDomains := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierTransitionControlCNFAt V t)
    (tmVerifierTransitionWindowStackCNFAt V B p t ++
      tmVerifierHaltedRowsCNFAt V p t) a).1
      (by simpa [tmVerifierTransitionRowCNFAt] using h)
  have hstack := (CNF.satisfies_append
    (tmVerifierTransitionWindowStackCNFAt V B p t)
    (tmVerifierHaltedRowsCNFAt V p t) a).1 hsplit.2 |>.1
  have hControl :=
    tmVerifierTransitionControlCNFAt_satisfies_window V t l s w a hsplit.1 hl hs hw
  have hStack :=
    tmVerifierTransitionWindowStackCNFAt_satisfies_window V B p t l s w a hstack hl hs hw
  exact tmVerifierTransitionWindowCNFAt_satisfies_finite_effect V B p t l s w a
    (by
      rw [tmVerifierTransitionWindowCNFAt]
      exact (CNF.satisfies_append
        (tmVerifierWindowControlCNFAt V t l s w)
        (tmVerifierWindowStackActionCNFAt V B p t w
          (tmVerifierWindowAntecedents V t l s w)) a).2
        ⟨hControl, hStack⟩)
    hDomains hAntecedents

theorem tmVerifierTransitionRowCNFAt_satisfies_window_finite_reads
    {L : EncodedDecisionProblem}
    (V : TMVerifier L) (B : TMVerifierPushPayloadBoundary V)
    (p : L.Instance.Carrier × V.Cert.Carrier) (t : Nat)
    (l : (tmVerifierTM V).Λ) (s : (tmVerifierTM V).σ)
    (w : TMVerifierStmtWindow V) (a : Assignment)
    (h : CNF.Satisfies (tmVerifierTransitionRowCNFAt V B p t) a)
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (hDomains : TMVerifierWindowActionDomainEvidence V p t w a)
    (hAntecedents :
      ∀ g ∈ tmVerifierWindowAntecedents V t l s w, g.eval a = true) :
    TMVerifierWindowStackReadsFinite V p t w a hDomains := by
  have hsplit := (CNF.satisfies_append
    (tmVerifierTransitionControlCNFAt V t)
    (tmVerifierTransitionWindowStackCNFAt V B p t ++
      tmVerifierHaltedRowsCNFAt V p t) a).1
      (by simpa [tmVerifierTransitionRowCNFAt] using h)
  have hstack := (CNF.satisfies_append
    (tmVerifierTransitionWindowStackCNFAt V B p t)
    (tmVerifierHaltedRowsCNFAt V p t) a).1 hsplit.2 |>.1
  have hControl :=
    tmVerifierTransitionControlCNFAt_satisfies_window V t l s w a hsplit.1 hl hs hw
  have hStack :=
    tmVerifierTransitionWindowStackCNFAt_satisfies_window V B p t l s w a hstack hl hs hw
  exact tmVerifierTransitionWindowCNFAt_satisfies_finite_reads V B p t l s w a
    (by
      rw [tmVerifierTransitionWindowCNFAt]
      exact (CNF.satisfies_append
        (tmVerifierWindowControlCNFAt V t l s w)
        (tmVerifierWindowStackActionCNFAt V B p t w
          (tmVerifierWindowAntecedents V t l s w)) a).2
        ⟨hControl, hStack⟩)
    hDomains hAntecedents
    (fun entry hentry =>
      tmVerifierStmtWindowsAt_zipIdx_action_readChoiceMem V t ((tmVerifierTM V).m l) s hw
        entry hentry)

/-! ### Aggregate-tableau extraction of finite micro-domain effects -/

namespace TMVerifierFixedPairTableauEvidence

theorem windowActionDomainEvidence
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    TMVerifierWindowActionDomainEvidence V p t w a := by
  intro entry hentry
  have hWindow :
      CNF.Satisfies (tmVerifierWindowMicroDomainCNFAt V p t w) a :=
    tmVerifierTransitionMicroDomainCNFAt_satisfies_window V p t l s w a
      (E.transitionMicroDomainRow t ht) hl hs hw
  constructor
  · intro k
    exact tmVerifierWindowMicroDomainCNFAt_satisfies_domain V p t w entry.2 a
      hWindow (tmVerifierWindowActionMicroTimeRange_input_mem V w entry hentry) k
  · intro k
    exact tmVerifierWindowMicroDomainCNFAt_satisfies_domain V p t w (entry.2 + 1) a
      hWindow (tmVerifierWindowActionMicroTimeRange_output_mem V w entry hentry) k

theorem windowActionWellFormedEvidence
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    TMVerifierWindowActionWellFormedEvidence V p t w a := by
  intro entry hentry
  have hWindow :
      CNF.Satisfies (tmVerifierWindowMicroDomainCNFAt V p t w) a :=
    tmVerifierTransitionMicroDomainCNFAt_satisfies_window V p t l s w a
      (E.transitionMicroDomainRow t ht) hl hs hw
  constructor
  · intro k
    exact tmVerifierWindowMicroDomainCNFAt_satisfies_wellFormed V p t w entry.2 a
      hWindow (tmVerifierWindowActionMicroTimeRange_input_mem V w entry hentry) k
  · intro k
    exact tmVerifierWindowMicroDomainCNFAt_satisfies_wellFormed V p t w (entry.2 + 1) a
      hWindow (tmVerifierWindowActionMicroTimeRange_output_mem V w entry hentry) k

theorem windowStartWellFormed
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t 0) k) a := by
  have hWindow :
      CNF.Satisfies (tmVerifierWindowMicroDomainCNFAt V p t w) a :=
    tmVerifierTransitionMicroDomainCNFAt_satisfies_window V p t l s w a
      (E.transitionMicroDomainRow t ht) hl hs hw
  exact tmVerifierWindowMicroDomainCNFAt_satisfies_wellFormed_of_microTime V p t w 0 a
    hWindow (tmVerifierWindowMicroTimeRange_zero_mem V w) k

theorem windowStartDomain
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t 0) k) a :=
  tmVerifierStackWellFormedCNFAt_satisfies_domains V p (tmVerifierMicroTime t 0) k a
    (E.windowStartWellFormed ht hl hs hw k)

theorem windowFinalWellFormed
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierStackWellFormedCNFAt V p (tmVerifierMicroTime t w.actions.length) k)
      a := by
  have hWindow :
      CNF.Satisfies (tmVerifierWindowMicroDomainCNFAt V p t w) a :=
    tmVerifierTransitionMicroDomainCNFAt_satisfies_window V p t l s w a
      (E.transitionMicroDomainRow t ht) hl hs hw
  exact tmVerifierWindowMicroDomainCNFAt_satisfies_wellFormed_of_microTime V p t w
    w.actions.length a hWindow (tmVerifierWindowMicroTimeRange_final_mem V w) k

theorem windowFinalDomain
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {p : L.Instance.Carrier × V.Cert.Carrier}
    {a : Assignment} (E : TMVerifierFixedPairTableauEvidence V B p a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V p)
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierStackCellDomainsCNFAt V p (tmVerifierMicroTime t w.actions.length) k)
      a :=
  tmVerifierStackWellFormedCNFAt_satisfies_domains V p
    (tmVerifierMicroTime t w.actions.length) k a
    (E.windowFinalWellFormed ht hl hs hw k)

theorem transitionWindowFiniteRowEffect
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
    TMVerifierWindowRowFiniteEffect V B p t l s w a
      (E.windowActionDomainEvidence ht hl hs hw) :=
  tmVerifierTransitionRowCNFAt_satisfies_window_finite_effect V B p t l s w a
    (E.transitionRow t ht) hl hs hw (E.windowActionDomainEvidence ht hl hs hw)
    (E.windowAntecedents_true ht hLabel hState hGuards)

theorem transitionWindowFiniteReads
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
    TMVerifierWindowStackReadsFinite V p t w a
      (E.windowActionDomainEvidence ht hl hs hw) :=
  tmVerifierTransitionRowCNFAt_satisfies_window_finite_reads V B p t l s w a
    (E.transitionRow t ht) hl hs hw (E.windowActionDomainEvidence ht hl hs hw)
    (E.windowAntecedents_true ht hLabel hState hGuards)

end TMVerifierFixedPairTableauEvidence

namespace TMVerifierXOnlyTableauSeed

theorem windowActionDomainEvidence
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, wSeed.cert))
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    TMVerifierWindowActionDomainEvidence V (x, wSeed.cert) t w a :=
  wSeed.fixedPairEvidence.windowActionDomainEvidence ht hl hs hw

theorem windowActionWellFormedEvidence
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, wSeed.cert))
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s) :
    TMVerifierWindowActionWellFormedEvidence V (x, wSeed.cert) t w a :=
  wSeed.fixedPairEvidence.windowActionWellFormedEvidence ht hl hs hw

theorem windowStartWellFormed
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, wSeed.cert))
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierStackWellFormedCNFAt V (x, wSeed.cert) (tmVerifierMicroTime t 0) k)
      a :=
  wSeed.fixedPairEvidence.windowStartWellFormed ht hl hs hw k

theorem windowStartDomain
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, wSeed.cert))
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierStackCellDomainsCNFAt V (x, wSeed.cert) (tmVerifierMicroTime t 0) k)
      a :=
  wSeed.fixedPairEvidence.windowStartDomain ht hl hs hw k

theorem windowFinalWellFormed
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, wSeed.cert))
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierStackWellFormedCNFAt V (x, wSeed.cert)
        (tmVerifierMicroTime t w.actions.length) k) a :=
  wSeed.fixedPairEvidence.windowFinalWellFormed ht hl hs hw k

theorem windowFinalDomain
    {L : EncodedDecisionProblem} {V : TMVerifier L}
    {B : TMVerifierPushPayloadBoundary V} {x : L.Instance.Carrier}
    {a : Assignment} (wSeed : TMVerifierXOnlyTableauSeed V B x a)
    {t : Nat} (ht : t ∈ tmVerifierTransitionTimeRange V (x, wSeed.cert))
    {l : (tmVerifierTM V).Λ} {s : (tmVerifierTM V).σ}
    {w : TMVerifierStmtWindow V}
    (hl : l ∈ tmVerifierLabelList V)
    (hs : s ∈ tmVerifierStateList V)
    (hw : w ∈ tmVerifierStmtWindowsAt V t ((tmVerifierTM V).m l) s)
    (k : tmVerifierStackIndex V) :
    CNF.Satisfies
      (tmVerifierStackCellDomainsCNFAt V (x, wSeed.cert)
        (tmVerifierMicroTime t w.actions.length) k) a :=
  wSeed.fixedPairEvidence.windowFinalDomain ht hl hs hw k

theorem transitionWindowFiniteRowEffect
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
    TMVerifierWindowRowFiniteEffect V B (x, wSeed.cert) t l s w a
      (wSeed.windowActionDomainEvidence ht hl hs hw) :=
  wSeed.fixedPairEvidence.transitionWindowFiniteRowEffect ht hl hs hw hLabel hState hGuards

theorem transitionWindowFiniteReads
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
    TMVerifierWindowStackReadsFinite V (x, wSeed.cert) t w a
      (wSeed.windowActionDomainEvidence ht hl hs hw) :=
  wSeed.fixedPairEvidence.transitionWindowFiniteReads ht hl hs hw hLabel hState hGuards

end TMVerifierXOnlyTableauSeed

end SAT
end ComplexityReduction
